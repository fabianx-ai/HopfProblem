/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.GroupTheory.GeneratingSet
public import Lib.LinearAlgebra.CyclicAverage
public import Lib.LinearAlgebra.FreeModule.RankTwoCokernel
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Two-exceptional-fibre gluing arithmetic

This proof-owned adapter specializes reusable rank-two cokernel and commuting-generator lemmas to
the relation data of Theorem 6.8. It also retains the paper-facing presentation and projected-seed
names. No assertion about the analytic construction or a complex structure on the six-sphere is
made here.
-/

@[expose] public section

namespace S6.TwoExceptionalGluing

open Module

/-- The defect integer in the two-exceptional-fibre relation matrix. -/
def gluingDefect (m n : ℕ) (ell0 ellM ellN : ℤ) : ℤ :=
  (m : ℤ) * (n : ℤ) * ell0 - (n : ℤ) * ellM - (m : ℤ) * ellN

/-- The common projected-seed exponents `(0, 1, -1)` have defect `m - n`. -/
theorem gluingDefect_common_projected_seed (m n : ℕ) :
    gluingDefect m n 0 1 (-1) = (m : ℤ) - (n : ℤ) := by
  simp [gluingDefect]
  ring

/-- Consecutive exceptional orders give unit defect. -/
theorem gluingDefect_consecutive (m : ℕ) :
    gluingDefect m (m + 1) 0 1 (-1) = -1 := by
  rw [gluingDefect_common_projected_seed]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The matrix of the two remaining relations on `(x, c)` after eliminating `y`. -/
def relationMatrix (m n : ℕ) (ell0 ellM ellN : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(m : ℤ), (n : ℤ); -ellM, ellN - (n : ℤ) * ell0]

/-- The two remaining relations on `(x, c)` after eliminating `y`. -/
def relationMap (m n : ℕ) (ell0 ellM ellN : ℤ) :
    (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun z :=
    ((m : ℤ) * z.1 + (n : ℤ) * z.2,
      -ellM * z.1 + (ellN - (n : ℤ) * ell0) * z.2)
  map_add' u v := by ext <;> simp <;> ring
  map_smul' r u := by ext <;> simp <;> ring

/-- The paper's relation map is the linear map represented by `relationMatrix` in the standard
product basis. -/
theorem relationMap_eq_toLin (m n : ℕ) (ell0 ellM ellN : ℤ) :
    relationMap m n ell0 ellM ellN =
      Matrix.toLin (Basis.finTwoProd ℤ) (Basis.finTwoProd ℤ)
        (relationMatrix m n ell0 ellM ellN) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext <;>
    simp [relationMap, relationMatrix, Matrix.toLin_finTwoProd_apply]

/-- The abelian relation group associated to the two-exceptional presentation. -/
abbrev GluingCokernel (m n : ℕ) (ell0 ellM ellN : ℤ) :=
  (ℤ × ℤ) ⧸ LinearMap.range (relationMap m n ell0 ellM ellN)

/-- Smith reduction of the paper's relation cokernel to the cyclic factor determined by its
defect. The integer-linear-algebra proof is supplied by the reusable rank-two cokernel theorem. -/
noncomputable def gluingCokernelEquivZMod {m n : ℕ} (hcop : m.Coprime n)
    (ell0 ellM ellN : ℤ) :
    GluingCokernel m n ell0 ellM ellN ≃+
      ZMod (gluingDefect m n ell0 ellM ellN).natAbs := by
  have hrange : LinearMap.range (relationMap m n ell0 ellM ellN) =
      LinearMap.range (Matrix.toLin (Basis.finTwoProd ℤ) (Basis.finTwoProd ℤ)
        (relationMatrix m n ell0 ellM ellN)) :=
    congrArg LinearMap.range (relationMap_eq_toLin m n ell0 ellM ellN)
  let erange := Submodule.quotEquivOfEq _ _ hrange
  let e := Matrix.quotientRangeToLinEquivZModOfIsCoprime (Basis.finTwoProd ℤ)
    (relationMatrix m n ell0 ellM ellN) hcop.isCoprime
  have hdet : (relationMatrix m n ell0 ellM ellN).det =
      -gluingDefect m n ell0 ellM ellN := by
    simp [relationMatrix, Matrix.det_fin_two, gluingDefect]
    ring
  rw [hdet, Int.natAbs_neg] at e
  exact (erange.trans e).toAddEquiv

/-- Multiplicative form of the abelian gluing group. -/
abbrev GluingGroup (m n : ℕ) (ell0 ellM ellN : ℤ) :=
  Multiplicative (GluingCokernel m n ell0 ellM ellN)

/-- The gluing group is abelian. -/
instance gluingGroupCommGroup (m n : ℕ) (ell0 ellM ellN : ℤ) :
    CommGroup (GluingGroup m n ell0 ellM ellN) := inferInstance

/-- Multiplicative classification of the gluing group by the defect. -/
noncomputable def gluingGroupEquivZMod {m n : ℕ} (hcop : m.Coprime n)
    (ell0 ellM ellN : ℤ) :
    GluingGroup m n ell0 ellM ellN ≃*
      Multiplicative (ZMod (gluingDefect m n ell0 ellM ellN).natAbs) :=
  AddEquiv.toMultiplicative (gluingCokernelEquivZMod hcop ell0 ellM ellN)

/-- When the defect vanishes, the relation cokernel is infinite cyclic. -/
noncomputable def gluingCokernelEquivIntOfDefectEqZero {m n : ℕ} (hcop : m.Coprime n)
    (ell0 ellM ellN : ℤ) (hp : gluingDefect m n ell0 ellM ellN = 0) :
    GluingCokernel m n ell0 ellM ellN ≃+ ℤ := by
  let e := gluingCokernelEquivZMod hcop ell0 ellM ellN
  have hp' : (gluingDefect m n ell0 ellM ellN).natAbs = 0 := by simp [hp]
  rw [hp'] at e
  exact e

/-- Unit defect makes the relation cokernel trivial. -/
theorem gluingCokernel_subsingleton_of_defect_natAbs_eq_one {m n : ℕ}
    (hcop : m.Coprime n) (ell0 ellM ellN : ℤ)
    (hp : (gluingDefect m n ell0 ellM ellN).natAbs = 1) :
    Subsingleton (GluingCokernel m n ell0 ellM ellN) := by
  let e := gluingCokernelEquivZMod hcop ell0 ellM ellN
  rw [hp] at e
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-- For consecutive orders and common projected-seed exponents, the relation cokernel is trivial. -/
theorem consecutive_gluingCokernel_subsingleton (m : ℕ) :
    Subsingleton (GluingCokernel m (m + 1) 0 1 (-1)) := by
  apply gluingCokernel_subsingleton_of_defect_natAbs_eq_one
  · simp
  · rw [gluingDefect_consecutive]
    simp

section GroupRelations

variable {G : Type*} [Group G]

/--
The decisive nonabelian step in the two-exceptional presentation: if `c, x, y` generate a group,
`c` is central, and `x * y` is a power of `c`, then the whole group is abelian. The remaining
power relations are needed for the cyclic classification, but not for commutativity.
-/
theorem isMulCommutative_of_twoExceptionalRelations (c x y : G) (ell0 : ℤ)
    (hc : c ∈ Subgroup.center G) (hxy : x * y = c ^ ell0)
    (hgen : Subgroup.closure ({c, x, y} : Set G) = ⊤) : IsMulCommutative G := by
  have hxyCenter : x * y ∈ Subgroup.center G := by
    rw [hxy]
    exact Subgroup.zpow_mem _ hc ell0
  have hxyComm : x * y = y * x := by
    apply mul_left_cancel (a := x)
    calc
      x * (x * y) = (x * y) * x := Subgroup.mem_center_iff.mp hxyCenter x
      _ = x * (y * x) := mul_assoc x y x
  have hcomm : ∀ a ∈ ({c, x, y} : Set G), ∀ b ∈ ({c, x, y} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | rfl
      | exact (Subgroup.mem_center_iff.mp hc _).symm
      | exact Subgroup.mem_center_iff.mp hc _
      | exact hxyComm
      | exact hxyComm.symm
  exact Subgroup.isMulCommutative_of_closure_eq_top hgen hcomm

end GroupRelations

section PresentedGroup

/-- The three generators in the two-exceptional group presentation. -/
inductive GluingGenerator
  | central
  | first
  | second
  deriving DecidableEq

/--
The five relation words: `c` commutes with `x` and `y`, followed by the seam relation and the two
exceptional-power relations.
-/
def gluingRelations (m n : ℕ) (ell0 ellM ellN : ℤ) : Set (FreeGroup GluingGenerator) :=
  {FreeGroup.of .central * FreeGroup.of .first *
      (FreeGroup.of .first * FreeGroup.of .central)⁻¹,
    FreeGroup.of .central * FreeGroup.of .second *
      (FreeGroup.of .second * FreeGroup.of .central)⁻¹,
    FreeGroup.of .first * FreeGroup.of .second * (FreeGroup.of .central ^ ell0)⁻¹,
    FreeGroup.of .first ^ m * (FreeGroup.of .central ^ ellM)⁻¹,
    FreeGroup.of .second ^ n * (FreeGroup.of .central ^ ellN)⁻¹}

/-- The literal group presentation used in the two-exceptional gluing calculation. -/
abbrev PresentedGluingGroup (m n : ℕ) (ell0 ellM ellN : ℤ) :=
  PresentedGroup (gluingRelations m n ell0 ellM ellN)

/-- The literal presented group is abelian; this is the nonabelian half of Theorem 6.8. -/
theorem presentedGluingGroup_isMulCommutative (m n : ℕ) (ell0 ellM ellN : ℤ) :
    IsMulCommutative (PresentedGluingGroup m n ell0 ellM ellN) := by
  let c : PresentedGluingGroup m n ell0 ellM ellN := PresentedGroup.of .central
  let x : PresentedGluingGroup m n ell0 ellM ellN := PresentedGroup.of .first
  let y : PresentedGluingGroup m n ell0 ellM ellN := PresentedGroup.of .second
  have relation_eq_one {w : FreeGroup GluingGenerator}
      (hw : w ∈ gluingRelations m n ell0 ellM ellN) :
      PresentedGroup.mk (gluingRelations m n ell0 ellM ellN) w = 1 :=
    PresentedGroup.one_of_mem hw
  have hcx : c * x = x * c := by
    apply eq_of_mul_inv_eq_one
    simpa only [map_mul, map_inv, PresentedGroup.of, c, x] using
      (relation_eq_one (show FreeGroup.of .central * FreeGroup.of .first *
          (FreeGroup.of .first * FreeGroup.of .central)⁻¹ ∈
            gluingRelations m n ell0 ellM ellN by simp [gluingRelations]))
  have hcy : c * y = y * c := by
    apply eq_of_mul_inv_eq_one
    simpa only [map_mul, map_inv, PresentedGroup.of, c, y] using
      (relation_eq_one (show FreeGroup.of .central * FreeGroup.of .second *
          (FreeGroup.of .second * FreeGroup.of .central)⁻¹ ∈
            gluingRelations m n ell0 ellM ellN by simp [gluingRelations]))
  have hxy : x * y = c ^ ell0 := by
    apply eq_of_mul_inv_eq_one
    simpa only [map_mul, map_inv, map_zpow, PresentedGroup.of, c, x, y] using
      (relation_eq_one (show FreeGroup.of .first * FreeGroup.of .second *
          (FreeGroup.of .central ^ ell0)⁻¹ ∈
            gluingRelations m n ell0 ellM ellN by simp [gluingRelations]))
  have hgen : Subgroup.closure ({c, x, y} : Set (PresentedGluingGroup m n ell0 ellM ellN)) = ⊤ := by
    rw [← PresentedGroup.closure_range_of (gluingRelations m n ell0 ellM ellN)]
    congr 1
    ext g
    constructor
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨.central, rfl⟩
      · exact ⟨.first, rfl⟩
      · exact ⟨.second, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i <;> simp [c, x, y]
  have hc : c ∈ Subgroup.center (PresentedGluingGroup m n ell0 ellM ellN) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.closure ({c, x, y} :
        Set (PresentedGluingGroup m n ell0 ellM ellN)) := by rw [hgen]; trivial
    have hle : Subgroup.closure ({c, x, y} :
        Set (PresentedGluingGroup m n ell0 ellM ellN)) ≤ Subgroup.centralizer {c} :=
      (Subgroup.closure_le _).mpr fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hcx.symm
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hcy.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  exact isMulCommutative_of_twoExceptionalRelations c x y ell0 hc hxy hgen

end PresentedGroup

section ProjectedSeed

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/--
An invariant observable evaluates a common seed and its two oppositely signed cyclic projections
as `(1, -1)`. This is the abstract averaging input behind the exponent triple `(0, 1, -1)`.
-/
theorem common_projected_seed_observables (m n : ℕ) [Invertible (m : ℚ)] [Invertible (n : ℚ)]
    (A B : Module.End ℚ M) (lambda : M →ₗ[ℚ] ℚ) (g : M)
    (hA : lambda.comp A = lambda) (hB : lambda.comp B = lambda) (hg : lambda g = 1) :
    lambda (Module.End.cyclicAverage m A g) = 1 ∧
      lambda (-Module.End.cyclicAverage n B g) = -1 := by
  constructor
  · have h := DFunLike.congr_fun
      (Module.End.comp_cyclicAverage (m := m) lambda hA) g
    simpa only [LinearMap.comp_apply, hg] using h
  · have h := DFunLike.congr_fun
      (Module.End.comp_cyclicAverage (m := n) lambda hB) g
    simp only [LinearMap.comp_apply] at h
    rw [map_neg, h, hg]

end ProjectedSeed

end S6.TwoExceptionalGluing
