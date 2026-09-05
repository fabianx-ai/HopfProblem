/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.OpenCover

/-!
# Ordered indices and intersections for normalized Čech cochains

This file constructs the strictly-increasing fixed-open-cover Čech model in textbook section
CD-04. A degree-`n` index is an order embedding `Fin (n + 1) ↪o ι`, which is exactly a tuple
`i₀ < ... < iₙ`. Its associated open is the intersection of those cover members. Deleting a
vertex gives a face, and the inclusion of the full intersection into a face intersection gives
the restriction direction used by Čech cofaces.

For a coefficient presheaf, the normalized degree-`n` object is the product of its values on
these ordered intersections. The differential is the alternating sum of the cofaces; its square
is zero because the two orders of deleting any pair of vertices cancel.

This file introduces no refinement maps, direct limits, or comparison with derived sheaf
cohomology.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v} [LinearOrder ι]

/-- CD-04's strictly increasing degree-`n` index tuple `i₀ < ... < iₙ`. -/
abbrev OrderedSimplex (ι : Type v) [LinearOrder ι] (n : ℕ) : Type v :=
  Fin (n + 1) ↪o ι

namespace OrderedSimplex

variable {n : ℕ}

/-- CD-04's `k`th face, obtained by deleting the `k`th entry of an ordered tuple. -/
def face (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    OrderedSimplex ι n :=
  (Fin.succAboveOrderEmb k).trans σ

/-- CD-04's deletion face evaluates by skipping the deleted position. -/
@[simp]
theorem face_apply (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2))
    (j : Fin (n + 1)) :
    σ.face k j = σ (k.succAbove j) :=
  rfl

/-- CD-04's face coherence: deleting two entries in either order gives the same ordered tuple,
with the second pair of positions adjusted by `predAbove` and `succAbove`. -/
theorem face_face_swap (σ : OrderedSimplex ι (n + 2))
    (i : Fin (n + 2)) (j : Fin (n + 3)) :
    (σ.face j).face i =
      (σ.face (j.succAbove i)).face (i.predAbove j) := by
  ext k
  exact congrFun (Fin.removeNth_removeNth_eq_swap (fun a => σ a) i j) k

/-- CD-04's open `U_{i₀} ∩ ... ∩ U_{iₙ}` associated to an ordered index tuple. -/
def intersection (U : ι → TopologicalSpace.Opens X) (σ : OrderedSimplex ι n) :
    TopologicalSpace.Opens X :=
  ⨅ j, U (σ j)

/-- CD-04's ordered open intersection has the expected underlying set. -/
@[simp]
theorem coe_intersection (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι n) :
    ((σ.intersection U : TopologicalSpace.Opens X) : Set X) =
      ⋂ j, (U (σ j) : Set X) :=
  TopologicalSpace.Opens.coe_iInf _

/-- CD-04's pointwise membership criterion for an ordered open intersection. -/
@[simp]
theorem mem_intersection_iff (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι n) (x : X) :
    x ∈ σ.intersection U ↔ ∀ j, x ∈ U (σ j) := by
  change x ∈ ((σ.intersection U : TopologicalSpace.Opens X) : Set X) ↔ _
  rw [coe_intersection]
  exact Set.mem_iInter

/-- CD-04's ordered intersection is contained in each indexed cover member. -/
theorem intersection_le (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι n) (j : Fin (n + 1)) :
    σ.intersection U ≤ U (σ j) :=
  iInf_le _ j

/-- CD-04's full intersection is contained in every face intersection. -/
theorem intersection_le_face (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    σ.intersection U ≤ (σ.face k).intersection U := by
  apply le_iInf
  intro j
  exact σ.intersection_le U (k.succAbove j)

/-- CD-04's inclusion from a full ordered intersection to a face intersection. After applying a
presheaf contravariantly, this is the restriction map occurring in the `k`th Čech coface. -/
def faceHom (U : ι → TopologicalSpace.Opens X)
    (σ : OrderedSimplex ι (n + 1)) (k : Fin (n + 2)) :
    σ.intersection U ⟶ (σ.face k).intersection U :=
  CategoryTheory.homOfLE (σ.intersection_le_face U k)

end OrderedSimplex

namespace OrderedCech

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]
variable {A : Type w} [Category.{t} A] [HasProducts.{v} A]

/-- CD-04's normalized degree-`n` Čech cochain object: the product of the coefficient
presheaf over the intersections indexed by strictly increasing `(n + 1)`-tuples. -/
@[implicit_reducible]
noncomputable def object (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) : A :=
  ∏ᶜ fun σ : OrderedSimplex ι n => P.obj (op (σ.intersection U))

/-- Projection from the normalized degree-`n` Čech object to the component indexed by an
ordered simplex. -/
@[implicit_reducible]
noncomputable def π (P : TopCat.Presheaf A X) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (σ : OrderedSimplex ι n) :
    object P U n ⟶ P.obj (op (σ.intersection U)) :=
  Limits.Pi.π _ σ

/-- The `k`th Čech coface. Its component at an ordered `(n + 1)`-simplex restricts the
component indexed by the face obtained by deleting `k`. -/
noncomputable def coface (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) (k : Fin (n + 2)) :
    object P U n ⟶ object P U (n + 1) :=
  Limits.Pi.map' (fun σ => σ.face k) fun σ => P.map (σ.faceHom U k).op

/-- The component formula for an ordered Čech coface. -/
@[reassoc (attr := simp)]
theorem coface_π (P : TopCat.Presheaf A X) (U : ι → TopologicalSpace.Opens X)
    (n : ℕ) (k : Fin (n + 2)) (σ : OrderedSimplex ι (n + 1)) :
    coface P U n k ≫ π P U (n + 1) σ =
      π P U n (σ.face k) ≫ P.map (σ.faceHom U k).op :=
  Limits.Pi.map'_comp_π _ _ _

/-- The coface identity, expressed without an inequality by adjusting the two deleted
positions with `predAbove` and `succAbove`. -/
theorem coface_comp_coface (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ)
    (i : Fin (n + 2)) (j : Fin (n + 3)) :
    coface P U n i ≫ coface P U (n + 1) j =
      coface P U n (i.predAbove j) ≫
        coface P U (n + 1) (j.succAbove i) := by
  dsimp only [coface]
  rw [Limits.Pi.map'_comp_map', Limits.Pi.map'_comp_map']
  apply Limits.Pi.map'_eq
      (funext fun σ => σ.face_face_swap i j)
  intro σ
  let hopen :
      op (((σ.face (j.succAbove i)).face (i.predAbove j)).intersection U) =
        op (((σ.face j).face i).intersection U) :=
    congrArg (fun τ => op (τ.intersection U)) (σ.face_face_swap i j).symm
  rw [← eqToHom_map P hopen]
  simp only [← P.map_comp]
  congr 1

variable [Preadditive A]

/-- The normalized ordered Čech differential, the alternating sum of the cofaces. -/
noncomputable def differential (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    object P U n ⟶ object P U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • coface P U n k

/-- The component formula for the normalized ordered Čech differential. -/
@[reassoc]
theorem differential_π (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ)
    (σ : OrderedSimplex ι (n + 1)) :
    differential P U n ≫ π P U (n + 1) σ =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (π P U n (σ.face k) ≫ P.map (σ.faceHom U k).op) := by
  simp only [differential, Preadditive.sum_comp, Preadditive.zsmul_comp, coface_π]

/-- Consecutive normalized ordered Čech differentials compose to zero. Each pair of deleted
vertices cancels with the deletion in the opposite order. -/
theorem differential_comp_differential (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    differential P U n ≫ differential P U (n + 1) = 0 := by
  dsimp only [differential]
  rw [Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, ← Finset.sum_product']
  let Q := Fin (n + 2) × Fin (n + 3)
  let S : Finset Q := {ij : Q | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : Q, ij ∈ S → Q := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp [φ, pow_succ, mul_comm]
    · have hji : j ≤ Fin.castSucc i := by
        exact Fin.le_iff_val_le_val.mpr (Finset.mem_filter.mp hij).right
      rw [coface_comp_coface P U n i j]
      simp only [Fin.predAbove_of_le_castSucc _ _ hji,
        Fin.succAbove_of_le_castSucc _ _ hji]
      rfl

/-- The normalized ordered Čech cochain complex of one indexed open family. -/
@[implicit_reducible]
noncomputable def complex (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) : CochainComplex A ℕ :=
  CochainComplex.of (object P U) (differential P U)
    (differential_comp_differential P U)

@[simp]
theorem complex_X (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    (complex P U).X n = object P U n :=
  rfl

@[simp]
theorem complex_d (P : TopCat.Presheaf A X)
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    (complex P U).d n (n + 1) = differential P U n :=
  CochainComplex.of_d _ _ n

end OrderedCech

end TopologicalSpace.OpenCover
