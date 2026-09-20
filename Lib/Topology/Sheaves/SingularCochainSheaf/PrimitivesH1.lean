/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.SingularCochainSheaf.Augmentation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Primitives for singular cochains pulled back along a nullhomotopic map

A nullhomotopic map pulls a closed singular cochain back to a coboundary (in degree zero, to a
constant cochain): this is cochain homotopy invariance of singular cohomology, dual to Hatcher,
*Algebraic Topology* Thm. 2.10, and the local input to the exactness of the singular-cochain
resolution (Bredon, *Sheaf Theory* III.1).  Degrees zero and one are developed here.

## Main results

* `TopCat.SingularCochainSheaf.nullhomotopic_pullback_closed_zero`
* `TopCat.SingularCochainSheaf.nullhomotopic_pullback_closed_one`
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Simplicial

namespace TopCat.SingularCochainSheaf

/-- The underlying additive maps of the group of singular cochains. -/
private abbrev Cochains (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) (n : ℕ) :=
  ((AlgebraicTopology.SingularCochains.chains X).X n : Type) →+ A

/-- The chain represented by a single singular simplex. -/
private def simplexChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : (singularSet X) _⦋n⦌) :
    (AlgebraicTopology.SingularCochains.chains X).X n :=
  ((singularSet X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1

/-- An additive cochain regarded as an integer-linear morphism. -/
private def cochainHom (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0})
    (n : ℕ) (c : Cochains X A n) :
    (AlgebraicTopology.SingularCochains.chains X).X n ⟶ ModuleCat.of ℤ A :=
  ConcreteCategory.ofHom (C := ModuleCat ℤ)
    ({ toFun := c
       map_add' := c.map_add
       map_smul' := by
         intro z x
         calc
           c (((AlgebraicTopology.SingularCochains.chains X).X n).isModule.smul z x) =
               c (z • x) := congrArg c (int_smul_eq_zsmul
                 ((AlgebraicTopology.SingularCochains.chains X).X n).isModule z x)
           _ = z • c x := c.map_zsmul z x
           _ = (ModuleCat.of ℤ A).isModule.smul z (c x) :=
             (int_smul_eq_zsmul (ModuleCat.of ℤ A).isModule z (c x)).symm
           _ = (RingHom.id ℤ) z • c x := by rfl } :
      ((AlgebraicTopology.SingularCochains.chains X).X n : Type) →ₗ[ℤ] A)

/-- Evaluation of a cochain on a chain. -/
private def cochainValue (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0})
    (n : ℕ) (c : (AlgebraicTopology.SingularCochains.complex X A).X n)
    (z : (AlgebraicTopology.SingularCochains.chains X).X n) : A := by
  change Cochains X A n at c
  exact c z

/-- Cochains are determined by their values on singular simplices. -/
private theorem cochain_ext (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0})
    (n : ℕ) {c d : (AlgebraicTopology.SingularCochains.complex X A).X n}
    (h : ∀ σ : (singularSet X) _⦋n⦌,
      cochainValue X A n c (simplexChain X n σ) =
        cochainValue X A n d (simplexChain X n σ)) : c = d := by
  change Cochains X A n at c d
  apply AddMonoidHom.ext
  have he : cochainHom X A n c = cochainHom X A n d := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rw [show z = z • (1 : ℤ) by simp, map_smul, map_smul]
    have h1 :
        (((singularSet X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) ≫
          cochainHom X A n c).hom 1 =
        (((singularSet X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) ≫
          cochainHom X A n d).hom 1 := by
      change cochainValue X A n c (simplexChain X n σ) =
        cochainValue X A n d (simplexChain X n σ)
      exact h σ
    exact congrArg (fun a : A => z • a) h1
  intro z
  exact ConcreteCategory.congr_hom he z

/-- Pullback evaluated on a simplex is evaluation on its image simplex. -/
private theorem pullback_simplex {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (f : C(X, Y)) (n : ℕ)
    (c : (AlgebraicTopology.SingularCochains.complex Y A).X n)
    (σ : (singularSet X) _⦋n⦌) :
    cochainValue X A n ((AlgebraicTopology.SingularCochains.pullback A f).f n c)
        (simplexChain X n σ) =
      cochainValue Y A n c
        (simplexChain Y n ((TopCat.toSSet.map (TopCat.ofHom f)).app _ σ)) := by
  change (show Cochains Y A n from c)
      ((chainMap f).f n (simplexChain X n σ)) = _
  exact congrArg (show Cochains Y A n from c) (ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) σ) 1)

/-- A constant zero-cochain takes its defining value on every singular vertex. -/
private theorem constantCochain_simplex (X : Type) [TopologicalSpace X]
    (A : AddCommGrpCat.{0}) (a : A) (σ : (singularSet X) _⦋0⦌) :
    cochainValue X A 0 (constantCochain X A a) (simplexChain X 0 σ) = a := by
  change integerMultiple A a
      ((chainAugmentation X).hom
        (((singularSet X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) = a
  have h := ConcreteCategory.congr_hom (simplex_chainAugmentation X σ) 1
  change (chainAugmentation X).hom
    (((singularSet X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) = 1 at h
  rw [h]
  exact one_zsmul _

/-- On a nonempty space a constant zero-cochain determines its coefficient: the map from `A` to
zero-cochains is injective. -/
theorem constantCochain_injective (X : Type) [TopologicalSpace X] [Nonempty X]
    (A : AddCommGrpCat.{0}) : Function.Injective (constantCochain X A) := by
  intro a b hab
  let σ : (singularSet X) _⦋0⦌ :=
    TopCat.toSSetObj₀Equiv.symm (Classical.choice (inferInstance : Nonempty X))
  have h := congrArg
    (fun c => cochainValue X A 0 c (simplexChain X 0 σ)) hab
  simpa only [constantCochain_simplex] using h

/-- Pulling a zero-cochain back along a constant map gives a constant cochain. -/
private theorem pullback_const_zero {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (y : Y)
    (c : (AlgebraicTopology.SingularCochains.complex Y A).X 0) :
    ∃ a : A, (AlgebraicTopology.SingularCochains.pullback A
      (ContinuousMap.const X y)).f 0 c = constantCochain X A a := by
  let τ : (singularSet Y) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm y
  refine ⟨cochainValue Y A 0 c (simplexChain Y 0 τ), ?_⟩
  apply cochain_ext X A 0
  intro σ
  rw [pullback_simplex, constantCochain_simplex]
  change cochainValue Y A 0 c
      (simplexChain Y 0 (TopCat.toSSetObj₀Equiv.symm y)) =
    cochainValue Y A 0 c (simplexChain Y 0 τ)
  rfl

section Homotopy

universe u

variable {K L : CochainComplex AddCommGrpCat.{u} ℕ} {f g : K ⟶ L}

/-- A closed degree-one cochain is detected by the degree-lowering component of a cochain
homotopy. -/
private theorem homotopy_apply_closed_one (h : _root_.Homotopy f g)
    (c : K.X 1) (hc : K.d 1 2 c = 0) :
    f.f 1 c = L.d 0 1 (h.hom 1 0 c) + g.f 1 c := by
  have he := h.comm 1
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 1 2 from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl)] at he
  have hv := ConcreteCategory.congr_hom he c
  change f.f 1 c = h.hom 2 1 (K.d 1 2 c) +
    L.d 0 1 (h.hom 1 0 c) + g.f 1 c at hv
  rw [hc, map_zero, zero_add] at hv
  exact hv

/-- A closed degree-zero cochain has equal values under homotopic cochain maps. -/
private theorem homotopy_apply_closed_zero (h : _root_.Homotopy f g)
    (c : K.X 0) (hc : K.d 0 1 c = 0) : f.f 0 c = g.f 0 c := by
  have he := h.comm 0
  rw [dNext_eq h.hom (show (ComplexShape.up ℕ).Rel 0 1 from rfl),
    prevD_eq_zero h.hom 0 (by simp)] at he
  have hv := ConcreteCategory.congr_hom he c
  change f.f 0 c = h.hom 1 0 (K.d 0 1 c) + 0 + g.f 0 c at hv
  rw [hc, map_zero, zero_add, zero_add] at hv
  exact hv

end Homotopy

/-- Pullback preserves the cocycle equation. -/
private theorem pullback_closed {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : AddCommGrpCat.{0}) (f : C(X, Y)) (i j : ℕ)
    (c : (AlgebraicTopology.SingularCochains.complex Y A).X i)
    (hc : (AlgebraicTopology.SingularCochains.complex Y A).d i j c = 0) :
    (AlgebraicTopology.SingularCochains.complex X A).d i j
      ((AlgebraicTopology.SingularCochains.pullback A f).f i c) = 0 := by
  have he := ConcreteCategory.congr_hom
    ((AlgebraicTopology.SingularCochains.pullback A f).comm i j) c
  change (AlgebraicTopology.SingularCochains.complex X A).d i j
      ((AlgebraicTopology.SingularCochains.pullback A f).f i c) =
    (AlgebraicTopology.SingularCochains.pullback A f).f j
      ((AlgebraicTopology.SingularCochains.complex Y A).d i j c) at he
  exact he.trans (by rw [hc, map_zero])

private abbrev pointSSet := TopCat.toSSet.obj (TopCat.of Unit)

private def pointSimplex (n : ℕ) : pointSSet _⦋n⦌ :=
  ((TopCat.of Unit).toSSetObjEquiv (.op ⦋n⦌)).symm
    (ContinuousMap.const _ ())

private theorem pointSimplex_eq (n : ℕ) (x y : pointSSet _⦋n⦌) : x = y := by
  apply ((TopCat.of Unit).toSSetObjEquiv (.op ⦋n⦌)).injective
  exact Subsingleton.elim _ _

private def pointChain (n : ℕ) :
    (AlgebraicTopology.SingularCochains.chains Unit).X n :=
  (pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (pointSimplex n)) 1

private theorem pointBoundaryTwo :
    (AlgebraicTopology.SingularCochains.chains Unit).d 2 1 (pointChain 2) =
      pointChain 1 := by
  unfold pointChain
  change
    ((pointSSet.chainComplex (ModuleCat.of ℤ ℤ)).d 2 1).hom
        ((pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (pointSimplex 2)).hom 1) =
      (pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) (pointSimplex 1)).hom 1
  calc
    _ = (∑ i : Fin 3,
        (-1 : ℤ) ^ i.val • pointSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (pointSSet.δ i (pointSimplex 2))).hom 1 := by
      exact congrArg (fun q => q.hom 1)
        (pointSSet.ιChainComplex_d (R := ModuleCat.of ℤ ℤ) (pointSimplex 2))
    _ = _ := by
      have hface (i : Fin 3) : pointSSet.δ i (pointSimplex 2) = pointSimplex 1 :=
        pointSimplex_eq 1 _ _
      simp_rw [hface]
      simp [Fin.sum_univ_succ]

private def addHomToIntLinearMap {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [modM : Module ℤ M] [modN : Module ℤ N]
    (q : M →+ N) : M →ₗ[ℤ] N where
  toFun := q
  map_add' := q.map_add
  map_smul' z x := by
    change q (modM.smul z x) = modN.smul z (q x)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact q.map_zsmul z x

/-- A degree-one cocycle on a one-point space is zero. -/
private theorem cocycle_one_point_zero (A : AddCommGrpCat.{0})
    (c : (AlgebraicTopology.SingularCochains.complex Unit A).X 1)
    (hc : (AlgebraicTopology.SingularCochains.complex Unit A).d 1 2 c = 0) :
    c = 0 := by
  change ((AlgebraicTopology.SingularCochains.chains Unit).X 1 →+ A) at c
  change c.comp
    ((AlgebraicTopology.SingularCochains.chains Unit).d 2 1).hom.toAddMonoidHom = 0 at hc
  have hc_point : c (pointChain 1) = 0 := by
    have h := DFunLike.congr_fun hc (pointChain 2)
    change c ((AlgebraicTopology.SingularCochains.chains Unit).d 2 1
      (pointChain 2)) = 0 at h
    simpa only [pointBoundaryTwo] using h
  have hlin : addHomToIntLinearMap c = 0 := by
    apply LinearMap.ext
    intro z
    change c z = 0
    let q : (AlgebraicTopology.SingularCochains.chains Unit).X 1 ⟶
        ModuleCat.of ℤ A := ModuleCat.ofHom (addHomToIntLinearMap c)
    have hq : q = 0 := by
      apply pointSSet.chainComplex_hom_ext
      intro x
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change c ((pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom m) = 0
      rw [show x = pointSimplex 1 from pointSimplex_eq 1 _ _]
      have hm :
          (pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
              (pointSimplex 1)).hom m =
            m • (pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
              (pointSimplex 1)).hom (1 : ℤ) := by
        simpa using (pointSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (pointSimplex 1)).hom.toAddMonoidHom.map_zsmul m (1 : ℤ)
      rw [hm]
      change c (m • pointChain 1) = 0
      exact (c.map_zsmul m (pointChain 1)).trans (by simp [hc_point])
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hq) z
  apply AddMonoidHom.ext
  intro z
  exact LinearMap.congr_fun hlin z

private theorem pullback_const_closed_one_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (A : AddCommGrpCat.{0})
    (y : Y) (c : (AlgebraicTopology.SingularCochains.complex Y A).X 1)
    (hc : (AlgebraicTopology.SingularCochains.complex Y A).d 1 2 c = 0) :
    (AlgebraicTopology.SingularCochains.pullback A
      (ContinuousMap.const X y)).f 1 c = 0 := by
  let p : C(X, Unit) := ContinuousMap.const X ()
  let q : C(Unit, Y) := ContinuousMap.const Unit y
  let cPoint := (AlgebraicTopology.SingularCochains.pullback A q).f 1 c
  have hcPoint :
      (AlgebraicTopology.SingularCochains.complex Unit A).d 1 2 cPoint = 0 :=
    pullback_closed A q 1 2 c hc
  have hPoint : cPoint = 0 := cocycle_one_point_zero A cPoint hcPoint
  have hcomp := AlgebraicTopology.SingularCochains.pullback_comp A p q
  have happ := ConcreteCategory.congr_hom
    (congrArg (fun t : AlgebraicTopology.SingularCochains.complex Y A ⟶
      AlgebraicTopology.SingularCochains.complex X A => t.f 1) hcomp) c
  change (AlgebraicTopology.SingularCochains.pullback A
      (ContinuousMap.const X y)).f 1 c =
    (AlgebraicTopology.SingularCochains.pullback A p).f 1 cPoint at happ
  exact happ.trans (by rw [hPoint, map_zero])

/-- A nullhomotopic map pulls a closed zero-cochain back to a constant cochain. -/
theorem nullhomotopic_pullback_closed_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (A : AddCommGrpCat.{0})
    (f : C(X, Y)) (hf : f.Nullhomotopic)
    (c : (AlgebraicTopology.SingularCochains.complex Y A).X 0)
    (hc : (AlgebraicTopology.SingularCochains.complex Y A).d 0 1 c = 0) :
    ∃ a : A, (AlgebraicTopology.SingularCochains.pullback A f).f 0 c =
      constantCochain X A a := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  obtain ⟨a, ha⟩ := pullback_const_zero (X := X) A y c
  exact ⟨a, (homotopy_apply_closed_zero
    (AlgebraicTopology.SingularCochains.pullbackHomotopy A H) c hc).trans ha⟩

/-- A nullhomotopic map pulls a closed degree-one cochain back to a coboundary. -/
theorem nullhomotopic_pullback_closed_one {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (A : AddCommGrpCat.{0})
    (f : C(X, Y)) (hf : f.Nullhomotopic)
    (c : (AlgebraicTopology.SingularCochains.complex Y A).X 1)
    (hc : (AlgebraicTopology.SingularCochains.complex Y A).d 1 2 c = 0) :
    ∃ b : (AlgebraicTopology.SingularCochains.complex X A).X 0,
      (AlgebraicTopology.SingularCochains.complex X A).d 0 1 b =
        (AlgebraicTopology.SingularCochains.pullback A f).f 1 c := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let h := AlgebraicTopology.SingularCochains.pullbackHomotopy A H
  refine ⟨h.hom 1 0 c, ?_⟩
  have hconst := pullback_const_closed_one_zero (X := X) A y c hc
  have he := homotopy_apply_closed_one h c hc
  rw [hconst, add_zero] at he
  exact he.symm

end TopCat.SingularCochainSheaf
