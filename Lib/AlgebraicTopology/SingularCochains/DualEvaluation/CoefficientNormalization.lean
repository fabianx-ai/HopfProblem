/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.SingularCochains.DualEvaluation.Free

/-!
# Coefficient-normalized Kronecker evaluation

This file transports additive Kronecker evaluation through a chosen integral-linear coefficient
equivalence and proves that the transported evaluation remains natural for chain maps.  It also
records the normalization `ULift ℤ ≃ₗ[ℤ] ℤ` of the coefficient group and the corresponding
universal coefficient statement for native singular chains.

## References

* [A. Hatcher, *Algebraic topology*][hatcher2002], §3.1 and Theorem 3.2.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT

universe v w

variable (A : AddCommGrpCat.{w})

/-- Transport additive functionals through a chosen linear coefficient equivalence. -/
def dualCoefficientEquiv
    {B : Type w} {M : Type*} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M]
    (e : A ≃ₗ[ℤ] B) :
    (M →+ A) ≃+ (M →ₗ[ℤ] B) where
  toFun phi := e.toLinearMap.comp (addHomToIntLinear phi)
  invFun psi := (e.symm.toLinearMap.comp psi).toAddMonoidHom
  left_inv phi := by
    apply AddMonoidHom.ext
    intro x
    exact e.symm_apply_apply (phi x)
  right_inv psi := by
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply (psi x)
  map_add' phi psi := by
    apply LinearMap.ext
    intro x
    exact e.map_add (phi x) (psi x)

/-- The transported functional is the original one followed by the coefficient equivalence. -/
@[simp]
theorem dualCoefficientEquiv_apply_apply
    {B : Type w} {M : Type*} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M]
    (e : A ≃ₗ[ℤ] B) (phi : M →+ A) (x : M) :
    dualCoefficientEquiv A e phi x = e (phi x) := rfl

/-- Precomposition on integral-linear maps, for an arbitrary displayed integral-module
structure on the codomain. -/
def precomposeLinear
    {B M N : Type*} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) : (N →ₗ[ℤ] B) →ₗ[ℤ] (M →ₗ[ℤ] B) where
  toFun phi := phi.comp f
  map_add' phi psi := by ext; rfl
  map_smul' z phi := by ext; rfl

/-- Precomposition acts on a linear functional by composing it with the given map. -/
@[simp]
theorem precomposeLinear_apply
    {B M N : Type*} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (phi : N →ₗ[ℤ] B) (x : M) :
    precomposeLinear f phi x = phi (f x) := rfl

/-- For literal integer-valued functionals, generic precomposition is Mathlib's algebraic dual
map. -/
theorem precomposeLinear_int_eq_dualMap
    {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    precomposeLinear (B := ℤ) f = f.dualMap := by
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro x
  rfl

variable (K : ChainComplex (ModuleCat.{v} ℤ) ℕ)

/-- Kronecker evaluation with its coefficient target transported through a chosen linear
equivalence. -/
def cohomologyEvaluationAlongCoefficient
    {B : Type w} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ) :
    (dualComplex A K).homology (n + 1) ⟶
      AddCommGrpCat.of (K.homology (n + 1) →ₗ[ℤ] B) :=
  cohomologyEvaluation A K n ≫
    AddCommGrpCat.ofHom (dualCoefficientEquiv A e).toAddMonoidHom

/-- The transported Kronecker evaluation is the original evaluation followed by the coefficient
equivalence. -/
@[simp]
theorem cohomologyEvaluationAlongCoefficient_apply
    {B : Type w} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ)
    (a : (dualComplex A K).homology (n + 1))
    (x : K.homology (n + 1)) :
    cohomologyEvaluationAlongCoefficient A K e n a x =
      e (cohomologyEvaluation A K n a x) := rfl

variable {K L : ChainComplex (ModuleCat.{v} ℤ) ℕ}

/-- Coefficient-normalized Kronecker evaluation remains contravariantly natural for chain maps. -/
theorem cohomologyEvaluationAlongCoefficient_natural
    {B : Type w} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (dualMap A f) (n + 1) ≫
        cohomologyEvaluationAlongCoefficient A K e n =
      cohomologyEvaluationAlongCoefficient A L e n ≫
        AddCommGrpCat.ofHom
          (precomposeLinear
            (HomologicalComplex.homologyMap f (n + 1)).hom).toAddMonoidHom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LinearMap.ext
  intro x
  change e (cohomologyEvaluation A K n
      (HomologicalComplex.homologyMap (dualMap A f) (n + 1) a) x) =
    e (cohomologyEvaluation A L n a
      (HomologicalComplex.homologyMap f (n + 1) x))
  have h := ConcreteCategory.congr_hom
    (cohomologyEvaluation_natural A f n) a
  exact congrArg e (congrArg (fun phi ↦ phi x) h)

section FreeChains

variable [∀ k, Module.Free ℤ (K.X k)]

/-- Free-chain form of coefficient-normalized local UCT. -/
theorem cohomologyEvaluationAlongCoefficient_isIso_of_free_of_projective
    {B : Type w} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ)
    [Module.Projective ℤ (K.homology n)] :
    IsIso (cohomologyEvaluationAlongCoefficient A K e n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (dualCoefficientEquiv A e).bijective.comp
    ((ConcreteCategory.isIso_iff_bijective
      (cohomologyEvaluation A K n)).mp
        (cohomologyEvaluation_isIso_of_free_of_projective A K n))

end FreeChains

/-- The normalization sending the small coefficient group `ULift ℤ` back to literal integers. -/
abbrev uliftIntCoefficientEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ :=
  ULift.moduleEquiv

/-- Positive-degree integral evaluation with the small `ULift ℤ` coefficient group
normalized to literal integer-valued functionals. -/
abbrev uliftIntCohomologyEvaluation
    (K : ChainComplex (ModuleCat.{v} ℤ) ℕ) (n : ℕ) :=
  cohomologyEvaluationAlongCoefficient
    (AddCommGrpCat.of (ULift.{0} ℤ)) K uliftIntCoefficientEquiv n

/-- The `ULift ℤ`-normalized evaluation is the original evaluation followed by `ULift.down`. -/
theorem uliftIntCohomologyEvaluation_apply
    (K : ChainComplex (ModuleCat.{v} ℤ) ℕ) (n : ℕ)
    (a : (dualComplex (AddCommGrpCat.of (ULift.{0} ℤ)) K).homology (n + 1))
    (x : K.homology (n + 1)) :
    uliftIntCohomologyEvaluation K n a x =
      (cohomologyEvaluation (AddCommGrpCat.of (ULift.{0} ℤ)) K n a x).down := by
  rfl

/-- The `ULift ℤ → ℤ` normalization commutes with contravariant pullback along every
integral chain map. -/
theorem uliftIntCohomologyEvaluation_natural
    {K L : ChainComplex (ModuleCat.{v} ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (dualMap (AddCommGrpCat.of (ULift.{0} ℤ)) f) (n + 1) ≫
        uliftIntCohomologyEvaluation K n =
      uliftIntCohomologyEvaluation L n ≫
        AddCommGrpCat.ofHom
          (precomposeLinear
            (HomologicalComplex.homologyMap f (n + 1)).hom).toAddMonoidHom := by
  exact cohomologyEvaluationAlongCoefficient_natural
    (AddCommGrpCat.of (ULift.{0} ℤ)) uliftIntCoefficientEquiv f n

/-- Native singular-chain form of the coefficient-normalized UCT. -/
theorem singularUliftIntCohomologyEvaluation_isIso_of_projective
    (X : Type) [TopologicalSpace X] (n : ℕ)
    [Module.Projective ℤ ((chains X).homology n)] :
    IsIso (uliftIntCohomologyEvaluation (chains X) n) := by
  exact @cohomologyEvaluationAlongCoefficient_isIso_of_free_of_projective
    (AddCommGrpCat.of (ULift.{0} ℤ)) (chains X)
      (fun k ↦ singularChains_free X k) ℤ inferInstance inferInstance
      uliftIntCoefficientEquiv n inferInstance

/-- The contravariant map on `ULift ℤ` dual-complex cohomology is injective whenever the
original map on homology in the same positive degree is surjective and the source cohomology's
preceding homology is projective. -/
theorem uliftIntDualHomologyMap_injective_of_homologyMap_surjective
    {K L : ChainComplex (ModuleCat.{v} ℤ) ℕ}
    [∀ k, Module.Free ℤ (L.X k)] (f : K ⟶ L) (n : ℕ)
    [Module.Projective ℤ (L.homology n)]
    (h : Function.Surjective (HomologicalComplex.homologyMap f (n + 1))) :
    Function.Injective (HomologicalComplex.homologyMap
      (dualMap (AddCommGrpCat.of (ULift.{0} ℤ)) f) (n + 1)) := by
  let eX := uliftIntCohomologyEvaluation K n
  let eY := uliftIntCohomologyEvaluation L n
  let fH := HomologicalComplex.homologyMap f (n + 1)
  have hfH : Function.Surjective fH := h
  have hdual : Function.Injective (precomposeLinear (B := ℤ) fH.hom) := by
    rw [precomposeLinear_int_eq_dualMap]
    exact LinearMap.dualMap_injective_of_surjective hfH
  have heYIso : IsIso eY :=
    cohomologyEvaluationAlongCoefficient_isIso_of_free_of_projective
      (K := L) (AddCommGrpCat.of (ULift.{0} ℤ)) uliftIntCoefficientEquiv n
  have heYInjective : Function.Injective eY :=
    ((ConcreteCategory.isIso_iff_bijective eY).mp heYIso).1
  intro a b hab
  have heX :
      eX
          (HomologicalComplex.homologyMap
            (dualMap (AddCommGrpCat.of (ULift.{0} ℤ)) f) (n + 1) a) =
        eX
          (HomologicalComplex.homologyMap
            (dualMap (AddCommGrpCat.of (ULift.{0} ℤ)) f) (n + 1) b) :=
    congrArg eX hab
  have hnat := uliftIntCohomologyEvaluation_natural f n
  have hnatA := ConcreteCategory.congr_hom hnat a
  have hnatB := ConcreteCategory.congr_hom hnat b
  simp only [ConcreteCategory.comp_apply] at hnatA hnatB
  change eX
      (HomologicalComplex.homologyMap
        (dualMap (AddCommGrpCat.of (ULift.{0} ℤ)) f) (n + 1) a) =
      precomposeLinear fH.hom (eY a) at hnatA
  change eX
      (HomologicalComplex.homologyMap
        (dualMap (AddCommGrpCat.of (ULift.{0} ℤ)) f) (n + 1) b) =
      precomposeLinear fH.hom (eY b) at hnatB
  have hpre : precomposeLinear fH.hom (eY a) =
      precomposeLinear fH.hom (eY b) := by
    simpa only [eX, eY, fH] using hnatA.symm.trans (heX.trans hnatB)
  have heY : eY a = eY b := hdual hpre
  exact heYInjective heY

end AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT
