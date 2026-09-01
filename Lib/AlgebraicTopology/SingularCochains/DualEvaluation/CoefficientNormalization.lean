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
records the repository convention `ULift ℤ ≃ₗ[ℤ] ℤ` and the corresponding local UCT for
native singular chains.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT

variable (A : AddCommGrpCat.{0})

/-- Transport additive functionals through a chosen linear coefficient equivalence. -/
def dualCoefficientEquiv
    {B M : Type} [AddCommGroup B] [Module ℤ B]
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

@[simp]
theorem dualCoefficientEquiv_apply_apply
    {B M : Type} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M]
    (e : A ≃ₗ[ℤ] B) (phi : M →+ A) (x : M) :
    dualCoefficientEquiv A e phi x = e (phi x) := rfl

/-- Precomposition on integral-linear maps, for an arbitrary displayed integral-module
structure on the codomain. -/
def precomposeLinear
    {B M N : Type} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) : (N →ₗ[ℤ] B) →ₗ[ℤ] (M →ₗ[ℤ] B) where
  toFun phi := phi.comp f
  map_add' phi psi := by ext; rfl
  map_smul' z phi := by ext; rfl

@[simp]
theorem precomposeLinear_apply
    {B M N : Type} [AddCommGroup B] [Module ℤ B]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (phi : N →ₗ[ℤ] B) (x : M) :
    precomposeLinear f phi x = phi (f x) := rfl

/-- For literal integer-valued functionals, generic precomposition is Mathlib's algebraic dual
map. -/
theorem precomposeLinear_int_eq_dualMap
    {M N : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    precomposeLinear (B := ℤ) f = f.dualMap := by
  apply LinearMap.ext
  intro phi
  apply LinearMap.ext
  intro x
  rfl

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- Kronecker evaluation with its coefficient target transported through a chosen linear
equivalence. -/
def cohomologyEvaluationAlongCoefficient
    {B : Type} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ) :
    (dualComplex A K).homology (n + 1) ⟶
      AddCommGrpCat.of (K.homology (n + 1) →ₗ[ℤ] B) :=
  cohomologyEvaluation A K n ≫
    AddCommGrpCat.ofHom (dualCoefficientEquiv A e).toAddMonoidHom

@[simp]
theorem cohomologyEvaluationAlongCoefficient_apply
    {B : Type} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ)
    (a : (dualComplex A K).homology (n + 1))
    (x : K.homology (n + 1)) :
    cohomologyEvaluationAlongCoefficient A K e n a x =
      e (cohomologyEvaluation A K n a x) := rfl

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Coefficient-normalized Kronecker evaluation remains contravariantly natural for chain maps. -/
theorem cohomologyEvaluationAlongCoefficient_natural
    {B : Type} [AddCommGroup B] [Module ℤ B]
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
    {B : Type} [AddCommGroup B] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ)
    [Module.Projective ℤ (K.homology n)] :
    IsIso (cohomologyEvaluationAlongCoefficient A K e n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (dualCoefficientEquiv A e).bijective.comp
    ((ConcreteCategory.isIso_iff_bijective
      (cohomologyEvaluation A K n)).mp
        (cohomologyEvaluation_isIso_of_free_of_projective A K n))

end FreeChains

/-- The fixed convention sending the sheaf coefficient `ULift ℤ` back to literal integers. -/
abbrev uliftIntCoefficientEquiv : ULift.{0} ℤ ≃ₗ[ℤ] ℤ :=
  ULift.moduleEquiv

/-- Positive-degree integral evaluation with the repository's small `ULift ℤ` coefficient
convention normalized to literal integer-valued functionals. -/
abbrev uliftIntCohomologyEvaluation
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :=
  cohomologyEvaluationAlongCoefficient
    (AddCommGrpCat.of (ULift.{0} ℤ)) K uliftIntCoefficientEquiv n

theorem uliftIntCohomologyEvaluation_apply
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : (dualComplex (AddCommGrpCat.of (ULift.{0} ℤ)) K).homology (n + 1))
    (x : K.homology (n + 1)) :
    uliftIntCohomologyEvaluation K n a x =
      (cohomologyEvaluation (AddCommGrpCat.of (ULift.{0} ℤ)) K n a x).down := by
  rfl

/-- The `ULift ℤ → ℤ` normalization commutes with contravariant pullback along every
integral chain map. -/
theorem uliftIntCohomologyEvaluation_natural
    {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
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

end AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT
