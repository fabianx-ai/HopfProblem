/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Algebra.Module.FreeIntSubmodule
public import Lib.AlgebraicTopology.SingularCochains.DualEvaluation
public import Lib.AlgebraicTopology.SingularSmallChains.Basic

/-!
# Local integral universal coefficients for free chain complexes

For a chain complex of free integral modules, canonical cohomology evaluation in degree `n+1`
is an isomorphism when the preceding homology `Hₙ` is projective.  The native singular-chain
specialization uses the genuine arbitrary simplex basis, so it has no finite-generation
hypothesis.

## References

* [A. Hatcher, *Algebraic topology*][hatcher02], Theorem 3.2 (the universal coefficient
  theorem for a free chain complex, the `Ext` term vanishing when `Hₙ` is projective).
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT

universe v w

open HomologicalComplex.ChainCycleLift

variable (A : AddCommGrpCat.{w})
  (K : ChainComplex (ModuleCat.{v} ℤ) ℕ)

section FreeChains

variable [∀ k, Module.Free ℤ (K.X k)]

/-- Every outgoing image in a free integral chain complex is projective. -/
theorem outgoingImage_projective (n : ℕ) :
    @Module.Projective ℤ _ (OutgoingImage K n) _ (outgoingImageModule K n) :=
  Module.FreeIntSubmodule.submodule_projective_int_with_module
    (OutgoingImage K n) (outgoingImageModule K n)

/-- The canonical local UCT map in degree `n+1` is an isomorphism when only `Hₙ` is
projective. -/
theorem cohomologyEvaluation_isIso_of_free_of_projective (n : ℕ)
    [Module.Projective ℤ (K.homology n)] :
    IsIso (cohomologyEvaluation A K n) := by
  exact @cohomologyEvaluation_isIso_of_local_projective K n A
    (outgoingImage_projective K n)
    (outgoingImage_projective K (n + 1)) inferInstance

end FreeChains

/-! ### Integral-linear target and transport along homology coordinates -/

/-- The canonical integral evaluation map, with its additive-Hom target re-bundled as the
ordinary integral dual. -/
def cohomologyEvaluationLinear (n : ℕ) :
    (dualComplex (AddCommGrpCat.of ℤ) K).homology (n + 1) ⟶
      AddCommGrpCat.of (Module.Dual ℤ (K.homology (n + 1))) :=
  cohomologyEvaluation (AddCommGrpCat.of ℤ) K n ≫
    AddCommGrpCat.ofHom
      (addHomIntLinearEquiv (K.homology (n + 1)) ℤ).toAddMonoidHom

/-- The integral-linear evaluation has the same values as the canonical evaluation. -/
@[simp]
theorem cohomologyEvaluationLinear_apply (n : ℕ)
    (a : (dualComplex (AddCommGrpCat.of ℤ) K).homology (n + 1))
    (b : K.homology (n + 1)) :
    cohomologyEvaluationLinear K n a b =
      cohomologyEvaluation (AddCommGrpCat.of ℤ) K n a b := rfl

/-- Re-express the canonical evaluation through chosen coordinates on homology.  Its value is
literally evaluation on the inverse-coordinate class. -/
def cohomologyEvaluationAlong {L : Type v} [AddCommGroup L] [Module ℤ L]
    (n : ℕ) (e : K.homology (n + 1) ≃ₗ[ℤ] L) :
    (dualComplex (AddCommGrpCat.of ℤ) K).homology (n + 1) ⟶
      AddCommGrpCat.of (Module.Dual ℤ L) :=
  cohomologyEvaluationLinear K n ≫
    AddCommGrpCat.ofHom e.dualMap.symm.toAddEquiv.toAddMonoidHom

/-- Evaluation in chosen homology coordinates is evaluation on the inverse-coordinate class. -/
@[simp]
theorem cohomologyEvaluationAlong_apply {L : Type v} [AddCommGroup L] [Module ℤ L]
    (n : ℕ) (e : K.homology (n + 1) ≃ₗ[ℤ] L)
    (a : (dualComplex (AddCommGrpCat.of ℤ) K).homology (n + 1)) (x : L) :
    cohomologyEvaluationAlong K n e a x =
      cohomologyEvaluation (AddCommGrpCat.of ℤ) K n a (e.symm x) := rfl

section FreeChains

variable [∀ k, Module.Free ℤ (K.X k)]

/-- The integral-linear evaluation remains an isomorphism under the local UCT hypotheses. -/
theorem cohomologyEvaluationLinear_isIso_of_free_of_projective (n : ℕ)
    [Module.Projective ℤ (K.homology n)] :
    IsIso (cohomologyEvaluationLinear K n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (addHomIntLinearEquiv (K.homology (n + 1)) ℤ).bijective.comp
    ((ConcreteCategory.isIso_iff_bijective
      (cohomologyEvaluation (AddCommGrpCat.of ℤ) K n)).mp
        (cohomologyEvaluation_isIso_of_free_of_projective
          (AddCommGrpCat.of ℤ) K n))

/-- Transporting the homology target along any linear equivalence preserves the local UCT
isomorphism. -/
theorem cohomologyEvaluationAlong_isIso_of_free_of_projective
    {L : Type v} [AddCommGroup L] [Module ℤ L]
    (n : ℕ) (e : K.homology (n + 1) ≃ₗ[ℤ] L)
    [Module.Projective ℤ (K.homology n)] :
    IsIso (cohomologyEvaluationAlong K n e) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact e.dualMap.symm.bijective.comp
    ((ConcreteCategory.isIso_iff_bijective
      (cohomologyEvaluationLinear K n)).mp
        (cohomologyEvaluationLinear_isIso_of_free_of_projective K n))

end FreeChains

/-! ### Native singular chains -/

section Singular

variable (X : Type) [TopologicalSpace X]

/-- Mathlib's native integral singular-chain groups are free in every degree. -/
theorem singularChains_free (n : ℕ) : Module.Free ℤ ((chains X).X n) := by
  exact Module.Free.of_basis (TopCat.SingularSmallChains.chainBasis X n)

/-- For native singular chains, the canonical `H¹ → Hom(H₁, ℤ)` evaluation is an isomorphism
as soon as `H₀` is projective. -/
theorem singularH1Evaluation_isIso [Module.Projective ℤ ((chains X).homology 0)] :
    IsIso (cohomologyEvaluationLinear (chains X) 0) := by
  exact @cohomologyEvaluationLinear_isIso_of_free_of_projective
    (chains X) (fun n ↦ singularChains_free X n) 0 inferInstance

/-- Coordinate form of native integral `H¹`: evaluation followed by any chosen `H₁`
coordinates is an isomorphism. -/
theorem singularH1EvaluationAlong_isIso {L : Type} [AddCommGroup L] [Module ℤ L]
    (e : (chains X).homology 1 ≃ₗ[ℤ] L)
    [Module.Projective ℤ ((chains X).homology 0)] :
    IsIso (cohomologyEvaluationAlong (chains X) 0 e) := by
  exact @cohomologyEvaluationAlong_isIso_of_free_of_projective
    (chains X) (fun n ↦ singularChains_free X n) L inferInstance inferInstance 0 e
      inferInstance

end Singular

end AlgebraicTopology.SingularCochains.DualEvaluation.LocalUCT
