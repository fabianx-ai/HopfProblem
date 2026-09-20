/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Square-zero one-plus-scalar flows

A square-zero endomorphism generates an additive one-parameter family of linear equivalences.
Bilinear forms for which the endomorphism is infinitesimally skew are invariant under the family.
-/

@[expose] public section

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The endomorphism `1 + s N`. -/
def oneAddSMul (N : Module.End R M) (s : R) : Module.End R M :=
  1 + s • N

@[simp]
theorem oneAddSMul_zero (N : Module.End R M) : oneAddSMul N 0 = 1 := by
  simp [oneAddSMul]

@[simp]
theorem oneAddSMul_apply (N : Module.End R M) (s : R) (x : M) :
    oneAddSMul N s x = x + s • N x := by
  simp [oneAddSMul]

/-- If `N` is square-zero, the endomorphisms `1 + s N` compose by adding parameters. -/
theorem oneAddSMul_mul_oneAddSMul {N : Module.End R M} (hN : N * N = 0) (s t : R) :
    oneAddSMul N s * oneAddSMul N t = oneAddSMul N (s + t) := by
  ext x
  have hNN : N (N x) = 0 := by
    simpa [Module.End.mul_apply] using DFunLike.congr_fun hN x
  simp only [Module.End.mul_apply, oneAddSMul_apply, map_add, map_smul, hNN, smul_zero,
    add_zero]
  module

/-- The linear equivalence `1 + s N` for a square-zero endomorphism `N`. -/
def oneAddSMulEquiv (N : Module.End R M) (hN : N * N = 0) (s : R) : M ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap (oneAddSMul N s) (oneAddSMul N (-s))
    (by
      rw [← Module.End.mul_eq_comp, oneAddSMul_mul_oneAddSMul hN, add_neg_cancel,
        oneAddSMul_zero]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, oneAddSMul_mul_oneAddSMul hN, neg_add_cancel,
        oneAddSMul_zero]
      rfl)

@[simp]
theorem oneAddSMulEquiv_toLinearMap {N : Module.End R M} (hN : N * N = 0) (s : R) :
    (oneAddSMulEquiv N hN s).toLinearMap = oneAddSMul N s :=
  rfl

@[simp]
theorem oneAddSMulEquiv_apply {N : Module.End R M} (hN : N * N = 0) (s : R) (x : M) :
    oneAddSMulEquiv N hN s x = oneAddSMul N s x :=
  rfl

/-- The inverse of `1 + s N` is `1 - s N`. -/
theorem oneAddSMulEquiv_symm_toLinearMap {N : Module.End R M} (hN : N * N = 0) (s : R) :
    (oneAddSMulEquiv N hN s).symm.toLinearMap = oneAddSMul N (-s) :=
  rfl

/-- The quadratic term forced by a square-zero skew operator vanishes. -/
theorem quadratic_term_eq_zero {N : Module.End R M} (hN : N * N = 0)
    (Q : LinearMap.BilinForm R M)
    (hskew : ∀ x y, Q (N x) y + Q x (N y) = 0) (x y : M) :
    Q (N x) (N y) = 0 := by
  have hNN : N (N y) = 0 := by
    simpa [Module.End.mul_apply] using DFunLike.congr_fun hN y
  simpa [hNN] using hskew x (N y)

/-- An infinitesimally invariant bilinear form is preserved by every square-zero exchange. -/
theorem oneAddSMul_preserves_bilin {N : Module.End R M} (hN : N * N = 0)
    (Q : LinearMap.BilinForm R M)
    (hskew : ∀ x y, Q (N x) y + Q x (N y) = 0) (s : R) (x y : M) :
    Q (oneAddSMul N s x) (oneAddSMul N s y) = Q x y := by
  have hquad := quadratic_term_eq_zero hN Q hskew x y
  simp only [oneAddSMul_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  linear_combination s * hskew x y + s ^ 2 * hquad

/-- The bilinear conservation theorem stated using Mathlib's skew-adjoint predicate. -/
theorem oneAddSMul_preserves_bilin_of_isSkewAdjoint {N : Module.End R M} (hN : N * N = 0)
    (Q : LinearMap.BilinForm R M) (hskew : Q.IsSkewAdjoint N) (s : R) (x y : M) :
    Q (oneAddSMul N s x) (oneAddSMul N s y) = Q x y := by
  apply oneAddSMul_preserves_bilin hN Q
  intro u v
  rw [hskew u v]
  simp

end Module.End
