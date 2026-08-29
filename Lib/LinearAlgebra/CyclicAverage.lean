/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib

/-!
# Finite cyclic averaging

This file exports the proof-independent content of V10 Lemmas 6.2 and 6.3. Averaging a
finite-order endomorphism projects onto its fixed submodule, and invariant linear observables
survive the averaging. The statements require no finite-dimensionality and work over a
commutative ring whenever the order is invertible.
-/

open scoped BigOperators

namespace Lib.LinearAlgebra.CyclicAverage

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- The normalized sum of the first `m` powers of an endomorphism. -/
noncomputable def cyclicAverage (m : ℕ) [Invertible (m : K)] (A : Module.End K M) :
    Module.End K M :=
  ⅟(m : K) • ∑ k ∈ Finset.range m, A ^ k

/-- The unnormalized orbit sum is fixed by multiplication by `A` on the left. -/
theorem mul_sum_powers_eq_sum_powers {m : ℕ} {A : Module.End K M} (hA : A ^ m = 1) :
    A * (∑ k ∈ Finset.range m, A ^ k) = ∑ k ∈ Finset.range m, A ^ k := by
  apply sub_eq_zero.mp
  have h := mul_geom_sum A m
  rw [hA, sub_self] at h
  simpa [sub_mul] using h

/-- The unnormalized orbit sum is fixed by multiplication by `A` on the right. -/
theorem sum_powers_mul_eq_sum_powers {m : ℕ} {A : Module.End K M} (hA : A ^ m = 1) :
    (∑ k ∈ Finset.range m, A ^ k) * A = ∑ k ∈ Finset.range m, A ^ k := by
  apply sub_eq_zero.mp
  have h := geom_sum_mul A m
  rw [hA, sub_self] at h
  simpa [mul_sub] using h

/-- The cyclic average is fixed by `A` on the left. -/
theorem mul_cyclicAverage {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    (hA : A ^ m = 1) : A * cyclicAverage m A = cyclicAverage m A := by
  rw [cyclicAverage, mul_smul_comm, mul_sum_powers_eq_sum_powers hA]

/-- The cyclic average is fixed by `A` on the right. -/
theorem cyclicAverage_mul {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    (hA : A ^ m = 1) : cyclicAverage m A * A = cyclicAverage m A := by
  rw [cyclicAverage, smul_mul_assoc, sum_powers_mul_eq_sum_powers hA]

/-- A vector fixed by `A` is fixed by its cyclic average. -/
theorem cyclicAverage_apply_of_fixed {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    {x : M} (hx : A x = x) : cyclicAverage m A x = x := by
  have hpow : ∀ k : ℕ, (A ^ k) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hx]
  simp [cyclicAverage, hpow, ← Nat.cast_smul_eq_nsmul K, smul_smul]

/-- The cyclic average is a projection onto the fixed submodule `ker (A - 1)`. -/
theorem isProj_cyclicAverage {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    (hA : A ^ m = 1) :
    LinearMap.IsProj (LinearMap.ker (A - 1)) (cyclicAverage m A) := by
  constructor
  · intro x
    rw [LinearMap.mem_ker]
    change A (cyclicAverage m A x) - cyclicAverage m A x = 0
    rw [← Module.End.mul_apply, mul_cyclicAverage hA, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    apply cyclicAverage_apply_of_fixed
    simpa using sub_eq_zero.mp hx

/-- The cyclic average is idempotent. -/
theorem cyclicAverage_idempotent {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    (hA : A ^ m = 1) : cyclicAverage m A * cyclicAverage m A = cyclicAverage m A :=
  (isProj_cyclicAverage hA).isIdempotentElem

/-- The range of the cyclic average is exactly the fixed submodule of `A`. -/
theorem range_cyclicAverage {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    (hA : A ^ m = 1) :
    LinearMap.range (cyclicAverage m A) = LinearMap.ker (A - 1) :=
  (isProj_cyclicAverage hA).range

/-- A linear observable invariant under `A` is unchanged by cyclic averaging. -/
theorem comp_cyclicAverage {m : ℕ} [Invertible (m : K)] {A : Module.End K M}
    (lambda : M →ₗ[K] K) (hlambda : lambda.comp A = lambda) :
    lambda.comp (cyclicAverage m A) = lambda := by
  have hinvariant : ∀ x : M, lambda (A x) = lambda x := by
    intro x
    exact DFunLike.congr_fun hlambda x
  have hpow : ∀ (k : ℕ) (x : M), lambda ((A ^ k) x) = lambda x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, hinvariant, ih]
  ext x
  simp [cyclicAverage, hpow, ← Nat.cast_smul_eq_nsmul K]

end Lib.LinearAlgebra.CyclicAverage
