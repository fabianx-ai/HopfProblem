/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Dual ranges of triangular rank-two maps

This file records two elementary facts used when a specialization map has triangular integral
coordinates. A surjective source-coordinate map can be cancelled on algebraic duals, and a
rank-two map with diagonal `(1,m)` meets the second-coordinate dual line in exactly the multiples
of `m`.

The statements work over an arbitrary commutative semiring. No topology, homology, sheaf, or
proof-specific data occur here.
-/

@[expose] public section

open Module

namespace LinearMap

variable {R : Type*} [CommSemiring R]

/-- A surjective coordinate map may be cancelled when testing membership in the dual range of a
composite. -/
theorem dualMap_mem_range_comp_iff_of_surjective
    {M N P : Type*}
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (S : M →ₗ[R] N) (F : N →ₗ[R] P) (hS : Function.Surjective S)
    (phi : Dual R N) :
    S.dualMap phi ∈ range (F.comp S).dualMap ↔ phi ∈ range F.dualMap := by
  rw [← dualMap_comp_dualMap S F]
  constructor
  · rintro ⟨psi, hpsi⟩
    refine ⟨psi, ?_⟩
    exact (dualMap_injective_of_surjective hS) hpsi
  · rintro ⟨psi, rfl⟩
    exact ⟨psi, rfl⟩

/-- The second coordinate on a free rank-two module. -/
def finTwoSecondCoordinate : Dual R (Fin 2 → R) :=
  LinearMap.proj (1 : Fin 2)

/-- For a triangular rank-two map whose diagonal is `(1,m)`, the dual image meets the
second-coordinate line in precisely the multiples of `m`. -/
theorem smul_finTwoSecondCoordinate_mem_range_dualMap_iff
    (F : (Fin 2 → R) →ₗ[R] (Fin 2 → R)) (m z : R)
    (hfirst : F ![1, 0] = ![1, 0])
    (hsecond : ∀ v, F v 1 = m * v 1) :
    z • finTwoSecondCoordinate ∈ range F.dualMap ↔ m ∣ z := by
  constructor
  · rintro ⟨phi, hphi⟩
    have hphi0 := LinearMap.congr_fun hphi ![1, 0]
    have hphi1 := LinearMap.congr_fun hphi ![0, 1]
    change phi (F ![1, 0]) = z * (![1, 0] : Fin 2 → R) 1 at hphi0
    change phi (F ![0, 1]) = z * (![0, 1] : Fin 2 → R) 1 at hphi1
    rw [hfirst] at hphi0
    have hzero : phi ![1, 0] = 0 := by
      simpa using hphi0
    have hdecomp :
        F ![0, 1] =
          (F ![0, 1] 0) • ![1, 0] + m • ![0, 1] := by
      funext i
      fin_cases i
      · simp
      · simp [hsecond]
    refine ⟨phi ![0, 1], ?_⟩
    rw [show z = phi (F ![0, 1]) by
          simpa using hphi1.symm,
      hdecomp, map_add, map_smul, map_smul]
    simp [hzero, mul_comm]
  · rintro ⟨c, rfl⟩
    refine ⟨c • finTwoSecondCoordinate, ?_⟩
    apply LinearMap.ext
    intro v
    change c * F v 1 = (m * c) * v 1
    rw [hsecond]
    ring

end LinearMap
