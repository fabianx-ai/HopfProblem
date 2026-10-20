/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.LinearAlgebra.Dual.TriangularRankTwo

/-!
# Injectivity on duals of integral triangular rank-two maps

A triangular endomorphism of `ℤ²` with nonzero diagonal `(1,m)` has full rank.  Consequently its
dual map is injective, even when `m` is not a unit.  This is the elementary torsion-free argument
needed when a finite-index specialization is dualized to cohomology.
-/

@[expose] public section

open Module

namespace LinearMap

/-- The dual of an integral triangular rank-two map with nonzero second diagonal entry is
injective.  No invertibility assumption on that entry is needed. -/
theorem dualMap_injective_of_finTwo_triangular
    (F : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) (m : ℤ)
    (hfirst : F ![1, 0] = ![1, 0])
    (hsecond : ∀ v, F v 1 = m * v 1) (hm : m ≠ 0) :
    Function.Injective F.dualMap := by
  intro phi psi hphi
  apply LinearMap.ext
  intro v
  have hzero : phi ![1, 0] = psi ![1, 0] := by
    have h := LinearMap.congr_fun hphi ![1, 0]
    change phi (F ![1, 0]) = psi (F ![1, 0]) at h
    simpa [hfirst] using h
  have hdecomp :
      F ![0, 1] =
        (F ![0, 1] 0) • ![1, 0] + m • ![0, 1] := by
    funext i
    fin_cases i
    · simp
    · simp [hsecond]
  have hone : phi ![0, 1] = psi ![0, 1] := by
    have h := LinearMap.congr_fun hphi ![0, 1]
    change phi (F ![0, 1]) = psi (F ![0, 1]) at h
    rw [hdecomp, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      hzero] at h
    exact mul_left_cancel₀ hm (add_left_cancel h)
  have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp [Pi.add_apply]
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hzero, hone]

end LinearMap
