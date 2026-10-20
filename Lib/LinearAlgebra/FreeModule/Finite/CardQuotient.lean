/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Cardinality of an integral matrix cokernel

The quotient by the range of a full-rank square integral matrix has cardinality equal to the
absolute value of its determinant.
-/

@[expose] public section

namespace Matrix

/-- The absolute determinant of a nonsingular integral matrix is the cardinality of its cokernel. -/
theorem natAbs_det_eq_natCard_quotient_range_toLin'
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) :
    B.det.natAbs = Nat.card ((ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' B)) := by
  let f := Matrix.toLin' B
  have hf : Function.Injective f := by
    intro x y hxy
    apply B.mulVec_injective_of_det_ne_zero hB
    simpa only [f, Matrix.toLin'_apply] using hxy
  let e : (ι → ℤ) ≃ₗ[ℤ] LinearMap.range f := LinearEquiv.ofInjective f hf
  have hcard := Submodule.natAbs_det_equiv (LinearMap.range f) e
  rw [← hcard]
  congr 1
  rw [← LinearMap.det_toLin']
  congr 1

end Matrix
