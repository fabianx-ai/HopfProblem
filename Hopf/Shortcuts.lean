/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Hopf.FiniteCore
import Lib.LinearAlgebra.SquareZeroExchange

/-!
# Short-proof adapters for HopfProblem

This module owns finite, dependency-early bridges from the HopfProblem data to the reusable V10
algebraic interfaces.  It contains no analytic construction and makes no assertion that the
six-sphere carries a complex structure.
-/

open Matrix
open scoped Matrix

namespace Mathoverflow1973

/-- The integral dual-cusp nilpotent as a lattice endomorphism. -/
abbrev dualCuspN : Module.End ℤ Lattice :=
  Matrix.toLin' (M₀ - 1)

/-- The dual-cusp endomorphism is square-zero. -/
theorem dualCuspN_square_zero : dualCuspN * dualCuspN = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  change ((M₀ - 1) *ᵥ ((M₀ - 1) *ᵥ v)) i = 0
  rw [M₀_sub_one_mulVec, M₀_sub_one_mulVec]
  fin_cases i <;> rfl

/-- The real scalar extension of the dual-cusp nilpotent. -/
abbrev dualCuspNReal : Module.End ℝ (Fin 4 → ℝ) :=
  Matrix.toLin' ((M₀ - 1).map (Int.castRingHom ℝ))

/-- The scalar-extended dual-cusp operator has its integral coordinate formula. -/
@[simp]
theorem dualCuspNReal_apply (x : Fin 4 → ℝ) :
    dualCuspNReal x = ![0, 0, x 1, -x 0] := by
  ext i
  fin_cases i <;>
    simp [dualCuspNReal, M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

/-- The real scalar extension remains square-zero. -/
theorem dualCuspNReal_square_zero : dualCuspNReal * dualCuspNReal = 0 := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, dualCuspNReal_apply, dualCuspNReal_apply]
  ext i
  fin_cases i <;> simp

end Mathoverflow1973
