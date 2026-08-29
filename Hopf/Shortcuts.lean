/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Hopf.FiniteCore
import S6.SquareZeroExchange

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

end Mathoverflow1973
