/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The signed residual coordinate of the threefold's fifth homology

Proof-specific: the coefficients `3`, `-4` and the regularity relation below are the project's
`(12 d - 1) k = 0` computation for the fifth Wang coordinate of the threefold
(`Hopf/Proof/LCP/IntegralHomology.lean`), not a general divisibility statement.  The whole content
is one `linear_combination` and one `omega`.

Moved out of `Lib/Data/Int/SignedResidual.lean` by the round-8 D-file pass
(`Lib/reports/round-7/judgement/d-files.md`), where it also had to squat in Mathlib's `Int`
namespace and `Data/Int/` directory.
-/

namespace ThreefoldHomology

/-- The signed equations `3u = k`, `-4v = k` and `u + v = dk` force `k = 0` for
arbitrary integers: `(12d - 1)k = 0` and `12d - 1` is nonzero. -/
theorem signed_residual_coordinate_zero (k u v d : ℤ)
    (hthree : 3 * u = k) (hfour : -4 * v = k) (hregular : u + v = d * k) : k = 0 := by
  have h : (12 * d - 1) * k = 0 := by linear_combination 4 * hthree - 3 * hfour - 12 * hregular
  have hn : 12 * d - 1 ≠ 0 := by omega
  exact (mul_eq_zero.mp h).resolve_left hn

end ThreefoldHomology
