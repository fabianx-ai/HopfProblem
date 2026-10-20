/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Group.Basic

/-!
# Cancellation of the project's residual gluing relations

Proof-specific: the exponents `3` and `4` below are the orders of the two exceptional gluing
matrices `T₁`, `T₂` of `Hopf/Proof/FiniteCore.lean`, and the conclusion is the residual step of
the centre-triviality argument.  In any group, `x * y = 1` eliminates `y` as `x⁻¹`; the cube and
inverse-fourth-power relations then identify two consecutive powers of `x`, forcing `x`, `y` and
the common power `d` to be trivial.

This module carries no textbook statement; the reusable content of the argument is Mathlib's
`mul_left_cancel` on `x ^ 3 * x = x ^ 3 * 1`.  Moved out of `Lib/Algebra/Group/ResidualRelations.lean`
by the round-8 D-file pass (`Lib/reports/round-7/judgement/d-files.md`).
-/

universe u

namespace ResidualRelations

/-- The relations `x * y = 1`, `x ^ 3 = d`, and `y ^ 4 = d⁻¹` force all
three elements to be identities. Eliminate `y`, invert the fourth-power
equation, and cancel the common cube on the left (reviewed NT1). -/
theorem eq_one_of_mul_eq_one_cube_fourth
    {H : Type u} [Group H] (d x y : H)
    (hxy : x * y = 1) (hx : x ^ 3 = d) (hy : y ^ 4 = d⁻¹) :
    d = 1 ∧ x = 1 ∧ y = 1 := by
  have hyinv : y = x⁻¹ := eq_inv_of_mul_eq_one_right hxy
  have hfour : x ^ 4 = d := by
    apply inv_inj.mp
    rw [← inv_pow, ← hyinv]
    exact hy
  have hcancel : x ^ 3 * x = x ^ 3 * 1 := by
    rw [← pow_succ, mul_one]
    exact hfour.trans hx.symm
  have hxone : x = 1 := mul_left_cancel hcancel
  have hdone : d = 1 := by
    rw [← hx, hxone, one_pow]
  have hyone : y = 1 := by
    rw [hyinv, hxone, inv_one]
  exact ⟨hdone, hxone, hyone⟩

end ResidualRelations
