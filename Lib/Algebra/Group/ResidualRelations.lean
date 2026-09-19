/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Cancellation of residual group relations

In any group, an ordered product-one relation eliminates the second element
as the inverse of the first. A cube and inverse fourth-power relation then
identify consecutive powers of that first element, forcing it and the common
power to be the identity. No commutativity or generation assumption is needed.
Source: CENTER_NATIVE_TRIVIALITY_TEXTBOOK.md, reviewed NT1.
-/

@[expose] public section
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
