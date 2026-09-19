module
public import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section
namespace Int

/-- The signed equations `3u = k`, `-4v = k` and `u + v = dk` force `k = 0` for
arbitrary integers: `(12d - 1)k = 0` and `12d - 1` is nonzero.
Textbook: `CENTER_NATIVE_H5_VANISHING_TEXTBOOK.md`, HV10. -/
theorem signed_residual_coordinate_zero (k u v d : ℤ)
    (hthree : 3 * u = k) (hfour : -4 * v = k) (hregular : u + v = d * k) : k = 0 := by
  have h : (12 * d - 1) * k = 0 := by linear_combination 4 * hthree - 3 * hfour - 12 * hregular
  have hn : 12 * d - 1 ≠ 0 := by omega
  exact (mul_eq_zero.mp h).resolve_left hn

end Int
