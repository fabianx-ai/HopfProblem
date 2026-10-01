/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# The principal `n`-th root on the closed upper half-plane

`RiemannBoundary.principalRoot n z = z ^ (1 / n)` (principal branch). It is a right inverse of
`w ↦ w ^ n`, injective, of norm `‖z‖ ^ (1/n)` and argument `arg z / n`; it is continuous at `0` and
on the closed upper half-plane, analytic on the open upper half-plane, and maps the open upper
half-plane onto the open sector `0 < arg w < π / n`, the nonnegative reals to themselves and the
nonpositive reals onto the ray `arg w = π / n`.

These are the corner-straightening maps `z ↦ z ^ (α / π)` at a boundary corner of opening `π / n`
(Ahlfors, *Complex Analysis*, Ch. 6 §2.2; Pommerenke, *Boundary Behaviour of Conformal Maps*, §3.4).
-/

open Set Function Filter Topology

noncomputable section

/-- The principal `n`-th root `z ^ (1 / n)`. -/
def RiemannBoundary.principalRoot (n : ℕ) (z : ℂ) : ℂ :=
  z ^ ((n : ℂ)⁻¹)

/-- `(principalRoot n z) ^ n = z` for `n > 0`. -/
@[simp]
theorem RiemannBoundary.principalRoot_pow {n : ℕ} (hn : 0 < n) (z : ℂ) :
    principalRoot n z ^ n = z :=
  Complex.cpow_nat_inv_pow z hn.ne'

/-- The principal root of zero is zero. -/
@[simp]
theorem RiemannBoundary.principalRoot_zero {n : ℕ} (hn : 0 < n) : principalRoot n 0 = 0 := by
  exact Complex.zero_cpow (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))

/-- The principal root is injective. -/
theorem RiemannBoundary.principalRoot_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (principalRoot n) := by
  intro z w h
  simpa only [principalRoot_pow hn] using congrArg (fun u : ℂ => u ^ n) h

/-- The principal root vanishes only at zero. -/
@[simp]
theorem RiemannBoundary.principalRoot_eq_zero_iff {n : ℕ} (hn : 0 < n) {z : ℂ} :
    principalRoot n z = 0 ↔ z = 0 := by
  have h : principalRoot n z = principalRoot n 0 ↔ z = 0 := (principalRoot_injective hn).eq_iff
  simpa only [principalRoot_zero hn] using h

/-- The norm of the principal root. -/
@[simp]
theorem RiemannBoundary.norm_principalRoot (n : ℕ) (z : ℂ) :
    ‖principalRoot n z‖ = ‖z‖ ^ ((n : ℝ)⁻¹) :=
  Complex.norm_cpow_inv_nat z n

/-- For `n > 0` the exponent `1 / n` has positive real part. -/
theorem RiemannBoundary.principalRoot_exponent_re_pos {n : ℕ} (hn : 0 < n) :
    0 < ((n : ℂ)⁻¹).re := by
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re] using
    inv_pos.mpr (Nat.cast_pos.mpr hn : (0 : ℝ) < n)

/-- The principal root is continuous at zero. -/
theorem RiemannBoundary.continuousAt_principalRoot_zero {n : ℕ} (hn : 0 < n) :
    ContinuousAt (principalRoot n) 0 :=
  Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
    (principalRoot_exponent_re_pos hn)

/-- The principal root is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousOn_principalRoot_closedUpper {n : ℕ} (hn : 0 < n) :
    ContinuousOn (principalRoot n) {z : ℂ | 0 ≤ z.im} := by
  intro z _hz
  change ContinuousWithinAt (fun w : ℂ => w ^ ((n : ℂ)⁻¹)) _ z
  by_cases h : 0 ≤ z.re ∨ z.im ≠ 0
  · exact
      (Complex.continuousAt_cpow_const_of_re_pos h
          (principalRoot_exponent_re_pos hn)).continuousWithinAt
  push Not at h
  have hz0 : z ≠ 0 := fun hz => by simpa only [hz, Complex.zero_re, lt_self_iff_false] using h.1
  have hc :
    ContinuousWithinAt (fun w : ℂ => Complex.exp (Complex.log w * (n : ℂ)⁻¹)) {w : ℂ | 0 ≤ w.im}
      z :=
    Complex.continuous_exp.continuousAt.comp_continuousWithinAt
      ((Complex.continuousWithinAt_log_of_re_neg_of_im_zero h.1 h.2).mul_const _)
  exact
    hc.congr_of_eventuallyEq ((cpow_eq_nhds hz0).filter_mono nhdsWithin_le_nhds)
      (Complex.cpow_def_of_ne_zero hz0 _)

/-- The principal root is differentiable on the open upper half-plane. -/
theorem RiemannBoundary.differentiableOn_principalRoot_upper (n : ℕ) :
    DifferentiableOn ℂ (principalRoot n) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact
    ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).cpow_const
        (Or.inr (ne_of_gt hz))).differentiableWithinAt

/-- The principal root is analytic on the upper half-plane. -/
theorem RiemannBoundary.analyticOnNhd_principalRoot_upper (n : ℕ) :
    AnalyticOnNhd ℂ (principalRoot n) {z : ℂ | 0 < z.im} :=
  (differentiableOn_principalRoot_upper n).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im)

/-- The principal root of a nonnegative real is nonnegative. -/
theorem RiemannBoundary.principalRoot_ofReal_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    principalRoot n (x : ℂ) = (x ^ ((n : ℝ)⁻¹) : ℝ) := by
  simpa only [principalRoot, Complex.ofReal_inv, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow hx ((n : ℝ)⁻¹)).symm

/-- For real `x ≤ 0`, `principalRoot n x = (-x) ^ (1 / n) e^{iπ/n}`. -/
theorem RiemannBoundary.principalRoot_ofReal_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    principalRoot n (x : ℂ) =
      ((-x) ^ ((n : ℝ)⁻¹) : ℝ) * Complex.exp ((Real.pi / (n : ℝ) : ℝ) * Complex.I) := by
  rw [principalRoot, Complex.ofReal_cpow_of_nonpos hx]
  have hr : (-(x : ℂ)) ^ ((n : ℂ)⁻¹) = ((-x) ^ ((n : ℝ)⁻¹) : ℝ) := by
    simpa only [principalRoot, Complex.ofReal_neg] using
      principalRoot_ofReal_nonneg n (neg_nonneg.mpr hx)
  rw [hr]
  congr 2
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- For `n > 0`, `arg z / n` lies in `(-π, π]`. -/
theorem RiemannBoundary.arg_div_nat_mem_Ioc {n : ℕ} (hn : 0 < n) (z : ℂ) :
    z.arg / (n : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · rw [lt_div_iff₀ hnR]
    have hl : -Real.pi * (n : ℝ) ≤ -Real.pi := by nlinarith [Real.pi_pos]
    exact hl.trans_lt (Complex.neg_pi_lt_arg z)
  · rw [div_le_iff₀ hnR]
    have hu : Real.pi ≤ Real.pi * (n : ℝ) := by nlinarith [Real.pi_pos]
    exact (Complex.arg_le_pi z).trans hu

/-- The argument of the principal root is the divided argument. -/
theorem RiemannBoundary.arg_principalRoot {n : ℕ} (hn : 0 < n) (z : ℂ) :
    Complex.arg (principalRoot n z) = z.arg / (n : ℝ) := by
  by_cases hz : z = 0
  · simp only [hz, principalRoot_zero hn, Complex.arg_zero, zero_div]
  have hpolar :
    principalRoot n z =
      (‖z‖ ^ ((n : ℝ)⁻¹) : ℝ) *
        (Real.cos (z.arg / (n : ℝ)) + Real.sin (z.arg / (n : ℝ)) * Complex.I) := by
    simpa only [principalRoot, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv] using
      Complex.cpow_ofReal z ((n : ℝ)⁻¹)
  rw [hpolar]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) ((n : ℝ)⁻¹))
      (arg_div_nat_mem_Ioc hn z)

/-- For `n > 0` and `Im z > 0`, `arg (principalRoot n z)` lies in `(0, π / n)`. -/
theorem RiemannBoundary.principalRoot_arg_mem_Ioo {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : 0 < z.im) :
    Complex.arg (principalRoot n z) ∈ Set.Ioo 0 (Real.pi / (n : ℝ)) := by
  rw [arg_principalRoot hn]
  have harg0 : z.arg ≠ 0 := fun h => (ne_of_gt hz) (Complex.arg_eq_zero_iff.mp h).2
  have harg : 0 < z.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) harg0.symm
  exact
    ⟨div_pos harg (Nat.cast_pos.mpr hn),
      (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).mpr
        (Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hz)))⟩

/-- If `0 ≤ arg z ≤ π / n` (`n > 0`), then `principalRoot n (z ^ n) = z`. -/
theorem RiemannBoundary.principalRoot_pow_of_sector {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z.arg ∈ Set.Icc 0 (Real.pi / (n : ℝ))) : principalRoot n (z ^ n) = z := by
  apply Complex.pow_cpow_nat_inv hn.ne' _ hz.2
  exact (neg_neg_of_pos (div_pos Real.pi_pos (Nat.cast_pos.mpr hn))).trans_le hz.1
