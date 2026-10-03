/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.PrincipalRoot

/-!
# Cube and rotated fourth roots for the corners of the project's triangles

Project material for `Hopf/Proof/LCP/AnalyticFillings.lean`: the corner-straightening maps at the
triangle corners of opening `π / 3` and `π / 4`, i.e. `principalRoot 3` (onto the sector
`0 < arg w < π / 3`) and `rotatedPrincipalRootFour = e^{-iπ/4} · principalRoot 4` (onto the sector
`-π/4 < arg w < 0`), with the images of the upper half-plane and of the real axis.

Moved verbatim from `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`: the declarations
of that file that both the old proof and the center construction use
(`Lib/reports/center-proof/RECEIPT.md`).
-/

open Set Function Filter Topology

noncomputable section

/-- The cubic sector leaves angular slack. -/
theorem RiemannBoundary.cubic_sector_slack (w : ℂ) :
    3 * w.re - Real.sqrt 3 * w.im = (2 * Real.sqrt 3 * ‖w‖) * Real.sin (Real.pi / 3 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
  rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  calc
    3 * (‖w‖ * Real.cos w.arg) - Real.sqrt 3 * (‖w‖ * Real.sin w.arg) =
        ‖w‖ * ((Real.sqrt 3 * Real.sqrt 3) * Real.cos w.arg - Real.sqrt 3 * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    _ = _ := by ring

/-- The quartic sector leaves angular slack. -/
theorem RiemannBoundary.quartic_sector_slack (w : ℂ) :
    w.re - w.im = (Real.sqrt 2 * ‖w‖) * Real.sin (Real.pi / 4 - w.arg) := by
  rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  calc
    ‖w‖ * Real.cos w.arg - ‖w‖ * Real.sin w.arg =
        (‖w‖ / 2) *
          ((Real.sqrt 2 * Real.sqrt 2) * Real.cos w.arg -
            (Real.sqrt 2 * Real.sqrt 2) * Real.sin w.arg) := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ = _ := by ring

/-- The cube root maps the upper half-plane to a sector. -/
theorem RiemannBoundary.principalRoot_three_upper {z : ℂ} (hz : 0 < z.im) :
    0 < (principalRoot 3 z).im ∧
      Real.sqrt 3 * (principalRoot 3 z).im < 3 * (principalRoot 3 z).re := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 3) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 3 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 3)]
    exact fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  constructor
  · rw [← Complex.norm_mul_sin_arg]
    exact
      mul_pos (norm_pos_iff.mpr hw)
        (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  · apply sub_pos.mp
    rw [cubic_sector_slack]
    exact
      mul_pos
        (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))) (norm_pos_iff.mpr hw))
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2]) (by linarith [Real.pi_pos, ha.1]))

/-- The rotation aligning the quartic root with the sector. -/
def RiemannBoundary.quarticRootRotation : ℂ :=
  Complex.exp (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The real part of the quartic rotation. -/
@[simp]
theorem RiemannBoundary.quarticRootRotation_re : quarticRootRotation.re = Real.sqrt 2 / 2 := by
  simp only [quarticRootRotation, Complex.exp_ofReal_mul_I_re, neg_div, Real.cos_neg,
    Real.cos_pi_div_four]

/-- The imaginary part of the quartic rotation. -/
@[simp]
theorem RiemannBoundary.quarticRootRotation_im : quarticRootRotation.im = -(Real.sqrt 2 / 2) := by
  simp only [quarticRootRotation, Complex.exp_ofReal_mul_I_im, neg_div, Real.sin_neg,
    Real.sin_pi_div_four]

/-- The quartic rotation has norm one. -/
@[simp]
theorem RiemannBoundary.norm_quarticRootRotation : ‖quarticRootRotation‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The fourth power of the quartic rotation. -/
@[simp]
theorem RiemannBoundary.quarticRootRotation_pow_four : quarticRootRotation ^ 4 = -1 := by
  rw [quarticRootRotation, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (4 : ℂ) * (((-Real.pi / 4 : ℝ) : ℂ) * Complex.I) = -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The rotated principal fourth root. -/
def RiemannBoundary.rotatedPrincipalRootFour (z : ℂ) : ℂ :=
  quarticRootRotation * principalRoot 4 z

/-- The rotated fourth root raised to four. -/
@[simp]
theorem RiemannBoundary.rotatedPrincipalRootFour_pow (z : ℂ) :
    rotatedPrincipalRootFour z ^ 4 = -z := by
  rw [rotatedPrincipalRootFour, mul_pow, quarticRootRotation_pow_four,
    principalRoot_pow (by norm_num : 0 < 4)]
  ring

/-- The rotated fourth root of zero is zero. -/
@[simp]
theorem RiemannBoundary.rotatedPrincipalRootFour_zero : rotatedPrincipalRootFour 0 = 0 := by
  rw [rotatedPrincipalRootFour, principalRoot_zero (by norm_num : 0 < 4), MulZeroClass.mul_zero]

/-- The norm of the rotated fourth root. -/
@[simp]
theorem RiemannBoundary.norm_rotatedPrincipalRootFour (z : ℂ) :
    ‖rotatedPrincipalRootFour z‖ = ‖z‖ ^ (4 : ℝ)⁻¹ := by
  rw [rotatedPrincipalRootFour, norm_mul, norm_quarticRootRotation, one_mul, norm_principalRoot]
  norm_num only [Nat.cast_ofNat]

/-- The real part of the rotated fourth root. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_re (z : ℂ) :
    (rotatedPrincipalRootFour z).re =
      (Real.sqrt 2 / 2) * ((principalRoot 4 z).re + (principalRoot 4 z).im) := by
  simp only [rotatedPrincipalRootFour, Complex.mul_re, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

/-- The imaginary part of the rotated fourth root. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_im (z : ℂ) :
    (rotatedPrincipalRootFour z).im =
      (Real.sqrt 2 / 2) * ((principalRoot 4 z).im - (principalRoot 4 z).re) := by
  simp only [rotatedPrincipalRootFour, Complex.mul_im, quarticRootRotation_re,
    quarticRootRotation_im]
  ring

/-- The sum of real and imaginary parts of the rotated fourth root. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_re_add_im (z : ℂ) :
    (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im =
      Real.sqrt 2 * (principalRoot 4 z).im := by
  rw [rotatedPrincipalRootFour_re, rotatedPrincipalRootFour_im]
  ring

/-- The rotated fourth root maps the upper half-plane into the sector. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_upper {z : ℂ} (hz : 0 < z.im) :
    (rotatedPrincipalRootFour z).im < 0 ∧
      0 < (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im := by
  have ha := principalRoot_arg_mem_Ioo (by norm_num : 0 < 4) hz
  norm_num only [Nat.cast_ofNat] at ha
  have hw : principalRoot 4 z ≠ 0 := by
    rw [ne_eq, principalRoot_eq_zero_iff (by norm_num : 0 < 4)]
    exact fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  have hi : 0 < (principalRoot 4 z).im := by
    rw [← Complex.norm_mul_sin_arg]
    exact
      mul_pos (norm_pos_iff.mpr hw)
        (Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [Real.pi_pos, ha.2]))
  have hri : (principalRoot 4 z).im < (principalRoot 4 z).re := by
    apply sub_pos.mp
    rw [quartic_sector_slack]
    exact
      mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (norm_pos_iff.mpr hw))
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.2]) (by linarith [Real.pi_pos, ha.1]))
  constructor
  · rw [rotatedPrincipalRootFour_im]
    exact mul_neg_of_pos_of_neg (by positivity) (sub_neg.mpr hri)
  · rw [rotatedPrincipalRootFour_re_add_im]
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hi

/-- The rotated fourth root of a nonnegative real lies on the boundary ray. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonneg_boundary {x : ℝ} (hx : 0 ≤ x) :
    (rotatedPrincipalRootFour (x : ℂ)).re + (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_re_add_im, principalRoot_ofReal_nonneg 4 hx]
  simp only [Complex.ofReal_im, MulZeroClass.mul_zero]

/-- The rotated fourth root of a nonpositive real has controlled imaginary part. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_ofReal_nonpos_im {x : ℝ} (hx : x ≤ 0) :
    (rotatedPrincipalRootFour (x : ℂ)).im = 0 := by
  rw [rotatedPrincipalRootFour_im, principalRoot_ofReal_nonpos 4 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_four, Real.cos_pi_div_four,
    sub_self, MulZeroClass.mul_zero]

/-- The rotated fourth root is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper :
    ContinuousOn rotatedPrincipalRootFour {z : ℂ | 0 ≤ z.im} :=
  continuousOn_const.mul (continuousOn_principalRoot_closedUpper (by norm_num : 0 < 4))

/-- The rotated fourth root is continuous at zero. -/
theorem RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero :
    ContinuousAt rotatedPrincipalRootFour 0 :=
  continuousAt_const.mul (continuousAt_principalRoot_zero (by norm_num : 0 < 4))

/-- The rotated fourth root is analytic on the upper half-plane. -/
theorem RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper :
    AnalyticOnNhd ℂ rotatedPrincipalRootFour {z : ℂ | 0 < z.im} := by
  intro z hz
  exact analyticAt_const.mul (analyticOnNhd_principalRoot_upper 4 z hz)
