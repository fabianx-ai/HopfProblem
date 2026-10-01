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

/-- The cube root of a nonnegative real has zero imaginary part. -/
theorem RiemannBoundary.principalRoot_three_ofReal_nonneg_im {x : ℝ} (hx : 0 ≤ x) :
    (principalRoot 3 (x : ℂ)).im = 0 := by
  rw [principalRoot_ofReal_nonneg 3 hx]
  exact Complex.ofReal_im _

/-- The cube root of a nonpositive real lies on the sector boundary. -/
theorem RiemannBoundary.principalRoot_three_ofReal_nonpos_boundary {x : ℝ} (hx : x ≤ 0) :
    Real.sqrt 3 * (principalRoot 3 (x : ℂ)).im = 3 * (principalRoot 3 (x : ℂ)).re := by
  rw [principalRoot_ofReal_nonpos 3 hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, sub_zero, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Nat.cast_ofNat, Real.sin_pi_div_three, Real.cos_pi_div_three]
  have hsq := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  calc
    Real.sqrt 3 * ((-x) ^ (3 : ℝ)⁻¹ * (Real.sqrt 3 / 2)) =
        (Real.sqrt 3 * Real.sqrt 3) * ((-x) ^ (3 : ℝ)⁻¹ / 2) := by ring
    _ = _ := by rw [hsq]; ring

/-- The cube root maps the real axis to the sector boundary. -/
theorem RiemannBoundary.principalRoot_three_real_boundary {z : ℂ} (hz : z.im = 0) :
    (principalRoot 3 z).im = 0 ∨
      Real.sqrt 3 * (principalRoot 3 z).im = 3 * (principalRoot 3 z).re := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inl (principalRoot_three_ofReal_nonneg_im hp)
  · exact Or.inr (principalRoot_three_ofReal_nonpos_boundary hn)

/-- The open wedge `0 < Im u`, `sqrt 3 * Im u < 3 * Re u` selects the
principal cube-root branch. The packet retains the first-quadrant tangent
bound and the positive polar cube with its unwrapped principal argument.
Textbook source: `CENTER_LCP_FREE_CORNER3_LIMITS_TEXTBOOK.md`, lines 86–100,
FREE G3a–G3c. No particular domain or conformal map is a hypothesis. -/
theorem RiemannBoundary.principalRoot_three_reverse_of_wedge (u : ℂ) (hi : 0 < u.im)
    (hw : 0 < 3 * u.re - Real.sqrt 3 * u.im) :
    0 < u.im / Real.sqrt 3 ∧ u.im / Real.sqrt 3 < u.re ∧ u ≠ 0 ∧
    0 < u.arg ∧ u.arg < Real.pi / 2 ∧
    Real.tan u.arg = u.im / u.re ∧ u.im / u.re < Real.sqrt 3 ∧
    u.arg < Real.pi / 3 ∧ 0 < ‖u‖ ∧
    u = (‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I) ∧
    u ^ 3 = ((‖u‖ ^ 3 : ℝ) : ℂ) *
      Complex.exp (((3 * u.arg : ℝ) : ℂ) * Complex.I) ∧
    0 < 3 * u.arg ∧ 3 * u.arg < Real.pi ∧
    0 < (u ^ 3).im ∧ (u ^ 3).arg = 3 * u.arg ∧
    RiemannBoundary.principalRoot 3 (u ^ 3) = u := by
  have wedge_angle (u : ℂ) (hi : 0 < u.im)
      (hw : 0 < 3 * u.re - Real.sqrt 3 * u.im) :
      0 < u.im / Real.sqrt 3 ∧ u.im / Real.sqrt 3 < u.re ∧ u ≠ 0 ∧
      0 < u.arg ∧ u.arg < Real.pi / 2 ∧
      Real.tan u.arg = u.im / u.re ∧ u.im / u.re < Real.sqrt 3 ∧
      u.arg < Real.pi / 3 := by
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : Real.sqrt 3 * Real.sqrt 3 = 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hp : 0 < u.im / Real.sqrt 3 := div_pos hi hs
    have hx : u.im / Real.sqrt 3 < u.re := by
      apply (div_lt_iff₀ hs).mpr
      have hm := mul_pos hs hw
      nlinarith [hs2]
    have hr : 0 < u.re := lt_trans hp hx
    have hn : u ≠ 0 := by
      intro h
      simpa [h] using hi
    have ha : 0 < u.arg := by
      by_contra h
      have hz : u.arg = 0 :=
        le_antisymm (le_of_not_gt h) (Complex.arg_nonneg_iff.mpr hi.le)
      have hsin : 0 < Real.sin u.arg := by
        rw [Complex.sin_arg]
        exact div_pos hi (norm_pos_iff.mpr hn)
      simpa [hz] using hsin
    have hh : u.arg < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hr)
    have hratio : u.im / u.re < Real.sqrt 3 := by
      apply (div_lt_iff₀ hr).mpr
      have hy := (div_lt_iff₀ hs).mp hx
      nlinarith
    have hb : u.arg < Real.pi / 3 := by
      have hθ : u.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], hh⟩
      have hthird : Real.pi / 3 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      by_contra h
      have hle := Real.strictMonoOn_tan.monotoneOn hthird hθ (le_of_not_gt h)
      rw [Real.tan_pi_div_three, Complex.tan_arg] at hle
      exact (not_lt_of_ge hle) hratio
    exact ⟨hp, hx, hn, ha, hh, Complex.tan_arg u, hratio, hb⟩
  have polar_cube (u : ℂ) (hu : u ≠ 0)
      (ha : 0 < u.arg) (hb : u.arg < Real.pi / 3) :
      0 < ‖u‖ ∧ u = (‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I) ∧
      u ^ 3 = ((‖u‖ ^ 3 : ℝ) : ℂ) *
        Complex.exp (((3 * u.arg : ℝ) : ℂ) * Complex.I) ∧
      0 < 3 * u.arg ∧ 3 * u.arg < Real.pi ∧
      0 < (u ^ 3).im ∧ (u ^ 3).arg = 3 * u.arg := by
    have hq : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hpolar := (Complex.norm_mul_exp_arg_mul_I u).symm
    have hcube : u ^ 3 = ((‖u‖ ^ 3 : ℝ) : ℂ) *
        Complex.exp (((3 * u.arg : ℝ) : ℂ) * Complex.I) := by
      calc
        u ^ 3 = ((‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I)) ^ 3 :=
          congrArg (fun z : ℂ => z ^ 3) hpolar
        _ = _ := by
          rw [mul_pow, ← Complex.exp_nat_mul]
          push_cast
          congr 1
          congr 1
          ring
    have h3a : 0 < 3 * u.arg := by linarith
    have h3b : 3 * u.arg < Real.pi := by linarith
    have him : 0 < (u ^ 3).im := by
      rw [hcube, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
      exact mul_pos (pow_pos hq 3) (Real.sin_pos_of_pos_of_lt_pi h3a h3b)
    have harg : (u ^ 3).arg = 3 * u.arg := by
      rw [hcube, Complex.exp_mul_I]
      apply Complex.arg_mul_cos_add_sin_mul_I (pow_pos hq 3)
      exact ⟨by linarith [Real.pi_pos], h3b.le⟩
    exact ⟨hq, hpolar, hcube, h3a, h3b, him, harg⟩
  obtain ⟨hp, hx, hn, ha, hh, ht, hratio, hb⟩ := wedge_angle u hi hw
  obtain ⟨hq, hpolar, hcube, h3a, h3b, him, harg⟩ := polar_cube u hn ha hb
  have hroot : RiemannBoundary.principalRoot 3 (u ^ 3) = u := by
    apply RiemannBoundary.principalRoot_pow_of_sector (by norm_num : 0 < 3)
    exact ⟨ha.le, by simpa only [Nat.cast_ofNat] using hb.le⟩
  exact ⟨hp, hx, hn, ha, hh, ht, hratio, hb, hq, hpolar, hcube,
    h3a, h3b, him, harg, hroot⟩

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

/-- The quartic rotation is nonzero. -/
theorem RiemannBoundary.quarticRootRotation_ne_zero : quarticRootRotation ≠ 0 :=
  Complex.exp_ne_zero _

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

/-- The rotated fourth root maps the real axis to the sector boundary. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_real_boundary {z : ℂ} (hz : z.im = 0) :
    (rotatedPrincipalRootFour z).im = 0 ∨
      (rotatedPrincipalRootFour z).re + (rotatedPrincipalRootFour z).im = 0 := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [he]
  rcases le_total 0 z.re with hp | hn
  · exact Or.inr (rotatedPrincipalRootFour_ofReal_nonneg_boundary hp)
  · exact Or.inl (rotatedPrincipalRootFour_ofReal_nonpos_im hn)

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

/-- Reverse the rotated principal fourth root on the open wedge below the positive real axis.
The packet retains the tangent-selected angle, the unwrapped argument of the negative fourth
power, and its principal-root polar value before the rotation cancels.
Source: `CENTER_LCP_FREE_CORNER4_LIMITS_TEXTBOOK.md`, G3, lines 84–105. -/
theorem RiemannBoundary.rotatedPrincipalRootFour_reverse_of_wedge (u : ℂ)
    (hi : u.im < 0) (hw : 0 < u.re + u.im) :
    0 < -u.im ∧ -u.im < u.re ∧ u ≠ 0 ∧
    -(Real.pi / 2) < u.arg ∧ u.arg < 0 ∧
    Real.tan u.arg = u.im / u.re ∧ -1 < u.im / u.re ∧
    -(Real.pi / 4) < u.arg ∧ 0 < ‖u‖ ∧
    u = (‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I) ∧
    u ^ 4 = ((‖u‖ ^ 4 : ℝ) : ℂ) *
      Complex.exp (((4 * u.arg : ℝ) : ℂ) * Complex.I) ∧
    -Real.pi < 4 * u.arg ∧ 4 * u.arg < 0 ∧
    -(u ^ 4) = ((‖u‖ ^ 4 : ℝ) : ℂ) *
      Complex.exp (((4 * u.arg + Real.pi : ℝ) : ℂ) * Complex.I) ∧
    0 < 4 * u.arg + Real.pi ∧ 4 * u.arg + Real.pi < Real.pi ∧
    0 < (-(u ^ 4)).im ∧ (-(u ^ 4)).arg = 4 * u.arg + Real.pi ∧
    RiemannBoundary.principalRoot 4 (-(u ^ 4)) =
      (‖u‖ : ℂ) * Complex.exp (((u.arg + Real.pi / 4 : ℝ) : ℂ) * Complex.I) ∧
    RiemannBoundary.rotatedPrincipalRootFour (-(u ^ 4)) = u := by
  have wedge_angle (u : ℂ) (hi : u.im < 0) (hw : 0 < u.re + u.im) :
      0 < -u.im ∧ -u.im < u.re ∧ u ≠ 0 ∧
      -(Real.pi / 2) < u.arg ∧ u.arg < 0 ∧
      Real.tan u.arg = u.im / u.re ∧ -1 < u.im / u.re ∧
      -(Real.pi / 4) < u.arg := by
    have hp : 0 < -u.im := by linarith
    have hx : -u.im < u.re := by linarith
    have hrpos : 0 < u.re := lt_trans hp hx
    have hn : u ≠ 0 := by
      intro hz
      simpa only [hz, Complex.zero_im, lt_self_iff_false] using hi
    have ha : -(Real.pi / 2) < u.arg :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hrpos)
    have hb : u.arg < 0 := Complex.arg_neg_iff.mpr hi
    have ht : Real.tan u.arg = u.im / u.re := Complex.tan_arg u
    have hr : -1 < u.im / u.re := (lt_div_iff₀ hrpos).mpr (by linarith)
    have hqtr : -(Real.pi / 4) < u.arg := by
      have hθ : u.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨ha, by linarith [Real.pi_pos]⟩
      have hquarter : -(Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      by_contra hnot
      have hle := Real.strictMonoOn_tan.monotoneOn hθ hquarter (le_of_not_gt hnot)
      rw [Real.tan_neg, Real.tan_pi_div_four, ht] at hle
      exact (not_lt_of_ge hle) hr
    exact ⟨hp, hx, hn, ha, hb, ht, hr, hqtr⟩
  have polar_negative_fourth (u : ℂ) (hu : u ≠ 0)
      (ha : -(Real.pi / 4) < u.arg) (hb : u.arg < 0) :
      0 < ‖u‖ ∧ u = (‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I) ∧
      u ^ 4 = ((‖u‖ ^ 4 : ℝ) : ℂ) *
        Complex.exp (((4 * u.arg : ℝ) : ℂ) * Complex.I) ∧
      -Real.pi < 4 * u.arg ∧ 4 * u.arg < 0 ∧
      -(u ^ 4) = ((‖u‖ ^ 4 : ℝ) : ℂ) *
        Complex.exp (((4 * u.arg + Real.pi : ℝ) : ℂ) * Complex.I) ∧
      0 < 4 * u.arg + Real.pi ∧ 4 * u.arg + Real.pi < Real.pi ∧
      0 < (-(u ^ 4)).im ∧ (-(u ^ 4)).arg = 4 * u.arg + Real.pi := by
    have hq : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hpolar : u = (‖u‖ : ℂ) * Complex.exp ((u.arg : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I u).symm
    have hpow : u ^ 4 = ((‖u‖ ^ 4 : ℝ) : ℂ) *
        Complex.exp (((4 * u.arg : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [hpolar]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      congr 1
      congr 1
      ring
    have h4a : -Real.pi < 4 * u.arg := by linarith
    have h4b : 4 * u.arg < 0 := by linarith
    have hneg : -(u ^ 4) = ((‖u‖ ^ 4 : ℝ) : ℂ) *
        Complex.exp (((4 * u.arg + Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [hpow]
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    have hsa : 0 < 4 * u.arg + Real.pi := by linarith
    have hsb : 4 * u.arg + Real.pi < Real.pi := by linarith
    have him : 0 < (-(u ^ 4)).im := by
      rw [hneg]
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.exp_ofReal_mul_I_im]
      exact mul_pos (pow_pos hq 4) (Real.sin_pos_of_pos_of_lt_pi hsa hsb)
    have harg : (-(u ^ 4)).arg = 4 * u.arg + Real.pi := by
      rw [hneg, Complex.exp_mul_I]
      apply Complex.arg_mul_cos_add_sin_mul_I (pow_pos hq 4)
      exact ⟨by linarith [Real.pi_pos], hsb.le⟩
    exact ⟨hq, hpolar, hpow, h4a, h4b, hneg, hsa, hsb, him, harg⟩
  have root_polar_recipe (u : ℂ)
      (harg : (-(u ^ 4)).arg = 4 * u.arg + Real.pi) :
      RiemannBoundary.principalRoot 4 (-(u ^ 4)) =
        (‖u‖ : ℂ) * Complex.exp (((u.arg + Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.norm_mul_exp_arg_mul_I (RiemannBoundary.principalRoot 4 (-(u ^ 4))),
      RiemannBoundary.norm_principalRoot, norm_neg, norm_pow,
      RiemannBoundary.arg_principalRoot (by norm_num : 0 < 4), harg]
    rw [Real.pow_rpow_inv_natCast (norm_nonneg u) (by norm_num : (4 : ℕ) ≠ 0)]
    norm_num only [Nat.cast_ofNat]
    congr 2
    push_cast
    ring
  have rotation_recipe (q θ : ℝ) :
      RiemannBoundary.quarticRootRotation *
        ((q : ℂ) * Complex.exp (((θ + Real.pi / 4 : ℝ) : ℂ) * Complex.I)) =
        (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [RiemannBoundary.quarticRootRotation, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  obtain ⟨hp, hx, hn, ha, hb, ht, hr, hqtr⟩ := wedge_angle u hi hw
  obtain ⟨hq, hpolar, hpow, h4a, h4b, hneg, hsa, hsb, him, harg⟩ :=
    polar_negative_fourth u hn hqtr hb
  have hroot := root_polar_recipe u harg
  have hreverse : RiemannBoundary.rotatedPrincipalRootFour (-(u ^ 4)) = u := by
    rw [RiemannBoundary.rotatedPrincipalRootFour, hroot, rotation_recipe, ← hpolar]
  exact ⟨hp, hx, hn, ha, hb, ht, hr, hqtr, hq, hpolar, hpow, h4a, h4b,
    hneg, hsa, hsb, him, harg, hroot, hreverse⟩
