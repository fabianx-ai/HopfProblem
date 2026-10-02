/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.PrincipalRoot

/-!
# Cube-root wedge reversal for the center construction's corners

Center-construction material: the reversal of `principalRoot 3` on the open wedge
`0 < arg u < π / 3`, consumed by the corner-three analysis of the center construction.
Moved verbatim from `Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`.
-/

open Set Function Filter Topology

noncomputable section

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
