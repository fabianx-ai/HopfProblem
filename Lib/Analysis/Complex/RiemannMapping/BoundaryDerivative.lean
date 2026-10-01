/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# Nonvanishing derivative at a boundary point of the upper half-plane

If `f` is analytic at a real point `a`, `f a = 0`, and `f` maps nearby points of the upper half-plane
into the upper half-plane, then `f` has a zero of order exactly one at `a`, so `f' a ≠ 0`: a zero of
order `m ≥ 2` would rotate some direction of the upper half-plane into the lower half-plane. Through
the boundary logarithm `-i log (f z / f a)` the same holds for a map `f` analytic at `a` with
`‖f a‖ = 1` sending the upper half-plane near `a` into the unit disc.

This is the local form of conformality at the boundary for maps that extend by reflection (cf.
Ahlfors, *Complex Analysis*, Ch. 6 §1.4; Pommerenke, *Boundary Behaviour of Conformal Maps*, §3.1).
-/

open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff Interval NNReal UniformConvergence Uniformity

noncomputable section

/-- `Im (c e^{iθ}) = ‖c‖ sin (arg c + θ)`. -/
theorem RiemannMapping.im_mul_exp_real (c : ℂ) (θ : ℝ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I)).im = ‖c‖ * Real.sin (c.arg + θ) := by
  calc
    (c * Complex.exp ((θ : ℂ) * Complex.I)).im =
        (((‖c‖ : ℝ) : ℂ) *
            (Complex.exp ((c.arg : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I))).im := by
      rw [← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
    _ = (((‖c‖ : ℝ) : ℂ) * Complex.exp (((c.arg + θ : ℝ) : ℂ) * Complex.I)).im := by
      rw [← Complex.exp_add]
      congr 3
      push_cast
      ring
    _ = ‖c‖ * Real.sin (c.arg + θ) := by rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- `Im (c (e^{iθ})ⁿ) = ‖c‖ sin (arg c + n θ)`. -/
theorem RiemannMapping.im_mul_exp_real_pow (c : ℂ) (θ : ℝ) (n : ℕ) :
    (c * Complex.exp ((θ : ℂ) * Complex.I) ^ n).im = ‖c‖ * Real.sin (c.arg + (n : ℝ) * θ) := by
  rw [← Complex.exp_nat_mul]
  have h : (n : ℂ) * ((θ : ℂ) * Complex.I) = (((n : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h]
  exact im_mul_exp_real c ((n : ℝ) * θ)

/-- For `c ≠ 0` and `n ≥ 2` some unit `v` in the upper half-plane has `c vⁿ` in the lower
half-plane. -/
theorem RiemannMapping.exists_unit_upperHalf_power_direction {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ∃ v : ℂ, ‖v‖ = 1 ∧ 0 < v.im ∧ (c * v ^ n).im < 0 := by
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hc₀ : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hπ : 0 < Real.pi := Real.pi_pos
  have ha₁ : -Real.pi < c.arg := Complex.neg_pi_lt_arg c
  have ha₂ : c.arg ≤ Real.pi := Complex.arg_le_pi c
  have hπn : 2 * Real.pi ≤ Real.pi * n := by nlinarith
  by_cases ha : -(Real.pi / 2) < c.arg
  · let θ : ℝ := (3 * Real.pi / 2 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = 3 * Real.pi / 2 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow, hphase]
      rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
        Real.sin_pi_div_two]
      linarith
  · have ha' : c.arg ≤ -(Real.pi / 2) := le_of_not_gt ha
    let θ : ℝ := (-Real.pi / 4 - c.arg) / n
    have hθ₀ : 0 < θ := div_pos (by linarith) hn₀
    have hθπ : θ < Real.pi := by
      apply (div_lt_iff₀ hn₀).mpr
      linarith
    have hphase : c.arg + (n : ℝ) * θ = -Real.pi / 4 := by
      dsimp [θ]
      rw [mul_comm (n : ℝ), div_mul_cancel₀ _ hn₀.ne']
      ring
    refine ⟨Complex.exp ((θ : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I θ, ?_, ?_⟩
    · rw [Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ
    · rw [im_mul_exp_real_pow, hphase]
      exact
        mul_neg_of_pos_of_neg hc₀ (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))

/-- For `c ≠ 0` and `n ≥ 2` some `v` in the upper half-plane has `c vⁿ` in the lower half-plane. -/
theorem RiemannMapping.exists_upperHalf_power_direction {c : ℂ} (hc : c ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) : ∃ v : ℂ, 0 < v.im ∧ (c * v ^ n).im < 0 := by
  obtain ⟨v, _, hv, hcv⟩ := exists_unit_upperHalf_power_direction hc hn
  exact ⟨v, hv, hcv⟩

/-- `a + t v → a` as `t → 0⁺`. -/
theorem RiemannMapping.tendsto_boundaryRay (a v : ℂ) :
    Filter.Tendsto (fun t : ℝ => a + (t : ℂ) * v) (𝓝[>] 0) (𝓝 a) := by
  have hc : Continuous (fun t : ℝ => a + (t : ℂ) * v) := by fun_prop
  simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

/-- For real `a`, `Im v > 0` and `t > 0`, the point `a + t v` lies in the upper half-plane. -/
theorem RiemannMapping.boundaryRay_im_pos {a v : ℂ} (ha : a.im = 0) (hv : 0 < v.im) {t : ℝ}
    (ht : 0 < t) : 0 < (a + (t : ℂ) * v).im := by
  simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, ha,
    MulZeroClass.zero_mul, MulZeroClass.mul_zero, add_zero, zero_add] using mul_pos ht hv

/-- If `f` maps the upper half-plane near a real point `a` into the upper half-plane, then `f` does
not vanish identically near `a`. -/
theorem RiemannMapping.analyticOrderAt_ne_top_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (ha : a.im = 0) (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : analyticOrderAt f a ≠ ⊤ := by
  intro htop
  have hz := (tendsto_boundaryRay a Complex.I).eventually (analyticOrderAt_eq_top.mp htop)
  have hp := (tendsto_boundaryRay a Complex.I).eventually hupper
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] 0, False := by
    filter_upwards [self_mem_nhdsWithin, hz, hp] with t ht hzero hpos
    have hi := hpos (boundaryRay_im_pos ha (by simp) ht)
    simp only [hzero, Complex.zero_im, lt_self_iff_false] at hi
  obtain ⟨t, ht⟩ := hfalse.exists
  exact ht

/-- If `f z = (z - a) ^ m u z` near a real point `a` with `u` continuous at `a`, and `f` maps the
upper half-plane near `a` into the upper half-plane, then `Im (vᵐ u a) ≥ 0` whenever `Im v > 0`. -/
theorem RiemannMapping.nonneg_im_leading_of_upper_halfPlane {f u : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (ha : a.im = 0) (hu : ContinuousAt u a) (hfactor : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ m * u z)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) {v : ℂ} (hv : 0 < v.im) :
    0 ≤ (v ^ m * u a).im := by
  have hray := tendsto_boundaryRay a v
  have hlimC :
    Filter.Tendsto (fun t : ℝ => v ^ m * u (a + (t : ℂ) * v)) (𝓝[>] 0) (𝓝 (v ^ m * u a)) :=
    tendsto_const_nhds.mul (hu.tendsto.comp hray)
  have hlim :
    Filter.Tendsto (fun t : ℝ => (v ^ m * u (a + (t : ℂ) * v)).im) (𝓝[>] 0)
      (𝓝 (v ^ m * u a).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlimC
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin, hray.eventually hfactor, hray.eventually hupper] with t ht
    hft hpos
  have hft' : (f (a + (t : ℂ) * v)).im = t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [hft, add_sub_cancel_left, mul_pow, mul_assoc]
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      MulZeroClass.zero_mul, add_zero]
  have hp : 0 < t ^ m * (v ^ m * u (a + (t : ℂ) * v)).im := by
    rw [← hft']
    exact hpos (boundaryRay_im_pos ha hv ht)
  exact ((mul_pos_iff_of_pos_left (pow_pos ht m)).mp hp).le

/-- If `f` is analytic at a real point `a`, `f a = 0`, and `f` maps the upper half-plane near `a`
into the upper half-plane, then `f` has a zero of order one at `a`. -/
theorem RiemannMapping.analyticOrderAt_eq_one_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : analyticOrderAt f a = 1 := by
  have hfin := analyticOrderAt_ne_top_of_upper_halfPlane ha hupper
  let m := analyticOrderNatAt f a
  have horder : (m : ℕ∞) = analyticOrderAt f a := Nat.cast_analyticOrderNatAt hfin
  have hm0 : m ≠ 0 := by
    intro hm
    have hf0 : analyticOrderAt f a = 0 := by simpa [hm] using horder.symm
    exact (hf.analyticOrderAt_ne_zero.mpr hfa) hf0
  obtain ⟨u, hu, hua, hfactor⟩ := hf.analyticOrderAt_eq_natCast.mp horder.symm
  have hm2 : ¬2 ≤ m := by
    intro hm
    obtain ⟨v, hv, hneg⟩ := exists_upperHalf_power_direction hua hm
    have hnonneg : 0 ≤ (v ^ m * u a).im :=
      nonneg_im_leading_of_upper_halfPlane ha hu.continuousAt
        (by simpa only [smul_eq_mul] using hfactor) hupper hv
    rw [mul_comm] at hneg
    exact hneg.not_ge hnonneg
  have hm : m = 1 := by omega
  rw [← horder, hm]
  rfl

/-- If `f` is analytic at a real point `a`, `f a = 0`, and `f` maps the upper half-plane near `a`
into the upper half-plane, then `deriv f a ≠ 0`. -/
theorem RiemannMapping.deriv_ne_zero_of_upper_halfPlane {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : f a = 0)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (f z).im) : deriv f a ≠ 0 := by
  have ho := analyticOrderAt_eq_one_of_upper_halfPlane hf ha hfa hupper
  have hd := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp ho
  simpa only [iteratedDeriv_one] using hd.2

/-- `boundaryLog f a z = -i log (f z / f a)`. -/
def RiemannMapping.boundaryLog (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  -Complex.I * Complex.log (f z / f a)

/-- `boundaryLog f a a = 0` when `f a ≠ 0`. -/
@[simp]
theorem RiemannMapping.boundaryLog_self {f : ℂ → ℂ} {a : ℂ} (hfa : f a ≠ 0) :
    boundaryLog f a a = 0 := by simp [boundaryLog, hfa]

/-- `boundaryLog f a` is analytic at `a` when `f` is and `f a ≠ 0`. -/
theorem RiemannMapping.analyticAt_boundaryLog {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hfa : f a ≠ 0) : AnalyticAt ℂ (boundaryLog f a) a := by
  have hratio : AnalyticAt ℂ (fun z => f z / f a) a := hf.div_const
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  exact analyticAt_const.mul (hratio.clog hslit)

/-- If `f' a = d` and `f a ≠ 0`, then `boundaryLog f a` has derivative `-i d / f a` at `a`. -/
theorem RiemannMapping.hasDerivAt_boundaryLog {f : ℂ → ℂ} {a d : ℂ} (hf : HasDerivAt f d a)
    (hfa : f a ≠ 0) : HasDerivAt (boundaryLog f a) (-Complex.I * (d / f a)) a := by
  have hslit : f a / f a ∈ Complex.slitPlane := by simp [hfa]
  have hlog := (hf.div_const (f a)).clog hslit
  change HasDerivAt (fun z => -Complex.I * Complex.log (f z / f a)) (-Complex.I * (d / f a)) a
  simpa only [div_self hfa, div_one] using hlog.const_mul (-Complex.I)

/-- If `‖f a‖ = 1`, `f z ≠ 0` and `‖f z‖ < 1`, then `Im (boundaryLog f a z) > 0`. -/
theorem RiemannMapping.im_boundaryLog_pos {f : ℂ → ℂ} {a z : ℂ} (hfa : ‖f a‖ = 1) (hfz : f z ≠ 0)
    (hz : ‖f z‖ < 1) : 0 < (boundaryLog f a z).im := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hratio0 : 0 < ‖f z / f a‖ := norm_pos_iff.mpr (div_ne_zero hfz hfa0)
  have hratio1 : ‖f z / f a‖ < 1 := by simpa only [norm_div, hfa, div_one] using hz
  have hlog := Real.log_neg hratio0 hratio1
  simpa [boundaryLog, Complex.mul_im, Complex.log_re] using neg_pos.mpr hlog

/-- If `f` is analytic at a real point `a`, `‖f a‖ = 1`, and `f` maps the upper half-plane near `a`
into the open unit disc, then `deriv f a ≠ 0`. -/
theorem RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (ha : a.im = 0) (hfa : ‖f a‖ = 1)
    (hupper : ∀ᶠ z in 𝓝 a, 0 < z.im → ‖f z‖ < 1) : deriv f a ≠ 0 := by
  have hfa0 : f a ≠ 0 := by
    intro hzero
    simp [hzero] at hfa
  have hnz : ∀ᶠ z in 𝓝 a, f z ≠ 0 := hf.continuousAt.eventually_ne hfa0
  have hlogUpper : ∀ᶠ z in 𝓝 a, 0 < z.im → 0 < (boundaryLog f a z).im := by
    filter_upwards [hupper, hnz] with z hz hzne hzim
    exact im_boundaryLog_pos hfa hzne (hz hzim)
  have hlogDeriv :=
    deriv_ne_zero_of_upper_halfPlane (analyticAt_boundaryLog hf hfa0) ha (boundaryLog_self hfa0)
      hlogUpper
  intro hderiv
  apply hlogDeriv
  simpa [hderiv] using (hasDerivAt_boundaryLog hf.differentiableAt.hasDerivAt hfa0).deriv
