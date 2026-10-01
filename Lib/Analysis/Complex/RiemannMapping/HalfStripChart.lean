/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.DiscBoundaryEscape

/-!
# The logarithmic chart of a half-strip

For `a c : ℝ` with `0 < c`, `logHalfStrip a c q = a - i c log q` maps the upper half-plane
biholomorphically onto the half-strip `a < Re z < a + cπ` (with `Im z = -c log ‖q‖ → ∞` as
`q → 0`), and the real axis onto the two edges `Re z = a`, `Re z = a + cπ`; its inverse is
`halfStripExp a c z = exp (i (z - a) / c)`. The file records these elementary properties
(real and imaginary parts, continuity on the closed half-plane away from `0`, analyticity, the
inverse identity) and the one-point compactification picture: the chart extended by `0 ↦ ∞` is
continuous into `OnePoint ℂ`, and a domain `D ⊆ ℂ` that is cocompactly unbounded has `∞` in the
frontier of its image in `OnePoint ℂ`.

This is the standard chart at the end of a strip used for boundary behaviour of conformal maps at
an infinite vertex (Ahlfors, *Complex Analysis*, Ch. 6 §2, the Schwarz–Christoffel discussion).
-/

open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff Interval NNReal UniformConvergence Uniformity

noncomputable section

/-- `logHalfStrip a c q = a - i c log q`; for `c > 0` it maps the upper half-plane onto the
half-strip `a < Re z < a + cπ`. -/
def RiemannBoundary.logHalfStrip (a c : ℝ) (q : ℂ) : ℂ :=
  a - Complex.I * c * Complex.log q

/-- The real part of the logarithmic half-strip coordinate. -/
@[simp]
theorem RiemannBoundary.logHalfStrip_re (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).re = a + c * q.arg := by
  simp [logHalfStrip, Complex.mul_re, Complex.mul_im, Complex.log_im]

/-- The imaginary part of the logarithmic half-strip coordinate. -/
@[simp]
theorem RiemannBoundary.logHalfStrip_im (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).im = -c * Real.log ‖q‖ := by
  simp [logHalfStrip, Complex.mul_re, Complex.mul_im, Complex.log_re]

/-- The half-strip imaginary part tends to infinity. -/
theorem RiemannBoundary.tendsto_logHalfStrip_im_atTop (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun q : ℂ => (logHalfStrip a c q).im) (𝓝[≠] 0) Filter.atTop := by
  simp only [logHalfStrip_im]
  exact
    (Filter.tendsto_const_mul_atTop_of_neg (neg_neg_of_pos hc)).mpr
      (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)

/-- The disc norm along the half-strip tends to `1`. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_logHalfStrip {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (a : ℝ) {c : ℝ}
    (hc : 0 < c) (hmem : ∀ᶠ q in 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ), logHalfStrip a c q ∈ D) :
    Filter.Tendsto (fun q => ‖f (logHalfStrip a c q)‖) (𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ)) (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_im_atTop e he _ hmem
  apply (tendsto_logHalfStrip_im_atTop a hc).mono_left
  apply nhdsWithin_mono
  intro z hz
  change 0 < z.im at hz
  change z ≠ 0
  intro heq
  rw [heq, Complex.zero_im] at hz
  exact (lt_irrefl 0) hz

/-- The half-strip chart as a map into `OnePoint ℂ`, sending `0` to `∞`. -/
def RiemannBoundary.onePointLogHalfStrip (a c : ℝ) (q : ℂ) : OnePoint ℂ :=
  if q = 0 then (OnePoint.infty) else (logHalfStrip a c q : OnePoint ℂ)

/-- The half-strip coordinate at the marked point. -/
@[simp]
theorem RiemannBoundary.onePointLogHalfStrip_zero (a c : ℝ) :
    onePointLogHalfStrip a c 0 = (OnePoint.infty) := by simp [onePointLogHalfStrip]

/-- The half-strip coordinate off the marked point. -/
theorem RiemannBoundary.onePointLogHalfStrip_of_ne_zero (a c : ℝ) {q : ℂ} (hq : q ≠ 0) :
    onePointLogHalfStrip a c q = (logHalfStrip a c q : OnePoint ℂ) := by
  simp [onePointLogHalfStrip, hq]

/-- The half-strip coordinate tends to infinity cocompactly. -/
theorem RiemannBoundary.tendsto_logHalfStrip_cocompact (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (logHalfStrip a c) (𝓝[≠] 0) (Filter.cocompact ℂ) := by
  have hn : Filter.Tendsto (fun q : ℂ => ‖logHalfStrip a c q‖) (𝓝[≠] 0) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun q => Complex.im_le_norm (logHalfStrip a c q))
      (tendsto_logHalfStrip_im_atTop a hc)
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hn

/-- The coerced half-strip coordinate tends to `∞`. -/
theorem RiemannBoundary.tendsto_coe_logHalfStrip_infty (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun q : ℂ => (logHalfStrip a c q : OnePoint ℂ)) (𝓝[≠] 0)
      (𝓝 (OnePoint.infty)) := by
  have hcoe : Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (OnePoint.infty)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  exact hcoe.comp (tendsto_logHalfStrip_cocompact a hc)

/-- The one-point half-strip coordinate is continuous at zero. -/
theorem RiemannBoundary.continuousAt_onePointLogHalfStrip_zero (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousAt (onePointLogHalfStrip a c) 0 := by
  rw [continuousAt_iff_punctured_nhds, onePointLogHalfStrip_zero]
  apply (tendsto_coe_logHalfStrip_infty a hc).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (onePointLogHalfStrip_of_ne_zero a c hq).symm

/-- The image of `D ⊆ ℂ` in `OnePoint ℂ`. -/
def RiemannBoundary.onePointDomain (D : Set ℂ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' D

/-- A finite point lies in the one-point domain. -/
@[simp]
theorem RiemannBoundary.coe_mem_onePointDomain {D : Set ℂ} {z : ℂ} :
    (z : OnePoint ℂ) ∈ onePointDomain D ↔ z ∈ D := by exact OnePoint.coe_injective.mem_set_image

/-- `∞` is not in the one-point domain. -/
@[simp]
theorem RiemannBoundary.infty_notMem_onePointDomain (D : Set ℂ) :
    (OnePoint.infty) ∉ onePointDomain D :=
  OnePoint.infty_notMem_image_coe

/-- The one-point domain is open. -/
theorem RiemannBoundary.isOpen_onePointDomain {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (onePointDomain D) :=
  OnePoint.isOpen_image_coe.mpr hD

/-- `D` is homeomorphic to its image in `OnePoint ℂ`. -/
def RiemannBoundary.onePointDomainHomeomorph (D : Set ℂ) : D ≃ₜ onePointDomain D :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage D

/-- The one-point homeomorphism computes the coordinate. -/
@[simp]
theorem RiemannBoundary.onePointDomainHomeomorph_apply_coe (D : Set ℂ) (z : D) :
    (onePointDomainHomeomorph D z : OnePoint ℂ) = (z : ℂ) :=
  rfl

/-- A homeomorphism `D ≃ₜ 𝔻` transported to the image of `D` in `OnePoint ℂ`. -/
def RiemannBoundary.onePointDomainDiscHomeomorph {D : Set ℂ} (e : D ≃ₜ Metric.ball (0 : ℂ) 1) :
    onePointDomain D ≃ₜ Metric.ball (0 : ℂ) 1 :=
  (onePointDomainHomeomorph D).symm.trans e

/-- The disc homeomorphism computes the disc coordinate. -/
@[simp]
theorem RiemannBoundary.onePointDomainDiscHomeomorph_apply {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) (z : D) :
    onePointDomainDiscHomeomorph e (onePointDomainHomeomorph D z) = e z := by
  simp [onePointDomainDiscHomeomorph]

/-- If `f` restricts to `e : D ≃ₜ 𝔻`, then `OnePoint.elim b f` computes the transported
homeomorphism on the image of `D`. -/
theorem RiemannBoundary.onePointDomainDiscHomeomorph_representative {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (b : ℂ)
    (z : onePointDomain D) : (z : OnePoint ℂ).elim b f = (onePointDomainDiscHomeomorph e z : ℂ) :=
  by
  obtain ⟨w, rfl⟩ := (onePointDomainHomeomorph D).surjective z
  simpa only [onePointDomainHomeomorph_apply_coe, OnePoint.elim_some,
    onePointDomainDiscHomeomorph_apply] using he w

/-- If `z i ∈ D` eventually along a nontrivial filter and `z i` tends to infinity cocompactly, then
`∞` lies in the frontier of the image of `D` in `OnePoint ℂ`. -/
theorem RiemannBoundary.infty_mem_frontier_onePointDomain_of_cocompact {D : Set ℂ} {α : Type*}
    {l : Filter α} [Filter.NeBot l] {z : α → ℂ} (hz : Filter.Tendsto z l (Filter.cocompact ℂ))
    (hmem : ∀ᶠ i in l, z i ∈ D) : ((OnePoint.infty) : OnePoint ℂ) ∈ frontier (onePointDomain D) :=
  by
  have hcoe : Filter.Tendsto ((↑) : ℂ → OnePoint ℂ) (Filter.cocompact ℂ) (𝓝 (OnePoint.infty)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using (OnePoint.tendsto_coe_infty (X := ℂ))
  have hcl : ((OnePoint.infty) : OnePoint ℂ) ∈ closure (onePointDomain D) := by
    apply isClosed_closure.mem_of_tendsto (hcoe.comp hz)
    filter_upwards [hmem] with i hi
    exact subset_closure (coe_mem_onePointDomain.mpr hi)
  exact ⟨hcl, fun hi => infty_notMem_onePointDomain D (interior_subset hi)⟩

/-- The logarithm is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousWithinAt_log_closedUpper {q : ℂ} (hq : q ≠ 0) :
    ContinuousWithinAt Complex.log {z : ℂ | 0 ≤ z.im} q := by
  by_cases hi : q.im = 0
  · by_cases hr : 0 < q.re
    · exact (continuousAt_clog (Or.inl hr)).continuousWithinAt
    · have hre : q.re < 0 := by
        have hne : q.re ≠ 0 := by
          intro heq
          apply hq
          exact Complex.ext heq hi
        exact lt_of_le_of_ne (le_of_not_gt hr) hne
      exact Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hi
  · exact (continuousAt_clog (Or.inr hi)).continuousWithinAt

/-- The half-strip logarithm is continuous on the closed upper half-plane. -/
theorem RiemannBoundary.continuousWithinAt_logHalfStrip_closedUpper (a c : ℝ) {q : ℂ}
    (hq : q ≠ 0) : ContinuousWithinAt (logHalfStrip a c) {z : ℂ | 0 ≤ z.im} q := by
  exact
    continuousWithinAt_const.sub
      (continuousWithinAt_const.mul (continuousWithinAt_log_closedUpper hq))

/-- The half-strip logarithm is analytic on the upper half-plane. -/
theorem RiemannBoundary.analyticOnNhd_logHalfStrip_upper (a c : ℝ) :
    AnalyticOnNhd ℂ (logHalfStrip a c) {z : ℂ | 0 < z.im} := by
  intro q hq
  exact analyticAt_const.sub (analyticAt_const.mul (analyticAt_clog (Or.inr (ne_of_gt hq))))

/-- The half-strip real part lies in the strip interval. -/
theorem RiemannBoundary.logHalfStrip_re_mem_Ioo (a : ℝ) {c : ℝ} (hc : 0 < c) {q : ℂ}
    (hq : 0 < q.im) : (logHalfStrip a c q).re ∈ Set.Ioo a (a + c * Real.pi) := by
  have harg0 : q.arg ≠ 0 := fun h => (ne_of_gt hq) (Complex.arg_eq_zero_iff.mp h).2
  have harg : 0 < q.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hq.le) harg0.symm
  have hargπ : q.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hq))
  rw [logHalfStrip_re]
  constructor <;> nlinarith

/-- The half-strip real part of a real input. -/
theorem RiemannBoundary.logHalfStrip_real_re (a c : ℝ) (t : ℝ) :
    (logHalfStrip a c (t : ℂ)).re = a ∨ (logHalfStrip a c (t : ℂ)).re = a + c * Real.pi := by
  by_cases ht : 0 ≤ t
  · left
    simp [logHalfStrip_re, Complex.arg_ofReal_of_nonneg ht]
  · right
    simp [logHalfStrip_re, Complex.arg_ofReal_of_neg (lt_of_not_ge ht)]

/-- A half-strip height bounding the radius exists. -/
theorem RiemannBoundary.exists_logHalfStrip_height_radius (a B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ R > 0, ∀ q ∈ Metric.ball (0 : ℂ) R, q ≠ 0 → B < (logHalfStrip a c q).im := by
  have ht : ∀ᶠ q in 𝓝[≠] (0 : ℂ), B < (logHalfStrip a c q).im :=
    (tendsto_logHalfStrip_im_atTop a hc).eventually_gt_atTop B
  obtain ⟨R, hR, hs⟩ := Metric.mem_nhdsWithin_iff.mp ht
  exact ⟨R, hR, fun q hq hne => hs ⟨hq, hne⟩⟩

/-- `halfStripExp a c z = exp (i (z - a) / c)`, the inverse of `logHalfStrip a c` on the half-strip.
-/
def RiemannBoundary.halfStripExp (a c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (z - a) / c)

/-- The half-strip logarithm inverts the exponential. -/
theorem RiemannBoundary.logHalfStrip_halfStripExp (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Set.Ioo a (a + c * Real.pi)) : logHalfStrip a c (halfStripExp a c z) = z := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have him : (Complex.I * (z - a) / c).im = (z.re - a) / c := by simp
  have hpos : 0 < (Complex.I * (z - a) / c).im := by
    rw [him]
    exact div_pos (sub_pos.mpr hz.1) hc
  have hpi : (Complex.I * (z - a) / c).im < Real.pi := by
    rw [him, div_lt_iff₀ hc]
    linarith [hz.2]
  rw [logHalfStrip, halfStripExp, Complex.log_exp (by linarith [Real.pi_pos]) hpi.le]
  field_simp
  ring_nf
  simp

/-- The norm of the half-strip exponential. -/
@[simp]
theorem RiemannBoundary.norm_halfStripExp (a c : ℝ) (z : ℂ) :
    ‖halfStripExp a c z‖ = Real.exp (-z.im / c) := by simp [halfStripExp, Complex.norm_exp]

/-- The half-strip exponential has positive imaginary part. -/
theorem RiemannBoundary.halfStripExp_im_pos (a : ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z.re ∈ Set.Ioo a (a + c * Real.pi)) : 0 < (halfStripExp a c z).im := by
  rw [halfStripExp, Complex.exp_im]
  apply mul_pos (Real.exp_pos _)
  apply Real.sin_pos_of_pos_of_lt_pi
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, MulZeroClass.zero_mul, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      one_mul, zero_add]
    exact div_pos (sub_pos.mpr hz.1) hc
  · simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, MulZeroClass.zero_mul, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      one_mul, zero_add]
    rw [div_lt_iff₀ hc]
    linarith [hz.2]
