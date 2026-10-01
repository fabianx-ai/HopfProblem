/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.RiemannMapping.DiscBoundaryEscape
import Lib.Analysis.Complex.RiemannMapping.HalfStripChart
import Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection
import Lib.Analysis.Complex.RiemannMapping.BoundaryDerivative

/-!
# Conformal extension of a disc map across an analytic boundary arc

Let `f : D → 𝔻` be holomorphic and a homeomorphism onto the disc. If a chart `φ` of the closed upper
half-plane near a real point `x` maps the open half-plane into `D` and the real axis outside `D`,
then `f ∘ φ` extends across the real axis to a function `H` analytic near `x`, with `‖H‖ = 1` on the
real axis, `H' x ≠ 0`, and `‖H z‖ < 1 ↔ Im z > 0` near `x`
(`RiemannBoundary.exists_conformal_extension_discHomeomorph_in_half_chart`); the same holds at an
infinite vertex where `D` contains a half-strip, via the logarithmic half-strip chart
(`RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex`).

This is the reflection-principle proof that a Riemann map extends conformally across free analytic
boundary arcs (Ahlfors, *Complex Analysis*, Ch. 6 §1.4; Pommerenke, *Boundary Behaviour of
Conformal Maps*, §3.3).
-/

open Set Function Filter Manifold Topology

open scoped ComplexConjugate ContDiff Interval NNReal UniformConvergence Uniformity

noncomputable section

/-- For a partial homeomorphism `e` with `a ∈ e.source` and `r > 0`, some ball around `e a` lies in
`e.target` and is sent by `e.symm` into `B(a, r)`. -/
theorem RiemannMapping.exists_boundary_chart_target_ball (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ w ∈ Metric.ball (e a) δ, w ∈ e.target ∧ e.symm w ∈ Metric.ball a r := by
  have hat := e.map_source ha
  have hinv : Filter.Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
    have h := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hat)).tendsto
    rwa [e.left_inv ha] at h
  have hnear : ∀ᶠ w in 𝓝 (e a), w ∈ e.target ∧ e.symm w ∈ Metric.ball a r := by
    filter_upwards [e.open_target.mem_nhds hat, hinv.eventually (Metric.ball_mem_nhds a hr)] with
      w hw hb
    exact ⟨hw, hb⟩
  exact Metric.mem_nhds_iff.mp hnear

/-- Let `H` be continuous at a real `x` with `‖H x‖ = 1`, equal near `x` to `k` on the upper
half-plane, to `z ↦ (conj (k (conj z)))⁻¹` on the lower half-plane, of modulus `1` on the real axis,
with `‖k‖ < 1` on the upper half-plane. Then near `x`, `‖H z‖ < 1 ↔ Im z > 0`. -/
theorem RiemannBoundary.norm_lt_one_iff_im_pos_eventually {H k : ℂ → ℂ} {x : ℝ}
    (hH : ContinuousAt H (x : ℂ)) (hcenter : ‖H (x : ℂ)‖ = 1)
    (hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖k z‖ < 1) (hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = k z)
    (hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (k (conj z)))⁻¹)
    (hr : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1) : ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  have hcenter0 : H (x : ℂ) ≠ 0 := by
    intro hzero
    simp [hzero] at hcenter
  have hnz := hH.eventually_ne hcenter0
  have hconj : Filter.Tendsto (conj : ℂ → ℂ) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
    simpa only [Complex.conj_ofReal] using Complex.continuous_conj.tendsto (x : ℂ)
  have hkc := hconj.eventually hk
  filter_upwards [hk, hu, hl, hr, hnz, hkc] with z hzk hzu hzl hzr hzne hzconj
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hw : ‖k (conj z)‖ < 1 := hzconj (by simpa using hneg)
    have hw0 : k (conj z) ≠ 0 := by
      intro heq
      apply hzne
      rw [hzl hneg, heq]
      simp
    have hlarge : 1 < ‖H z‖ := by
      rw [hzl hneg, norm_inv, Complex.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw
    exact iff_of_false (not_lt_of_ge hlarge.le) (not_lt_of_ge hneg.le)
  · rw [hzr hzero]
    simp only [lt_self_iff_false, hzero]
  · rw [hzu hpos]
    exact iff_of_true (hzk hpos) hpos

/-- Under the hypotheses of `exists_analytic_extension_of_modulus_one` and `‖f‖ < 1` on `U ∩ {Im z >
0}`, the reflected extension `H` near a real `x ∈ U` moreover has a nonzero strict derivative at `x`
and satisfies `‖H z‖ < 1 ↔ Im z > 0` near `x`. -/
theorem RiemannBoundary.exists_conformal_extension_of_modulus_one {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U) (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod :
      ∀ t : ℝ,
        (t : ℂ) ∈ U → Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1))
    (hdisc : ∀ z ∈ U ∩ {z : ℂ | 0 < z.im}, ‖f z‖ < 1) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (conj z)))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
                  deriv H (x : ℂ) ≠ 0 ∧ ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨r, hr, H, hHa, hHe, hHl, hHc⟩ := exists_analytic_extension_of_modulus_one hU hx hf hmod
  have hHx := hHa (x : ℂ) (Metric.mem_ball_self hr)
  have hcenter := hHc x (Metric.mem_ball_self hr)
  have hk : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖f z‖ < 1 := by
    filter_upwards [hU.mem_nhds hx] with z hz hpos
    exact hdisc z ⟨hz, hpos⟩
  have hu : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → H z = f z := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hpos
    exact hHe ⟨hz, hpos⟩
  have hl : ∀ᶠ z in 𝓝 (x : ℂ), z.im < 0 → H z = (conj (f (conj z)))⁻¹ := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hneg
    exact hHl ⟨hz, hneg⟩
  have hreal : ∀ᶠ z in 𝓝 (x : ℂ), z.im = 0 → ‖H z‖ = 1 := by
    filter_upwards [Metric.ball_mem_nhds (x : ℂ) hr] with z hz hzero
    have heq : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hzero.symm)
    simpa only [heq] using hHc z.re (by simpa only [heq] using hz)
  have hinside : ∀ᶠ z in 𝓝 (x : ℂ), 0 < z.im → ‖H z‖ < 1 := by
    filter_upwards [hu, hk] with z heq hz hpos
    rw [heq hpos]
    exact hz hpos
  have hnonzero :=
    RiemannMapping.deriv_ne_zero_of_upper_halfPlane_to_unitDisc hHx (by simp) hcenter hinside
  exact
    ⟨r, hr, H, hHa, hHe, hHl, hHc, hHx.hasStrictDerivAt, hnonzero,
      norm_lt_one_iff_im_pos_eventually hHx.continuousAt hcenter hk hu hl hreal⟩

/-- Let `f` be holomorphic on `D` and restrict to a homeomorphism `D ≃ₜ 𝔻`, and let `φ` be
holomorphic on `U ∩ {Im z > 0}` (`U` open), continuous on `U ∩ {Im z ≥ 0}`, mapping `U ∩ {Im z > 0}`
into `D` and the real points of `U` outside `D`. Then near each real `x ∈ U`, `f ∘ φ` extends by
reflection to `H` analytic on a ball with `‖H‖ = 1` on the real axis, a nonzero strict derivative at
`x`, and `‖H z‖ < 1 ↔ Im z > 0` near `x`. -/
theorem RiemannBoundary.exists_conformal_extension_discHomeomorph_in_half_chart {D U : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f φ : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f D) (hφ : DifferentiableOn ℂ φ (U ∩ {z : ℂ | 0 < z.im}))
    (hφc : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : Set.MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D)
    (hout : ∀ t : ℝ, (t : ℂ) ∈ U → φ (t : ℂ) ∉ D) {x : ℝ} (hx : (x : ℂ) ∈ U) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H (f ∘ φ) (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (φ (conj z))))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H (x : ℂ)) (x : ℂ) ∧
                  deriv H (x : ℂ) ≠ 0 ∧ ∀ᶠ z in 𝓝 (x : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  apply exists_conformal_extension_of_modulus_one hU hx (hf.comp hφ hside)
  · intro t ht
    exact tendsto_norm_discHomeomorph_in_boundary_chart e he hU hφc hside ht (hout t ht)
  · intro z hz
    have hp := hside hz
    have hv := he ⟨φ z, hp⟩
    simpa only [Function.comp_def, Metric.mem_ball, dist_zero_right, ← hv] using
      (e ⟨φ z, hp⟩).property

/-- Let `f` be holomorphic on `D` and restrict to a homeomorphism `D ≃ₜ 𝔻`. If `D` contains the
half-strip `a < Re z < a + cπ`, `Im z > B` (`c > 0`), and its two edges above height `B` lie outside
`D`, then `f ∘ logHalfStrip a c` extends by reflection to `H` analytic on a ball around `0` with
`‖H‖ = 1` on the real axis, a nonzero strict derivative at `0`, and `‖H z‖ < 1 ↔ Im z > 0` near `0`.
-/
theorem RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ))
    (hf : DifferentiableOn ℂ f D) (a B : ℝ) {c : ℝ} (hc : 0 < c)
    (hstrip : ∀ z : ℂ, a < z.re → z.re < a + c * Real.pi → B < z.im → z ∈ D)
    (hedge : ∀ z : ℂ, B < z.im → (z.re = a ∨ z.re = a + c * Real.pi) → z ∉ D) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
          Set.EqOn H (f ∘ logHalfStrip a c) (Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (logHalfStrip a c (conj z))))⁻¹)
                (Metric.ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H 0) 0 ∧
                  deriv H 0 ≠ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨R, hR, hheight⟩ := exists_logHalfStrip_height_radius a B hc
  let U : Set ℂ := Metric.ball (0 : ℂ) R
  have hU : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hR
  have hside : Set.MapsTo (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) D := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro heq
      have hi := hq.2
      rw [heq] at hi
      exact (lt_irrefl (0 : ℝ)) hi
    have hRe := logHalfStrip_re_mem_Ioo a hc hq.2
    exact hstrip _ hRe.1 hRe.2 (hheight q hq.1 hq0)
  have hφ : DifferentiableOn ℂ (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    (analyticOnNhd_logHalfStrip_upper a c).differentiableOn.mono Set.inter_subset_right
  have hdiff : DifferentiableOn ℂ (f ∘ logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    hf.comp hφ hside
  have hmod :
    ∀ t : ℝ,
      (t : ℂ) ∈ U →
        Filter.Tendsto (fun q => ‖f (logHalfStrip a c q)‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ))
          (𝓝 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      apply tendsto_norm_discHomeomorph_logHalfStrip e he a hc
      have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0U)
      filter_upwards [hnear, self_mem_nhdsWithin] with q hq hi
      exact hside ⟨hq, hi⟩
    · let V : Set ℂ := U \ {0}
      have hV : IsOpen V := hU.sdiff isClosed_singleton
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
      have htV : (t : ℂ) ∈ V := ⟨ht, htC⟩
      have hcont : ContinuousOn (logHalfStrip a c) (V ∩ {z : ℂ | 0 ≤ z.im}) := by
        intro q hq
        exact (continuousWithinAt_logHalfStrip_closedUpper a c hq.1.2).mono Set.inter_subset_right
      have hsideV : Set.MapsTo (logHalfStrip a c) (V ∩ {z : ℂ | 0 < z.im}) D := by
        intro q hq
        exact hside ⟨hq.1.1, hq.2⟩
      exact
        tendsto_norm_discHomeomorph_in_boundary_chart e he hV hcont hsideV htV
          (hedge _ (hheight _ ht htC) (logHalfStrip_real_re a c t))
  apply exists_conformal_extension_of_modulus_one hU h0U hdiff hmod
  intro q hq
  have hp := hside hq
  have hv := he ⟨logHalfStrip a c q, hp⟩
  simpa only [Function.comp_def, Metric.mem_ball, dist_zero_right, ← hv] using
    (e ⟨logHalfStrip a c q, hp⟩).property
