/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Analysis.Complex.SchwarzReflection
import Lib.Analysis.Complex.RiemannMapping.RectanglePrimitive

/-!
# Reflection across a boundary arc of modulus one

Let `f` be holomorphic and bounded above the real segment `(a, b)` and `g` below it, with
`f z - g (conj z) → 0` as `z` approaches the segment from above. Then `f` and `g` are the
restrictions of one function analytic on the full rectangle (a Painlevé/Morera-type gluing proved via
continuous primitives on the two half-rectangles). Applied to `g z = 1 / conj (f (conj z))`, this is
the Schwarz reflection principle across the unit circle: if `‖f z‖ → 1` as `z` approaches a real
interval from above, `f` extends analytically across the interval with `‖f‖ = 1` on it
(`RiemannBoundary.exists_analytic_extension_of_modulus_one`).

Reference: Ahlfors, *Complex Analysis*, Ch. 4 §6.5 and Ch. 6 §1.4 (reflection principle and its use
for boundary extension of conformal maps); Rudin, *Real and Complex Analysis*, Thm 11.14.
-/

open Set Function Filter Topology

open scoped ComplexConjugate

noncomputable section

/-- If `F` has derivative `f` at `x + y i`, then `t ↦ F (t + y i)` has derivative `f` at `x`. -/
theorem RiemannBoundary.hasDerivAt_horizontal {F : ℂ → ℂ} {f : ℂ} {x y : ℝ}
    (hF : HasDerivAt F f ((x : ℂ) + y * Complex.I)) :
    HasDerivAt (fun t : ℝ => F (t + y * Complex.I)) f x := by
  have h := hF.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (y * Complex.I))
  simpa only [mul_one, Function.comp_def, id_eq] using h.comp_ofReal

/-- If `q z → 0` as `z → x` from the upper half-plane, then `q (t + y i) → 0` uniformly for `t` near
`x` as `y → 0⁺`. -/
theorem RiemannBoundary.upper_limit_tendstoUniformlyOnFilter {q : ℂ → ℂ} {x : ℝ}
    (hq : Filter.Tendsto q (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    TendstoUniformlyOnFilter (fun y t : ℝ => q (t + y * Complex.I)) (fun _ => 0) (𝓝[>] 0) (𝓝 x) :=
  by
  have ht :
    Filter.Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ) + p.1 * Complex.I) ((𝓝[>] 0) ×ˢ 𝓝 x)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h₁ : Filter.Tendsto (fun p : ℝ × ℝ => (p.1 : ℂ)) ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (0 : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (Filter.tendsto_fst.mono_right nhdsWithin_le_nhds)
      have h₂ : Filter.Tendsto (fun p : ℝ × ℝ => (p.2 : ℂ)) ((𝓝[>] 0) ×ˢ 𝓝 x) (𝓝 (x : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp Filter.tendsto_snd
      simpa using h₂.add (h₁.mul_const Complex.I)
    · have hy : ∀ᶠ p : ℝ × ℝ in (𝓝[>] 0) ×ˢ 𝓝 x, 0 < p.1 :=
        Filter.tendsto_fst.eventually eventually_mem_nhdsWithin
      filter_upwards [hy] with p hp
      simpa using hp
  apply Metric.tendstoUniformlyOnFilter_iff.mpr
  intro ε hε
  simpa only [Function.comp_def, dist_zero_left, dist_zero_right] using
    Metric.tendsto_nhds.mp (hq.comp ht) ε hε

/-- Let `F`, `G` be continuous with `F' = f` on `(a, b) × (0, h)` and `G' = g` on `(a, b) × (-h,
0)`. If `f z - g (conj z) → 0` as `z` approaches each point of `(a, b)` from above, then `t ↦ F t -
G t` has derivative `0` at every `x ∈ (a, b)`. -/
theorem RiemannBoundary.hasDerivAt_boundary_trace_sub {F G f g : ℂ → ℂ} {a b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (t + y * Complex.I)) (t + y * Complex.I))
    (hGd :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (t - y * Complex.I)) (t - y * Complex.I))
    (hjump :
      ∀ t ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 0)) :
    HasDerivAt (fun t : ℝ => F t - G t) 0 x := by
  let H : ℝ → ℝ → ℂ := fun y t => F (t + y * Complex.I) - G (t - y * Complex.I)
  let H' : ℝ → ℝ → ℂ := fun y t => f (t + y * Complex.I) - g (t - y * Complex.I)
  have hd : ∀ᶠ y in 𝓝[>] 0, ∀ t ∈ Set.Ioo a b, HasDerivAt (H y) (H' y t) t := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy t ht
    have hu := hasDerivAt_horizontal (hFd t ht y hy)
    have hl : HasDerivAt (fun s : ℝ => G (s - y * Complex.I)) (g (t - y * Complex.I)) t := by
      have hi :=
        hasDerivAt_horizontal (y := -y)
          (by simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hGd t ht y hy)
      simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hi
    exact hu.sub hl
  have hdu : TendstoLocallyUniformlyOn H' (fun _ => 0) (𝓝[>] 0) (Set.Ioo a b) := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro t ht
    rw [isOpen_Ioo.nhdsWithin_eq ht]
    simpa only [H', map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      ← sub_eq_add_neg] using upper_limit_tendstoUniformlyOnFilter (hjump t ht)
  have hlim :
    ∀ t ∈ Set.Ioo a b, Filter.Tendsto (fun y => H y t) (𝓝[>] 0) (𝓝 (F (t : ℂ) - G (t : ℂ))) := by
    intro t _
    have hc : Continuous (fun y : ℝ => H y t) := by dsimp [H]; fun_prop
    simpa [H] using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo hdu hd hlim hx

/-- Under the hypotheses of `hasDerivAt_boundary_trace_sub`, `F - G` takes the same value at any two
points of `(a, b)`. -/
theorem RiemannBoundary.boundary_trace_sub_eq {F G f g : ℂ → ℂ} {a b h x t : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hF : Continuous F) (hG : Continuous G)
    (hFd :
      ∀ s ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (s + y * Complex.I)) (s + y * Complex.I))
    (hGd :
      ∀ s ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (s - y * Complex.I)) (s - y * Complex.I))
    (hjump :
      ∀ s ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (s : ℂ)) (𝓝 0)) :
    F (x : ℂ) - G (x : ℂ) = F (t : ℂ) - G (t : ℂ) := by
  have hd (s : ℝ) (hs : s ∈ Set.Ioo a b) :=
    hasDerivAt_boundary_trace_sub hh hs hF hG hFd hGd hjump
  exact
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) hx ht

/-- If `f` is holomorphic and bounded on `(a, b) × (0, h)`, `g` on `(a, b) × (-h, 0)`, and `f z - g
(conj z) → 0` as `z` approaches each point of `(a, b)` from above, then some `H` analytic on `(a, b)
× (-h, h)` equals `f` above and `g` below the real axis. -/
theorem RiemannBoundary.exists_analytic_extension_of_vanishing_jump {f g : ℂ → ℂ} {a b h M N : ℝ}
    (hab : a < b) (hh : 0 < h) (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M)
    (hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ N)
    (hjump :
      ∀ x ∈ Set.Ioo a b,
        Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0)) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
        Set.EqOn H f (openRectangle a b 0 h) ∧ Set.EqOn H g (openRectangle a b (-h) 0) := by
  obtain ⟨F, hFc, hFd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hf hfb
  obtain ⟨G, hGc, hGd⟩ := exists_continuous_primitive_openRectangle_of_norm_le hg hgb
  let x₀ : ℝ := (a + b) / 2
  have hx₀ : x₀ ∈ Set.Ioo a b := by dsimp [x₀]; constructor <;> linarith
  let c : ℂ := F x₀ - G x₀
  have htrace : ∀ x ∈ Set.Ioo a b, F (x : ℂ) = G (x : ℂ) + c := by
    intro x hx
    have hdF :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt F (f (t + y * Complex.I)) (t + y * Complex.I) := by
      intro t ht y hy
      exact hFd _ (by simpa [openRectangle] using And.intro ht hy)
    have hdG :
      ∀ t ∈ Set.Ioo a b,
        ∀ y ∈ Set.Ioo 0 h, HasDerivAt G (g (t - y * Complex.I)) (t - y * Complex.I) := by
      intro t ht y hy
      apply hGd
      simpa [openRectangle] using
        And.intro ht (show -y ∈ Set.Ioo (-h) 0 by constructor <;> linarith [hy.1, hy.2])
    have he := boundary_trace_sub_eq hh hx hx₀ hFc hGc hdF hdG hjump
    dsimp [c]
    linear_combination he
  let P := SchwarzReflection.pasteUpper F (fun z => G z + c)
  have hP : AnalyticOnNhd ℂ P (openRectangle a b (-h) h) := by
    apply
      SchwarzReflection.analyticOnNhd_pasteUpper (isOpen_openRectangle _ _ _ _) hFc.continuousOn
        (hGc.add continuous_const).continuousOn
    · intro z hz hpos
      exact (hFd z ⟨hz.1, hpos, hz.2.2⟩).differentiableAt
    · intro z hz hneg
      exact ((hGd z ⟨hz.1, hz.2.1, hneg⟩).add_const c).differentiableAt
    · intro z hz hzero
      change F z = G z + c
      have heq : (z.re : ℂ) = z := by exact Complex.ext (by simp) (by simpa using hzero.symm)
      simpa only [heq] using htrace z.re hz.1
  refine ⟨deriv P, hP.deriv, ?_, ?_⟩
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] F := by
      filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt
          hz.2.1] with
        w hw
      exact SchwarzReflection.pasteUpper_of_nonneg F (fun w => G w + c) hw.le
    exact ((hFd z hz).congr_of_eventuallyEq hnear).deriv
  · intro z hz
    have hnear : P =ᶠ[𝓝 z] (fun w => G w + c) := by
      filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const
          hz.2.2] with
        w hw
      exact SchwarzReflection.pasteUpper_of_neg F (fun w => G w + c) hw
    exact (((hGd z hz).add_const c).congr_of_eventuallyEq hnear).deriv

/-- `‖w - (conj w)⁻¹‖ = |‖w‖ ^ 2 - 1| / ‖w‖`. -/
theorem RiemannBoundary.norm_sub_inv_conj (w : ℂ) : ‖w - (conj w)⁻¹‖ = |‖w‖ ^ 2 - 1| / ‖w‖ := by
  have heq : w - (conj w)⁻¹ = ((‖w‖ ^ 2 - 1 : ℝ) : ℂ) / conj w := by
    by_cases hw : w = 0
    · simp [hw]
    have hc : conj w ≠ 0 := by simpa using hw
    apply (eq_div_iff hc).mpr
    rw [sub_mul, inv_mul_cancel₀ hc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_sub, Complex.ofReal_one]
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]

/-- If `‖f x‖ → 1`, then `f x - (conj (f x))⁻¹ → 0`. -/
theorem RiemannBoundary.tendsto_sub_inv_conj_of_norm {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Filter.Tendsto (fun x => ‖f x‖) l (𝓝 1)) :
    Filter.Tendsto (fun x => f x - (conj (f x))⁻¹) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_sub_inv_conj]
  have hn : Filter.Tendsto (fun x => |‖f x‖ ^ 2 - 1|) l (𝓝 (0 : ℝ)) := by
    simpa using ((hf.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  have hdiv := hn.div hf one_ne_zero
  have hfun :
    ((fun x => |‖f x‖ ^ 2 - 1|) / (fun x => ‖f x‖)) = (fun x => |‖f x‖ ^ 2 - 1| / ‖f x‖) := by rfl
  rw [hfun] at hdiv
  simpa only [zero_div] using hdiv

/-- If `H` is continuous on `(a, b) × (-h, h)`, equals `f` on `(a, b) × (0, h)`, and `‖f z‖ → 1` as
`z → x` from above for some `x ∈ (a, b)`, then `‖H x‖ = 1`. -/
theorem RiemannBoundary.norm_axis_eq_one_of_extension {H f : ℂ → ℂ} {a b h x : ℝ} (hh : 0 < h)
    (hx : x ∈ Set.Ioo a b) (hH : ContinuousOn H (openRectangle a b (-h) h))
    (heq : Set.EqOn H f (openRectangle a b 0 h))
    (hmod : Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ‖H (x : ℂ)‖ = 1 := by
  have hxU : (x : ℂ) ∈ openRectangle a b (-h) h := by
    simpa [openRectangle] using
      And.intro hx (show (0 : ℝ) ∈ Set.Ioo (-h) h by constructor <;> linarith)
  have hHt : Filter.Tendsto (fun y : ℝ => ‖H (x + y * Complex.I)‖) (𝓝[>] 0) (𝓝 ‖H (x : ℂ)‖) := by
    have hcont := (hH.continuousAt ((isOpen_openRectangle _ _ _ _).mem_nhds hxU)).norm
    have ht : Filter.Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    exact hcont.tendsto.comp ht
  have hft : Filter.Tendsto (fun y : ℝ => ‖f (x + y * Complex.I)‖) (𝓝[>] 0) (𝓝 1) := by
    apply hmod.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have hevent :
    (fun y : ℝ => ‖H (x + y * Complex.I)‖) =ᶠ[𝓝[>] 0] (fun y : ℝ => ‖f (x + y * Complex.I)‖) := by
    filter_upwards [Ioo_mem_nhdsGT hh] with y hy
    rw [heq (by simpa [openRectangle] using And.intro hx hy)]
  exact tendsto_nhds_unique hHt (hft.congr' hevent.symm)

/-- Schwarz reflection in the circle on a rectangle: if `f` is holomorphic on `(a, b) × (0, h)` with
`m ≤ ‖f‖ ≤ M` (`m > 0`) and `‖f z‖ → 1` as `z` approaches each point of `(a, b)` from above, then
some `H` analytic on `(a, b) × (-h, h)` equals `f` above the axis, `z ↦ (conj (f (conj z)))⁻¹` below
it, and has modulus `1` on `(a, b)`. -/
theorem RiemannBoundary.exists_analytic_extension_of_modulus_one_bounded {f : ℂ → ℂ}
    {a b h M m : ℝ} (hab : a < b) (hh : 0 < h) (hm : 0 < m)
    (hf : DifferentiableOn ℂ f (openRectangle a b 0 h))
    (hfb : ∀ z ∈ openRectangle a b 0 h, ‖f z‖ ≤ M) (hfl : ∀ z ∈ openRectangle a b 0 h, m ≤ ‖f z‖)
    (hmod :
      ∀ x ∈ Set.Ioo a b, Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1)) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (openRectangle a b (-h) h) ∧
        Set.EqOn H f (openRectangle a b 0 h) ∧
          Set.EqOn H (fun z => (conj (f (conj z)))⁻¹) (openRectangle a b (-h) 0) ∧
            ∀ x ∈ Set.Ioo a b, ‖H (x : ℂ)‖ = 1 := by
  let g : ℂ → ℂ := fun z => (conj (f (conj z)))⁻¹
  have hconj : ∀ z ∈ openRectangle a b (-h) 0, conj z ∈ openRectangle a b 0 h := by
    intro z hz
    refine ⟨by simpa using hz.1, ?_⟩
    simp only [Complex.conj_im, Set.mem_Ioo]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hnz : ∀ z ∈ openRectangle a b 0 h, f z ≠ 0 := by
    intro z hz heq
    have hb := hfl z hz
    rw [heq, norm_zero] at hb
    exact (not_le.mpr hm) hb
  have hg : DifferentiableOn ℂ g (openRectangle a b (-h) 0) := by
    intro z hz
    have hd :=
      (hf.differentiableAt ((isOpen_openRectangle _ _ _ _).mem_nhds (hconj z hz))).conj_conj
    have hd' : DifferentiableAt ℂ (fun w => conj (f (conj w))) z := by
      simpa only [Function.comp_def, starRingEnd_self_apply] using hd
    exact (hd'.inv (by simpa using hnz (conj z) (hconj z hz))).differentiableWithinAt
  have hgb : ∀ z ∈ openRectangle a b (-h) 0, ‖g z‖ ≤ m⁻¹ := by
    intro z hz
    simp only [g, norm_inv, Complex.norm_conj]
    exact (inv_le_inv₀ (hm.trans_le (hfl _ (hconj z hz))) hm).mpr (hfl _ (hconj z hz))
  have hjump :
    ∀ x ∈ Set.Ioo a b,
      Filter.Tendsto (fun z => f z - g (conj z)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 0) := by
    intro x hx
    simpa only [g, starRingEnd_self_apply] using tendsto_sub_inv_conj_of_norm (hmod x hx)
  obtain ⟨H, hH, he, hl⟩ := exists_analytic_extension_of_vanishing_jump hab hh hf hg hfb hgb hjump
  exact
    ⟨H, hH, he, hl, fun x hx =>
      norm_axis_eq_one_of_extension hh hx hH.continuousOn he (hmod x hx)⟩

/-- Points of the rectangle `(x - r, x + r) × (-r, r)` lie within distance `2 r` of `x`. -/
theorem RiemannBoundary.dist_lt_two_mul_of_mem_centeredRectangle {x r : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle (x - r) (x + r) (-r) r) : Dist.dist z (x : ℂ) < 2 * r := by
  have hre : |(z - x).re| < r := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact abs_lt.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |(z - x).im| < r := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using abs_lt.mpr hz.2
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (z - x)).trans_lt (by linarith)

/-- The ball `B(x, r)` lies in the rectangle `(x - r, x + r) × (-r, r)`. -/
theorem RiemannBoundary.ball_subset_centeredRectangle (x r : ℝ) :
    Metric.ball (x : ℂ) r ⊆ openRectangle (x - r) (x + r) (-r) r := by
  intro z hz
  have hn : ‖z - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hre := abs_lt.mp ((Complex.abs_re_le_norm (z - x)).trans_lt hn)
  have him := abs_lt.mp ((Complex.abs_im_le_norm (z - x)).trans_lt hn)
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero] at hre him
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩

/-- Schwarz reflection in the circle: let `U` be open and `f` holomorphic on `U ∩ {Im z > 0}` with
`‖f z‖ → 1` as `z` approaches any real point of `U` from above. Then near each real `x ∈ U` some `H`
analytic on a ball `B(x, r)` equals `f` on its upper half, `z ↦ (conj (f (conj z)))⁻¹` on its lower
half, and has modulus `1` at its real points (Ahlfors, *Complex Analysis*, Ch. 4 §6.5). -/
theorem RiemannBoundary.exists_analytic_extension_of_modulus_one {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {x : ℝ} (hx : (x : ℂ) ∈ U) (hf : DifferentiableOn ℂ f (U ∩ {z : ℂ | 0 < z.im}))
    (hmod :
      ∀ t : ℝ,
        (t : ℂ) ∈ U → Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1)) :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (x : ℂ) r) ∧
          Set.EqOn H f (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (f (conj z)))⁻¹)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              ∀ t : ℝ, (t : ℂ) ∈ Metric.ball (x : ℂ) r → ‖H (t : ℂ)‖ = 1 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU (x : ℂ) hx
  obtain ⟨δ, hδ, hδf⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hmod x hx) (1 / 2) (by norm_num)
  let r : ℝ := Min.min ε δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : 2 * r < ε := by
    have hm := min_le_left ε δ
    dsimp [r]
    linarith
  have hrδ : 2 * r < δ := by
    have hm := min_le_right ε δ
    dsimp [r]
    linarith
  have hrectU : openRectangle (x - r) (x + r) (-r) r ⊆ U := by
    intro z hz
    apply hεU
    exact (dist_lt_two_mul_of_mem_centeredRectangle hz).trans hrε
  have hu : openRectangle (x - r) (x + r) 0 r ⊆ U ∩ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ⟨hrectU ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩, hz.2.1⟩
  have hsize : ∀ z ∈ openRectangle (x - r) (x + r) 0 r, 1 / 2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 := by
    intro z hz
    have hzR : z ∈ openRectangle (x - r) (x + r) (-r) r := ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
    have he := hδf hz.2.1 ((dist_lt_two_mul_of_mem_centeredRectangle hzR).trans hrδ)
    rw [Real.dist_eq, abs_lt] at he
    constructor <;> linarith [he.1, he.2]
  have hmodR :
    ∀ t ∈ Set.Ioo (x - r) (x + r),
      Filter.Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1) := by
    intro t ht
    apply hmod
    apply hrectU
    simpa only [openRectangle, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im] using
      And.intro ht (show (0 : ℝ) ∈ Set.Ioo (-r) r by constructor <;> linarith)
  obtain ⟨H, hH, hHe, hHl, hHcircle⟩ :=
    exists_analytic_extension_of_modulus_one_bounded (by linarith) hr
      (show (0 : ℝ) < 1 / 2 by norm_num) (hf.mono hu) (fun z hz => (hsize z hz).2)
      (fun z hz => (hsize z hz).1) hmodR
  refine ⟨r, hr, H, hH.mono (ball_subset_centeredRectangle x r), ?_, ?_, ?_⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHe ⟨hzR.1, hz.2, hzR.2.2⟩
  · intro z hz
    have hzR := ball_subset_centeredRectangle x r hz.1
    exact hHl ⟨hzR.1, hzR.2.1, hz.2⟩
  · intro t ht
    have htR := ball_subset_centeredRectangle x r ht
    exact hHcircle t (by simpa only [Complex.ofReal_re] using htR.1)
