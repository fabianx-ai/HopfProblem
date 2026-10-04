/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative
public import Lib.Geometry.Manifold.LocalDiffeomorph
/-!
# Flow lines, level crossings and the smooth level time

* Two flows `F`, `G` whose fields agree along the forward (backward) half orbit of `G` through
  `x` agree there (`FlowCancellation.native_flow_eq_on_positive_halfline`,
  `native_flow_eq_on_negative_halfline`): uniqueness of integral curves of a `C¹` field.
* A flow line with limits `p` (backward) and `q` (forward) and `f q < c < f p` crosses the level
  `{f = c}` (`exists_level_crossing_of_endpoint_limits`).
* Implicit function theorem for a scalar time: if `F : P × ℝ → ℝ` is smooth at `(p, t)`,
  `F (p, t) = c` and `∂F/∂t ≠ 0`, there is a smooth germ `θ` with `θ p = t` and
  `F (q, θ q) = c` near `p` (`SmoothODE.exists_smooth_scalar_time_germ`; manifold version
  `FlowCancellation.exists_native_smooth_time_germ`).
* For a smooth field `V` on a compact manifold with `mvfderiv f x (V x) < 0` on the regular level
  `{f = c}`: the basin `levelBasin F f c` of the level is open, the signed level time
  `signedLevelTime F f c` is smooth on it and satisfies `θ (F s x) = θ x - s`
  (`smooth_signed_level_time`), and `(z, s) ↦ F s z` is a diffeomorphism
  `{f = c} × ℝ ≃ levelBasin F f c` with inverse second coordinate `-θ`
  (`exists_native_level_flow_cylinder`).

The last item is the flow-out of a regular level along a transverse field
(cf. Lee, *Introduction to Smooth Manifolds*, Ch. 9, flowouts; Milnor, *Morse Theory*, §3).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Flow lines and level crossings -/

/-- The native flow is the chart flow on the positive half-line. -/
theorem FlowCancellation.native_flow_eq_on_positive_halfline {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) {x : M}
    (hagrees : ∀ t : ℝ, 0 ≤ t → W (G t x) = V (G t x)) : ∀ t : ℝ, 0 ≤ t → G t x = F t x := by
  intro t ht
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Set.Ioo (0 : ℝ) t) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.1.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh :=
      FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    simpa only [sub_zero, G.map_zero_apply] using hh.symm

/-- The native flow is the chart flow on the negative half-line. -/
theorem FlowCancellation.native_flow_eq_on_negative_halfline {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W) {x : M}
    (hagrees : ∀ t : ℝ, t ≤ 0 → W (G t x) = V (G t x)) : ∀ t : ℝ, t ≤ 0 → G t x = F t x := by
  intro t ht
  rcases ht.lt_or_eq with ht | ht
  · have hc : IsMIntegralCurveOn (fun s => G s x) V (Set.Ioo t (0 : ℝ)) := by
      intro s hs
      have hd := hG x s
      rw [hagrees s hs.2.le] at hd
      exact hd.hasMFDerivWithinAt
    have hh :=
      FlowSuspension.native_flow_segment_endpoints hV F hF ht
        (hG x).continuous.continuousOn hc
    have he := congrArg (F t) hh
    simpa only [zero_sub, ← F.map_add, add_neg_cancel, F.map_zero_apply, G.map_zero_apply] using
      he
  · subst t
    rw [G.map_zero_apply, F.map_zero_apply]

/-- A flow line between endpoint limits crosses the intermediate level. -/
theorem FlowCancellation.exists_level_crossing_of_endpoint_limits {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {x p q : X}
    (hp : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 q)) {c : ℝ} (hpc : c < f p)
    (hqc : f q < c) : ∃ t, f (F t x) = c := by
  have htop : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f q)) :=
    hf.continuousAt.tendsto.comp hq
  have hbot : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hp
  obtain ⟨s, hs⟩ := (htop.eventually (eventually_lt_nhds hqc)).exists
  obtain ⟨t, ht⟩ := (hbot.eventually (eventually_gt_nhds hpc)).exists
  exact
    mem_range_of_exists_le_of_exists_ge (hf.comp (F.continuous continuous_id continuous_const))
      ⟨s, hs.le⟩ ⟨t, ht.le⟩

/-! ### Smooth time germs and level cylinders -/

/-- Nonzero time derivative makes the time partial invertible. -/
theorem SmoothODE.scalar_partial_invertible {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {F : P × ℝ → ℝ} {p : P} {t v : ℝ} (hF : ContDiffAt ℝ ∞ F (p, t))
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ)).IsInvertible := by
  have hd :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp t
      ((hasFDerivAt_const p t).prodMk (hasFDerivAt_id t))
  change
    HasFDerivAt (fun s : ℝ => F (p, s)) ((fderiv ℝ F (p, t)).comp (ContinuousLinearMap.inr ℝ P ℝ))
      t at hd
  have heq := hd.unique htime.hasFDerivAt
  let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ v hv).toContinuousLinearEquiv
  refine ⟨L, ?_⟩
  rw [heq]
  apply ContinuousLinearMap.ext
  intro r
  change v * r = r * v
  exact mul_comm v r

/-- A smooth time germ solving `F(q, θ q) = c` near a point of nonzero time derivative. -/
theorem SmoothODE.exists_smooth_scalar_time_germ {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [CompleteSpace P] {F : P × ℝ → ℝ} {p : P} {t c v : ℝ}
    (hF : ContDiffAt ℝ ∞ F (p, t)) (hlevel : F (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => F (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : P → ℝ, θ p = t ∧ ContDiffAt ℝ ∞ θ p ∧ ∀ᶠ q in 𝓝 p, F (q, θ q) = c := by
  have hinv := scalar_partial_invertible hF htime hv
  let θ := hF.implicitFunction (by simp) hinv
  refine
    ⟨θ, hF.implicitFunction_apply_self (by simp) hinv,
      hF.contDiffAt_implicitFunction (by simp) hinv, ?_⟩
  filter_upwards [hF.eventually_apply_implicitFunction (by simp) hinv] with q hq
  exact hq.trans hlevel

/-- The manifold version: a smooth level-time germ near nonzero time derivative. -/
theorem FlowCancellation.exists_native_smooth_time_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {H : M × ℝ → ℝ} {p : M} {t c v : ℝ}
    (hH : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (p, t)) (hlevel : H (p, t) = c)
    (htime : HasDerivAt (fun s : ℝ => H (p, s)) v t) (hv : v ≠ 0) :
    ∃ θ : M → ℝ, θ p = t ∧ ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, H (q, θ q) = c := by
  let e := modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let B (q : E × ℝ) : M × ℝ := (e.symm q.1, q.2)
  let F : E × ℝ → ℝ := H ∘ B
  have hleft : e.symm (e p) = p := e.left_inv' hp
  have hB : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ B (e p, t) := by
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞ (Prod.fst : E × ℝ → E) (e p, t) :=
      contDiffAt_fst.contMDiffAt
    have hfirst := hi.comp (e p, t) hfst
    exact hfirst.prodMk contDiffAt_snd.contMDiffAt
  have hB0 : B (e p, t) = (p, t) := Prod.ext hleft rfl
  have hH' : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (B (e p, t)) := by
    rw [hB0]
    exact hH
  have hF : ContDiffAt ℝ ∞ F (e p, t) := (hH'.comp (e p, t) hB).contDiffAt
  have hFtime : (fun s : ℝ => F (e p, s)) = fun s => H (p, s) := by
    funext s
    change H (e.symm (e p), s) = H (p, s)
    rw [hleft]
  have hFt : HasDerivAt (fun s : ℝ => F (e p, s)) v t := by rw [hFtime]; exact htime
  have hFc : F (e p, t) = c := by
    change H (B (e p, t)) = c
    rw [hB0]
    exact hlevel
  obtain ⟨θ, hθ, hsmooth, hroot⟩ := SmoothODE.exists_smooth_scalar_time_germ hF hFc hFt hv
  refine ⟨θ ∘ e, hθ, hsmooth.contMDiffAt.comp p he, ?_⟩
  filter_upwards [e.open_source.mem_nhds hp, he.continuousAt hroot] with q hq hrootq
  have hqleft : e.symm (e q) = q := e.left_inv' hq
  change H (e.symm (e q), θ (e q)) = c at hrootq
  change H (q, θ (e q)) = c
  rwa [hqleft] at hrootq

/-- A smooth signed time to reach a regular level along a vector field. -/
theorem FlowCancellation.smooth_signed_level_time {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (levelBasin F f c) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (signedLevelTime F f c) (levelBasin F f c) ∧
        ∀ x ∈ levelBasin F f c,
          ∀ s : ℝ, signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hH : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ => f (F q.2 q.1)) :=
    hf.comp (SmoothODE.contMDiff_native_flow hV F hcurve)
  have hgerm (p : M) (hp : p ∈ levelBasin F f c) :
    ∃ θ : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧ ∀ᶠ q in 𝓝 p, f (F (θ q) q) = c := by
    let t := signedLevelTime F f c p
    have hhit : f (F t p) = c := signedLevelTime_hits F f c hp
    obtain ⟨θ, -, hθ, heq⟩ :=
      exists_native_smooth_time_germ hH.contMDiffAt hhit (hder p t) (hboundary (F t p) hhit).ne
    exact ⟨θ, hθ, heq⟩
  have hB : IsOpen (levelBasin F f c) := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨θ, -, heq⟩ := hgerm p hp
    exact heq.mono (fun q hq => ⟨θ q, hq⟩)
  refine ⟨hB, ?_, ?_⟩
  · intro p hp
    obtain ⟨θ, hθ, heq⟩ := hgerm p hp
    apply ContMDiffAt.contMDiffWithinAt
    apply hθ.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    exact signedLevelTime_eq_of_level F hf.continuous hD hder hboundary hq
  · intro x hx s
    exact signedLevelTime_flow F hf.continuous hD hder hboundary hx s

/-- A flow cylinder over a regular level along a nonvanishing field. -/
theorem FlowCancellation.exists_native_level_flow_cylinder {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) (z : { x : M // f x = c }) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ Φ :
      PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({ x : M // f x = c } × ℝ) M ∞,
      Φ.source = Set.univ ∧
        Φ.target = levelBasin F f c ∧
          (∀ p, Φ p = F p.2 p.1) ∧ ∀ x ∈ Φ.target, (Φ.symm x).2 = -signedLevelTime F f c x := by
  classical
  let _ := RegularLevel.chartedSpace hf hreg
  let L := { x : M // f x = c }
  let B := levelBasin F f c
  let θ := signedLevelTime F f c
  obtain ⟨hB, hθ, htranslate⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  let r : M → L := fun x => if hx : x ∈ B then ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ else z
  let φ : L × ℝ → M := fun p => F p.2 p.1
  let ψ : M → L × ℝ := fun x => (r x, -θ x)
  have hflow := SmoothODE.contMDiff_native_flow hV F hcurve
  have hφ : ContMDiff (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ φ :=
    hflow.comp
      (((RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst).prodMk contMDiff_snd)
  have hψ : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) ∞ ψ B := by
    intro x hx
    have hθx := (hθ x hx).contMDiffAt (hB.mem_nhds hx)
    have hr : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, RegularLevel.Model E) ∞ r x := by
      apply (RegularLevel.contMDiffAt_iff_inclusion hf hreg 𝓘(ℝ, E) r x).mpr
      apply (hflow.contMDiffAt.comp x (contMDiffAt_id.prodMk hθx)).congr_of_eventuallyEq
      filter_upwards [hB.mem_nhds hx] with y hy
      change (r y : M) = F (θ y) y
      have hyB : y ∈ B := hy
      simp only [r, dif_pos hyB]
    exact (hr.prodMk hθx.neg).contMDiffWithinAt
  have hD : Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) :=
    (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hlevel (x : L) : (x : M) ∈ B := ⟨0, by simpa only [F.map_zero_apply] using x.property⟩
  have hφB (p : L × ℝ) : φ p ∈ B := (levelBasin_flow_iff F f c p.2 p.1).mpr (hlevel p.1)
  have hclock (p : L × ℝ) : θ (φ p) = -p.2 := by
    have hh := htranslate p.1 (hlevel p.1) p.2
    rw [signedLevelTime_eq_zero F hf.continuous hD hder hboundary p.1.property, zero_sub] at hh
    exact hh
  have hleft (p : L × ℝ) : ψ (φ p) = p := by
    apply Prod.ext
    · apply Subtype.ext
      change (r (φ p) : M) = p.1
      rw [show r (φ p) = ⟨F (θ (φ p)) (φ p), signedLevelTime_hits F f c (hφB p)⟩ by
          simp only [r, dif_pos (hφB p)] ]
      change F (θ (φ p)) (F p.2 p.1) = p.1
      rw [hclock, ← F.map_add, neg_add_cancel, F.map_zero_apply]
    · change -θ (φ p) = p.2
      rw [hclock, neg_neg]
  have hright (x : M) (hx : x ∈ B) : φ (ψ x) = x := by
    change F (-θ x) (r x) = x
    rw [show r x = ⟨F (θ x) x, signedLevelTime_hits F f c hx⟩ by simp only [r, dif_pos hx] ]
    change F (-θ x) (F (θ x) x) = x
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  let Φ :
    PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (L × ℝ) M ∞ :=
    { toFun := φ
      invFun := ψ
      source := Set.univ
      target := B
      map_source' := fun p _ => hφB p
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun p _ => hleft p
      right_inv' := hright
      open_source := isOpen_univ
      open_target := hB
      contMDiffOn_toFun := hφ.contMDiffOn
      contMDiffOn_invFun := hψ }
  exact ⟨Φ, rfl, rfl, fun _ => rfl, fun _ _ => rfl⟩
