/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime
import Lib.Geometry.Manifold.Morse.Cancellation.LogarithmicCutoff

/-!
# The flow band height and its smooth corrections

Let `V` be a smooth vector field with flow `F` on a compact manifold and `f` a
smooth function decreasing along `V` on two levels `c < d`. On the crossing
basin `crossingBasin F f c d` (the points whose orbit meets both levels) the
crossing duration `crossingDuration F f c d` is positive and flow-invariant,
and the band height
`flowBandHeight F f c d x = c + (d - c) * signedLevelTime F f c x / crossingDuration F f c d x`
is a smooth function equal to `c` on `{f = c}`, to `d` on `{f = d}`, and
strictly decreasing along `V` (`smooth_flowBandHeight`).

The band height does not have the germ of `f` on the boundary levels. The
descent blend `descentBlend χ θ f g = g + χ (θ x) * (f x - g x)` with a cutoff
`χ` of `Morse.Cancellation.LogarithmicCutoff` and `θ` the signed level time
corrects this (`exists_native_descent_blend`, `exists_boundary_germ_correction`,
`exists_boundary_correction_preserving_level`): the time collar bounds
`exists_native_time_collar_bounds` control `|f - g|` by `|θ|` on a flow tube
`flowTube F {f = c} ε`. The result is a smooth function on an open set
containing the band `f ⁻¹' (Icc c d)`, strictly decreasing along `V`, with the
germ of `f` on both boundary levels (`exists_smooth_band_height_germs`).

This is the construction of a new height function on a product cobordism
between two regular levels, cf. Milnor, *Lectures on the h-cobordism theorem*,
§4 (rearrangement) and §5.

## Tags

gradient-like-flow, level-set, smooth-function
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-! ### The band height -/

/-- A function along a native integral curve differentiates at a point. -/
theorem FlowCancellation.hasDerivAt_comp_native_integralCurve_at {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ t)) (hγ : IsMIntegralCurve γ V) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t := by
  have hd := hf.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (V (γ t))
  exact map_smul _ _ _

/-- The manifold derivative of the signed level time. -/
theorem FlowCancellation.mvfderiv_signedLevelTime {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hx : x ∈ levelBasin F f c) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 := by
  obtain ⟨hB, hsmooth, hshift⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  have hlocal := (hsmooth x hx).contMDiffAt (hB.mem_nhds hx)
  have hlocal0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (signedLevelTime F f c) (F 0 x) := by
    rw [F.map_zero_apply]
    exact hlocal.mdifferentiableAt (by simp)
  have hd := hasDerivAt_comp_native_integralCurve_at hlocal0 (hcurve x)
  have heq :
    (signedLevelTime F f c ∘ (fun t => F t x)) = fun t : ℝ => signedLevelTime F f c x - t :=
    funext (hshift x hx)
  rw [heq] at hd
  have hh := hd.unique ((hasDerivAt_id (0 : ℝ)).const_sub (signedLevelTime F f c x))
  have he :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) y (V y)) (F.map_zero_apply x)
  exact he.symm.trans hh

/-- The basin of a band crossing. -/
def FlowCancellation.crossingBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) : Set X :=
  levelBasin F f c ∩ levelBasin F f d

/-- The duration of a band crossing. -/
def FlowCancellation.crossingDuration {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  signedLevelTime F f c x - signedLevelTime F f d x

/-- The height of the flow band. -/
def FlowCancellation.flowBandHeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  c + (d - c) * signedLevelTime F f c x / crossingDuration F f c d x

/-- The crossing duration is positive. -/
theorem FlowCancellation.crossingDuration_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hcd : c < d) {x : X} (hx : x ∈ crossingBasin F f c d) :
    0 < crossingDuration F f c d x := by
  apply sub_pos.mpr
  by_contra h
  have hle := le_of_not_gt h
  have hh :=
    forwardInvariant_sublevel_of_boundary F hf hD hder hc (F (signedLevelTime F f c x) x)
      (signedLevelTime_hits F f c hx.1).le (signedLevelTime F f d x - signedLevelTime F f c x)
      (sub_nonneg.mpr hle)
  rw [← F.map_add, sub_add_cancel, signedLevelTime_hits F f d hx.2] at hh
  exact (not_le_of_gt hcd) hh

/-- The crossing duration under the flow. -/
theorem FlowCancellation.crossingDuration_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    crossingDuration F f c d (F s x) = crossingDuration F f c d x := by
  simp only [crossingDuration, signedLevelTime_flow F hf hD hder hc hx.1 s,
    signedLevelTime_flow F hf hD hder hd hx.2 s]
  ring

/-- The band height under the flow. -/
theorem FlowCancellation.flowBandHeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    flowBandHeight F f c d (F s x) =
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * s := by
  simp only [flowBandHeight, crossingDuration_flow F hf hD hder hc hd hx s,
    signedLevelTime_flow F hf hD hder hc hx.1 s]
  ring

/-- The band height's lower bound. -/
theorem FlowCancellation.flowBandHeight_lower {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : flowBandHeight F f c d x = c := by
  simp only [flowBandHeight, signedLevelTime_eq_zero F hf hD hder hc hx, MulZeroClass.mul_zero,
    zero_div, add_zero]

/-- The band height's upper bound. -/
theorem FlowCancellation.flowBandHeight_upper {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) (hcd : c < d) {x : X}
    (hx : x ∈ crossingBasin F f c d) (hfx : f x = d) : flowBandHeight F f c d x = d := by
  have hz := signedLevelTime_eq_zero F hf hD hder hd hfx
  have hpos := crossingDuration_pos F hf hD hder hc hcd hx
  have heq : signedLevelTime F f c x = crossingDuration F f c d x := by
    simp only [crossingDuration, hz, sub_zero]
  rw [flowBandHeight, heq, mul_div_cancel_right₀ _ hpos.ne']
  ring

/-- The band height is smooth. -/
theorem FlowCancellation.smooth_flowBandHeight {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (crossingBasin F f c d) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) ∧
        ∀ x ∈ crossingBasin F f c d,
          mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) =
              -((d - c) / crossingDuration F f c d x) ∧
            mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) < 0 := by
  obtain ⟨hBc, htc, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  obtain ⟨hBd, htd, -⟩ := smooth_signed_level_time hf hV F hcurve hd
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hB : IsOpen (crossingBasin F f c d) := hBc.inter hBd
  have hpos (x : M) (hx : x ∈ crossingBasin F f c d) : 0 < crossingDuration F f c d x :=
    crossingDuration_pos F hf.continuous hD hder hc hcd hx
  have hsc := htc.mono (Set.inter_subset_left : crossingBasin F f c d ⊆ levelBasin F f c)
  have hsd := htd.mono (Set.inter_subset_right : crossingBasin F f c d ⊆ levelBasin F f d)
  have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (crossingDuration F f c d) (crossingBasin F f c d) :=
    hsc.sub hsd
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) :=
    contMDiffOn_const.add ((contMDiffOn_const.mul hsc).div₀ hA (fun x hx => (hpos x hx).ne'))
  refine ⟨hB, hg, ?_⟩
  intro x hx
  have hlocal : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (flowBandHeight F f c d) (F 0 x) := by
    rw [F.map_zero_apply]
    exact ((hg x hx).contMDiffAt (hB.mem_nhds hx)).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_comp_native_integralCurve_at hlocal (hcurve x)
  have heq :
    (flowBandHeight F f c d ∘ (fun t => F t x)) = fun t =>
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * t :=
    funext (fun t => flowBandHeight_flow F hf.continuous hD hder hc hd hx t)
  rw [heq] at hchain
  have hline :=
    ((hasDerivAt_id (0 : ℝ)).const_mul ((d - c) / crossingDuration F f c d x)).const_sub
      (flowBandHeight F f c d x)
  have hnative :
    mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) = -((d - c) / crossingDuration F f c d x) :=
    by
    have he :=
      congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) y (V y))
        (F.map_zero_apply x)
    exact he.symm.trans (by simpa using hchain.unique hline)
  exact ⟨hnative, hnative ▸ neg_neg_of_pos (div_pos (sub_pos.mpr hcd) (hpos x hx))⟩

/-! ### Derivatives along the flow -/

/-- The flow height's derivative at a critical point is zero. -/
theorem FlowCancellation.hasDerivAt_flow_height_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (F : Flow ℝ M)
    (hcurve : IsMIntegralCurve (fun t => F t x) V) :
    HasDerivAt (fun t => f (F t x)) (mvfderiv 𝓘(ℝ, E) f x (V x)) 0 := by
  have hf0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (F 0 x) := by
    rw [F.map_zero_apply]
    exact hf
  have hh := hasDerivAt_comp_native_integralCurve_at hf0 hcurve
  have he := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  exact he ▸ hh

/-! ### The descent blend -/

/-- The descent blend of two Lyapunov functions. -/
def FlowCancellation.descentBlend {M : Type*} (χ : ℝ → ℝ) (θ f g : M → ℝ) (x : M) : ℝ :=
  g x + χ (θ x) * (f x - g x)

/-- The descent blend's manifold derivative. -/
theorem FlowCancellation.mvfderiv_descentBlend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {χ : ℝ → ℝ} {θ f g : M → ℝ} {x : M}
    (hχ : ContDiff ℝ ∞ χ) (hθ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ x)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f x) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g x)
    (F : Flow ℝ M) (hcurve : IsMIntegralCurve (fun t => F t x) V)
    (htime : mvfderiv 𝓘(ℝ, E) θ x (V x) = -1) :
    mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) =
      mvfderiv 𝓘(ℝ, E) g x (V x) +
          χ (θ x) * (mvfderiv 𝓘(ℝ, E) f x (V x) - mvfderiv 𝓘(ℝ, E) g x (V x)) -
        deriv χ (θ x) * (f x - g x) := by
  have dθ := hasDerivAt_flow_height_zero (hθ.mdifferentiableAt (by simp)) F hcurve
  have df := hasDerivAt_flow_height_zero (hf.mdifferentiableAt (by simp)) F hcurve
  have dg := hasDerivAt_flow_height_zero (hg.mdifferentiableAt (by simp)) F hcurve
  rw [htime] at dθ
  have dχ := ((hχ.differentiable (by simp)) (θ (F 0 x))).hasDerivAt.comp 0 dθ
  have db := dg.add (dχ.mul (df.sub dg))
  have hb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (descentBlend χ θ f g) x :=
    hg.add ((hχ.contMDiff.contMDiffAt.comp x hθ).mul (hf.sub hg))
  have dn := hasDerivAt_flow_height_zero (hb.mdifferentiableAt (by simp)) F hcurve
  have he := dn.unique db
  simp only [Pi.sub_apply, Function.comp_apply, F.map_zero_apply] at he
  exact he.trans (by ring)

/-- A native descent blend exists. -/
theorem FlowCancellation.exists_native_descent_blend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {θ f g : M → ℝ}
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (htime : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) θ x (V x) = -1)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {ε μ C : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hC : 0 ≤ C)
    (hcollar :
      ∀ x ∈ U,
        |θ x| < ε →
          mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
            mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |θ x|) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x ∈ U, θ x = 0 → b =ᶠ[𝓝 x] f) ∧
            (∀ x, ε ≤ |θ x| → b x = g x) ∧ ∀ x ∈ U, ε < |θ x| → b =ᶠ[𝓝 x] g := by
  let δ := μ / (C + 1)
  have hδ : 0 < δ := div_pos hμ (by positivity)
  have hsmall : C * δ < μ := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  obtain ⟨χ, hχ, -, hone, hzero, hrange, hweight⟩ := exists_logarithmic_cutoff hε hδ
  let b := descentBlend χ θ f g
  have hb : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U :=
    hg.add ((hχ.contMDiff.comp_contMDiffOn hθ).mul (hf.sub hg))
  have hout (x : M) (hx : ε ≤ |θ x|) : b x = g x := by
    simp only [b, descentBlend, hzero _ hx, MulZeroClass.zero_mul, add_zero]
  refine ⟨b, hb, ?_, ?_, hout, ?_⟩
  · intro x hx
    have hder :=
      mvfderiv_descentBlend hχ ((hθ x hx).contMDiffAt (hU.mem_nhds hx))
        ((hf x hx).contMDiffAt (hU.mem_nhds hx)) ((hg x hx).contMDiffAt (hU.mem_nhds hx)) F
        (hcurve x) (htime x hx)
    change mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) < 0
    rw [hder]
    by_cases hnear : |θ x| < ε
    · obtain ⟨hdf, hdg, hdiff⟩ := hcollar x hx hnear
      exact weighted_blend_neg (hrange _) hdf hdg hC hdiff (hweight _).le hsmall
    · have hz := hzero (θ x) (le_of_not_gt hnear)
      have hdχ :=
        deriv_eq_zero_of_nonneg_zero (hχ.differentiable (by simp)) (fun t => (hrange t).1) hz
      simpa only [hz, hdχ, MulZeroClass.zero_mul, add_zero, sub_zero] using hgneg x hx
  · intro x hx hxzero
    have ht : ContinuousAt θ x := (hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hone' : ∀ᶠ t in 𝓝 (θ x), χ t = 1 := by simpa only [hxzero] using hone
    filter_upwards [ht.eventually hone'] with y hy
    change g y + χ (θ y) * (f y - g y) = f y
    rw [hy]
    ring
  · intro x hx hxout
    have ht : ContinuousAt (fun y => |θ y|) x :=
      ((hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)).abs
    filter_upwards [ht (eventually_gt_nhds hxout)] with y hy
    exact hout y hy.le

/-! ### Flow tubes -/

/-- The flow tube of a compact set. -/
def FlowCancellation.flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (S : Set X)
    (ε : ℝ) : Set X :=
  (fun q : ℝ × X => F q.1 q.2) '' (Set.Icc (-ε) ε ×ˢ S)

/-- The flow tube is compact. -/
theorem FlowCancellation.isCompact_flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {S : Set X} (hS : IsCompact S) (ε : ℝ) : IsCompact (flowTube F S ε) :=
  (CompactIccSpace.isCompact_Icc.prod hS).image (F.continuous continuous_fst continuous_snd)

/-- A flow tube inside an open set exists. -/
theorem FlowCancellation.exists_flowTube_subset {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S N : Set X} (hS : IsCompact S) (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ ε : ℝ, 0 < ε ∧ flowTube F S ε ⊆ N := by
  have hopen : IsOpen {t : ℝ | ∀ x ∈ S, F t x ∈ N} :=
    MorsePerturbation.isOpen_forall_mem_compact hS
      (hN.preimage (F.continuous continuous_fst continuous_snd))
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∀ x ∈ S, F t x ∈ N} := by
    intro x hx
    simpa only [F.map_zero_apply] using hSN hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  apply hball ?_ x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- Signed-time membership in the flow tube. -/
theorem FlowCancellation.mem_flowTube_of_signedTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {ε : ℝ} {x : X} (hx : x ∈ levelBasin F f c)
    (ht : |signedLevelTime F f c x| ≤ ε) : x ∈ flowTube F {y | f y = c} ε := by
  refine
    ⟨(-signedLevelTime F f c x, F (signedLevelTime F f c x) x),
      ⟨?_, signedLevelTime_hits F f c hx⟩, ?_⟩
  · constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  · simp only [← F.map_add, neg_add_cancel, F.map_zero_apply]

/-- A compact negative margin exists. -/
theorem FlowCancellation.exists_compact_negative_margin {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {D : X → ℝ} (hD : ContinuousOn D S) (hneg : ∀ x ∈ S, D x < 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ S, D x < -μ := by
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hS.exists_isMaxOn hne hD
    refine ⟨-D p / 2, by linarith [hneg p hp], ?_⟩
    intro x hx
    have hle : D x ≤ D p := hmax hx
    linarith [hneg p hp]
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- The directional derivative is smooth on a set. -/
theorem FlowCancellation.contMDiffOn_directionalDerivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U)
    {g : M → ℝ} (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) g x (V x)) U := by
  have ht :=
    (hg.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn).comp hV.contMDiffOn
      (fun x hx => hx)
  have hh := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn ht
  apply hh.congr
  intro x hx
  change
    (NormedSpace.fromTangentSpace (g x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (V x)) =
      (NormedSpace.fromTangentSpace (g x)) (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g U x (V x))
  rw [mfderivWithin_of_isOpen hU hx]

/-- Native time collar bounds exist. -/
theorem FlowCancellation.exists_native_time_collar_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {U : Set M}
    (hU : IsOpen U) {f g : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ ε μ C : ℝ,
      0 < ε ∧
        0 < μ ∧
          0 ≤ C ∧
            ∀ x ∈ U,
              |signedLevelTime F f c x| < ε →
                mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
                  mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |signedLevelTime F f c x| :=
  by
  let S : Set M := {x | f x = c}
  have hS : IsCompact S := (isClosed_eq hf.continuous continuous_const).isCompact
  let Df (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let Dg (x : M) := mvfderiv 𝓘(ℝ, E) g x (V x)
  have hDf : Continuous Df := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hDg : ContinuousOn Dg U := (contMDiffOn_directionalDerivative hU hg hV).continuousOn
  have hmax : ContinuousOn (fun x => Max.max (Df x) (Dg x)) U :=
    continuous_max.comp_continuousOn (hDf.continuousOn.prodMk hDg)
  obtain ⟨μ, hμ, hmargin⟩ :=
    exists_compact_negative_margin hS (hmax.mono hlevel)
      (fun x hx => max_lt (hfc x hx) (hgc x hx))
  let N : Set M := U ∩ (fun x => Max.max (Df x) (Dg x)) ⁻¹' Set.Iio (-μ)
  have hN : IsOpen N := hmax.isOpen_inter_preimage hU isOpen_Iio
  have hSN : S ⊆ N := fun x hx => ⟨hlevel hx, hmargin x hx⟩
  obtain ⟨ε, hε, htube⟩ := exists_flowTube_subset F hS hN hSN
  let K := flowTube F S ε
  have hK : IsCompact K := isCompact_flowTube F hS ε
  have hKU : K ⊆ U := fun x hx => (htube hx).1
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hDf.continuousOn.sub (hDg.mono hKU))
  let C : ℝ := Max.max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : M) (hx : x ∈ K) : ‖Df x - Dg x‖ ≤ C := (hC₀ x hx).trans (le_max_left _ _)
  refine ⟨ε, μ, C, hε, hμ, hC, ?_⟩
  intro x hx hxε
  have hxK : x ∈ K := mem_flowTube_of_signedTime F f c (hbasin hx) hxε.le
  have hxN := htube hxK
  have hneg : Max.max (Df x) (Dg x) < -μ := hxN.2
  refine
    ⟨(lt_of_le_of_lt (le_max_left _ _) hneg).le, (lt_of_le_of_lt (le_max_right _ _) hneg).le, ?_⟩
  let θ := signedLevelTime F f c x
  let y := F θ x
  have hy : f y = c := signedLevelTime_hits F f c (hbasin hx)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : F t y ∈ K := ⟨(t, y), ⟨ht, hy⟩, rfl⟩
  let ℓ (t : ℝ) := f (F t y) - g (F t y)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : HasDerivAt ℓ (Df (F t y) - Dg (F t y)) t := by
    have hgpoint :=
      ((hg (F t y) (hKU (hpoint t ht))).contMDiffAt
            (hU.mem_nhds (hKU (hpoint t ht)))).mdifferentiableAt
        (by simp)
    exact
      (hasDerivAt_comp_native_integralCurve_at (hf.mdifferentiableAt (by simp)) (hcurve y)).sub
        (hasDerivAt_comp_native_integralCurve_at hgpoint (hcurve y))
  have h0 : (0 : ℝ) ∈ Set.Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hθ : -θ ∈ Set.Icc (-ε) ε := by
    constructor <;> linarith [(abs_lt.mp hxε).1, (abs_lt.mp hxε).2]
  have hmvt :=
    (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).differentiableAt)
      (fun t ht => by rw [(hd t ht).deriv]; exact hbound _ (hpoint t ht)) h0 hθ
  have hreturn : F (-θ) y = x := by
    dsimp [y]
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  simpa only [ℓ, F.map_zero_apply, hreturn, heq y hy, sub_self, sub_zero, Real.norm_eq_abs,
    abs_neg] using hmvt

/-- A boundary germ correction exists. -/
theorem FlowCancellation.exists_boundary_germ_correction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {r : ℝ} (hr : 0 < r) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x ∈ U, r ≤ |signedLevelTime F f c x| → b =ᶠ[𝓝 x] g := by
  obtain ⟨ε₀, μ, C, hε₀, hμ, hC, hbounds⟩ :=
    exists_native_time_collar_bounds hU hf hg hV F hcurve hlevel hbasin heq hfc
      (fun x hx => hgneg x (hlevel hx))
  let ε := Min.min ε₀ (r / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hr)
  have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hfc
  have htime (x : M) (hx : x ∈ U) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 :=
    mvfderiv_signedLevelTime hf hV F hcurve hfc (hbasin hx)
  obtain ⟨b, hb, hbneg, hbone, -, hboff⟩ :=
    exists_native_descent_blend hU (hθ.mono hbasin) hf.contMDiffOn hg F hcurve htime hgneg hε hμ
      hC (fun x hx ht => hbounds x hx (lt_of_lt_of_le ht (min_le_left _ _)))
  refine ⟨b, hb, hbneg, ?_, fun x hx ht => hboff x hx (hεr.trans_le ht)⟩
  intro x hx
  apply hbone x (hlevel hx)
  let D (y : M) := mvfderiv 𝓘(ℝ, E) f y (V y)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  exact
    signedLevelTime_eq_zero F hf.continuous hD
      (fun y t => FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve y) t) hfc hx

/-- A signed-time level separation exists. -/
theorem FlowCancellation.exists_signedTime_level_separation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hlevel : {x | f x = d} ⊆ levelBasin F f c) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, f x = d → r < |signedLevelTime F f c x| := by
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  have hS : IsCompact {x | f x = d} := (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨r, hr, hmargin⟩ :=
    exists_compact_negative_margin hS ((hθ.continuousOn.mono hlevel).abs.neg)
      (fun x hx => by
        apply neg_neg_of_pos
        apply abs_pos.mpr
        intro hz
        have hhit := signedLevelTime_hits F f c (hlevel hx)
        rw [hz, F.map_zero_apply] at hhit
        exact hcd (hhit.symm.trans hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  have hh : -|signedLevelTime F f c x| < -r := hmargin x hx
  linarith

/-- A level-preserving boundary correction exists. -/
theorem FlowCancellation.exists_boundary_correction_preserving_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hcU : {x | f x = c} ⊆ U) (hdU : {x | f x = d} ⊆ U) (hbasin : U ⊆ levelBasin F f c)
    (heq : ∀ x, f x = c → g x = f x) (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x, f x = d → b =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hsep⟩ :=
    exists_signedTime_level_separation hf hV F hcurve hcd hfc (hdU.trans hbasin)
  obtain ⟨b, hb, hbneg, hbc, hboff⟩ :=
    exists_boundary_germ_correction hU hf hg hV F hcurve hcU hbasin heq hfc hgneg hr
  exact ⟨b, hb, hbneg, hbc, fun x hx => hboff x (hdU hx) (hsep x hx).le⟩

/-- The band lies in the crossing basin. -/
theorem FlowCancellation.band_subset_crossingBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {c d T : ℝ} (hT : 0 < T)
    (hforward : ∀ x, f x ≤ d → f (F T x) < c) (hbackward : ∀ x, c ≤ f x → d < f (F (-T) x)) :
    f ⁻¹' Set.Icc c d ⊆ crossingBasin F f c d := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  constructor
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' hT.le hcont.continuousOn
        (show c ∈ Set.Icc (f (F T x)) (f (F 0 x)) from
          ⟨(hforward x hx.2).le, by simpa only [F.map_zero_apply] using hx.1⟩)
    exact ⟨t, ht⟩
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' (show -T ≤ (0 : ℝ) by linarith) hcont.continuousOn
        (show d ∈ Set.Icc (f (F 0 x)) (f (F (-T) x)) from
          ⟨by simpa only [F.map_zero_apply] using hx.2, (hbackward x hx.1).le⟩)
    exact ⟨t, ht⟩

/-- Smooth band height germs exist. -/
theorem FlowCancellation.exists_smooth_band_height_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ (U : Set M) (g : M → ℝ),
      IsOpen U ∧
        f ⁻¹' Set.Icc c d ⊆ U ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧
            (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧ ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f := by
  let U := crossingBasin F f c d
  let g := flowBandHeight F f c d
  obtain ⟨hU, hg, hgder⟩ := smooth_flowBandHeight hf hV F hcurve hcd hc hd
  obtain ⟨T, hT, hforward, hbackward⟩ := hcross
  have hband : f ⁻¹' Set.Icc c d ⊆ U :=
    band_subset_crossingBasin F hf.continuous hT hforward hbackward
  have hcU : {x | f x = c} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx], by rw [hx]; exact hcd.le⟩)
  have hdU : {x | f x = d} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx]; exact hcd.le, by rw [hx]⟩)
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hgc (x : M) (hx : f x = c) : g x = f x :=
    (flowBandHeight_lower F hf.continuous hD hder hc hx).trans hx.symm
  have hgd (x : M) (hx : f x = d) : g x = f x :=
    (flowBandHeight_upper F hf.continuous hD hder hc hd hcd (hdU hx) hx).trans hx.symm
  obtain ⟨b, hb, hbneg, hbc, hbd⟩ :=
    exists_boundary_correction_preserving_level hU hf hg hV F hcurve hcd.ne hcU hdU
      Set.inter_subset_left hgc hc (fun x hx => (hgder x hx).2)
  have hbdval (x : M) (hx : f x = d) : b x = f x := (hbd x hx).eq_of_nhds.trans (hgd x hx)
  obtain ⟨k, hk, hkneg, hkd, hkc⟩ :=
    exists_boundary_correction_preserving_level hU hf hb hV F hcurve hcd.ne' hdU hcU
      Set.inter_subset_right hbdval hd hbneg
  refine ⟨U, k, hU, hband, hk, hkneg, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hkc x hx).trans (hbc x hx)
  · exact hkd x hx

end
