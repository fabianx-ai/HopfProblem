/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.Geometry.Manifold.Morse.MinimalSystem
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.Geometry.Manifold.Morse.OrderedCancellation

/-!
# Adapted windows of a Morse surgery system

For a Morse function `f` on a compact manifold `M` with a gradient-like field and a system
`S : AdaptedWindows E f` of surgery windows around its critical points, this file collects the
facts about the trajectories of `S` that the handle-rearrangement argument uses:

* realising a compactly supported relative isotopy of a regular level by a modification of the
  gradient-like field (`RegularLevel.exists_flow_realization_of_relative_isotopy`,
  `AdaptedWindows.exists_relative_level_surgery_system`), the mechanism behind Milnor,
  *Lectures on the h-cobordism theorem*, §4 (Theorem 4.1, rearrangement);
* which points of a level flow down to a lower level (`attachingSphere_reaches_lower_cut`,
  `backward_basin_reaches_attaching_level`, `reaches_lower_in_regular_band`,
  `reaches_lower_of_excluded_critical_limit`, `reaches_old_lower_of_belt_avoidance`);
* identification of the descending sphere of a critical point with the set of points whose
  backward orbit converges to it (`transported_attaching_range_iff`,
  `transported_backward_basin_image`, `not_backward_basin_on_upper_level`);
* the absence of a gradient trajectory between two critical points when one of the two relevant
  index spaces is trivial (`no_connection_of_upper_index_zero`,
  `no_connection_of_lower_positive_zero`), the elementary case of Milnor §4;
* a regular value separating the critical points of index `≤ k` from those of index `≥ k+1`
  once the function is ordered by index (`exists_ordered_index_cut`), the cut used by Milnor's
  self-indexing theorem (Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.8).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- A compactly supported relative isotopy `D` of a regular level `f⁻¹(c)` is realised by the
flow of a modified descending vector field: there are a band `f⁻¹(c-r, c)` and fields `W`, `V'`
whose flows `H`, `G` have the same orbits and the same limit points as the original flow, agree
with it near the critical points and outside a compact subset of the band, and satisfy
`G 1 x = H 1 (D x)` on the level, `H 1` carrying `f⁻¹(c)` to `f⁻¹(c-r)`, with `G = H` on the set
where `D` is the identity.  This is the modification of a gradient-like field used in the proof
of Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.1. -/
theorem RegularLevel.exists_flow_realization_of_relative_isotopy {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    let _ := RegularLevel.chartedSpace hf hreg
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          { y : M // f y = c } { y : M // f y = c } ∞)
      (K T : Set { y : M // f y = c }),
      IsCompact K →
        SupportedDiffeomorph.SupportedRelativeIsotopy D K T →
          ∃ (r : ℝ) (C : Set M) (W V' : (y : M) → TangentSpace 𝓘(ℝ, E) y) (H G : Flow ℝ M),
            0 < r ∧
              r < c - a ∧
                IsCompact C ∧
                  C ⊆ f ⁻¹' Set.Ioo a b ∧
                    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                      (∀ y, IsMIntegralCurve (fun t => H t y) W) ∧
                        (∀ y,
                            Set.range (fun t => H t y) = Set.range (fun t => F t y) ∧
                              (∀ p,
                                  Filter.Tendsto (fun t => H t y) Filter.atTop (𝓝 p) ↔
                                    Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                                ∀ p,
                                  Filter.Tendsto (fun t => H t y) Filter.atBot (𝓝 p) ↔
                                    Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ y, IsMIntegralCurve (fun t => G t y) V') ∧
                              (∀ y, V' y = 0 ↔ V y = 0) ∧
                                (∀ y,
                                    y ∉ ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f y (V' y) < 0) ∧
                                  (∀ y ∈ ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ x in 𝓝 y, V' x = V x) ∧
                                    (∀ y ∉ C, ∀ᶠ x in 𝓝 y, V' x = W x) ∧
                                      (∀ x : { y : M // f y = c }, G 1 x = H 1 (D x)) ∧
                                        (∀ x : { y : M // f y = c }, f (H 1 x) = c - r) ∧
                                          (∀ x : { y : M // f y = c },
                                              ∀ t : ℝ, t ≤ 0 → G t x = H t x) ∧
                                            (∀ x : { y : M // f y = c },
                                                ∀ t : ℝ, 0 ≤ t → G t (H 1 x) = H t (H 1 x)) ∧
                                              ∀ x ∈ T, ∀ t : ℝ, G t x = H t x := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  dsimp only
  intro D K T hK I
  obtain
    ⟨r, W, H, A, hr, hrbound, hW, hH, hWzero, hWneg, hWgerm, hgeometry, hsource, -, hformula,
      hheight, hmodel⟩ :=
    FlowTimeChange.exists_normalized_whole_level_cylinder hf hV hdesc F hF ha hb hband hreg
      z
  obtain
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, hneg, hgerm, -, -, hfull, hend, hfixed, -, hleft,
      hright, -⟩ :=
    FlowSuspension.exists_native_whole_level_holonomy A hsource hf hr
      (fun p hp => hheight p ⟨hp.1.le, hp.2.le⟩)
      W hW hmodel H hH D hK I
  have hCband : C ⊆ f ⁻¹' Set.Ioo a b := by
    intro y hy
    have hh := (hCsub hy).2
    change f y ∈ Set.Ioo (c - r) c at hh
    exact ⟨by linarith [hh.1], lt_trans hh.2 hb⟩
  have hcritical (y : M) (hy : y ∈ ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 y, V' x = V x := by
    have hout : y ∉ C := fun hc => hband y ⟨(hCband hc).1.le, (hCband hc).2.le⟩ hy
    filter_upwards [hgerm y hout, hWgerm y hy] with x hx hx'
    exact hx.trans hx'
  obtain ⟨htailLeft, htailRight⟩ :=
    FlowSuspension.native_whole_level_exterior_tails A Subtype.val H G hformula D Ψ hleft
      hright hfull
  have hA0 (x : { y : M // f y = c }) : A (x, 0) = (x : M) := by rw [hformula, H.map_zero_apply]
  have hA1 (x : { y : M // f y = c }) : A (x, 1) = H 1 x := hformula (x, 1)
  refine
    ⟨r, C, W, V', H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV', hG, fun y =>
      (hzero y).trans (hWzero y), fun y hy => hneg y (hWneg y hy), hcritical, hgerm, ?_, ?_, ?_,
      ?_, ?_⟩
  · intro x
    rw [← hA0 x, hend, hA1]
  · intro x
    have hh := hheight (x, 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [hA1, mul_one] at hh
    exact hh
  · intro x t ht
    simpa only [hA0] using htailLeft x t ht
  · intro x t ht
    simpa only [hA1] using htailRight x t ht
  · intro x hx t
    have hh := hfixed x hx 0 t
    rw [hA0, zero_add, hformula] at hh
    exact hh

/-- If `a` lies below the critical value `f p` and above every smaller critical value, then every
point of the attaching (descending) sphere of `p` flows forward to the level `a`. -/
theorem AdaptedWindows.attachingSphere_reaches_lower_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hap : a < f p) (hgap : ∀ q : ManifoldMorse.criticalPoints E f, f q < f p → f q < a)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) :
    ((S.data p).surgery.attachingSphere u).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let x := (S.data p).surgery.attachingSphere u
  have hback := (S.attaching_basin_iff hf p x).mpr ⟨u, rfl⟩
  obtain ⟨r, hr, q, hq, -, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hxreg : x.val ∉ ManifoldMorse.criticalPoints E f :=
    (S.data p).lower_regular x.val x.property
  have hxp : f x.val < f p := by
    have hh := x.property
    change f x.val = f p - (S.data p).radius ^ 2 at hh
    rw [hh]
    nlinarith [(S.data p).radius_pos]
  have hqa : f q < a := hgap ⟨q, hq⟩ ((hheights hxreg).1.trans hxp)
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward hap hqa

/-- A regular point whose backward orbit converges to the critical point `p` flows forward to
the lower level of the window around `p`. -/
theorem AdaptedWindows.backward_basin_reaches_attaching_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)) :
    x ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨r, hr, q, hq, hback', hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x
  have hrp : r = p.val := tendsto_nhds_unique hback' hback
  have hqp : f q < f p := by
    have hh := (hheights hx).1.trans (hheights hx).2
    rwa [hrp] at hh
  have hqlo : f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper ⟨q, hq⟩).trans (S.separated ⟨q, hq⟩ p hqp)
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (S.toSurgeryWindows.lower_lt_value p) hqlo

/-- If a family `Γ` in a regular level `f⁻¹(a)` is obtained by flowing the attaching sphere of
`p` and `e` covers that sphere, then the image of `Γ` is exactly the set of points of `f⁻¹(a)`
whose backward orbit converges to `p`: the descending sphere of `p` traced out on the level. -/
theorem AdaptedWindows.transported_attaching_range_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {X : Type*}
    (e : X → Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (he : Function.Surjective e) (Γ : X → { y : M // f y = a })
    (hflow : ∀ z, ∃ t : ℝ, S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val)
    (y : { x : M // f x = a }) :
    y ∈ Set.range Γ ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := hflow z
    have hback :=
      (S.attaching_basin_iff hf p ((S.data p).surgery.attachingSphere (e z))).mpr ⟨e z, rfl⟩
    rw [← ht]
    exact (MorseCancellation.flow_time_atBot_limit_iff S.flow t _ p.val).mpr hback
  · intro hy
    obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p (ha y.val y.property) hy
    let x : (S.data p).LowerLevel := ⟨S.flow t y.val, ht⟩
    have hxback : Filter.Tendsto (fun s => S.flow s x.val) Filter.atBot (𝓝 p.val) :=
      (MorseCancellation.flow_time_atBot_limit_iff S.flow t y.val p.val).mpr hy
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p x).mp hxback
    obtain ⟨z, hz⟩ := he u
    obtain ⟨s, hs⟩ := hflow z
    have hattach : S.flow t y.val = ((S.data p).surgery.attachingSphere (e z)).val := by
      rw [hz]
      exact (congrArg Subtype.val hu).symm
    have hshared : S.flow 0 (Γ z).val = S.flow (s + t) y.val := by
      rw [S.flow.map_zero_apply, S.flow.map_add, hattach, hs]
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun w hw => S.descent w (ha w hw)) (Γ z).property y.property hshared

/-- If every point of the attaching sphere of `q` flows forward to `p`, then every regular point
whose backward orbit converges to `q` also flows forward to `p`. -/
theorem AdaptedWindows.forward_endpoint_of_attaching_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hbranches :
      ∀ u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
          (𝓝 p.val))
    {x : M} (hx : x ∉ ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val)) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val) := by
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf q hx hback
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff S.flow t x q.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  have hyforward : Filter.Tendsto (fun s => S.flow s y.val) Filter.atTop (𝓝 p.val) := by
    rw [← hu]
    exact hbranches u
  exact (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mp hyforward

/-- The property "every point of the attaching sphere of `q` flows forward to `p`" only depends
on the flow, so it transfers to a second window system with the same flow. -/
theorem AdaptedWindows.attaching_branches_of_same_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hflow : T.flow = S.flow)
    (hbranches :
      ∀ u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
          (𝓝 p.val)) :
    ∀ u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val) := by
  intro u
  let x := (T.data q).surgery.attachingSphere u
  have hback := (T.attaching_basin_iff hf q x).mpr ⟨u, rfl⟩
  rw [hflow] at hback ⊢
  exact
    S.forward_endpoint_of_attaching_branches hf p q hbranches
      ((T.data q).lower_regular x.val x.property) hback

attribute [local instance 100] Classical.propDecidable in
/-- Given a regular value `a`, the windows can be shrunk, keeping the same gradient-like field,
flow and Morse charts, so that no window meets the level `a`: the windows around critical points
below `a` stay below it and those above stay above. -/
theorem AdaptedWindows.exists_same_flow_windows_avoiding_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    ∃ T : AdaptedWindows E f,
      T.field = S.field ∧
        T.flow = S.flow ∧
          (∀ p, (T.data p).chart = (S.data p).chart) ∧
            (∀ p : ManifoldMorse.criticalPoints E f,
                f p < a → T.toSurgeryWindows.upper p < a) ∧
              ∀ p : ManifoldMorse.criticalPoints E f,
                a < f p → a < T.toSurgeryWindows.lower p := by
  let ε : ManifoldMorse.criticalPoints E f → ℝ := fun p => Real.sqrt |f p - a|
  have hε (p : ManifoldMorse.criticalPoints E f) : 0 < ε p := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (sub_ne_zero.mpr (fun h => ha p.val h p.property))
  obtain ⟨T, hfield, hflow, hcharts, hsmall⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
      S.integral S.zero S.descent (fun p => (S.data p).chart) S.critical_model_germ ε hε
  have hsq (p : ManifoldMorse.criticalPoints E f) : (T.data p).radius ^ 2 < |f p - a| := by
    have hp := mul_pos (sub_pos.mpr (hsmall p)) (add_pos (hε p) (T.data p).radius_pos)
    have heq : (ε p) ^ 2 = |f p - a| := Real.sq_sqrt (abs_nonneg _)
    nlinarith
  refine ⟨T, hfield, hflow, hcharts, ?_, ?_⟩
  · intro p hp
    have hh := hsq p
    rw [abs_of_neg (sub_neg.mpr hp)] at hh
    change f p + (T.data p).radius ^ 2 < a
    linarith
  · intro p hp
    have hh := hsq p
    rw [abs_of_pos (sub_pos.mpr hp)] at hh
    change a < f p - (T.data p).radius ^ 2
    linarith

/-- A regular value has a closed interval of regular values around it. -/
theorem AdaptedWindows.regular_interval_around_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    {a : ℝ} (hreg : ∀ x, f x = a → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ l u : ℝ,
      l < a ∧ a < u ∧ ∀ x, f x ∈ Set.Icc l u → x ∉ ManifoldMorse.criticalPoints E f := by
  have ha : a ∉ f '' ManifoldMorse.criticalPoints E f := by
    rintro ⟨x, hx, hfx⟩
    exact hreg x hfx hx
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp ((S.finite.image f).isClosed.isOpen_compl.mem_nhds ha)
  refine ⟨a - ε / 2, a + ε / 2, by linarith, by linarith, ?_⟩
  intro x hx hcrit
  have hh : f x ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact hball hh ⟨x, hcrit, rfl⟩

/-- Relative form of the previous realisation for a whole window system: a compactly supported
relative isotopy `D` of a regular level `f⁻¹(c)` is realised by a new window system `T` with
arbitrarily small window radii, with the same Morse charts, with the same field near the critical
points, with unchanged backward limits, with forward limits composed with `D`, and with unchanged
orbits over the set where `D` is the identity. -/
theorem AdaptedWindows.exists_relative_level_surgery_system {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f) (z : { y : M // f y = c })
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := RegularLevel.chartedSpace hf hc
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          { y : M // f y = c } { y : M // f y = c } ∞)
      (K P : Set { y : M // f y = c }),
      IsCompact K →
        SupportedDiffeomorph.SupportedRelativeIsotopy D K P →
          ∃ T : AdaptedWindows E f,
            (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < ε p) ∧
                (∀ p ∈ ManifoldMorse.criticalPoints E f,
                    ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
                  (∀ x : { y : M // f y = c },
                      ∀ p : M,
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
                          Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p)) ∧
                    (∀ x : { y : M // f y = c },
                        ∀ p : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
                            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p)) ∧
                      ∀ x ∈ P,
                        Set.range (fun t => T.flow t x.val) =
                          Set.range (fun t => S.flow t x.val) := by
  let _ := RegularLevel.chartedSpace hf hc
  dsimp only
  intro D K P hK I
  obtain ⟨a, b, ha, hb, hband⟩ := S.regular_interval_around_level hc
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright, hprotected⟩ :=
    RegularLevel.exists_flow_realization_of_relative_isotopy hf S.smooth S.descent
      S.flow S.integral ha hb hband hc z D K P hK I
  have hmodel (p : ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct hV G hG
      (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback, hforward⟩ :=
    FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val D
      (fun x p => (hgeometry x).2.1 p) (fun x p => (hgeometry x).2.2 p) hend hleft hright
  refine ⟨T, hcharts, hradii, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x p
    rw [hflow]
    exact hback x p
  · intro x p
    rw [hflow]
    exact hforward x p
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = (fun t => H t x.val) := funext (fun t => hprotected x hx t)
    rw [heq]
    exact (hgeometry x.val).1

/-- In a band `[a, b]` containing at most the critical point `p`, a point of the level `b` whose
forward orbit does not converge to `p` flows down to the level `a`. -/
theorem AdaptedWindows.reaches_lower_of_excluded_critical_limit {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (p : M)
    (hwindow : ∀ q ∈ ManifoldMorse.criticalPoints E f, f q ∈ Set.Icc a b → q = p)
    (x : { y : M // f y = b })
    (hexcluded : ¬Filter.Tendsto (fun t => S.flow t x.val) Filter.atTop (𝓝 p)) :
    x.val ∈ FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hregular := hb x.val x.property
  have hbelow : f r < a := by
    by_contra h
    have hrb : f r < b := by simpa only [x.property] using (hheights hregular).1
    have heq := hwindow r hr ⟨le_of_not_gt h, hrb.le⟩
    exact hexcluded (heq ▸ hforward)
  have habove : a < f q := by
    have hbq : b < f q := by simpa only [x.property] using (hheights hregular).2
    exact hab.trans hbq
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward habove hbelow

/-- A point of the upper level of the window around `p` whose transported image avoids the belt
sphere of `p` flows down, in the transported system, to the lower level of that window. -/
theorem AdaptedWindows.reaches_old_lower_of_belt_avoidance {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (D : (S.data p).UpperLevel → (S.data p).UpperLevel)
    (hforward :
      ∀ x : (S.data p).UpperLevel,
        ∀ q : M,
          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 q) ↔
            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 q))
    (x : (S.data p).UpperLevel) (hx : D x ∉ Set.range (S.data p).surgery.beltSphere) :
    x.val ∈ FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
  apply
    T.reaches_lower_of_excluded_critical_limit hf
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
      (S.data p).upper_regular p.val (S.isolated p) x
  intro h
  exact hx ((S.belt_basin_iff hf p (D x)).mp ((hforward x p.val).mp h))

/-- No point of the upper level of the window around `p` has its backward orbit converging to
`p`: the ascending sphere of `p` meets that level, but backward orbits leave the window. -/
theorem AdaptedWindows.not_backward_basin_on_upper_level {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (x : (S.data p).UpperLevel) :
    ¬Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) := by
  intro hx
  obtain ⟨q, hq, r, hr, hback, _, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have heq : q = p.val := tendsto_nhds_unique hback hx
  have hh := (hheights ((S.data p).upper_regular x.val x.property)).2
  rw [heq, x.property] at hh
  exact (not_lt_of_ge (S.toSurgeryWindows.value_lt_upper p).le) hh

/-- Flowing a family from a regular level `a` down to a lower regular level `b` preserves the
description of its image as the set of points whose backward orbit converges to `p`. -/
theorem AdaptedWindows.transported_backward_basin_image {E M X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) (p : M) (hap : a < f p)
    (α : X → { y : M // f y = a }) (β : X → { y : M // f y = b })
    (hα :
      ∀ x : { y : M // f y = a },
        x ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p))
    (horbit : ∀ z, ∃ t : ℝ, S.flow t (α z).val = (β z).val) :
    ∀ y : { x : M // f x = b },
      y ∈ Set.range β ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact
      (MorseCancellation.flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
        ((hα (α z)).mp (Set.mem_range_self z))
  · intro hy
    obtain ⟨q, hq, r, hr, _, hforward, hheights⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct y.val
    have hrb : f r < b := by simpa only [y.property] using (hheights (hb y.val y.property)).1
    obtain ⟨s, hs⟩ :=
      FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hy
        hforward hap (hrb.trans hab)
    let x : { z : M // f z = a } := ⟨S.flow s y.val, hs⟩
    have hx : Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) :=
      (MorseCancellation.flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hα x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

/-- If the band `[b, a]` contains no critical value, every point of the level `a` flows down to
the level `b`. -/
theorem AdaptedWindows.reaches_lower_in_regular_band {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (x : { y : M // f y = a }) : x.val ∈ FlowCancellation.levelBasin S.flow f b := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hra : f r < a := by simpa only [x.property] using (hheights (ha x.val x.property)).1
  have haq : a < f q := by simpa only [x.property] using (hheights (ha x.val x.property)).2
  have hrb : f r < b := by
    by_contra h
    exact hgap r hr ⟨le_of_not_gt h, hra.le⟩
  exact
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hab.trans haq) hrb

/-- There is no gradient trajectory from a critical point `q` of index `0` down to a critical
point `p` below it: a local minimum has no descending sphere. -/
theorem AdaptedWindows.no_connection_of_upper_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ := MorseCancellation.unitSphere_isEmpty_of_finrank_zero hqzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hxq hxp
      (S.toSurgeryWindows.lower_lt_value q)
      ((S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq))
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hlim : Filter.Tendsto (fun s => S.flow s (y : M)) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff S.flow t x q.val).mpr hxq
  obtain ⟨v, -⟩ := (S.attaching_basin_iff hf q y).mp hlim
  exact isEmptyElim v

/-- There is no gradient trajectory from a critical point `q` down to a critical point `p` of
index `dim M` below it: a local maximum has no ascending sphere. -/
theorem AdaptedWindows.no_connection_of_lower_positive_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ := MorseCancellation.unitSphere_isEmpty_of_finrank_zero hpzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ :=
    FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hxq hxp
      ((S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q))
      (S.toSurgeryWindows.value_lt_upper p)
  let y : (S.data p).UpperLevel := ⟨S.flow t x, ht⟩
  have hlim : Filter.Tendsto (fun s => S.flow s (y : M)) Filter.atTop (𝓝 p.val) :=
    (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mpr hxp
  obtain ⟨v, -⟩ := (S.belt_basin_iff hf p y).mp hlim
  exact isEmptyElim v

attribute [local instance 100] Classical.propDecidable in
/-- If the critical values are ordered by Morse index, then above any critical point of index
`≤ k` there is a regular value `a` separating the critical points of index `≤ k` (below `a`) from
those of index `≥ k+1` (above `a`).  This is the cut supplied by the self-indexing theorem,
Milnor, *Lectures on the h-cobordism theorem*, Theorem 4.8. -/
theorem AdaptedWindows.exists_ordered_index_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    {k : ℕ} (q : ManifoldMorse.criticalPoints E f)
    (hq : MorseCancellation.nativeMorseIndex E f q ≤ k) :
    ∃ a : ℝ,
      (∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) ∧
        f q < a ∧
          (∀ z : ManifoldMorse.criticalPoints E f,
              a ≤ f z → k + 1 ≤ MorseCancellation.nativeMorseIndex E f z) ∧
            ∀ z : ManifoldMorse.criticalPoints E f,
              f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ k := by
  let _ := S.finite.fintype
  let K :=
    Finset.univ.filter
      (fun z : ManifoldMorse.criticalPoints E f => MorseCancellation.nativeMorseIndex E f z ≤ k)
  have hqK : q ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  obtain ⟨r, hr, hmax⟩ :=
    K.exists_max_image (fun z : ManifoldMorse.criticalPoints E f => f z) ⟨q, hqK⟩
  have hrk : MorseCancellation.nativeMorseIndex E f r ≤ k := (Finset.mem_filter.mp hr).2
  let a := S.toSurgeryWindows.upper r
  have hra : f r < a := S.toSurgeryWindows.value_lt_upper r
  refine ⟨a, (S.data r).upper_regular, (hmax q hqK).trans_lt hra, ?_, ?_⟩
  · intro z haz
    by_contra hnot
    have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact (not_lt_of_ge (haz.trans (hmax z hzK))) hra
  · intro z hza
    rcases lt_trichotomy (f z) (f r) with hzr | hzr | hrz
    · exact (horder z r hzr).trans hrk
    · have he : z = r := Subtype.ext (S.distinct z.property r.property hzr)
      simpa only [he] using hrk
    · have he : z = r :=
        Subtype.ext
          (S.toSurgeryWindows.isolated r z.val z.property
            ⟨(S.toSurgeryWindows.lower_lt_value r).le.trans hrz.le, hza⟩)
      simpa only [he] using hrk

end
