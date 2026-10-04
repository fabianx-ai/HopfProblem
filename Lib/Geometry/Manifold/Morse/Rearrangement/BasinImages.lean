/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime
/-!
# Basins of critical points as countable unions of smooth images of balls

Let `S : AdaptedWindows E f` be a gradient-like flow for a Morse function `f` on a compact
manifold with Morse charts at the critical points. The forward basin
`{x | S.flow t x → p}` of a critical point `p` is the union over `n : ℕ` of the images under
`S.flow (-n)` of a ball in the positive coordinates of the Morse chart, each a smooth image
(`AdaptedWindows.exists_forward_basin_smooth_images`; backward basins and the negative
coordinates: `exists_backward_basin_smooth_images`). A ball of a `d'`-dimensional space with
`d' ≤ d` is the image of a smooth map from `EuclideanSpace ℝ (Fin d)`
(`MorseCancellation.exists_smooth_ball_parametrization`,
`exists_global_smooth_image_of_ball`), so a basin is covered by countably many global smooth
images of `EuclideanSpace ℝ (Fin d)` whenever `d` bounds the coindex (forward) or the index
(backward) of `p` (`exists_forward_basin_global_images`, `exists_backward_basin_global_images`).

`MorseCancellation.forwardHighBasins S a` (`backwardLowBasins S a`) is the union of the forward
basins of the critical points with `a ≤ f p` (backward basins with `f p ≤ a`); it is the
intersection of the sublevel conditions along the flow (`forwardHighBasins_eq_inter`), hence
closed (`isClosed_endpoint_obstruction`, `isClosed_backwardLowBasins`), and the union of the two
is the complement of the basin `FlowCancellation.levelBasin S.flow f a` of a regular level
(`levelBasin_compl_eq_endpoint_obstruction`). Indexed by the countable types
`EndpointBasinIndex` and `LowBackwardBasinIndex`, these obstructions are covered by countably
many smooth images of `EuclideanSpace ℝ (Fin d)` under the index bounds
(`AdaptedWindows.exists_endpoint_obstruction_global_images`,
`exists_low_backward_obstruction_images`).

Textbook: the stable and unstable manifolds of a nondegenerate critical point are injectively
immersed disks of dimension the coindex and the index (Milnor, *Lectures on the h-cobordism
theorem*, §4), which is what the general-position steps of the rearrangement and cancellation
theorems use.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Basin images of adapted windows -/

/-- Forward basins are covered by countably many smooth ball images. -/
theorem AdaptedWindows.exists_forward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) :
    ∃ r : ℝ,
      0 < r ∧
        (∀ n : ℕ,
            ContMDiffOn 𝓘(ℝ, (S.data p).chart.PositiveCoordinates) 𝓘(ℝ, E) ∞
              (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v)))
              (Metric.ball 0 r)) ∧
          {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
            ⋃ n : ℕ,
              (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v))) ''
                Metric.ball (0 : (S.data p).chart.PositiveCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.PositiveCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    (0, v) ∈ c.splitChart.target :=
    hblock
      ⟨Metric.mem_closedBall_self hr.le,
        Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
          (Metric.ball_subset_closedBall hv)⟩
  have hlocal :
    ContMDiffOn 𝓘(ℝ, c.PositiveCoordinates) 𝓘(ℝ, E) ∞ (fun v => c.splitChart.symm (0, v))
      (Metric.ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn
      htarget
  have hpoint (v : c.PositiveCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    Filter.Tendsto (fun t => S.flow t (c.splitChart.symm (0, v))) Filter.atTop (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (0, v) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (0, v)) = (0, v) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (0, v)) hs ?_ ?_).1).mpr
    · rw [he]
    · rw [he]
      simpa using hr
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact
      (SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (-(n : ℝ))).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim := hx.comp tendsto_natCast_atTop_atTop
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancellation.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancellation.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).1).mp hnew
      refine
        Set.mem_iUnion.mpr ⟨n, (c.splitChart (S.flow (n : ℝ) x)).2, mem_ball_zero_iff.mpr hp', ?_⟩
      have he : (0, (c.splitChart (S.flow (n : ℝ) x)).2) = c.splitChart (S.flow (n : ℝ) x) :=
        Prod.ext hz.symm rfl
      change S.flow (-(n : ℝ)) (c.splitChart.symm (0, (c.splitChart (S.flow (n : ℝ) x)).2)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (n : ℝ) x)) = S.flow (n : ℝ) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
      exact
        (MorseCancellation.flow_time_atTop_limit_iff S.flow (-(n : ℝ)) (c.splitChart.symm (0, v))
              p.val).mpr
          (hpoint v hv)

/-- Backward basins are covered by countably many smooth ball images. -/
theorem AdaptedWindows.exists_backward_basin_smooth_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) :
    ∃ r : ℝ,
      0 < r ∧
        (∀ n : ℕ,
            ContMDiffOn 𝓘(ℝ, (S.data p).chart.NegativeCoordinates) 𝓘(ℝ, E) ∞
              (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0)))
              (Metric.ball 0 r)) ∧
          {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
            ⋃ n : ℕ,
              (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0))) ''
                Metric.ball (0 : (S.data p).chart.NegativeCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.NegativeCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    (v, 0) ∈ c.splitChart.target :=
    hblock
      ⟨Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r)
          (Metric.ball_subset_closedBall hv),
        Metric.mem_closedBall_self hr.le⟩
  have hlocal :
    ContMDiffOn 𝓘(ℝ, c.NegativeCoordinates) 𝓘(ℝ, E) ∞ (fun v => c.splitChart.symm (v, 0))
      (Metric.ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
      htarget
  have hpoint (v : c.NegativeCoordinates) (hv : v ∈ Metric.ball 0 (r / 2)) :
    Filter.Tendsto (fun t => S.flow t (c.splitChart.symm (v, 0))) Filter.atBot (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (v, 0) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (v, 0)) = (v, 0) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (v, 0)) hs ?_ ?_).2).mpr
    · rw [he]
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
    · rw [he]
      simpa using hr
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact
      (SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
            (n : ℝ)).contMDiff.comp_contMDiffOn
        hlocal
  · ext x
    constructor
    · intro hx
      have hlim : Filter.Tendsto (fun n : ℕ => S.flow (-(n : ℝ)) x) Filter.atTop (𝓝 p.val) :=
        hx.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually
            (MorseCancellation.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (MorseCancellation.flow_time_atBot_limit_iff S.flow (-(n : ℝ)) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (-(n : ℝ)) x)).2 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).2).mp hnew
      refine
        Set.mem_iUnion.mpr
          ⟨n, (c.splitChart (S.flow (-(n : ℝ)) x)).1, mem_ball_zero_iff.mpr hn, ?_⟩
      have he :
        ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0) = c.splitChart (S.flow (-(n : ℝ)) x) :=
        Prod.ext rfl hz.symm
      change S.flow (n : ℝ) (c.splitChart.symm ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (-(n : ℝ)) x)) = S.flow (-(n : ℝ)) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, add_neg_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
      exact
        (MorseCancellation.flow_time_atBot_limit_iff S.flow (n : ℝ) (c.splitChart.symm (v, 0))
              p.val).mpr
          (hpoint v hv)

/-- A basis element admits a smooth ball parametrization. -/
theorem MorseCancellation.exists_smooth_ball_parametrization {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ}
    (hr : 0 < r) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → V, ContDiff ℝ ∞ ψ ∧ Set.range ψ = Metric.ball 0 r := by
  let W := EuclideanSpace ℝ (Fin (d - Module.finrank ℝ V))
  let L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (V × W) :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin, W]
        omega)
  let π : EuclideanSpace ℝ (Fin d) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V W).comp L.toContinuousLinearMap
  have hπ : Function.Surjective π := by
    intro v
    refine ⟨L.symm (v, 0), ?_⟩
    change (L (L.symm (v, 0))).1 = v
    rw [L.apply_symm_apply]
  let B := OpenPartialHomeomorph.univBall (0 : V) r
  let ψ : EuclideanSpace ℝ (Fin d) → V := B ∘ π
  have hψ : ContDiff ℝ ∞ ψ := OpenPartialHomeomorph.contDiff_univBall.comp π.contDiff
  refine ⟨ψ, hψ, ?_⟩
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    have hm : π z ∈ B.source := by rw [OpenPartialHomeomorph.univBall_source]; trivial
    have hh := B.map_source hm
    rwa [OpenPartialHomeomorph.univBall_target _ hr] at hh
  · intro hv
    have hvt : v ∈ B.target := by rw [OpenPartialHomeomorph.univBall_target _ hr]; exact hv
    obtain ⟨z, hz⟩ := hπ (B.symm v)
    refine ⟨z, ?_⟩
    change B (π z) = v
    rw [hz]
    exact B.right_inv hvt

/-- A local smooth ball parametrization extends to a global image. -/
theorem MorseCancellation.exists_global_smooth_image_of_ball {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ} (hr : 0 < r) {f : V → M}
    (hf : ContMDiffOn 𝓘(ℝ, V) I ∞ f (Metric.ball 0 r)) :
    ∃ g : EuclideanSpace ℝ (Fin d) → M,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I ∞ g ∧ Set.range g = f '' Metric.ball 0 r := by
  obtain ⟨ψ, hψ, hrange⟩ := exists_smooth_ball_parametrization hd hr
  refine ⟨f ∘ ψ, ?_, ?_⟩
  · intro x
    have hx : ψ x ∈ Metric.ball (0 : V) r := hrange ▸ Set.mem_range_self x
    exact (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).comp x hψ.contMDiff.contMDiffAt
  · rw [Set.range_comp, hrange]

/-! ### Endpoint obstructions and basin counts -/

/-- The union of forward basins of high critical points. -/
def MorseCancellation.forwardHighBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : ManifoldMorse.criticalPoints E f,
      a ≤ f p ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)}

/-- The union of backward basins of low critical points. -/
def MorseCancellation.backwardLowBasins {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (a : ℝ) : Set M :=
  {x |
    ∃ p : ManifoldMorse.criticalPoints E f,
      f p ≤ a ∧ Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)}

/-- The high forward basins as an intersection formulation. -/
theorem MorseCancellation.forwardHighBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : forwardHighBasins S a = ⋂ t : ℝ, {x | a ≤ f (S.flow t x)} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact hp.trans (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t)
  · intro hbound
    obtain ⟨-, -, q, hq, -, hlim, -⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨q, hq⟩, ?_, hlim⟩
    exact
      ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

/-- The low backward basins as an intersection formulation. -/
theorem MorseCancellation.backwardLowBasins_eq_inter {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : backwardLowBasins S a = ⋂ t : ℝ, {x | f (S.flow t x) ≤ a} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t).trans hp
  · intro hbound
    obtain ⟨p, hp, -, -, hlim, -, -⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    refine ⟨⟨p, hp⟩, ?_, hlim⟩
    exact
      le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
        (Filter.Eventually.of_forall hbound)

/-- The endpoint obstruction set is closed. -/
theorem MorseCancellation.isClosed_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (a : ℝ) : IsClosed (forwardHighBasins S a ∪ backwardLowBasins S a) := by
  rw [forwardHighBasins_eq_inter S hf, backwardLowBasins_eq_inter S hf]
  apply IsClosed.union
  · exact
      isClosed_iInter
        (fun t =>
          isClosed_le continuous_const
            (hf.continuous.comp (S.flow.continuous continuous_const continuous_id)))
  · exact
      isClosed_iInter
        (fun t =>
          isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
            continuous_const)

/-- The level minus the basins is the endpoint obstruction. -/
theorem MorseCancellation.levelBasin_compl_eq_endpoint_obstruction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) :
    (FlowCancellation.levelBasin S.flow f a)ᶜ =
      forwardHighBasins S a ∪ backwardLowBasins S a := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, q, hq, hback, hforward, -⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct x
    by_cases hqa : a ≤ f q
    · exact Or.inl ⟨⟨q, hq⟩, hqa, hforward⟩
    by_cases hpa : f p ≤ a
    · exact Or.inr ⟨⟨p, hp⟩, hpa, hback⟩
    exact
      False.elim
        (hx
          (FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
            hback hforward (lt_of_not_ge hpa) (lt_of_not_ge hqa)))
  · intro hx hcross
    obtain ⟨t, ht⟩ := hcross
    have hmono :=
      FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    rcases hx with ⟨p, hp, hlim⟩ | ⟨p, hp, hlim⟩
    · have hh := hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hh hp) p.property
    · have hh := hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hp hh) p.property

/-- Forward basins are covered by global smooth images. -/
theorem AdaptedWindows.exists_forward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_forward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.PositiveCoordinates ≤ d := by
    have hh := (S.data p).chart.finrank_negative_add_positive
    rw [MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hd
    omega
  choose g hg hrange using
    (fun n => MorseCancellation.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

/-- Backward basins are covered by global smooth images. -/
theorem AdaptedWindows.exists_backward_basin_global_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hd : MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → M,
      (∀ n, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g n)) ∧
        {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)} =
          ⋃ n, Set.range (g n) := by
  obtain ⟨r, hr, hsmooth, hcover⟩ := S.exists_backward_basin_smooth_images hf p
  have hdim : Module.finrank ℝ (S.data p).chart.NegativeCoordinates ≤ d := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hd
  choose g hg hrange using
    (fun n => MorseCancellation.exists_global_smooth_image_of_ball hdim hr (hsmooth n))
  refine ⟨g, hg, ?_⟩
  rw [hcover]
  exact Set.iUnion_congr (fun n => (hrange n).symm)

/-- The index type of endpoint obstruction basins. -/
abbrev MorseCancellation.EndpointBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (a : ℝ) :=
  ({ p : ManifoldMorse.criticalPoints E f // a ≤ f p.val } × ℕ) ⊕
    ({ p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ)

/-- There are countably many endpoint obstruction basins. -/
theorem MorseCancellation.endpointBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (EndpointBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold EndpointBasinIndex
  infer_instance

/-- The endpoint obstruction is covered by global smooth images. -/
theorem AdaptedWindows.exists_endpoint_obstruction_global_images {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancellation.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancellation.forwardHighBasins S a ∪ MorseCancellation.backwardLowBasins S a =
          ⋃ i, Set.range (g i) := by
  choose gF hgF hF using
    (fun p : { p : ManifoldMorse.criticalPoints E f // a ≤ f p.val } =>
      S.exists_forward_basin_global_images hf p.val (hhigh p.val p.property))
  choose gB hgB hB using
    (fun p : { p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  let g : MorseCancellation.EndpointBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M :=
    Sum.elim (fun i => gF i.1 i.2) (fun i => gB i.1 i.2)
  refine ⟨g, ?_, ?_⟩
  · intro i
    rcases i with ⟨p, n⟩ | ⟨p, n⟩
    · exact hgF p n
    · exact hgB p n
  · ext x
    constructor
    · rintro (⟨p, hp, hx⟩ | ⟨p, hp, hx⟩)
      · have hh : x ∈ ⋃ n, Set.range (gF ⟨p, hp⟩ n) := (hF ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨Sum.inl (⟨p, hp⟩, n), hn⟩
      · have hh : x ∈ ⋃ n, Set.range (gB ⟨p, hp⟩ n) := (hB ⟨p, hp⟩) ▸ hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨p, hp⟩, n), hn⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rcases i with ⟨p, n⟩ | ⟨p, n⟩
      · have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val.val)} :=
          by
          rw [hF p]
          exact Set.mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inl ⟨p.val, p.property, hh⟩
      · have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val.val)} :=
          by
          rw [hB p]
          exact Set.mem_iUnion.mpr ⟨n, hi⟩
        exact Or.inr ⟨p.val, p.property, hh⟩

/-- The low backward basins form a closed set. -/
theorem MorseCancellation.isClosed_backwardLowBasins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) : IsClosed (backwardLowBasins S a) := by
  rw [backwardLowBasins_eq_inter S hf]
  exact
    isClosed_iInter
      (fun t =>
        isClosed_le (hf.continuous.comp (S.flow.continuous continuous_const continuous_id))
          continuous_const)

/-- The index type of low backward basins. -/
abbrev MorseCancellation.LowBackwardBasinIndex {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (a : ℝ) :=
  { p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } × ℕ

/-- There are countably many low backward basins. -/
theorem MorseCancellation.lowBackwardBasinIndex_countable {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (a : ℝ) : Countable (LowBackwardBasinIndex (E := E) (f := f) a) := by
  let _ := S.finite.fintype
  unfold LowBackwardBasinIndex
  infer_instance

/-- The low backward obstruction is covered by smooth images. -/
theorem AdaptedWindows.exists_low_backward_obstruction_images {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) {d : ℕ}
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d) :
    ∃ g : MorseCancellation.LowBackwardBasinIndex (E := E) (f := f) a → EuclideanSpace ℝ (Fin d) → M,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, E) ∞ (g i)) ∧
        MorseCancellation.backwardLowBasins S a = ⋃ i, Set.range (g i) := by
  choose g hg hcover using
    (fun p : { p : ManifoldMorse.criticalPoints E f // f p.val ≤ a } =>
      S.exists_backward_basin_global_images hf p.val (hlow p.val p.property))
  refine ⟨fun i => g i.1 i.2, fun i => hg i.1 i.2, ?_⟩
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    have hh : x ∈ ⋃ n, Set.range (g ⟨p, hp⟩ n) := (hcover ⟨p, hp⟩) ▸ hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hh
    exact Set.mem_iUnion.mpr ⟨(⟨p, hp⟩, n), hn⟩
  · intro hx
    obtain ⟨⟨p, n⟩, hn⟩ := Set.mem_iUnion.mp hx
    have hh : x ∈ {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val.val)} := by
      rw [hcover p]
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    exact ⟨p.val, p.property, hh⟩
