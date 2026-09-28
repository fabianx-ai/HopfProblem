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
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.Immersion.Relative
public import Lib.Geometry.Manifold.LocalDiffeomorph
public import Lib.Geometry.Manifold.Morse.Rearrangement.LevelTime
public import Lib.Geometry.Manifold.Morse.Rearrangement.BasinImages
/-!
# Path connectedness of regular levels

Joining lemmas for a flow `F` on a locally path-connected space along which `f` is antitone:
a point `x` of the sublevel `{f ≤ a}` whose forward limit `p` has `f p < a` is joined to `p`
inside the sublevel (`MorseCancellation.joinedIn_sublevel_of_forward_limit`), two such points
with a common limit are joined (`joined_sublevel_of_common_forward_limit`), and points of an
open forward basin are joined to the limit inside the basin (`joinedIn_open_forward_basin`,
for a minimum of an adapted window: `AdaptedWindows.joinedIn_minimum_basin`). A discrete family
of smooth maps is one smooth map on the product with the discrete manifold
(`contMDiff_discrete_family`, `range_discrete_family`).

Main result, `AdaptedWindows.joinedIn_regular_level_of_endpoint_dimensions`: for a regular
value `a` of `f`, if every critical point above `a` has coindex `≤ d`, every critical point
below `a` has index `≤ d`, and `1 + d < dim M`, then two points of the level `{f = a}` joined
by a path in `M` are joined inside the level. The complement of the level basin is a countable
union of smooth images of `EuclideanSpace ℝ (Fin d)` (`BasinImages`), so the path can be pushed
off it (`MorseCancellation.exists_smooth_path_avoiding_closed_image`) and then projected into
the level along the flow cylinder (`FlowCancellation.exists_native_level_flow_cylinder`).
Consequently the level is path connected when `M` is
(`pathConnectedSpace_regular_level_of_endpoint_dimensions`).

This is the general-position argument for the connectedness of intermediate levels used in the
rearrangement and cancellation theorems (cf. Milnor, *Lectures on the h-cobordism theorem*, §4).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Joining in sublevels and basins -/

/-- A discrete family of smooth maps is jointly smooth. -/
theorem MorseCancellation.contMDiff_discrete_family {ι V E H M : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] (f : ι → V → M) (hf : ∀ i, ContMDiff 𝓘(ℝ, V) I ∞ (f i)) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun p : ι × V => f p.1 p.2) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 0)) ι := ChartedSpace.ofDiscreteTopology
  change ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun p : ι × V => f p.1 p.2)
  intro p
  have hg :
    ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin 0)).prod 𝓘(ℝ, V)) I ∞ (fun q : ι × V => f p.1 q.2)
      p :=
    (hf p.1).contMDiffAt.comp p contMDiffAt_snd
  apply hg.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ι × V in 𝓝 p, q.1 ∈ ({ p.1 } : Set ι) :=
    ((isOpen_discrete ({ p.1 } : Set ι)).preimage continuous_fst).mem_nhds (Set.mem_singleton _)
  filter_upwards [hnear] with q hq
  rw [Set.mem_singleton_iff.mp hq]

/-- The range of a discrete family is the union of the ranges. -/
theorem MorseCancellation.range_discrete_family {ι V M : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M]
    (f : ι → V → M) : Set.range (fun p : ι × V => f p.1 p.2) = ⋃ i, Set.range (f i) := by
  ext x
  constructor
  · rintro ⟨⟨i, v⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, v, rfl⟩
  · intro hx
    obtain ⟨i, v, hv⟩ := Set.mem_iUnion.mp hx
    exact ⟨(i, v), hv⟩

/-- A point forward-limiting to a lower point joins it in the sublevel. -/
theorem MorseCancellation.joinedIn_sublevel_of_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {x p : X} {a : ℝ} (hx : f x ≤ a)
    (hp : f p < a) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    JoinedIn {y : X | f y ≤ a} x p := by
  have hU : {y : X | f y < a} ∈ 𝓝 p := (isOpen_lt hf continuous_const).mem_nhds hp
  have hC := pathComponentIn_mem_nhds hU
  obtain ⟨T, hT, hFT⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and (hlim.eventually hC)).exists
  have htail : JoinedIn {y : X | f y ≤ a} (F T x) p :=
    (show JoinedIn {y : X | f y < a} p (F T x) from hFT).symm.mono
      (fun y hy => (show f y < a from hy).le)
  have hsegment : JoinedIn {y : X | f y ≤ a} x (F T x) := by
    let γ : Path x (F T x) :=
      { toFun := fun u => F ((u : ℝ) * T) x
        continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
        source' := by simp
        target' := by simp }
    refine ⟨γ, fun u => ?_⟩
    have htime : 0 ≤ (u : ℝ) * T := mul_nonneg u.property.1 hT
    have hh := hmono x htime
    have hh' : f (F ((u : ℝ) * T) x) ≤ f x := by simpa only [F.map_zero_apply] using hh
    exact hh'.trans hx
  exact hsegment.trans htail

/-- Points with a common forward limit join in the sublevel. -/
theorem MorseCancellation.joined_sublevel_of_common_forward_limit {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x))) {a : ℝ} (x y : { z : X // f z ≤ a }) {p : X}
    (hp : f p < a) (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hy : Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) : Joined x y := by
  exact
    ((joinedIn_sublevel_of_forward_limit F hf hmono x.property hp hx).trans
        (joinedIn_sublevel_of_forward_limit F hf hmono y.property hp hy).symm).joined_subtype

/-- Points in an open forward basin join the limit point in it. -/
theorem MorseCancellation.joinedIn_open_forward_basin {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] (F : Flow ℝ X) (p : X)
    (hopen : IsOpen {x : X | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)})
    (hp : Filter.Tendsto (fun t => F t p) Filter.atTop (𝓝 p)) {x : X}
    (hx : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    JoinedIn {y : X | Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)} x p := by
  let B : Set X := {y | Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)}
  have hC := pathComponentIn_mem_nhds (hopen.mem_nhds hp)
  obtain ⟨T, hT⟩ := (hx.eventually hC).exists
  have htail : JoinedIn B (F T x) p := (show JoinedIn B p (F T x) from hT).symm
  let γ : Path x (F T x) :=
    { toFun := fun u => F ((u : ℝ) * T) x
      continuous_toFun := F.continuous (continuous_subtype_val.mul_const T) continuous_const
      source' := by simp
      target' := by simp }
  have hsegment : JoinedIn B x (F T x) := by
    refine ⟨γ, fun u => ?_⟩
    exact (flow_time_atTop_limit_iff F ((u : ℝ) * T) x p).mpr hx
  exact hsegment.trans htail

/-- A minimum-index critical point's forward basin is joined. -/
theorem AdaptedWindows.joinedIn_minimum_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 0) {x y : M}
    (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val))
    (hy : Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p.val)) :
    JoinedIn {z : M | Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 p.val)} x y := by
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  have hpp : Filter.Tendsto (fun t => S.flow t p.val) Filter.atTop (𝓝 p.val) := by
    have heq : (fun t => S.flow t p.val) = fun _ => p.val :=
      funext
        (fun t =>
          FlowConstruction.flow_fixed_of_zero (S.smooth.of_le (by simp)) S.flow S.integral
            (S.zero p p.property) t)
    rw [heq]
    exact tendsto_const_nhds
  have hopen := S.isOpen_minimum_forward_basin hf p hp
  exact
    (MorseCancellation.joinedIn_open_forward_basin S.flow p.val hopen hpp hx).trans
      (MorseCancellation.joinedIn_open_forward_basin S.flow p.val hopen hpp hy).symm

/-! ### Connectedness of regular levels -/

/-- Endpoint basins join inside the regular level under the dimension bounds. -/
theorem AdaptedWindows.joinedIn_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxa : f x = a) (hya : f y = a) (γ : Path x y) :
    JoinedIn {z : M | f z = a} x y := by
  let _ := S.finite.fintype
  let K := MorseCancellation.EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := MorseCancellation.endpointBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun z : K × V => g z.1 z.2) :=
    MorseCancellation.contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : Set.range G = (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [MorseCancellation.levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact MorseCancellation.range_discrete_family g
  have hclosed : IsClosed (Set.range G) := by
    rw [hrange, MorseCancellation.levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact MorseCancellation.isClosed_endpoint_obstruction S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : f z = a) : z ∉ Set.range G := by
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact ⟨0, by simpa only [S.flow.map_zero_apply] using hz⟩
  obtain ⟨η, -, havoid⟩ :=
    MorseCancellation.exists_smooth_path_avoiding_closed_image γ G hG hclosed hdim' (hnot x hxa)
      (hnot y hya)
  have hcross (t : unitInterval) : η t ∈ FlowCancellation.levelBasin S.flow f a := by
    have hh := havoid t
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hh
  let _ := RegularLevel.chartedSpace hf hreg
  let xL : { z : M // f z = a } := ⟨x, hxa⟩
  let yL : { z : M // f z = a } := ⟨y, hya⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
      (fun z hz => S.descent z (hreg z hz)) xL
  have hcont : Continuous (fun t : unitInterval => Φ.symm (η t)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous η.continuous
      (fun t => htarget.symm ▸ hcross t)
  have hinverse (z : { w : M // f w = a }) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let ξ : Path x y :=
    { toFun := fun t => (Φ.symm (η t)).1.val
      continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
      source' := by
        rw [η.source]
        exact congrArg (fun z : { w : M // f w = a } × ℝ => z.1.val) (hinverse xL)
      target' := by
        rw [η.target]
        exact congrArg (fun z : { w : M // f w = a } × ℝ => z.1.val) (hinverse yL) }
  exact ⟨ξ, fun t => (Φ.symm (η t)).1.property⟩

/-- The regular level is path connected under the endpoint dimension bounds. -/
theorem AdaptedWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hlow :
      ∀ p : ManifoldMorse.criticalPoints E f,
        f p ≤ a → MorseCancellation.nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) (z₀ : { z : M // f z = a }) :
    PathConnectedSpace { z : M // f z = a }
    where
  nonempty := ⟨z₀⟩
  joined x
    y :=
    (S.joinedIn_regular_level_of_endpoint_dimensions hf hreg hhigh hlow hdim x.property y.property
        (PathConnectedSpace.somePath x.val y.val)).joined_subtype
