/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence.HomotopicRelWithin

/-!
# Perturbing a map inside a chart of the target

Let `f : X → N` be a map, `c` a `PartialDiffeomorph` from an open subset of `N` onto an open
subset of a normed space `F`, and `β : X → ℝ` a bump function with `tsupport β ⊆ f ⁻¹' c.source`.
For `a : F` (or a map `a : X → F`), `perturb c f β a` sends `x` to `c.symm (c (f x) + β x • a)`
when `f x ∈ c.source` and to `f x` otherwise; it is `Valid` when the shifted coordinates stay in
`c.target`, which holds for small `a`. The perturbation is smooth (resp. continuous) where `f`,
`β` and `a` are, and `t ↦ perturb c f β (t • a)` is a homotopy relative to `{β = 0}`
(`homotopyRel`, `variableHomotopyRel`) that maps `D` into `O` at all times whenever
`c.source ⊆ O` and `f` maps `D` into `O`. With `cutoffCoordinates c f χ = χ • (c ∘ f)` approximated by a
smooth `g` (`exists_smooth_coordinate_approximation`), `smoothedMap` replaces `f` on the plateau
`{χ = 1}` by a smooth map. This is the local step of the Whitney approximation theorem
(cf. Hirsch, *Differential Topology*, §2.2; Lee, *Introduction to Smooth Manifolds*, Ch. 6).

## Main definitions and results

* `ChartMapPerturbation.perturb`, `ChartMapPerturbation.Valid`,
  `ChartMapPerturbation.exists_radius_valid`
* `ChartMapPerturbation.homotopyRel`, `ChartMapPerturbation.variableHomotopyRel`,
  `ChartMapPerturbation.homotopicRelWithin_of_source_subset`
* `ChartMapPerturbation.cutoffCoordinates`, `ChartMapPerturbation.smoothedMap`,
  `ChartMapPerturbation.exists_smooth_coordinate_approximation`

## Tags

Whitney approximation, perturbation, chart
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Chart perturbations of maps -/

/-- A family of coordinate perturbations of a map. -/
def ChartMapPerturbation.coordinateFamily {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (q : F × X) : F :=
  c (f q.2) + β q.2 • q.1

/-- A coordinate perturbation is valid on a chart domain. -/
def ChartMapPerturbation.Valid {G F K X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) : Prop :=
  ∀ x ∈ tsupport β, coordinateFamily c f β (a, x) ∈ c.target

/-- The perturbed map in the chart. -/
def ChartMapPerturbation.perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) (x : X) : N := by
  classical exact if f x ∈ c.source then c.symm (coordinateFamily c f β (a, x)) else f x

/-- A zero perturbation leaves the map unchanged. -/
theorem ChartMapPerturbation.perturb_eq_of_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : F) {x : X}
    (hx : β x = 0) : perturb c f β a x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, if_pos, coordinateFamily, hx, zero_smul, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, if_false]

/-- The zero perturbation is the original map. -/
theorem ChartMapPerturbation.perturb_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (x : X) :
    perturb c f β 0 x = f x := by
  classical
  by_cases hs : f x ∈ c.source
  · simp only [perturb, hs, if_pos, coordinateFamily, smul_zero, add_zero]
    exact c.left_inv' hs
  · simp only [perturb, hs, if_false]

/-- The zero perturbation is valid. -/
theorem ChartMapPerturbation.valid_zero {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : Valid c f β (0 : F) := by
  intro x hx
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- The coordinate perturbation lands in the target chart. -/
theorem ChartMapPerturbation.coordinate_mem_target {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F}
    (ha : Valid c f β a) {x : X} (hx : f x ∈ c.source) :
    coordinateFamily c f β (a, x) ∈ c.target := by
  by_cases hβx : β x = 0
  · simpa only [coordinateFamily, hβx, zero_smul, add_zero] using c.map_source' hx
  · exact ha x (subset_tsupport β hβx)

/-- The perturbed map lands in the source. -/
theorem ChartMapPerturbation.perturb_mem_source {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F} (ha : Valid c f β a)
    {x : X} (hx : f x ∈ c.source) : perturb c f β a x ∈ c.source := by
  classical
  simp only [perturb, hx, if_pos]
  exact c.map_target' (coordinate_mem_target c f β ha hx)

/-- The perturbation computes in the chart. -/
theorem ChartMapPerturbation.chart_perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F} (ha : Valid c f β a)
    {x : X} (hx : f x ∈ c.source) : c (perturb c f β a x) = coordinateFamily c f β (a, x) := by
  classical
  simp only [perturb, hx, if_pos]
  exact c.right_inv' (coordinate_mem_target c f β ha hx)

/-- The coordinate family is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_coordinateFamily {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hq)).comp q
        (hf.comp contMDiff_snd).contMDiffAt).add
    (((hβ.comp contMDiff_snd).contMDiffAt).smul contMDiffAt_fst)

/-- Small perturbations are valid. -/
theorem ChartMapPerturbation.eventually_valid {E G F H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  have hh := (contMDiffAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).continuousAt
  apply hh.preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- If `f` and `β` are smooth, `β` has compact support and `tsupport β ⊆ f ⁻¹' c.source`, then
there is `ε > 0` such that the perturbation by every `a` with `‖a‖ < ε` is `Valid`. -/
theorem ChartMapPerturbation.exists_radius_valid {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_valid c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

/-- The perturbation is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_perturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := contMDiffAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
        (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

/-- The perturbation is jointly smooth. -/
theorem ChartMapPerturbation.contMDiff_perturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f β a) : ContMDiff I J ∞ (perturb c f β a) := by
  intro x
  exact
    (contMDiffAt_perturb c hf hβ hsupport (a, x) ha).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)

/-- The coordinate family is continuous. -/
theorem ChartMapPerturbation.continuousAt_coordinateFamily {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (q : F × X) (hq : f q.2 ∈ c.source) :
    ContinuousAt (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hq)).comp (f :=
        fun r : F × X => f r.2) (hf.comp continuous_snd).continuousAt).add
    ((hβ.comp continuous_snd).continuousAt.smul continuousAt_fst)

/-- A continuous small perturbation is eventually valid. -/
theorem ChartMapPerturbation.eventually_valid_of_continuous {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  apply (continuousAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

/-- A radius on which a continuous perturbation is valid exists. -/
theorem ChartMapPerturbation.exists_radius_valid_of_continuous {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) : ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (eventually_valid_of_continuous c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

/-- The perturbation is continuous. -/
theorem ChartMapPerturbation.continuousAt_perturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : Continuous f)
    (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (ha : Valid c f β q.1) : ContinuousAt (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := continuousAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh :=
      (c.contMDiffOn_invFun.continuousOn.continuousAt (c.open_target.mem_nhds htarget)).comp
        hcoord
    apply hh.congr
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.comp continuous_snd).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp continuous_snd).continuousAt.congr
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact (perturb_eq_of_zero c f β r.1 hr).symm

/-- A continuous family eventually maps a compact set into an open set. -/
theorem ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous
    {G F K X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [TopologicalSpace N] [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N}
    {β : X → ℝ} (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {L : Set X} (hL : IsCompact L) {U : Set N} (hU : IsOpen U) (hfL : Set.MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), Set.MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  apply
    (continuousAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

/-- The perturbation of a smooth map is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_perturb_of_contMDiffAt {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X) (hf : ContMDiffAt I J ∞ f q.2)
    (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β q.2) (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord : ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp q
            (hf.comp q contMDiffAt_snd)).add
        ((hβ.comp q contMDiffAt_snd).smul contMDiffAt_fst)
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuousAt.comp continuousAt_snd).preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp q contMDiffAt_snd).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

/-- A family eventually maps a compact set into an open set. -/
theorem ChartMapPerturbation.eventually_maps_compact_into_open {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {L : Set X}
    (hL : IsCompact L) {U : Set N} (hU : IsOpen U) (hfL : Set.MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), Set.MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  have hc :=
    (contMDiffAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

/-- A small interval scaling stays within the bound. -/
theorem ChartMapPerturbation.norm_interval_smul_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ε : ℝ} {a : F} (ha : ‖a‖ < ε) (t : unitInterval) : ‖(t : ℝ) • a‖ < ε := by
  calc
    ‖(t : ℝ) • a‖ = (t : ℝ) * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
    _ ≤ ‖a‖ := by nlinarith [t.2.2, norm_nonneg a]
    _ < ε := ha

/-- The perturbation is a homotopy relative to the fixed set. -/
def ChartMapPerturbation.homotopyRel {E G F H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {ε : ℝ} (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a)
    {a : F} (ha : ‖a‖ < ε) :
    (⟨f, hf.continuous⟩ : C(X, N)).HomotopyRel
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0}
    where
  toFun q := perturb c f β ((q.1 : ℝ) • a) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt ha q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const).prodMk continuous_snd
    exact
      ContinuousAt.comp (f := fun r : unitInterval × X => ((r.1 : ℝ) • a, r.2))
        (contMDiffAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a), q.2) hv).continuousAt
        hp.continuousAt
  map_zero_left
    x := by
    change perturb c f β ((0 : ℝ) • a) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left
    x := by
    change perturb c f β ((1 : ℝ) • a) x = perturb c f β a x
    rw [one_smul]
  prop' _ x hx := perturb_eq_of_zero c f β _ hx

/-- The time-variable perturbation of a homotopy. -/
def ChartMapPerturbation.variablePerturb {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) (a : X → F) (x : X) : N :=
  perturb c f β (a x) x

/-- The variable perturbation is continuous. -/
theorem ChartMapPerturbation.continuous_variablePerturb {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    {a : X → F} (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (ha : Continuous a) (hvalid : ∀ x, Valid c f β (a x)) :
    Continuous (variablePerturb c f β a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact
    (continuousAt_perturb c hf hβ hsupport (a x, x) (hvalid x)).comp (f := fun y : X => (a y, y))
      (ha.prodMk continuous_id).continuousAt

/-- The variable perturbation is smooth. -/
theorem ChartMapPerturbation.contMDiffAt_variablePerturb {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {a : X → F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {x : X} (hf : ContMDiffAt I J ∞ f x)
    (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x) (ha : ContMDiffAt I 𝓘(ℝ, F) ∞ a x)
    (hvalid : Valid c f β (a x)) : ContMDiffAt I J ∞ (variablePerturb c f β a) x :=
  (contMDiffAt_perturb_of_contMDiffAt c hsupport (a x, x) hf hβ hvalid).comp x (f := fun y : X =>
    (a y, y)) (ha.prodMk contMDiffAt_id)

/-- The variable perturbation is a relative homotopy. -/
def ChartMapPerturbation.variableHomotopyRel {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {a : X → F}
    (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C : Set X} (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0) :
    (⟨f, hf⟩ : C(X, N)).HomotopyRel
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩
      C
    where
  toFun q := perturb c f β ((q.1 : ℝ) • a q.2) q.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hv := hvalid _ (norm_interval_smul_lt (hbound q.2) q.1)
    have hp : Continuous (fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) :=
      ((continuous_subtype_val.comp continuous_fst).smul (ha.comp continuous_snd)).prodMk
        continuous_snd
    exact
      (continuousAt_perturb c hf hβ hsupport (((q.1 : ℝ) • a q.2), q.2) hv).comp (f :=
        fun r : unitInterval × X => ((r.1 : ℝ) • a r.2, r.2)) hp.continuousAt
  map_zero_left
    x := by
    change perturb c f β ((0 : ℝ) • a x) x = f x
    rw [zero_smul, perturb_zero]
  map_one_left
    x := by
    change perturb c f β ((1 : ℝ) • a x) x = perturb c f β (a x) x
    rw [one_smul]
  prop' t x
    hx := by
    rcases hfixed x hx with hb | ha₀
    · exact perturb_eq_of_zero c f β _ hb
    · change perturb c f β ((t : ℝ) • a x) x = f x
      rw [ha₀, smul_zero, perturb_zero]

/-- The perturbation cut off outside a plateau. -/
def ChartMapPerturbation.cutoffCoordinates {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ) (x : X) : F :=
  χ x • c (f x)

/-- The cutoff coordinates on the plateau. -/
theorem ChartMapPerturbation.cutoffCoordinates_eq_of_one {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (χ : X → ℝ) {x : X} (hx : χ x = 1) :
    cutoffCoordinates c f χ x = c (f x) := by simp only [cutoffCoordinates, hx, one_smul]

/-- The cutoff coordinates are continuous. -/
theorem ChartMapPerturbation.continuous_cutoffCoordinates {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ}
    (hf : Continuous f) (hχ : Continuous χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source) :
    Continuous (cutoffCoordinates c f χ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact
      hχ.continuousAt.smul
        ((c.contMDiffOn_toFun.continuousOn.continuousAt
              (c.open_source.mem_nhds (hsupport hx))).comp
          hf.continuousAt)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (continuousAt_const (y := (0 : F))).congr
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

/-- The cutoff coordinates are smooth. -/
theorem ChartMapPerturbation.contMDiffAt_cutoffCoordinates {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ}
    (hsupport : tsupport χ ⊆ f ⁻¹' c.source) {x : X} (hf : ContMDiffAt I J ∞ f x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) : ContMDiffAt I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) x := by
  by_cases hx : x ∈ tsupport χ
  · exact
      hχ.smul ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds (hsupport hx))).comp x hf)
  · have hz : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contMDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [cutoffCoordinates, hy, zero_smul, Pi.zero_apply]

/-- Whitney approximation in a chart: if `f` is continuous, smooth on an open set `U ⊇ C` with `C`
closed, and `χ` is a smooth bump with `tsupport χ ⊆ f ⁻¹' c.source`, then for every `ε > 0` there
is a smooth `g : X → F` within `ε` of `cutoffCoordinates c f χ` everywhere and equal to it on `C`
(cf. Lee, *Introduction to Smooth Manifolds*, Ch. 6, Whitney approximation). -/
theorem ChartMapPerturbation.exists_smooth_coordinate_approximation {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {χ : X → ℝ} [FiniteDimensional ℝ E]
    [IsManifold I ∞ X] [SigmaCompactSpace X] [T2Space X] (hf : Continuous f)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hsupport : tsupport χ ⊆ f ⁻¹' c.source) {C U : Set X}
    (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : X → F,
      ContMDiff I 𝓘(ℝ, F) ∞ g ∧
        (∀ x, Dist.dist (g x) (cutoffCoordinates c f χ x) < ε) ∧
          Set.EqOn g (cutoffCoordinates c f χ) C := by
  have hk := continuous_cutoffCoordinates c hf hχ.continuous hsupport
  have hkU : ContMDiffOn I 𝓘(ℝ, F) ∞ (cutoffCoordinates c f χ) U := by
    intro x hx
    exact
      (contMDiffAt_cutoffCoordinates c hsupport ((hfU x hx).contMDiffAt (hU.mem_nhds hx))
          hχ.contMDiffAt).contMDiffWithinAt
  have hUn : U ∈ 𝓝ˢ C := mem_nhdsSet_iff_forall.mpr (fun x hx => hU.mem_nhds (hCU hx))
  obtain ⟨g, hg, hgeq, _⟩ :=
    hk.exists_contMDiff_approx_and_eqOn I ⊤ (continuous_const (y := ε)) (fun _ => hε) hC hUn hkU
  exact ⟨g, g.contMDiff, hg, hgeq⟩

/-- The smoothed map built from the cutoff perturbation. -/
def ChartMapPerturbation.smoothedMap {G F K X N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F) : X → N :=
  variablePerturb c f β (fun x => g x - cutoffCoordinates c f χ x)

/-- The coordinate family on the plateau. -/
theorem ChartMapPerturbation.coordinateFamily_eq_on_plateau {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ) (g : X → F) {x : X}
    (hβx : β x = 1) (hχx : χ x = 1) :
    coordinateFamily c f β (g x - cutoffCoordinates c f χ x, x) = g x := by
  simp only [coordinateFamily, cutoffCoordinates, hβx, hχx, one_smul]
  abel

/-- The smoothed map on the plateau. -/
theorem ChartMapPerturbation.smoothedMap_eq_on_plateau {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β χ : X → ℝ)
    (g : X → F) (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hnested : ∀ x ∈ tsupport β, χ x = 1)
    {x : X} (hβx : β x = 1) : smoothedMap c f β χ g x = c.symm (g x) := by
  classical
  have hs : x ∈ tsupport β :=
    subset_tsupport β
      (by
        change β x ≠ 0
        rw [hβx]
        exact one_ne_zero)
  change perturb c f β (g x - cutoffCoordinates c f χ x) x = _
  have hsource : f x ∈ c.source := hsupport hs
  simp only [perturb, hsource, if_pos]
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)]

/-- The smoothed map is smooth on the plateau. -/
theorem ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {χ : X → ℝ} {g : X → F}
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (hnested : ∀ x ∈ tsupport β, χ x = 1) {x : X}
    (hplateau : β =ᶠ[𝓝 x] (fun _ => 1)) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x := by
  have hβx : β x = 1 := hplateau.eq_of_nhds
  have hs : x ∈ tsupport β :=
    subset_tsupport β
      (by
        change β x ≠ 0
        rw [hβx]
        exact one_ne_zero)
  have htarget := coordinate_mem_target c f β hvalid (hsupport hs)
  rw [coordinateFamily_eq_on_plateau c f β χ g hβx (hnested x hs)] at htarget
  have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp x hg
  apply hh.congr_of_eventuallyEq
  filter_upwards [hplateau] with y hy
  exact smoothedMap_eq_on_plateau c f β χ g hsupport hnested hy

/-- The smoothed map is smooth where the old map was. -/
theorem ChartMapPerturbation.contMDiffAt_smoothedMap_of_old {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} {χ : X → ℝ} {g : X → F}
    (hβsupport : tsupport β ⊆ f ⁻¹' c.source) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source) {x : X}
    (hf : ContMDiffAt I J ∞ f x) (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β x)
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ x) (hg : ContMDiffAt I 𝓘(ℝ, F) ∞ g x)
    (hvalid : Valid c f β (g x - cutoffCoordinates c f χ x)) :
    ContMDiffAt I J ∞ (smoothedMap c f β χ g) x :=
  contMDiffAt_variablePerturb c hβsupport hf hβ
    (hg.sub (contMDiffAt_cutoffCoordinates c hχsupport hf hχ)) hvalid

/-! ### Homotopy relative to a subset -/

/-- The perturbation lands in the target given a source subset. -/
theorem ChartMapPerturbation.perturb_mem_of_source_subset {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : X → N) (β : X → ℝ) {a : F}
    (ha : Valid c f β a) {O : Set N} (hsource : c.source ⊆ O) {x : X} (hx : f x ∈ O) :
    perturb c f β a x ∈ O := by
  by_cases hxc : f x ∈ c.source
  · exact hsource (perturb_mem_source c f β ha hxc)
  · simpa only [perturb, if_neg hxc] using hx

/-- The perturbation is homotopic relative to the fixed set within the target. -/
theorem ChartMapPerturbation.homotopicRelWithin_of_source_subset {E G F H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ} (hf : ContMDiff I J ∞ f)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {ε : ℝ}
    (hvalid : ∀ a : F, ‖a‖ < ε → Valid c f β a) {a : F} (ha : ‖a‖ < ε) {D : Set X} {O : Set N}
    (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    HomotopicRelWithin (⟨f, hf.continuous⟩ : C(X, N))
      ⟨perturb c f β a, (contMDiff_perturb c hf hβ hsupport (hvalid a ha)).continuous⟩
      {x | β x = 0} D O := by
  refine ⟨homotopyRel c hf hβ hsupport hvalid ha, ?_⟩
  intro t x hx
  exact
    perturb_mem_of_source_subset c f β (hvalid _ (norm_interval_smul_lt ha t)) hsource (hmaps hx)

/-- The variable perturbation is relatively homotopic within the target. -/
theorem ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset {G F K X N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace K N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}
    (hf : Continuous f) (hβ : Continuous β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : X → F}
    (ha : Continuous a) {ε : ℝ} (hvalid : ∀ v : F, ‖v‖ < ε → Valid c f β v)
    (hbound : ∀ x, ‖a x‖ < ε) {C D : Set X} {O : Set N} (hfixed : ∀ x ∈ C, β x = 0 ∨ a x = 0)
    (hsource : c.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    HomotopicRelWithin (⟨f, hf⟩ : C(X, N))
      ⟨variablePerturb c f β a,
        continuous_variablePerturb c hf hβ hsupport ha (fun x => hvalid _ (hbound x))⟩
      C D O := by
  refine ⟨variableHomotopyRel c hf hβ hsupport ha hvalid hbound hfixed, ?_⟩
  intro t x hx
  exact
    perturb_mem_of_source_subset c f β (hvalid _ (norm_interval_smul_lt (hbound x) t)) hsource
      (hmaps hx)
