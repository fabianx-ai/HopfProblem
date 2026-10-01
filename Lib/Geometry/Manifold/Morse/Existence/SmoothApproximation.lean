/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Flow.Compact
public import Lib.Geometry.Manifold.Morse.Existence.HomotopicRelWithin
public import Lib.Geometry.Manifold.Morse.Existence.PartialChart
public import Lib.Geometry.Manifold.Morse.Existence.HomotopyCollars
public import Lib.Geometry.Manifold.Morse.Existence.ChartPerturbation

/-!
# Smooth approximation of continuous maps

Every continuous map `f : X → N` from a compact (Hausdorff) manifold to a manifold without
boundary is homotopic to a smooth map, and the homotopy can be taken relative to a closed set
`C` on a neighbourhood of which `f` is already smooth; consequently, homotopic smooth maps are
smoothly homotopic by a homotopy that is stationary near both ends. The proof covers `X` by
finitely many `MapSmoothingPatch`es (a chart of `N` together with nested bump functions) and
smooths `f` one patch at a time (Hirsch, *Differential Topology*, Thm 2.2.6; Lee,
*Introduction to Smooth Manifolds*, Thms 6.26 and 6.29).

## Main definitions and results

* `ManifoldSmoothing.MapSmoothingPatch`
* `ManifoldSmoothing.exists_smooth_map_homotopicRel`
* `ManifoldSmoothing.exists_smooth_map_homotopic`
* `ManifoldSmoothing.exists_smooth_homotopy_with_collars`

## Tags

Whitney approximation, smoothing, homotopy
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Smoothing patches -/

/-- A patch on which a map can be smoothed relative to a boundary. -/
structure ManifoldSmoothing.MapSmoothingPatch {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N] where
  /-- A smooth partial diffeomorphism from an open subset of `N` onto an open subset of the
  model space `G`, in whose coordinates the map is modified. -/
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  /-- The inner bump function; its `plateau` is the interior of `{cutoff = 1}`. -/
  cutoff : X → ℝ
  /-- The outer bump function, equal to `1` on the topological support of `cutoff`. -/
  outer : X → ℝ
  /-- The inner bump function `cutoff` is smooth. -/
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  /-- The outer bump function `outer` is smooth. -/
  outer_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ outer
  /-- The inner bump function `cutoff` has compact support. -/
  compact : HasCompactSupport cutoff
  /-- The outer bump function `outer` has compact support. -/
  outer_compact : HasCompactSupport outer
  /-- `outer x = 1` for every `x` in the topological support of `cutoff`. -/
  nested : ∀ x ∈ tsupport cutoff, outer x = 1

/-- Two smoothing patches are compatible on their overlap. -/
def ManifoldSmoothing.MapSmoothingPatch.Compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    (f : X → N) : Prop :=
  Set.MapsTo f (tsupport p.outer) p.chart.source

/-- The plateau where the patch smoothing is exact. -/
def ManifoldSmoothing.MapSmoothingPatch.plateau {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N)) : Set X :=
  interior {x | p.cutoff x = 1}

/-- The inner support lies in the outer patch. -/
theorem ManifoldSmoothing.MapSmoothingPatch.inner_support_subset_outer {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N)) :
    tsupport p.cutoff ⊆ tsupport p.outer := by
  intro x hx
  apply subset_tsupport p.outer
  change p.outer x ≠ 0
  rw [p.nested x hx]
  exact one_ne_zero

/-- The inner patch is compatible with the outer. -/
theorem ManifoldSmoothing.MapSmoothingPatch.inner_compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    {f : X → N} (hf : p.Compatible f) : tsupport p.cutoff ⊆ f ⁻¹' p.chart.source := fun _ hx =>
  hf (p.inner_support_subset_outer hx)

/-- The plateau cutoff is eventually one. -/
theorem ManifoldSmoothing.MapSmoothingPatch.plateau_eventually_one {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] (p : ManifoldSmoothing.MapSmoothingPatch I J (X := X) (N := N))
    {x : X} (hx : x ∈ p.plateau) : p.cutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact interior_subset (s := {y : X | p.cutoff y = 1}) hy

/-- One patch smoothing step exists within the target. -/
theorem ManifoldSmoothing.exists_smoothing_patch_step_within_target {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ E] [IsManifold I ∞ X] [SigmaCompactSpace X]
    [T2Space X] {ι : Type*} [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (i : ι)
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C)
    (hU : IsOpen U) (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        HomotopicRelWithin f f' C D O ∧
          ∀ x, ContMDiffAt I J ∞ f x ∨ x ∈ (p i).plateau → ContMDiffAt I J ∞ f' x := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous (p i).chart
        f.continuous (p i).smooth.continuous hinner (p j).outer_compact.isCompact
        (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid_of_continuous (p i).chart f.continuous
      (p i).smooth.continuous (p i).compact hinner
  obtain ⟨g, hg, happrox, heq⟩ :=
    ChartMapPerturbation.exists_smooth_coordinate_approximation (p i).chart f.continuous
      (p i).outer_smooth (hcompatible i) hC hU hCU hfU (lt_min hδ hr)
  let a : X → G := fun x =>
    g x - ChartMapPerturbation.cutoffCoordinates (p i).chart f (p i).outer x
  have ha : Continuous a :=
    hg.continuous.sub
      (ChartMapPerturbation.continuous_cutoffCoordinates (p i).chart f.continuous
        (p i).outer_smooth.continuous (hcompatible i))
  have hbound (x : X) : ‖a x‖ < Min.min δ r := by simpa only [a, dist_eq_norm] using happrox x
  have haδ (x : X) : ‖a x‖ < δ := (lt_min_iff.mp (hbound x)).1
  have har (x : X) : ‖a x‖ < r := (lt_min_iff.mp (hbound x)).2
  let f' : C(X, N) :=
    ⟨ChartMapPerturbation.variablePerturb (p i).chart f (p i).cutoff a,
      ChartMapPerturbation.continuous_variablePerturb (p i).chart f.continuous
        (p i).smooth.continuous hinner ha (fun x => hvalid _ (har x))⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · intro j x hx
    have hh :=
      hδkeep
        (show a x ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ x)
    exact hh j hx
  · exact
      ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset (p i).chart
        f.continuous (p i).smooth.continuous hinner ha hvalid har
        (fun x hx => Or.inr (sub_eq_zero.mpr (heq hx))) hsource hmaps
  · intro x hx
    rcases hx with hold | hplateau
    · exact
        ChartMapPerturbation.contMDiffAt_smoothedMap_of_old (p i).chart hinner
          (hcompatible i) hold (p i).smooth.contMDiffAt (p i).outer_smooth.contMDiffAt
          hg.contMDiffAt (hvalid _ (har x))
    · exact
        ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau (p i).chart hinner
          (p i).nested ((p i).plateau_eventually_one hplateau) hg.contMDiffAt (hvalid _ (har x))

/-- Finite-patch smoothing: finitely many smoothing patches suffice to make a piecewise-defined function smooth on the whole compact manifold (Milnor, h-cobordism, Theorem 2.5 proof). -/
theorem ManifoldSmoothing.exists_finite_patch_smoothing_within_target {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        HomotopicRelWithin f f' C D O ∧
          ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) → ContMDiffAt I J ∞ f' x := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hcompatible, HomotopicRelWithin.refl f C hmaps, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hc₁, hhom₁, hsm₁⟩ := ih
    have hf₁U : ContMDiffOn I J ∞ f₁ U := by
      intro x hx
      exact (hsm₁ x (Or.inl ((hfU x hx).contMDiffAt (hU.mem_nhds hx)))).contMDiffWithinAt
    obtain ⟨f₂, hc₂, hhom₂, hsm₂⟩ :=
      exists_smoothing_patch_step_within_target p i f₁ hc₁ hC hU hCU hf₁U (hsource i)
        hhom₁.mapsTo_right
    refine ⟨f₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hsm₂ x
    rcases hx with hold | ⟨j, hj, hplateau⟩
    · exact Or.inl (hsm₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hplateau
      · exact Or.inl (hsm₁ x (Or.inr ⟨j, hjs, hplateau⟩))

/-- Finitely many patches give a global smoothing. -/
theorem ManifoldSmoothing.exists_finite_patch_smoothing {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) (s : Finset ι) :
    ∃ f' : C(X, N),
      (∀ j, (p j).Compatible f') ∧
        f.HomotopicRel f' C ∧
          ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) → ContMDiffAt I J ∞ f' x := by
  obtain ⟨f', hc, hrel, hsm⟩ :=
    exists_finite_patch_smoothing_within_target p f hcompatible hC hU hCU hfU
      (fun _ => Set.subset_univ _) (Set.mapsTo_univ f Set.univ) s
  exact ⟨f', hc, hrel.homotopicRel, hsm⟩

/-- A smoothing exists from a finite patch cover. -/
theorem ManifoldSmoothing.exists_smoothing_of_finite_patches {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [T2Space X] [SigmaCompactSpace X] [TopologicalSpace N] [ChartedSpace K N] {ι : Type*}
    [Finite ι] (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (f : C(X, N))
    (hcompatible : ∀ j, (p j).Compatible f) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hfU : ContMDiffOn I J ∞ f U) (hcover : ∀ x, ∃ i, x ∈ (p i).plateau) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing p f hcompatible hC hU hCU hfU Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hsm x (Or.inr ⟨i, Finset.mem_univ i, hi⟩)

/-! ### Existence of smoothings -/

/-- A smoothing patch exists at a point inside an open set. -/
theorem ManifoldSmoothing.exists_smoothing_patch_at_in_open {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) (x : X) {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N),
      p.Compatible f ∧ x ∈ p.plateau ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∈ 𝓝 x := (c.open_source.preimage f.continuous).mem_nhds hsource
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  have hχone : {y : X | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hχone
  let p : MapSmoothingPatch I J (X := X) (N := N) :=
    { chart := c
      cutoff := β
      outer := χ
      smooth := β.contMDiff
      outer_smooth := χ.contMDiff
      compact := β.hasCompactSupport
      outer_compact := χ.hasCompactSupport
      nested := fun y hy => hβ hy }
  refine ⟨p, hχ, ?_, fun _ hx => hx.2⟩
  change x ∈ interior {y : X | β y = 1}
  exact mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one

/-- A smoothing patch exists at every point. -/
theorem ManifoldSmoothing.exists_smoothing_patch_at {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau := by
  obtain ⟨p, hc, hp, _⟩ :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f x isOpen_univ (Set.mem_univ _)
  exact ⟨p, hc, hp⟩

/-- A smooth map homotopic relative to a closed set exists. -/
theorem ManifoldSmoothing.exists_smooth_map_homotopicRel {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [CompactSpace X] (f : C(X, N)) {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) : ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  have hp (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau :=
    exists_smoothing_patch_at f x
  choose p hpcompatible hpplateau using hp
  have hopen (x : X) : IsOpen (p x).plateau := isOpen_interior
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, (p x).plateau := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hpplateau x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (p x).plateau) hopen hcover
  apply
    exists_smoothing_of_finite_patches (fun i : s => p i.1) f (fun i => hpcompatible i.1) hC hU
      hCU hfU
  intro x
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hix⟩

/-- A smooth map homotopic to a continuous map exists. -/
theorem ManifoldSmoothing.exists_smooth_map_homotopic {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    [CompactSpace X] (f : C(X, N)) : ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.Homotopic f' := by
  obtain ⟨f', hf', ⟨H⟩⟩ :=
    exists_smooth_map_homotopicRel (I := I) (J := J) f isClosed_empty isOpen_empty
      (Set.Subset.refl ∅) contMDiffOn_empty
  exact ⟨f', hf', ⟨H.toHomotopy⟩⟩

/-- A smooth homotopy with collar control exists. -/
theorem ManifoldSmoothing.exists_smooth_homotopy_with_collars {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [CompactSpace X] [TopologicalSpace N] [ChartedSpace K N]
    [IsManifold J ∞ N] {f g : C(X, N)} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (H : f.Homotopy g) :
    ∃ H' : f.Homotopy g,
      ContMDiff ((𝓡∂ 1).prod I) J ∞ H' ∧
        (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H' (t, x) = f x) ∧
          (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H' (t, x) = g x) := by
  obtain ⟨F, hF, ⟨K⟩⟩ :=
    exists_smooth_map_homotopicRel (flattenedHomotopyMap H) isClosed_homotopyCollars
      isOpen_homotopyCollarNeighborhood homotopyCollars_subset
      (contMDiffOn_flattenedHomotopyMap hf hg H)
  have hlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : F (t, x) = f x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inl ht)
    rw [← heq]
    exact flattenedHomotopyMap_lower H t x (by linarith)
  have hhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : F (t, x) = g x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inr ht)
    rw [← heq]
    exact flattenedHomotopyMap_upper H t x (by linarith)
  let H' : f.Homotopy g :=
    { toContinuousMap := F
      map_zero_left := fun x => hlo 0 x (by norm_num)
      map_one_left := fun x => hhi 1 x (by norm_num) }
  exact ⟨H', hF, hlo, hhi⟩
