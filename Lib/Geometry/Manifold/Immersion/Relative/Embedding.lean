/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Immersion.Relative.ImmersionLocus
public import Lib.Geometry.Manifold.Immersion.Relative.ChartPerturbation

/-!
# Relative embedding theorems for a general source

Smooth maps `f : E → N` from a normed space `E` into a manifold `N` in the range
`2 dim E < dim N`. A chart-supported perturbation in one avoidance patch removes the double
points that the patch's cutoff separates while keeping `f` an immersion on a compact set
(`ManifoldImmersion.exists_selfIntersection_removal_step_within_target`); iterated over a finite
family of patches separating all double points
(`ManifoldImmersion.exists_finite_selfIntersection_removal_within_target`,
`ManifoldImmersion.exists_embedding_of_finite_separating_patches_within_target`) this gives the
relative embedding theorem: an immersion on a compact set `K` which is injective on `K ∩ C` is
homotopic rel the closed set `C` to a map which is a closed embedding and an immersion on `K`
(`ManifoldImmersion.exists_compact_embedding_of_immersion`, and the form with the homotopy kept
inside an open target). With the additional range `dim E + dim Y < dim N` the image can also be
pushed off a closed set `g '' A`, `g : Y → N`
(`ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image`,
`..._of_isClosed_range`, and the relative-neighbourhood forms
`ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood`,
`ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood`).

`OpenObstacle.restrict g U` restricts an obstacle map to the preimage of an open set `U`, so that
these statements can be applied inside `U`; the patch existence lemmas
`ManifoldImmersion.exists_relative_immersion_patch_at`, `..._in_open`, and the separating patches
`ManifoldImmersion.exists_separating_patch_in_open` provide the patches.

## References

* Hirsch, *Differential Topology*, Ch. 2 §2 (Whitney's embedding theorem, relative form) and
  Ch. 3 §2.
* Whitney, *Differentiable manifolds*, Thm 5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- One patch of the avoidance induction: a small perturbation supported in the patch `p i` keeps
the map an immersion on `K`, creates no new double points, stays inside the open set `O`, and
pushes the image off `g '' A` wherever that patch's cutoff is nonzero. -/
theorem ManifoldImmersion.exists_embedded_image_avoidance_step_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    {C K : Set E} (p : ι → GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (hK : IsCompact K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          HomotopicRelWithin f f' C K O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf (p i).smooth
      (p i).compact (hcompatible i) hK hderiv
  have hstay :=
    ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
      (hcompatible i) hK hO hmaps
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and (hold.and hstay))
  obtain ⟨r, hr, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hnoNew, havoid⟩ :=
    ChartMapPerturbation.exists_small_embedding_avoiding_parameter (p i).chart hf hg
      (p i).smooth (p i).compact (hcompatible i) hself hobstacle (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  let Hrel :=
    ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth (hcompatible i) hvalid har
  refine ⟨f', hsmooth, hretained.1, ?_, hretained.2.1, hnoNew, hretained.2.2, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t ((p i).fixed x hx) }, ?_⟩
    intro t x hx
    change ChartMapPerturbation.perturb (p i).chart f (p i).cutoff ((t : ℝ) • a) x ∈ O
    have hsmall : (t : ℝ) • a ∈ Metric.ball (0 : G) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        ChartMapPerturbation.norm_interval_smul_lt haδ t
    exact (hδkeep hsmall).2.2 hx
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ g '' A := hx.resolve_right (Classical.not_not.mpr hzero)
      change ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ g '' A
      rwa [ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, _, hy⟩
      exact havoid x hzero y hy.symm

/-- Iterating the previous step over a finite set of patches: the resulting map avoids `g '' A`
wherever one of the chosen cutoffs is nonzero. -/
theorem ManifoldImmersion.exists_finite_embedded_image_avoidance_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    {C K : Set E} (p : ι → GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (hK : IsCompact K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) (s : Finset ι) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          HomotopicRelWithin f f' C K O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧
                  ∀ x, (f x ∉ g '' A ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨f, hf, hcompatible, HomotopicRelWithin.refl f C hmaps, hderiv, (fun _ _ hxy => hxy),
        hmaps, ?_⟩
    intro x hx
    simpa only [Finset.notMem_empty, false_and, exists_false, or_false] using hx
  | @insert i s _
    ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, hd₁, hnoNew₁, hmaps₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, hd₂, hnoNew₂, hmaps₂, havoid₂⟩ :=
      exists_embedded_image_avoidance_step_controlled p i f₁ g A hf₁ hg hc₁ hself hobstacle hK hd₁
        hO hmaps₁
    refine
      ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, hd₂, (fun x y hxy => hnoNew₁ x y (hnoNew₂ x y hxy)),
        hmaps₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hactive⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hactive
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hactive⟩))

/-- Relative embedding with avoidance of a closed obstacle `g '' A`, keeping the map inside a
prescribed open set: in the general-position range `2 dim E < dim G`, `dim E + dim E' < dim G`,
the map can be made a closed embedding and an immersion on `K` while avoiding the obstacle on
`L`. -/
theorem ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image_controlled
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        HomotopicRelWithin f f' C K O ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  classical
  let bad : Set E := L ∩ f ⁻¹' g '' A
  have hbad : IsCompact bad := hL.inter_right (hclosed.preimage f.continuous)
  have hp (x : bad) :
    ∃ p : GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    GeneralPosition.exists_avoidance_patch_at (I := 𝓘(ℝ, E)) (J := J) f hC
      (fun hx => hfixed x.1 ⟨x.property.1, hx⟩ x.property.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff) hopen hcover
  obtain ⟨f', hf', -, hhom, hderiv', hnoNew, hmaps', havoid⟩ :=
    exists_finite_embedded_image_avoidance_controlled (fun i : s => p i.1) f g A hf hg
      (fun i => hpcompatible i.1) hself hobstacle hK hderiv hO hmaps Finset.univ
  refine ⟨f', hf', hhom, ?_, hderiv', hnoNew, hmaps', ?_⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (f'.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property (hnoNew x y hxy))
  · intro x hx
    apply havoid x
    rcases hx with hold | hxL
    · exact Or.inl hold
    · by_cases hxg : f x ∈ g '' A
      · have hx : x ∈ bad := ⟨hxL, hxg⟩
        obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs hx)
        exact Or.inr ⟨⟨i, hi⟩, Finset.mem_univ _, hix⟩
      · exact Or.inl hxg

/-- The same statement with an ordinary relative homotopy in place of the homotopy constrained to
the open target. -/
theorem ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_image
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                Set.MapsTo f' K O ∧ ∀ x, (f x ∉ g '' A ∨ x ∈ L) → f' x ∉ g '' A := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image_controlled f g A hf hg hclosed hself
      hobstacle hK hL hC hinj hderiv hfixed hO hmaps
  exact ⟨f', hf', hhom.homotopicRel, hemb, hd, hnoNew, hmaps', havoid⟩

/-- Version of the previous statement with the obstacle the whole closed image of `g`. -/
theorem ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K L C : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hfixed : ∀ x ∈ L ∩ C, f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              (∀ x y, f' x = f' y → f x = f y) ∧
                ∀ x, (f x ∉ Set.range g ∨ x ∈ L) → f' x ∉ Set.range g := by
  obtain ⟨f', hf', hhom, hemb, hd, hnoNew, -, havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g Set.univ hf hg
      (by simpa only [Set.image_univ] using hclosed) hself hobstacle hK hL hC hinj hderiv
      (by simpa only [Set.image_univ] using hfixed) isOpen_univ (fun _ _ => Set.mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, hnoNew, ?_⟩
  simpa only [Set.image_univ] using havoid


/-- Existence of a smoothing patch at a point off a closed set `C`, with chart inside a prescribed
open target and cutoff vanishing on `C`. -/
theorem ManifoldImmersion.exists_relative_immersion_patch_at_in_open {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E,
        p.Compatible f ∧
          IsCompact L ∧
            L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧ (∀ y ∈ C, p.cutoff y = 0) ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  have hχone : {y : E | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hχone
  let p : ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N) :=
    { chart := c
      cutoff := β
      outer := χ
      smooth := β.contMDiff
      outer_smooth := χ.contMDiff
      compact := β.hasCompactSupport
      outer_compact := χ.hasCompactSupport
      nested := fun y hy => hβ hy }
  have hxp : x ∈ p.plateau := mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
  obtain ⟨L, hxL, hLp, hL⟩ := local_compact_nhds (isOpen_interior.mem_nhds hxp)
  refine ⟨p, L, (fun _ hy => (hχ hy).1), hL, hxL, hLp, ?_, fun _ hz => hz.2⟩
  intro y hy
  change β y = 0
  by_contra hne
  have hi : y ∈ tsupport β := subset_tsupport β hne
  have ho : y ∈ tsupport χ :=
    subset_tsupport χ
      (by
        change χ y ≠ 0
        rw [hβ hi]
        exact one_ne_zero)
  exact (hχ ho).2 hy

/-- Existence of a smoothing patch at a point off a closed set `C`, with cutoff vanishing on `C`. -/
theorem ManifoldImmersion.exists_relative_immersion_patch_at {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) :
    ∃ p : ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E,
        p.Compatible f ∧ IsCompact L ∧ L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧ ∀ y ∈ C, p.cutoff y = 0 := by
  obtain ⟨p, L, hc, hL, hn, hp, hfix, _⟩ :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC hx isOpen_univ (Set.mem_univ _)
  exact ⟨p, L, hc, hL, hn, hp, hfix⟩


/-- One step of the self-intersection removal: a perturbation supported in a single avoidance patch
creates no new double points and keeps the map an immersion on `K`. -/
theorem ManifoldImmersion.exists_selfIntersection_removal_step_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {D : Set E} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          HomotopicRelWithin f g C D O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
              ∀ x y, g x = g y → f x = f y ∧ (p i).cutoff x = (p i).cutoff y := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf (p i).smooth
      (p i).compact (hcompatible i) hK hinj
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and hold)
  obtain ⟨r, hr, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hremove⟩ :=
    ChartMapPerturbation.exists_small_collision_removing_parameter (p i).chart hf
      (p i).smooth (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let g : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained :=
    hδkeep (show a ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine ⟨g, hsmooth, hretained.1, ?_, hretained.2, hremove⟩
  have hrel :=
    ChartMapPerturbation.homotopicRelWithin_of_source_subset (p i).chart hf (p i).smooth
      (hcompatible i) hvalid har hsource hmaps
  exact hrel.mono (fun x hx => (p i).fixed x hx) (Set.Subset.refl D) (Set.Subset.refl O)

/-- Iterating the removal step over a finite family of patches. -/
theorem ManifoldImmersion.exists_finite_selfIntersection_removal_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) {D : Set E} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) (s : Finset ι) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          HomotopicRelWithin f g C D O ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
              ∀ x y, g x = g y → f x = f y ∧ ∀ i ∈ s, (p i).cutoff x = (p i).cutoff y := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    exact
      ⟨f, hf, hcompatible, HomotopicRelWithin.refl f C hmaps, hinj, fun _ _ hxy =>
        ⟨hxy, fun _ hi => False.elim (Finset.notMem_empty _ hi)⟩⟩
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁, hpair₁⟩ := ih
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂, hpair₂⟩ :=
      exists_selfIntersection_removal_step_within_target p i g₁ hg₁ hc₁ hdim hK hinj₁ (hsource i)
        hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hinj₂, ?_⟩
    intro x y hxy
    have hnew := hpair₂ x y hxy
    have hold := hpair₁ x y hnew.1
    refine ⟨hold.1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact hnew.2
    · exact hold.2 j hjs

/-- If a finite family of patches separates every pair of double points on `K`, the map can be made
a closed embedding and an immersion on `K` by a homotopy rel `C` within the open target. -/
theorem ManifoldImmersion.exists_embedding_of_finite_separating_patches_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hseparate : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → f x = f y → ∃ i, (p i).cutoff x ≠ (p i).cutoff y)
    {D : Set E} {O : Set N} (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : Set.MapsTo f D O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        HomotopicRelWithin f g C D O ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨g, hg, -, hhom, hinjg, hpairs⟩ :=
    exists_finite_selfIntersection_removal_within_target p f hf hcompatible hdim hK hinj hsource
      hmaps Finset.univ
  refine ⟨g, hg, hhom, ?_, hinjg⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  obtain ⟨hold, hcutoffs⟩ := hpairs x y hxy
  obtain ⟨i, hi⟩ := hseparate x x.property y y.property hne hold
  exact hi (hcutoffs i (Finset.mem_univ i))

/-- Existence of an avoidance patch whose cutoff is `1` at `x` and `0` at a second point `y ≠ x`,
with chart inside a prescribed open target. -/
theorem ManifoldImmersion.exists_separating_patch_in_open {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x y : E} (hx : x ∉ C) (hxy : x ≠ y) {O : Set N} (hO : IsOpen O)
    (hxO : f x ∈ O) :
    ∃ p : GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x = 1 ∧ p.cutoff y = 0 ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ (C ∪ { y })ᶜ ∈ 𝓝 x := by
    apply
      ((c.open_source.preimage f.continuous).inter
          ((hC.union isClosed_singleton).isOpen_compl)).mem_nhds
    exact ⟨hsource, fun h => h.elim hx (fun h => hxy h)⟩
  obtain ⟨β, -, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  let p : GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C :=
    { chart := c
      cutoff := β
      smooth := β.contMDiff
      compact := β.hasCompactSupport
      fixed := fun z hz => image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inl hz)) }
  refine ⟨p, (fun _ ht => (hβ ht).1), β.eq_one, ?_, fun _ hz => hz.2⟩
  exact image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inr rfl))

/-- Existence of an avoidance patch separating two distinct points, provided they are not both in
the fixed closed set. -/
theorem ManifoldImmersion.exists_separating_patch_of_not_both_fixed_in_open
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] (f : C(E, N))
    {C : Set E} (hC : IsClosed C) {x y : E} (hxy : x ≠ y) (hfixed : ¬(x ∈ C ∧ y ∈ C)) {O : Set N}
    (hO : IsOpen O) (hxO : x ∉ C → f x ∈ O) (hyO : y ∉ C → f y ∈ O) :
    ∃ p : GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x ≠ p.cutoff y ∧ p.chart.source ⊆ O := by
  by_cases hx : x ∈ C
  · have hy : y ∉ C := fun hy => hfixed ⟨hx, hy⟩
    obtain ⟨p, hp, hpy, hpx, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hy hxy.symm hO (hyO hy)
    exact ⟨p, hp, by rw [hpx, hpy]; exact zero_ne_one, hs⟩
  · obtain ⟨p, hp, hpx, hpy, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hx hxy hO (hxO hx)
    exact ⟨p, hp, by rw [hpx, hpy]; exact one_ne_zero, hs⟩


/-- In the range `2 dim E < dim G`, an immersion on a compact set `K` which is already injective on
`K ∩ C` is homotopic rel `C`, within a prescribed open target, to a closed embedding of `K` that
is still an immersion there (Hirsch, *Differential Topology*, Ch. 3). -/
theorem ManifoldImmersion.exists_compact_embedding_of_immersion_within_target
    {E G H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C)) {O : Set N} (hO : IsOpen O) (hmaps : Set.MapsTo f (K \ C) O) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        HomotopicRelWithin f g C (K \ C) O ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  classical
  let bad := doublePoints f K
  have hbad : IsCompact bad := isCompact_doublePoints_of_injective_nativeDerivative hf hK hinj
  have hp (q : bad) :
    ∃ p : GeneralPosition.MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff q.1.1 ≠ p.cutoff q.1.2 ∧ p.chart.source ⊆ O := by
    have hq := q.property
    rcases hq with ⟨hx, hy, hne, heq⟩
    have hnot : ¬(q.1.1 ∈ C ∧ q.1.2 ∈ C) := by
      rintro ⟨hxC, hyC⟩
      exact hne (hfixed ⟨hx, hxC⟩ ⟨hy, hyC⟩ heq)
    exact
      exists_separating_patch_of_not_both_fixed_in_open f hC hne hnot hO
        (fun hxC => hmaps ⟨hx, hxC⟩) (fun hyC => hmaps ⟨hy, hyC⟩)
  choose p hpcompatible hpactive hpsource using hp
  let U (q : bad) : Set (E × E) := {r | (p q).cutoff r.1 ≠ (p q).cutoff r.2}
  have hU (q : bad) : IsOpen (U q) :=
    isOpen_ne_fun ((p q).smooth.continuous.comp continuous_fst)
      ((p q).smooth.continuous.comp continuous_snd)
  have hcover : bad ⊆ ⋃ q : bad, U q := by
    intro q hq
    exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hpactive ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover U hU hcover
  refine
    exists_embedding_of_finite_separating_patches_within_target (fun i : s => p i.1) f hf
      (fun i => hpcompatible i.1) hdim hK hinj ?_ (fun i => hpsource i.1) hmaps
  intro x hx y hy hne heq
  have hxy : (x, y) ∈ bad := ⟨hx, hy, hne, heq⟩
  obtain ⟨i, hi, hsep⟩ := Set.mem_iUnion₂.mp (hs hxy)
  exact ⟨⟨i, hi⟩, hsep⟩

/-- The same statement with an ordinary relative homotopy. -/
theorem ManifoldImmersion.exists_compact_embedding_of_immersion {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  obtain ⟨g, hg, hrel, he, hi⟩ :=
    exists_compact_embedding_of_immersion_within_target f hf hdim hK hinj hC hfixed isOpen_univ
      (Set.mapsTo_univ f (K \ C))
  exact ⟨g, hg, hrel.homotopicRel, he, hi⟩


/-- Relative embedding with avoidance: a map already clean on `K ∩ C` outside a neighbourhood `B` is
homotopic rel `C` to a closed embedding and immersion on `K` avoiding `g '' A` outside `B`. -/
theorem ManifoldImmersion.exists_embedded_image_avoidance_relative_neighborhood
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (A : Set Y) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (g '' A)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ g '' A) {O : Set N} (hO : IsOpen O)
    (hmaps : Set.MapsTo f K O) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              Set.MapsTo f' K O ∧ ∀ x ∈ K \ B, f' x ∉ g '' A := by
  let L : Set E := K \ interior C
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hfixed : ∀ x ∈ L ∩ C, f x ∉ g '' A := by
    intro x hx
    exact hclean x ⟨hx.1.1, hx.2⟩ (fun hxB => hx.1.2 (hBC hxB))
  obtain ⟨f', hf', hhom, hemb, hderiv', -, hmaps', havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image f g A hf hg hclosed hself hobstacle hK
      hL hC hinj hderiv hfixed hO hmaps
  refine ⟨f', hf', hhom, hemb, hderiv', hmaps', ?_⟩
  intro x hx
  by_cases hxC : x ∈ C
  · exact havoid x (Or.inl (hclean x ⟨hx.1, hxC⟩ hx.2))
  · exact havoid x (Or.inr ⟨hx.1, fun hi => hxC (interior_subset hi)⟩)

/-- Version of the previous statement with obstacle the closed image of `g`. -/
theorem ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g := by
  obtain ⟨f', hf', hhom, hemb, hd, -, havoid⟩ :=
    exists_embedded_image_avoidance_relative_neighborhood f g Set.univ hf hg
      (by simpa only [Set.image_univ] using hclosed) hself hobstacle hK hC hBC hinj hderiv
      (by simpa only [Set.image_univ] using hclean) isOpen_univ (fun _ _ => Set.mem_univ _)
  refine ⟨f', hf', hhom, hemb, hd, ?_⟩
  simpa only [Set.image_univ] using havoid


/-- Version of the previous statement for a compact source `Y`, where the closedness of the image of
`g` is automatic. -/
theorem ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] [CompactSpace Y]
    (f : C(E, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g :=
  exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hself hobstacle hK hC hBC hinj hderiv hclean

/-- The open preimage `g ⁻¹' U` of an open set under a continuous map. -/
def OpenObstacle.source {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) : TopologicalSpace.Opens Y :=
  ⟨g ⁻¹' (U : Set N), U.isOpen.preimage g.continuous⟩

/-- The restriction of `g` to the open preimage of `U`, as a map into `U`. -/
def OpenObstacle.restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) : C(source g U, U)
    where
  toFun y := ⟨g y, y.property⟩
  continuous_toFun := (g.continuous.comp continuous_subtype_val).subtype_mk _

/-- A point of `U` is in the image of the restriction exactly when it is in the image of `g`. -/
theorem OpenObstacle.mem_range_restrict_iff {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N) (x : U) :
    x ∈ Set.range (OpenObstacle.restrict g U) ↔ (x : N) ∈ Set.range g := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact hy.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, Subtype.ext hy⟩

/-- The image of the restriction is the trace of the image of `g` on `U`. -/
theorem OpenObstacle.range_restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) :
    Set.range (OpenObstacle.restrict g U) = (Subtype.val : U → N) ⁻¹' Set.range g := by
  ext x
  exact mem_range_restrict_iff g U x

/-- The image of the restriction is closed in `U` when the image of `g` is closed. -/
theorem OpenObstacle.isClosed_range_restrict {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N)
    (hclosed : IsClosed (Set.range g)) : IsClosed (Set.range (OpenObstacle.restrict g U)) :=
  by
  rw [OpenObstacle.range_restrict]
  exact hclosed.preimage continuous_subtype_val

/-- The image under the restriction of the trace of `A` is the trace on `U` of `g '' A`. -/
theorem OpenObstacle.image_restrict {Y N : Type*} [TopologicalSpace Y] [TopologicalSpace N]
    (g : C(Y, N)) (U : TopologicalSpace.Opens N) (A : Set Y) :
    OpenObstacle.restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A) =
      (Subtype.val : U → N) ⁻¹' (g '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact ⟨y, hy, congrArg Subtype.val heq⟩
  · rintro ⟨y, hy, heq⟩
    have hyU : y ∈ source g U := by
      change g y ∈ U
      exact heq.symm ▸ x.property
    exact ⟨⟨y, hyU⟩, hy, Subtype.ext heq⟩

/-- The restricted image of `A` is closed in `U` when `g '' A` is closed. -/
theorem OpenObstacle.isClosed_image_restrict {Y N : Type*} [TopologicalSpace Y]
    [TopologicalSpace N] (g : C(Y, N)) (U : TopologicalSpace.Opens N) (A : Set Y)
    (hclosed : IsClosed (g '' A)) :
    IsClosed (OpenObstacle.restrict g U '' ((Subtype.val : source g U → Y) ⁻¹' A)) := by
  rw [OpenObstacle.image_restrict]
  exact hclosed.preimage continuous_subtype_val

/-- The restriction of a smooth map to the open preimage of an open set is smooth. -/
theorem OpenObstacle.contMDiff_restrict {E' G H H' Y N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace H N] (g : C(Y, N))
    (U : TopologicalSpace.Opens N) (hg : ContMDiff I' J ∞ g) :
    ContMDiff I' J ∞ (OpenObstacle.restrict g U) := by
  apply (ContMDiff.subtypeVal_comp_iff U (OpenObstacle.restrict g U)).mp
  exact hg.comp contMDiff_subtype_val
