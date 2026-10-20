/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Immersion.Relative.Embedding
public import Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation

/-!
# Relative immersion and embedding theorems for the plane

`ManifoldImmersion.affinePatch c f β A` applies, inside a chart `c` of the target, the
cutoff-weighted affine perturbation of `Lib.Geometry.Manifold.Immersion.Relative.AffinePerturbation`
to a map `f : Plane → N`. For small parameters the patched map is smooth (jointly in the parameter),
keeps a compact set inside an open set and stays an immersion where `f` was
(`ManifoldImmersion.contMDiffAt_affinePatch_family`,
`ManifoldImmersion.eventually_affinePatch_maps_compact_into_open`,
`ManifoldImmersion.eventually_affinePatch_injective_derivative`). The patch step
`ManifoldImmersion.exists_affine_embedding_patch_with_property` makes the map an immersion on the
plateau of one patch; iterated over a finite family of smoothing patches
(`ManifoldImmersion.exists_finite_patch_immersion`) it gives the relative immersion theorem
`ManifoldImmersion.exists_immersion_on_compact_rel`: when `dim N ≥ 5`, a smooth map `Plane → N`
which is an immersion on a compact set `K` is homotopic rel a closed set `C` disjoint from `L` to an
immersion on `K ∪ L`. With the self-intersection removal of
`Lib.Geometry.Manifold.Immersion.Relative.Embedding` this is the relative embedding theorem for the
plane, `ManifoldImmersion.exists_relative_compact_embedding`, transported to any two-dimensional
source by a linear isomorphism (`ManifoldImmersion.exists_relative_compact_embedding_twoDimensional`)
and combined with the avoidance of a closed image
(`ManifoldImmersion.exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range`).

## References

* Hirsch, *Differential Topology*, Ch. 2 §2 (immersion and embedding theorems), here for a source
  of dimension `2` and a target of dimension at least `5 = 2 · 2 + 1`.
* Whitney, *Differentiable manifolds*, Thm 5.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section


/-- The map obtained from `f` by applying, inside the chart `c`, the cutoff-weighted affine
perturbation with matrix `A`. -/
def ManifoldImmersion.affinePatch {G F H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (f : PlaneImmersion.Plane → N) (β : PlaneImmersion.Plane → ℝ) (A : F × F) :
    PlaneImmersion.Plane → N :=
  ChartMapPerturbation.variablePerturb c f β (PlaneImmersion.displacement β A)

/-- On the plateau of the cutoff, the chart representative of the patched map is the affine
perturbation of the chart representative of `f`. -/
theorem ManifoldImmersion.chart_affinePatch_on_plateau {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : PlaneImmersion.Plane → N}
    {β χ : PlaneImmersion.Plane → ℝ} {A : F × F} (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hχ : ∀ x ∈ tsupport β, χ x = 1)
    (hvalid :
      ∀ x, ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β A x))
    {x : PlaneImmersion.Plane} (hx : β x = 1) :
    c (affinePatch c f β A x) =
      PlaneImmersion.perturb (ChartMapPerturbation.cutoffCoordinates c f χ) A x := by
  have hxs : x ∈ tsupport β := subset_tsupport β (by change β x ≠ 0; rw [hx]; norm_num)
  change
    c (ChartMapPerturbation.perturb c f β (PlaneImmersion.displacement β A x) x) = _
  rw [ChartMapPerturbation.chart_perturb c f β (hvalid x) (hsupport hxs)]
  simp only [ChartMapPerturbation.coordinateFamily, PlaneImmersion.perturb,
    ChartMapPerturbation.cutoffCoordinates, PlaneImmersion.displacement, hx, hχ x hxs,
    one_smul]

/-- The patched map is smooth. -/
theorem ManifoldImmersion.contMDiff_affinePatch {G F H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : PlaneImmersion.Plane → N}
    {β : PlaneImmersion.Plane → ℝ} {A : F × F}
    (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hvalid :
      ∀ x, ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β A x)) :
    ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ (affinePatch c f β A) := by
  have hd :=
    (PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
      (contDiff_const (c := A) |>.prodMk contDiff_id)
  intro x
  exact
    ChartMapPerturbation.contMDiffAt_variablePerturb c hsupport hf.contMDiffAt
      hβ.contMDiff.contMDiffAt hd.contMDiff.contMDiffAt (hvalid x)

/-- Patch step of the relative embedding theorem for the plane: if a property `Q` holds for all
small parameters, some patched map satisfies `Q`, is homotopic to `f` rel the zero set of the
cutoff, is a closed embedding on the compact set `K`, and is an immersion on the plateau. -/
theorem ManifoldImmersion.exists_affine_embedding_patch_with_property {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) [FiniteDimensional ℝ F] [T2Space N]
    (f : C(PlaneImmersion.Plane, N)) (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f)
    {β χ : PlaneImmersion.Plane → ℝ} (hβ : ContDiff ℝ ∞ β) (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport β) (hχsupport : tsupport χ ⊆ f ⁻¹' c.source)
    (hχone : ∀ x ∈ tsupport β, χ x = 1) (hdim : 5 ≤ Module.finrank ℝ F)
    (Q : (PlaneImmersion.Plane → N) → Prop)
    (hQ : ∀ᶠ A : F × F in 𝓝 0, Q (affinePatch c f β A)) {K : Set PlaneImmersion.Plane}
    (hK : IsCompact K) (hKsub : K ⊆ interior {x | β x = 1}) :
    ∃ g : C(PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ g ∧
        Q g ∧
          Nonempty (f.HomotopyRel g {x | β x = 0}) ∧
            Topology.IsClosedEmbedding (fun x : K => g x) ∧
              ∀ x ∈ interior {x | β x = 1},
                Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g x) := by
  have hsupport : tsupport β ⊆ f ⁻¹' c.source := by
    intro x hx
    exact hχsupport (subset_tsupport χ (by change χ x ≠ 0; rw [hχone x hx]; norm_num))
  let k := ChartMapPerturbation.cutoffCoordinates c f χ
  have hk : ContDiff ℝ ∞ k := by
    have hm : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) 𝓘(ℝ, F) ∞ k := fun x =>
      ChartMapPerturbation.contMDiffAt_cutoffCoordinates c hχsupport hf.contMDiffAt
        hχ.contMDiff.contMDiffAt
    exact hm.contDiff
  obtain ⟨ε, hε, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ :=
    PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  have hQmem : {A : F × F | Q (affinePatch c f β A)} ∈ 𝓝 0 := hQ
  obtain ⟨η, hη, hηkeep⟩ := Metric.mem_nhds_iff.mp hQmem
  obtain ⟨A, hA, -, hinj, hderiv⟩ :=
    PlaneImmersion.exists_small_affine_injective_immersion hk hdim (lt_min hδ hη)
  have hbound : ∀ x, ‖PlaneImmersion.displacement β A x‖ < ε :=
    hδbound A (lt_of_lt_of_le hA (min_le_left _ _))
  have hv :
    ∀ x, ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β A x) :=
    fun x => hvalid _ (hbound x)
  have hsmooth := contMDiff_affinePatch c hf hβ hsupport hv
  let g : C(PlaneImmersion.Plane, N) := ⟨affinePatch c f β A, hsmooth.continuous⟩
  have hcoord (x : PlaneImmersion.Plane) (hx : β x = 1) :
    c (g x) = PlaneImmersion.perturb k A x :=
    chart_affinePatch_on_plateau c hsupport hχone hv hx
  have hQg : Q g :=
    hηkeep
      (show A ∈ Metric.ball 0 η by
        simpa only [Metric.mem_ball, dist_zero_right] using
          (lt_of_lt_of_le hA (min_le_right δ η)))
  refine ⟨g, hsmooth, hQg, ?_, ?_, ?_⟩
  · have hd :=
      (PlaneImmersion.contDiff_displacement_family (F := F) hβ).comp
        (contDiff_const (c := A) |>.prodMk contDiff_id)
    exact
      ⟨ChartMapPerturbation.variableHomotopyRel c f.continuous hβ.continuous hsupport
          hd.continuous hvalid hbound (fun _ hx => Or.inl hx)⟩
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    change g x = g y at hxy
    apply Subtype.ext
    apply hinj
    rw [← hcoord x (interior_subset (s := {z | β z = 1}) (hKsub x.property)), ←
      hcoord y (interior_subset (s := {z | β z = 1}) (hKsub y.property)), hxy]
  · intro x hx
    have hβx : β x = 1 := interior_subset (s := {z | β z = 1}) hx
    have hxs : f x ∈ c.source :=
      hsupport (subset_tsupport β (by change β x ≠ 0; rw [hβx]; norm_num))
    have hgs : g x ∈ c.source := ChartMapPerturbation.perturb_mem_source c f β (hv x) hxs
    apply (injective_fderiv_chart_iff c (hsmooth.mdifferentiableAt (by simp)) hgs).mp
    have heq : (c ∘ g) =ᶠ[𝓝 x] PlaneImmersion.perturb k A := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact hcoord y (interior_subset (s := {z | β z = 1}) hy)
    change Function.Injective (fderiv ℝ (c ∘ g) x)
    rw [heq.fderiv_eq]
    exact hderiv x

/-- The zero parameter leaves the map unchanged. -/
theorem ManifoldImmersion.affinePatch_zero {G F H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (f : PlaneImmersion.Plane → N)
    (β : PlaneImmersion.Plane → ℝ) : affinePatch c f β (0 : F × F) = f := by
  funext x
  change
    ChartMapPerturbation.perturb c f β (PlaneImmersion.displacement β 0 x) x = f x
  rw [PlaneImmersion.displacement_zero, ChartMapPerturbation.perturb_zero]

/-- The patched map is smooth jointly in the parameter and the point. -/
theorem ManifoldImmersion.contMDiffAt_affinePatch_family {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : PlaneImmersion.Plane → N}
    {β : PlaneImmersion.Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (q : (F × F) × PlaneImmersion.Plane)
    (hvalid :
      ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β q.1 q.2)) :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, PlaneImmersion.Plane)) J ∞
      (fun r : (F × F) × PlaneImmersion.Plane => affinePatch c f β r.1 r.2) q := by
  have hid :
    ContMDiffAt (𝓘(ℝ, F × F).prod 𝓘(ℝ, PlaneImmersion.Plane))
      𝓘(ℝ, (F × F) × PlaneImmersion.Plane) ∞
      (fun r : (F × F) × PlaneImmersion.Plane => r) q :=
    (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_fst, contMDiffAt_snd⟩
  have hd :=
    (PlaneImmersion.contDiff_displacement_family (F := F) hβ).contMDiff.contMDiffAt |>.comp
      q hid
  exact
    (ChartMapPerturbation.contMDiffAt_perturb c hf hβ.contMDiff hsupport
          (PlaneImmersion.displacement β q.1 q.2, q.2) hvalid).comp
      q (f := fun r : (F × F) × PlaneImmersion.Plane =>
      (PlaneImmersion.displacement β r.1 r.2, r.2)) (hd.prodMk contMDiffAt_snd)

/-- Small parameters keep a compact set inside a prescribed open target. -/
theorem ManifoldImmersion.eventually_affinePatch_maps_compact_into_open {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : PlaneImmersion.Plane → N}
    {β : PlaneImmersion.Plane → ℝ} (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f)
    (hβ : ContDiff ℝ ∞ β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set PlaneImmersion.Plane} (hK : IsCompact K) {U : Set N} (hU : IsOpen U)
    (hmap : Set.MapsTo f K U) : ∀ᶠ A : F × F in 𝓝 0, Set.MapsTo (affinePatch c f β A) K U := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hvalid :
    ChartMapPerturbation.Valid c f β (PlaneImmersion.displacement β (0 : F × F) x) := by
    rw [PlaneImmersion.displacement_zero]
    exact ChartMapPerturbation.valid_zero c f β hsupport
  have hc := (contMDiffAt_affinePatch_family c hf hβ hsupport (0, x) hvalid).continuousAt
  apply hc.preimage_mem_nhds
  apply hU.mem_nhds
  rw [affinePatch_zero]
  exact hmap hx

/-- Small parameters preserve the immersion property on a compact set. -/
theorem ManifoldImmersion.eventually_affinePatch_injective_derivative {G F H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) [J.Boundaryless] [IsManifold J ∞ N]
    {f : PlaneImmersion.Plane → N} {β : PlaneImmersion.Plane → ℝ}
    (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    {K : Set PlaneImmersion.Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J f x)) :
    ∀ᶠ A : F × F in 𝓝 0,
      ∀ x ∈ K,
        Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J (affinePatch c f β A) x) :=
  by
  obtain ⟨ε, hε, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid c hf hβ.contMDiff hcompact hsupport
  obtain ⟨δ, hδ, hδbound⟩ :=
    PlaneImmersion.exists_radius_displacement_lt (F := F) hβ hcompact hε
  let W : Set ((F × F) × PlaneImmersion.Plane) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily :
    ContMDiffOn (𝓘(ℝ, F × F).prod 𝓘(ℝ, PlaneImmersion.Plane)) J ∞
      (fun q : (F × F) × PlaneImmersion.Plane => affinePatch c f β q.1 q.2) W := by
    intro q hq
    exact
      (contMDiffAt_affinePatch_family c hf hβ hsupport q
          (hvalid _ (hδbound q.1 hq q.2))).contMDiffWithinAt
  apply eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F × F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    change
      Function.Injective
        (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J (affinePatch c f β (0 : F × F)) x)
    rw [affinePatch_zero]
    exact hinj x hx

/-- One step of the immersion existence induction: a perturbation supported in a single patch makes
the map an immersion on the plateau of that patch while keeping it an immersion where it already
was. -/
theorem ManifoldImmersion.exists_immersion_patch_step {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    {ι : Type*} [Finite ι]
    (p :
      ι →
        ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, PlaneImmersion.Plane) J (X :=
          PlaneImmersion.Plane) (N := N))
    (i : ι) (f : C(PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set PlaneImmersion.Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J f x))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ x ∈ C, (p i).cutoff x = 0) :
    ∃ g : C(PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          f.HomotopicRel g C ∧
            Topology.IsClosedEmbedding (fun x : L => g x) ∧
              ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g x) := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep :
    ∀ᶠ A : G × G in 𝓝 0, ∀ j, (p j).Compatible (affinePatch (p i).chart f (p i).cutoff A) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      eventually_affinePatch_maps_compact_into_open (p i).chart hf (p i).smooth.contDiff hinner
        (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    eventually_affinePatch_injective_derivative (p i).chart hf (p i).smooth.contDiff (p i).compact
      hinner hK hinj
  let Q : (PlaneImmersion.Plane → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g x)
  have hQ : ∀ᶠ A : G × G in 𝓝 0, Q (affinePatch (p i).chart f (p i).cutoff A) := hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, ⟨Hrel⟩, hemb, hplateau⟩ :=
    exists_affine_embedding_patch_with_property (p i).chart f hf (p i).smooth.contDiff
      (p i).outer_smooth.contDiff (p i).compact (hcompatible i) (p i).nested hdim Q hQ hL hLsub
  refine ⟨g, hg, hc, ?_, hemb, ?_⟩
  · exact ⟨{ Hrel.toHomotopy with prop' := fun t x hx => Hrel.eq_fst t (hfixed x hx) }⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hKnew x hx
    · exact hplateau x (hLsub hx)

/-- Iterating the patch step over a finite family of patches gives a map that is an immersion on the
union of the chosen plateaus. -/
theorem ManifoldImmersion.exists_finite_patch_immersion {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {ι : Type*} [Finite ι]
    (p :
      ι →
        ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, PlaneImmersion.Plane) J (X :=
          PlaneImmersion.Plane) (N := N))
    (L : ι → Set PlaneImmersion.Plane) (hL : ∀ i, IsCompact (L i))
    (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set PlaneImmersion.Plane} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J f x))
    (hfixed : ∀ i x, x ∈ C → (p i).cutoff x = 0) (s : Finset ι) :
    ∃ g : C(PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          f.HomotopicRel g C ∧
            ∀ x ∈ K ∪ ⋃ i ∈ s, L i,
              Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g x) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, -, hinj₂⟩ :=
      exists_immersion_patch_step p i g₁ hg₁ hc₁ hdim hKold (hL i) hinj₁ (hLsub i) (hfixed i)
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hinj₂ x
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hxj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, hxj⟩))


/-- Relative immersion theorem for the plane: when `dim N ≥ 5`, a smooth map `Plane → N` which is
already an immersion on a compact set `K` is homotopic rel a closed set `C` disjoint from `L` to
a map that is an immersion on `K ∪ L` (Hirsch, *Differential Topology*, Ch. 2 §2, Ch. 3 §2). -/
theorem ManifoldImmersion.exists_immersion_on_compact_rel {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set PlaneImmersion.Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J f x))
    (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ g ∧
        f.HomotopicRel g C ∧
          ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g x) := by
  classical
  have hp (x : L) :=
    exists_relative_immersion_patch_at (J := J) f hC
      (show (x : PlaneImmersion.Plane) ∉ C from fun hx =>
        Set.disjoint_left.mp hdis x.property hx)
  choose p T hcompatible hT hn hsub hfixed using hp
  have hcover : L ⊆ ⋃ x : L, interior (T x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ :=
    hL.elim_finite_subcover (fun x : L => interior (T x)) (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ :=
    exists_finite_patch_immersion (fun i : s => p i.1) (fun i : s => T i.1) (fun i => hT i.1)
      (fun i => hsub i.1) f hf (fun i => hcompatible i.1) hdim hK hinj (fun i => hfixed i.1)
      Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro x hx
  apply hderiv x
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hxi⟩)


/-- Relative embedding theorem for the plane: when `dim N ≥ 5`, a smooth map `Plane → N` that is an
injective immersion on `K ∩ C` is homotopic rel the closed set `C` to a map which is a closed
embedding and an immersion on the compact set `K` (Hirsch, *Differential Topology*, Ch. 2 §2,
Ch. 3 §2; Whitney, *Differentiable manifolds*, Thm 5). -/
theorem ManifoldImmersion.exists_relative_compact_embedding {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] (f : C(PlaneImmersion.Plane, N))
    (hf : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K C : Set PlaneImmersion.Plane} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J f x)) :
    ∃ g : C(PlaneImmersion.Plane, N),
      ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g x) := by
  let U : Set PlaneImmersion.Plane :=
    {x | Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J f x)}
  have hU : IsOpen U := isOpen_injective_derivative hf
  have hCU : K ∩ C ⊆ U := fun x hx => hderiv x hx
  obtain ⟨D, hD, hCD, hDU⟩ := exists_compact_between (hK.inter_right hC) hU hCU
  let L := K \ interior D
  have hL : IsCompact L := hK.inter_right isOpen_interior.isClosed_compl
  have hdis : Disjoint L C := Set.disjoint_left.mpr (fun _ hx hxC => hx.2 (hCD ⟨hx.1, hxC⟩))
  obtain ⟨g₁, hg₁, hhom₁, hinj₁⟩ :=
    exists_immersion_on_compact_rel f hf hdim hD hL (fun x hx => hDU hx) hC hdis
  have hKinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J g₁ x) := by
    intro x hx
    apply hinj₁ x
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr ⟨hx, fun hi => hxD (interior_subset hi)⟩
  have hfixed₁ : Set.InjOn g₁ (K ∩ C) := by
    intro x hx y hy hxy
    apply hfixed hx hy
    rw [hhom₁.fst_eq_snd hx.2, hhom₁.fst_eq_snd hy.2]
    exact hxy
  have hd : 2 * Module.finrank ℝ PlaneImmersion.Plane < Module.finrank ℝ G := by
    simp only [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
    omega
  obtain ⟨g₂, hg₂, hhom₂, hemb, hinj₂⟩ :=
    exists_compact_embedding_of_immersion g₁ hg₁ hd hK hKinj hC hfixed₁
  exact ⟨g₂, hg₂, hhom₁.trans hhom₂, hemb, hinj₂⟩


/-- The relative embedding theorem for any two-dimensional source, obtained from the plane case by a
linear isomorphism `E ≃L[ℝ] Plane`. -/
theorem ManifoldImmersion.exists_relative_compact_embedding_twoDimensional {E G H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N]
    [T2Space N] (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  let e : PlaneImmersion.Plane ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
        omega)
  let fp : C(PlaneImmersion.Plane, N) := ⟨f ∘ e, f.continuous.comp e.continuous⟩
  have hfp : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ fp := hf.comp e.contDiff.contMDiff
  have hKp : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hCp : IsClosed (e ⁻¹' C) := hC.preimage e.continuous
  have hfixedp : Set.InjOn fp ((e ⁻¹' K) ∩ (e ⁻¹' C)) := by
    intro x hx y hy hxy
    exact e.injective (hfixed ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxy)
  have hderivp :
    ∀ x ∈ (e ⁻¹' K) ∩ (e ⁻¹' C),
      Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J fp x) := by
    intro x hx
    exact
      (injective_mfderiv_comp_linearEquiv_iff e (hf.mdifferentiableAt (by simp))).mpr
        (hderiv (e x) ⟨hx.1, hx.2⟩)
  obtain ⟨gp, hgp, ⟨Hrel⟩, hembp, hgpderiv⟩ :=
    exists_relative_compact_embedding fp hfp hdim hKp hCp hfixedp hderivp
  let g : C(E, N) := ⟨gp ∘ e.symm, gp.continuous.comp e.symm.continuous⟩
  have hg : ContMDiff 𝓘(ℝ, E) J ∞ g := hgp.comp e.symm.contDiff.contMDiff
  have hpreK (x : E) (hx : x ∈ K) : e.symm x ∈ e ⁻¹' K := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · refine
      ⟨{  toFun := fun q => Hrel (q.1, e.symm q.2)
          continuous_toFun :=
            Hrel.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩
    · intro x
      rw [Hrel.apply_zero]
      exact congrArg f (e.apply_symm_apply x)
    · intro x
      exact Hrel.apply_one (e.symm x)
    · intro t x hx
      change Hrel (t, e.symm x) = f x
      have hpreC : e.symm x ∈ e ⁻¹' C := by
        change e (e.symm x) ∈ C
        simpa only [e.apply_symm_apply] using hx
      rw [Hrel.eq_fst t hpreC]
      exact congrArg f (e.apply_symm_apply x)
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    have hpeq : gp (e.symm x) = gp (e.symm y) := hxy
    exact
      congrArg Subtype.val
        (hembp.injective (a₁ := ⟨e.symm x, hpreK x x.property⟩) (a₂ :=
          ⟨e.symm y, hpreK y y.property⟩) hpeq)
  · intro x hx
    exact
      (injective_mfderiv_comp_linearEquiv_iff e.symm (hgp.mdifferentiableAt (by simp))).mpr
        (hgpderiv (e.symm x) (hpreK x hx))


/-- Relative embedding with avoidance for a two-dimensional source: when `dim E = 2`, `dim N ≥ 5` and
`dim E + dim Y < dim N`, a smooth map `f : E → N` which is an injective immersion on `K ∩ C` and
whose image on `K ∩ C` lies off the closed image of `g : Y → N` except on `B ⊆ interior C` is
homotopic rel `C` to a map which is a closed embedding and an immersion on the compact set `K` and
avoids the image of `g` on `K \ B`. -/
theorem
  ManifoldImmersion.exists_relative_embedded_avoidance_of_clean_neighborhood_of_isClosed_range
    {E E' G H H' Y N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] (f : C(E, N))
    (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (Set.range g)) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {K C B : Set E}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C) (hinj : Set.InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (hclean : ∀ x ∈ K ∩ C, x ∉ B → f x ∉ Set.range g) :
    ∃ f' : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ f' ∧
        f.HomotopicRel f' C ∧
          Topology.IsClosedEmbedding (fun x : K => f' x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
              ∀ x ∈ K \ B, f' x ∉ Set.range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_embedding_twoDimensional f hf hsourceDim hdim hK hC hinj hderiv
  have hinj₁ : Set.InjOn f₁ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hclean₁ : ∀ x ∈ K ∩ C, x ∉ B → f₁ x ∉ Set.range g := by
    intro x hx hxB
    rw [← hhom₁.fst_eq_snd hx.2]
    exact hclean x hx hxB
  have hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G := by omega
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid₂⟩ :=
    exists_embedded_avoidance_relative_neighborhood_of_isClosed_range f₁ g hf₁ hg hclosed hself
      hobstacle hK hC hBC hinj₁ hderiv₁ hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid₂⟩
