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
/-!
# Morse surgery windows: chart primitives and the surgery data structures

The chart-level primitives of the Morse surgery theory and the data structures
for a surgery. A `ManifoldMorse.MorseSurgeryData` records the two critical
points to cancel, the separating and attaching levels, the chart in which the
cancellation is performed, and the compact support of the modifying field. A
`ManifoldMorse.SurgeryWindows` is the finitely many windows, pairwise
disjoint in level, together with the `AdaptedWindows` on which the cancellation
acts (Milnor, *Lectures on the h-cobordism theorem*, §3-4; Milnor, *Morse
Theory* §3).

## Outline

1. Coordinate primitives: hemispheres, doubled disks, surgery boundary pairs,
   sphere coordinates, image complements, open homotopy extensions and the
   punctured handle.
2. The `NoExotic` dimension cluster: Hausdorff-dimension bounds for images of
   charts, non-surjectivity in low dimension, and the zero-avoidance cutoffs.
3. The surgery window structures `MorseSurgeryData`, `SurgeryWindows` and
   `AdaptedWindows` with their small-perturbation stability.

The cancellation toolbox moved to `Morse/Cancellation.lean`, the
transversality basics to `Transversality/Basic.lean`, the immersion chain to
`Immersion/Relative.lean`, and the rearrangement block to
`Morse/Rearrangement.lean`.

## Main definitions and results

* `ManifoldMorse.MorseSurgeryData` - the data of one surgery.
* `ManifoldMorse.SurgeryWindows` - finitely many level-disjoint windows.
* `AdaptedWindows` - the windows adapted to a given cancellation.

## References

* [milnor65] J. Milnor, *Lectures on the h-cobordism theorem*, §3-4.
* [milnor63] J. Milnor, *Morse Theory*, §3.

## Tags

morse-theory, surgery, h-cobordism, handle-decomposition
-/



open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-! ### Hausdorff dimension of smooth images -/

/-- A chart image has Hausdorff dimension at most the domain's. -/
theorem GeneralPosition.dimH_image_chart_le {E F H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] {f : X → F} {s : Set X} (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (x : X) : dimH (f '' ((extChartAt I x).source ∩ s)) ≤ Module.finrank ℝ E := by
  let c := extChartAt I x
  let V : Set E := c.target ∩ c.symm ⁻¹' s
  have hfc : ContDiffOn ℝ ∞ (f ∘ c.symm) V :=
    (hf.comp ((contMDiffOn_extChartAt_symm x).mono Set.inter_subset_left)
        Set.inter_subset_right).contDiffOn
  have hVsub : V ⊆ Set.range I := fun y hy => extChartAt_target_subset_range x hy.1
  have hdim : dimH ((f ∘ c.symm) '' V) ≤ dimH V := by
    apply dimH_image_le_of_locally_lipschitzOn
    intro y hy
    have ht : c.target ∈ 𝓝[Set.range I] y := extChartAt_target_mem_nhdsWithin_of_mem hy.1
    have hp : c.symm ⁻¹' s ∈ 𝓝[Set.range I] y := by
      rw [← nhdsWithin_extChartAt_target_eq_of_mem hy.1]
      exact
        (contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) x).continuousOn y
            hy.1 |>.preimage_mem_nhdsWithin
          (hs.mem_nhds hy.2)
    have hV : V ∈ 𝓝[Set.range I] y := Filter.inter_mem ht hp
    have hd : ContDiffWithinAt ℝ 1 (f ∘ c.symm) (Set.range I) y :=
      ((hfc y hy).of_le (by simp)).mono_of_mem_nhdsWithin hV
    obtain ⟨L, U, hU, hLip⟩ := hd.exists_lipschitzOnWith I.convex_range
    exact ⟨L, U, nhdsWithin_mono y hVsub hU, hLip⟩
  have himage : f '' (c.source ∩ s) = (f ∘ c.symm) '' V := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      refine ⟨c y, ⟨c.map_source hyc, ?_⟩, ?_⟩
      · change c.symm (c y) ∈ s
        rwa [c.left_inv hyc]
      · exact congrArg f (c.left_inv hyc)
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      exact ⟨c.symm y, ⟨c.map_target hyc, hys⟩, rfl⟩
  change dimH (f '' (c.source ∩ s)) ≤ _
  rw [himage]
  exact hdim.trans ((dimH_mono (Set.subset_univ V)).trans_eq (Real.dimH_univ_eq_finrank E))

/-- A smooth image of a manifold has Hausdorff dimension at most the domain's. -/
theorem GeneralPosition.dimH_image_manifold_le {E F H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [LindelofSpace X] {f : X → F} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) : dimH (f '' s) ≤ Module.finrank ℝ E := by
  let U : X → Set X := fun x => (extChartAt I x).source
  have hU : ∀ x, IsOpen (U x) := fun x => isOpen_extChartAt_source x
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have himage : f '' s ⊆ ⋃ x ∈ t, f '' (U x ∩ s) := by
    rintro z ⟨y, hys, rfl⟩
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Set.mem_iUnion₂.mpr ⟨x, hxt, y, ⟨hyx, hys⟩, rfl⟩
  apply (dimH_mono himage).trans
  rw [dimH_bUnion htcount]
  exact iSup_le (fun x => iSup_le (fun _ => dimH_image_chart_le hs hf x))

/-- The complement of a lower-dimensional smooth image is dense. -/
theorem GeneralPosition.dense_compl_manifold_image {E F H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [LindelofSpace X] [FiniteDimensional ℝ F] {f : X → F} {s : Set X}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank ((dimH_image_manifold_le hs hf).trans_lt (Nat.cast_lt.mpr hd))

/-- A localized small parameter makes the image avoid a lower-dimensional set. -/
theorem exists_small_localized_image_avoidance {E E' F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold J ∞ Y] [LindelofSpace (X × Y)] {f : X → F} {g : Y → F} {β : X → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hg : ContMDiff J 𝓘(ℝ, F) ∞ g) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ ∀ x, β x ≠ 0 → ∀ y, f x + β x • a ≠ g y := by
  let s : Set (X × Y) := {p | β p.1 ≠ 0}
  let bad : X × Y → F := fun p => (β p.1)⁻¹ • (g p.2 - f p.1)
  have hs : IsOpen s := isOpen_ne_fun (hβ.continuous.comp continuous_fst) continuous_const
  have hb : ContMDiffOn (I.prod J) 𝓘(ℝ, F) ∞ bad s :=
    ((hβ.comp contMDiff_fst).contMDiffOn.inv₀ (fun _ hp => hp)).smul
      ((hg.comp contMDiff_snd).sub (hf.comp contMDiff_fst)).contMDiffOn
  have hd : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image hs hb hd
  obtain ⟨a, ha, haε⟩ := hdense.exists_dist_lt 0 hε
  refine ⟨a, ?_, ?_⟩
  · simpa only [dist_zero_left] using haε
  · intro x hx y hxy
    apply ha
    refine ⟨(x, y), hx, ?_⟩
    change (β x)⁻¹ • (g y - f x) = a
    rw [← hxy, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- A small chart-map parameter avoids the target set. -/
theorem ChartMapPerturbation.exists_small_avoiding_parameter {E E' G F H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N] [LindelofSpace (X × Y)]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {β : X → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        Valid c f β a ∧
          ContMDiff I J ∞ (perturb c f β a) ∧ ∀ x, β x ≠ 0 → ∀ y, perturb c f β a x ≠ g y := by
  let s : Set (X × Y) := {p | f p.1 ∈ c.source ∧ g p.2 ∈ c.source ∧ β p.1 ≠ 0}
  let bad : X × Y → F := fun p => (β p.1)⁻¹ • (c (g p.2) - c (f p.1))
  have hs : IsOpen s :=
    (c.open_source.preimage (hf.continuous.comp continuous_fst)).inter
      ((c.open_source.preimage (hg.continuous.comp continuous_snd)).inter
        (isOpen_ne_fun (hβ.continuous.comp continuous_fst) continuous_const))
  have hb : ContMDiffOn (I.prod I') 𝓘(ℝ, F) ∞ bad s := by
    intro p hp
    have hcf : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun q : X × Y => c (f q.1)) p :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hp.1)).comp p
        (hf.comp contMDiff_fst).contMDiffAt
    have hcg : ContMDiffAt (I.prod I') 𝓘(ℝ, F) ∞ (fun q : X × Y => c (g q.2)) p :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hp.2.1)).comp p
        (hg.comp contMDiff_snd).contMDiffAt
    exact (((hβ.comp contMDiff_fst).contMDiffAt.inv₀ hp.2.2).smul (hcg.sub hcf)).contMDiffWithinAt
  have hd : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image hs hb hd
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  obtain ⟨a, ha, har⟩ := hdense.exists_dist_lt 0 (lt_min hε hδ)
  have haε : ‖a‖ < ε :=
    (lt_min_iff.mp (show ‖a‖ < Min.min ε δ by simpa only [dist_zero_left] using har)).1
  have haδ : ‖a‖ < δ :=
    (lt_min_iff.mp (show ‖a‖ < Min.min ε δ by simpa only [dist_zero_left] using har)).2
  have hva : Valid c f β a := hvalid a haδ
  refine ⟨a, haε, hva, contMDiff_perturb c hf hβ hsupport hva, ?_⟩
  intro x hx y hxy
  have hfx : f x ∈ c.source := hsupport (subset_tsupport β hx)
  have hgy : g y ∈ c.source := hxy ▸ perturb_mem_source c f β hva hfx
  have heq : c (f x) + β x • a = c (g y) := by
    rw [← hxy, chart_perturb c f β hva hfx]
    rfl
  apply ha
  refine ⟨(x, y), ⟨hfx, hgy, hx⟩, ?_⟩
  change (β x)⁻¹ • (c (g y) - c (f x)) = a
  rw [← heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-! ### Avoidance patches -/

/-- A chart patch in which a map can be perturbed to avoid a set on a compact core. -/
structure GeneralPosition.MapAvoidancePatch {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (C : Set X) where
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : X → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  compact : HasCompactSupport cutoff
  fixed : ∀ x ∈ C, cutoff x = 0

/-- A patch is compatible with a map when the chart covers the image of the core. -/
def GeneralPosition.MapAvoidancePatch.Compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] {C : Set X} (p : GeneralPosition.MapAvoidancePatch I J (N := N) C)
    (f : X → N) : Prop :=
  Set.MapsTo f (tsupport p.cutoff) p.chart.source

/-- One avoidance step inside a patch. -/
theorem GeneralPosition.exists_patch_step {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    {E' H' Y : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y]
    [IsManifold I' ∞ Y] [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (i : ι) (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          f.HomotopicRel f' C ∧
            ∀ x, (f x ∉ Set.range g ∨ (p i).cutoff x ≠ 0) → f' x ∉ Set.range g := by
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf (p i).smooth
        (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ :=
    ChartMapPerturbation.exists_radius_valid (p i).chart hf (p i).smooth (p i).compact
      (hcompatible i)
  obtain ⟨a, ha, _, hsmooth, havoid⟩ :=
    ChartMapPerturbation.exists_small_avoiding_parameter (p i).chart hf hg (p i).smooth
      (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(X, N) := ⟨_, hsmooth.continuous⟩
  have H :=
    ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth (hcompatible i) hvalid har
  refine ⟨f', hsmooth, ?_, ?_, ?_⟩
  · exact hδkeep (by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  · exact
      ⟨{  toHomotopy := H.toHomotopy
          prop' := fun t x hx => H.prop t x ((p i).fixed x hx) }⟩
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ Set.range g := hx.resolve_right (Classical.not_not.mpr hzero)
      change ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ Set.range g
      rwa [ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, hy⟩
      exact havoid x hzero y hy.symm

/-- Finitely many patches give a global small avoidance perturbation. -/
theorem GeneralPosition.exists_finite_patch_avoidance {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) (s : Finset ι) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧
        (∀ j, (p j).Compatible f') ∧
          f.HomotopicRel f' C ∧
            ∀ x, (f x ∉ Set.range g ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ Set.range g := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, havoid₂⟩ := exists_patch_step p i f₁ g hf₁ hg hc₁ hdim
    refine ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hnonzero⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hnonzero
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hnonzero⟩))

/-- A finite patch cover yields a map avoiding the target. -/
theorem GeneralPosition.exists_avoidance_of_finite_patches {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N] [ChartedSpace K N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hcover : ∀ x, f x ∈ Set.range g → ∃ i, (p i).cutoff x ≠ 0) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ Disjoint (Set.range f') (Set.range g) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', hf', _, hhom, havoid⟩ :=
    exists_finite_patch_avoidance p f g hf hg hcompatible hdim Finset.univ
  refine ⟨f', hf', hhom, Set.disjoint_left.mpr ?_⟩
  rintro z ⟨x, rfl⟩ hz
  apply havoid x _ hz
  by_cases hx : f x ∈ Set.range g
  · obtain ⟨i, hi⟩ := hcover x hx
    exact Or.inr ⟨i, Finset.mem_univ i, hi⟩
  · exact Or.inl hx

/-- Every point admits an avoidance patch around it. -/
theorem GeneralPosition.exists_avoidance_patch_at {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (f : C(X, N)) {C : Set X} (hC : IsClosed C) {x : X} (hx : x ∉ C) :
    ∃ p : MapAvoidancePatch I J (N := N) C, p.Compatible f ∧ p.cutoff x ≠ 0 := by
  classical
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  have hsource : f x ∈ c.source := mem_extChartAt_source (I := J) (f x)
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  let p : MapAvoidancePatch I J (N := N) C :=
    { chart := c
      cutoff := φ
      smooth := φ.contMDiff
      compact := φ.hasCompactSupport
      fixed := by
        intro y hy
        exact image_eq_zero_of_notMem_tsupport (fun ht => (hφ ht).2 hy) }
  refine ⟨p, ?_, ?_⟩
  · exact fun y hy => (hφ hy).1
  · change φ x ≠ 0
    rw [φ.eq_one]
    exact one_ne_zero

/-- A smooth map can be perturbed rel a closed range to be disjoint from a lower-dimensional set. -/
theorem GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range
    {E G H K X N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] {E' H' Y : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace X] [LindelofSpace (X × Y)] (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff I' J ∞ g) (hclosed : IsClosed (Set.range g))
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {C : Set X}
    (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ Set.range g) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ Disjoint (Set.range f') (Set.range g) := by
  classical
  let bad : Set X := f ⁻¹' Set.range g
  have hbad : IsCompact bad := (hclosed.preimage f.continuous).isCompact
  have hp (x : bad) : ∃ p : MapAvoidancePatch I J (N := N) C, p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    exists_avoidance_patch_at f hC (fun hx => hfixed x.1 hx x.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ :=
    hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff) hopen hcover
  apply
    exists_avoidance_of_finite_patches (fun i : s => p i.1) f g hf hg (fun i => hpcompatible i.1)
      hdim
  intro x hx
  obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact ⟨⟨i, hi⟩, hix⟩

/-- A smooth map can be perturbed rel a closed set to be disjoint from a lower-dimensional set. -/
theorem GeneralPosition.exists_disjoint_smooth_map_homotopicRel {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] {E' H' Y : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace X] [CompactSpace Y] [T2Space N] (f : C(X, N)) (g : C(Y, N))
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) {C : Set X}
    (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ Set.range g) :
    ∃ f' : C(X, N),
      ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ Disjoint (Set.range f') (Set.range g) :=
  exists_disjoint_smooth_map_homotopicRel_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hdim hC hfixed

/-! ### Maps into the image complement -/

/-- The open complement of a compact image. -/
def ImageComplement.domain {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace N] [T2Space N] (g : C(Y, N)) : TopologicalSpace.Opens N :=
  ⟨(Set.range g)ᶜ, (isCompact_range g.continuous).isClosed.isOpen_compl⟩

/-- The inclusion of the image complement. -/
def ImageComplement.inclusion {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace N] [T2Space N] (g : C(Y, N)) : C(domain g, N) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- An ambient homotopy off the image gives a smooth homotopy in the complement. -/
theorem ImageComplement.exists_smooth_homotopy_of_ambient_homotopic {Y N : Type*}
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace N] [T2Space N]
    {E E' G H H' K X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [CompactSpace X] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [ChartedSpace K N] [IsManifold J ∞ N] (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g)) (hf₀ : ContMDiff I J ∞ f₀) (hf₁ : ContMDiff I J ∞ f₁)
    (hambient :
      ((ImageComplement.inclusion g).comp f₀).Homotopic
        ((ImageComplement.inclusion g).comp f₁)) :
    ∃ H : f₀.Homotopy f₁,
      ContMDiff ((𝓡∂ 1).prod I) J ∞ H ∧
        (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f₀ x) ∧
          (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = f₁ x) := by
  obtain ⟨H⟩ := hambient
  have hval : ContMDiff J J ∞ (ImageComplement.inclusion g) := contMDiff_subtype_val
  have hf₀val : ContMDiff I J ∞ ((ImageComplement.inclusion g).comp f₀) := hval.comp hf₀
  have hf₁val : ContMDiff I J ∞ ((ImageComplement.inclusion g).comp f₁) := hval.comp hf₁
  obtain ⟨H, hH, hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hf₀val hf₁val H
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × E) + Module.finrank ℝ E' < Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ q ∈ ManifoldSmoothing.homotopyCollars X, H q ∉ Set.range g := by
    rintro ⟨t, x⟩ (ht | ht)
    · rw [hlo t x ht]
      exact (f₀ x).property
    · rw [hhi t x ht]
      exact (f₁ x).property
  obtain ⟨F, hF, hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel H.toContinuousMap g hH hg hd
      ManifoldSmoothing.isClosed_homotopyCollars hfixed
  have heq : Set.EqOn F H (ManifoldSmoothing.homotopyCollars X) := fun _ hq =>
    (hrel.fst_eq_snd hq).symm
  have havoid : ∀ q, F q ∈ domain g := by
    intro q
    change F q ∉ Set.range g
    exact fun hq => Set.disjoint_left.mp hdisjoint ⟨q, rfl⟩ hq
  let A : C(unitInterval × X, domain g) := ⟨fun q => ⟨F q, havoid q⟩, F.continuous.subtype_mk _⟩
  have hA : ContMDiff ((𝓡∂ 1).prod I) J ∞ A := (ContMDiff.subtypeVal_comp_iff (domain g) A).mp hF
  have hAlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : A (t, x) = f₀ x := by
    apply Subtype.ext
    exact
      (heq (show (t, x) ∈ ManifoldSmoothing.homotopyCollars X from Or.inl ht)).trans
        (hlo t x ht)
  have hAhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : A (t, x) = f₁ x := by
    apply Subtype.ext
    exact
      (heq (show (t, x) ∈ ManifoldSmoothing.homotopyCollars X from Or.inr ht)).trans
        (hhi t x ht)
  exact
    ⟨{  toContinuousMap := A
        map_zero_left := fun x => hAlo 0 x (by norm_num)
        map_one_left := fun x => hAhi 1 x (by norm_num) }, hA, hAlo, hAhi⟩

/-- Maps ambiently homotopic off the image are homotopic in the complement. -/
theorem ImageComplement.homotopic_of_ambient_homotopic {Y N : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace N] [T2Space N] {E E' G H H' K X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [ChartedSpace K N] [IsManifold J ∞ N]
    (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g))
    (hambient :
      ((ImageComplement.inclusion g).comp f₀).Homotopic
        ((ImageComplement.inclusion g).comp f₁)) :
    f₀.Homotopic f₁ := by
  obtain ⟨f₀', hf₀', h₀⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₀
  obtain ⟨f₁', hf₁', h₁⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₁
  have ha₀ := (ContinuousMap.Homotopic.refl (ImageComplement.inclusion g)).comp h₀
  have ha₁ := (ContinuousMap.Homotopic.refl (ImageComplement.inclusion g)).comp h₁
  obtain ⟨H, -⟩ :=
    exists_smooth_homotopy_of_ambient_homotopic g hg hdim f₀' f₁' hf₀' hf₁'
      (ha₀.symm.trans (hambient.trans ha₁))
  exact h₀.trans ((show f₀'.Homotopic f₁' from ⟨H⟩).trans h₁.symm)

/-! ### The disk double -/

/-- The closed unit disk. -/
abbrev DiskDouble.Disk (E : Type*) [NormedAddCommGroup E] :=
  Metric.closedBall (0 : E) 1

/-- The boundary sphere of the disk. -/
abbrev DiskDouble.Boundary (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) 1

/-- A boundary point included into the disk. -/
def DiskDouble.boundary (E : Type*) [NormedAddCommGroup E] (x : Boundary E) : Disk E :=
  ⟨x, Metric.sphere_subset_closedBall x.property⟩

/-- The relation gluing two disks along a boundary homeomorphism. -/
def DiskDouble.Rel {E : Type*} [NormedAddCommGroup E] (e : Boundary E ≃ₜ Boundary E) :
    Disk E ⊕ Disk E → Disk E ⊕ Disk E → Prop
  | .inl x, .inr y => ∃ z : Boundary E, x = boundary E z ∧ y = boundary E (e z)
  | _, _ => False

/-- The double of a disk along a boundary homeomorphism. -/
abbrev DiskDouble.Space {E : Type*} [NormedAddCommGroup E] (e : Boundary E ≃ₜ Boundary E) :=
  Quot (DiskDouble.Rel e)

/-- The twist moved onto the second disk. -/
def DiskDouble.untwist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) : Disk E ⊕ Disk E ≃ₜ Disk E ⊕ Disk E :=
  (Homeomorph.refl (Disk E)).sumCongr (RadialExtension.closedBallHomeomorph e.symm)

/-- The twisted relation is the untwisted identity relation. -/
theorem DiskDouble.rel_untwist_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) (x y : Disk E ⊕ Disk E) :
    DiskDouble.Rel e x y ↔
      DiskDouble.Rel (Homeomorph.refl (Boundary E)) (untwist e x) (untwist e y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => rfl
    | inr
      y =>
      change
        (∃ z, x = boundary E z ∧ y = boundary E (e z)) ↔
          ∃ z,
            x = boundary E z ∧ RadialExtension.closedBallHomeomorph e.symm y = boundary E z
      constructor
      · rintro ⟨z, rfl, rfl⟩
        refine ⟨z, rfl, ?_⟩
        simp [boundary]
      · rintro ⟨z, hx, hy⟩
        refine ⟨z, hx, ?_⟩
        apply (RadialExtension.closedBallHomeomorph e.symm).injective
        rw [hy]
        simp [boundary]
  | inr x => cases y <;> rfl

/-- A twisted double is homeomorphic to the untwisted double. -/
def DiskDouble.homeomorphUntwisted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Boundary E ≃ₜ Boundary E) : Space e ≃ₜ Space (Homeomorph.refl (Boundary E)) :=
  Homeomorph.Quot.congr (untwist e) (rel_untwist_iff e)

/-! ### Hemisphere coordinates on the sphere -/

/-- The ambient Euclidean space of dimension `n`. -/
abbrev Hemisphere.Ambient (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

/-- The closed unit ball in `n` dimensions. -/
abbrev Hemisphere.Ball (n : ℕ) :=
  DiskDouble.Disk (Ambient n)

/-- The unit sphere in `n + 1` dimensions. -/
abbrev Hemisphere.Sphere (n : ℕ) :=
  Metric.sphere (0 : Ambient (n + 1)) 1

/-- The hemisphere height `√(1 − ‖x‖²)`. -/
def Hemisphere.radius {n : ℕ} (x : Ball n) : ℝ :=
  Real.sqrt (1 - ‖(x : Ambient n)‖ ^ 2)

/-- The radius squared is `1 − ‖x‖²`. -/
theorem Hemisphere.radius_sq {n : ℕ} (x : Ball n) :
    radius x ^ 2 = 1 - ‖(x : Ambient n)‖ ^ 2 := by
  apply Real.sq_sqrt
  have hx : ‖(x : Ambient n)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  nlinarith [norm_nonneg (x : Ambient n)]

/-- The hemisphere point above or below a ball point. -/
def Hemisphere.vector {n : ℕ} (b : Bool) (x : Ball n) : Ambient (n + 1) :=
  WithLp.toLp 2 (Fin.cons (if b then radius x else -radius x) (x : Ambient n))

/-- The zeroth hemisphere vector. -/
@[simp]
theorem Hemisphere.vector_zero {n : ℕ} (b : Bool) (x : Ball n) :
    vector b x 0 = if b then radius x else -radius x :=
  rfl

/-- The successor hemisphere vector. -/
@[simp]
theorem Hemisphere.vector_succ {n : ℕ} (b : Bool) (x : Ball n) (i : Fin n) :
    vector b x i.succ = (x : Ambient n) i :=
  rfl

/-- The hemisphere vector has norm one. -/
theorem Hemisphere.vector_norm_sq {n : ℕ} (b : Bool) (x : Ball n) : ‖vector b x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [vector_zero, vector_succ]
  rw [← EuclideanSpace.real_norm_sq_eq]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq] <;> rw [radius_sq] <;> ring

/-- A hemisphere point of the sphere. -/
def Hemisphere.point {n : ℕ} (b : Bool) (x : Ball n) : Sphere n :=
  ⟨vector b x, by
    rw [mem_sphere_zero_iff_norm]
    have h := vector_norm_sq b x
    nlinarith [norm_nonneg (vector b x)]⟩

/-- The hemisphere point at zero. -/
@[simp]
theorem Hemisphere.point_zero {n : ℕ} (b : Bool) (x : Ball n) :
    (point b x : Ambient (n + 1)) 0 = if b then radius x else -radius x :=
  rfl

/-- The hemisphere radius is continuous. -/
theorem Hemisphere.continuous_radius {n : ℕ} : Continuous (radius (n := n)) := by
  unfold radius
  fun_prop

/-- The hemisphere vector is continuous. -/
theorem Hemisphere.continuous_vector {n : ℕ} (b : Bool) : Continuous (vector (n := n) b) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases b
    · exact continuous_radius.neg
    · exact continuous_radius
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val

/-- The hemisphere point map is continuous. -/
theorem Hemisphere.continuous_point {n : ℕ} (b : Bool) : Continuous (point (n := n) b) :=
  (continuous_vector b).subtype_mk _

/-- Each hemisphere parametrization is injective. -/
theorem Hemisphere.point_injective {n : ℕ} (b : Bool) :
    Function.Injective (point (n := n) b) := by
  intro x y h
  apply Subtype.ext
  ext i
  exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h

/-- The hemisphere radius on the boundary. -/
@[simp]
theorem Hemisphere.radius_boundary {n : ℕ} (x : DiskDouble.Boundary (Ambient n)) :
    radius (DiskDouble.boundary (Ambient n) x) = 0 := by
  have hx : ‖(x : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  simp [radius, DiskDouble.boundary, hx]

/-- The two hemispheres agree on the boundary. -/
theorem Hemisphere.point_boundary {n : ℕ} (x : DiskDouble.Boundary (Ambient n)) :
    point Bool.false (DiskDouble.boundary (Ambient n) x) =
      point Bool.true (DiskDouble.boundary (Ambient n) x) := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rfl

/-- Hemisphere points coincide exactly at boundary points. -/
theorem Hemisphere.point_false_eq_true_iff {n : ℕ} (x y : Ball n) :
    point Bool.false x = point Bool.true y ↔
      ∃ z : DiskDouble.Boundary (Ambient n),
        x = DiskDouble.boundary (Ambient n) z ∧
          y = DiskDouble.boundary (Ambient n) z := by
  constructor
  · intro h
    have hxy : x = y := by
      apply Subtype.ext
      ext i
      exact congrArg (fun z : Sphere n => (z : Ambient (n + 1)) i.succ) h
    subst y
    have hr : radius x = 0 := by
      have hh := congrArg (fun z : Sphere n => (z : Ambient (n + 1)) 0) h
      simp only [point_zero, Bool.false_eq_true, ↓reduceIte] at hh
      linarith
    have hn : ‖(x : Ambient n)‖ = 1 := by
      have hs := radius_sq x
      rw [hr] at hs
      nlinarith [norm_nonneg (x : Ambient n)]
    exact ⟨⟨x, mem_sphere_zero_iff_norm.mpr hn⟩, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    exact point_boundary z

/-! ### Nullhomotopies in the belt complement -/

/-- An ambiently nullhomotopic map missing the image is nullhomotopic in the complement. -/
theorem ImageComplement.nullhomotopic_of_ambient_nullhomotopic {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f : C(X, domain g))
    (hambient :
      ∃ c, ((ImageComplement.inclusion g).comp f).Homotopic (ContinuousMap.const X c)) :
    ∃ c, f.Homotopic (ContinuousMap.const X c) := by
  classical
  obtain ⟨c, hc⟩ := hambient
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hconst :
    (ContinuousMap.const X ((f x₀ : domain g) : N)).Homotopic (ContinuousMap.const X c) :=
    hc.comp (ContinuousMap.Homotopic.refl (ContinuousMap.const X x₀))
  refine
    ⟨f x₀, homotopic_of_ambient_homotopic (I := I) g hg hdim f (ContinuousMap.const X (f x₀)) ?_⟩
  exact hc.trans hconst.symm

/-- Loops in the image complement are nullhomotopic in the target. -/
theorem ImageComplement.circle_nullhomotopies {E' G H' K Y N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H'] [TopologicalSpace K]
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] (g : C(Y, N))
    (hg : ContMDiff I' J ∞ g) (hdim : 2 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, N), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, domain g), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Nonempty (Hemisphere.Sphere 1) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro f
  apply nullhomotopic_of_ambient_nullhomotopic (I := 𝓡 1) g hg _ f (hnull _)
  simpa only [finrank_euclideanSpace_fin] using hdim

/-- Belt-complement loops are nullhomotopic in sphere dimension. -/
theorem SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_sphere_dimension
    {F R X Y G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X] {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)]
    (d : SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hold :
    ∀ f : C(Hemisphere.Sphere 1, d.OldComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
    apply ImageComplement.circle_nullhomotopies d.attachingSphere hattach _ hnull
    simpa only [finrank_euclideanSpace_fin] using hdim
  intro f
  let e := d.complementHomeomorph
  let forward : C(d.OldComplement, d.NewComplement) := ⟨e, e.continuous⟩
  let backward : C(d.NewComplement, d.OldComplement) := ⟨e.symm, e.symm.continuous⟩
  let f₀ : C(Hemisphere.Sphere 1, d.OldComplement) := backward.comp f
  obtain ⟨c, hc⟩ := hold f₀
  have heq : forward.comp f₀ = f := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (f x)
  have hout : (forward.comp f₀).Homotopic (ContinuousMap.const _ (e c)) :=
    (ContinuousMap.Homotopic.refl forward).comp hc
  exact ⟨e c, heq ▸ hout⟩

/-- Belt-complement loops are nullhomotopic in rank two. -/
theorem SurgeryBoundaryPair.beltComplement_circle_nullhomotopies_of_finrank_two
    {F R X Y G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [J.Boundaryless] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X] {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] [Fact (Module.finrank ℝ N = 1 + 1)]
    (d : SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 1) J ∞ d.attachingSphere)
    (hdim : 3 < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  d.beltComplement_circle_nullhomotopies_of_sphere_dimension 1 hattach hdim hnull

attribute [local instance 100] Classical.propDecidable in
/-- The attaching sphere is the attaching core map's image. -/
theorem ManifoldMorse.SignedMorseChart.attachingSphere_eq_attachingCoreMap {E M R Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2)) :
    d.attachingSphere = c.attachingCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (d.oldPiece (u, PuncturedHandle.ballZero) : M) = _
  rw [hpiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- The surgery attaching sphere map is smooth. -/
theorem ManifoldMorse.SignedMorseChart.contMDiff_surgeryAttachingSphere {E M R Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (n : ℕ) [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2)) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.attachingSphere := by
  let _ := RegularLevel.chartedSpace hf hreg
  rw [c.attachingSphere_eq_attachingCoreMap ρ hρ hblock d hpiece]
  exact c.contMDiff_attachingCoreMap n hf ρ hρ hblock hreg

attribute [local instance 100] Classical.propDecidable in
/-- Loops in the surgery belt complement are nullhomotopic. -/
theorem ManifoldMorse.SignedMorseChart.surgery_beltComplement_circle_nullhomotopies
    {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2))
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 2) (hdim : 4 < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p - ρ ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let _ : Fact (Module.finrank ℝ c.NegativeCoordinates = 1 + 1) := ⟨hindex⟩
  have hattach := c.contMDiff_surgeryAttachingSphere 1 hf ρ hρ hblock hreg d hpiece
  apply d.beltComplement_circle_nullhomotopies_of_finrank_two hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

/-! ### The new interior -/

/-- The open unit ball of a normed space. -/
abbrev PuncturedHandle.OpenUnitBall (N : Type*) [NormedAddCommGroup N] :=
  { x : N // ‖x‖ < 1 }

/-- The new level's interior: the complement plus the open new piece. -/
abbrev SurgeryBoundaryPair.NewInterior {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) : Set Y :=
  (Set.range d.newExterior)ᶜ

/-- The new interior is open. -/
theorem SurgeryBoundaryPair.isOpen_newInterior {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) : IsOpen d.NewInterior :=
  d.newExterior_closed.isClosed_range.isOpen_compl

/-- A new piece lies in the exterior exactly off the belt. -/
theorem SurgeryBoundaryPair.newPiece_mem_exterior_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (p : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P) :
    d.newPiece p ∈ Set.range d.newExterior ↔ ‖(p.1 : N)‖ = 1 := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨q, -, rfl⟩ := (d.new_overlap r p).mp hr
    exact mem_sphere_zero_iff_norm.mp q.1.property
  · intro hp
    let q : PuncturedHandle.UnitSphere N × PuncturedHandle.UnitSphere P :=
      (⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2)
    exact ⟨d.boundary q, (d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩⟩

/-- Every new piece lies in the new interior. -/
theorem SurgeryBoundaryPair.newPiece_mem_newInterior_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (p : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P) :
    d.newPiece p ∈ d.NewInterior ↔ ‖(p.1 : N)‖ < 1 := by
  change ¬d.newPiece p ∈ Set.range d.newExterior ↔ _
  rw [d.newPiece_mem_exterior_iff]
  constructor
  · intro hp
    rcases lt_or_eq_of_le p.1.property with h | h
    · exact h
    · exact (hp h).elim
  · exact fun h => h.ne

/-- The new interior lies in the union of the exterior and new piece. -/
theorem SurgeryBoundaryPair.newInterior_subset_range {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y) :
    d.NewInterior ⊆ Set.range d.newPiece := by
  intro y hy
  have hc : y ∈ Set.range d.newExterior ∪ Set.range d.newPiece := by rw [d.new_cover]; trivial
  exact hc.resolve_left hy

/-- The parametrization of the new interior by the open handle. -/
def SurgeryBoundaryPair.newInteriorParameter {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) :
    (PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) ≃ₜ
      (d.newPiece ⁻¹' d.NewInterior)
    where
  toFun p := ⟨(⟨p.1, p.1.property.le⟩, p.2), (d.newPiece_mem_newInterior_iff _).mpr p.1.property⟩
  invFun p := (⟨p.val.1, (d.newPiece_mem_newInterior_iff _).mp p.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The open new handle is homeomorphic to the new interior. -/
def SurgeryBoundaryPair.newInteriorHomeomorph {N P R X Y : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) :
    (PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) ≃ₜ
      d.NewInterior :=
  d.newInteriorParameter.trans
    (d.newPiece_closed.isEmbedding.homeomorphOfSubsetRange d.newInterior_subset_range)

/-- Belt-sphere points lie in the new interior. -/
theorem SurgeryBoundaryPair.beltSphere_mem_newInterior {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (v : PuncturedHandle.UnitSphere P) : d.beltSphere v ∈ d.NewInterior := by
  apply (d.newPiece_mem_newInterior_iff (PuncturedHandle.ballZero, v)).mpr
  simp [PuncturedHandle.ballZero]

/-- A new-interior point lies on the belt exactly at the core. -/
theorem SurgeryBoundaryPair.newInteriorHomeomorph_mem_belt_iff {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace R] [TopologicalSpace X]
    [TopologicalSpace Y] (d : SurgeryBoundaryPair N P R X Y)
    (p : PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) :
    (d.newInteriorHomeomorph p : Y) ∈ Set.range d.beltSphere ↔ (p.1 : N) = 0 :=
  d.newPiece_mem_belt_iff (⟨p.1, p.1.property.le⟩, p.2)

/-! ### Extending homotopies off a closed set -/

attribute [local instance 100] Classical.propDecidable in
/-- A function extended by another on an open set. -/
def OpenHomotopyExtension.extendFunction {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) : X → Y := fun x =>
  if hx : x ∈ U then g ⟨x, hx⟩ else f x

attribute [local instance 100] Classical.propDecidable in
/-- The homotopy extension computes inside the open set. -/
theorem OpenHomotopyExtension.extendFunction_of_mem {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) (x : U) :
    extendFunction U f g x = g x := by simp only [extendFunction, dif_pos x.property]

attribute [local instance 100] Classical.propDecidable in
/-- The homotopy extension is the original off the open set. -/
theorem OpenHomotopyExtension.extendFunction_of_not_mem {X Y : Type*} [TopologicalSpace X]
    (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y) {x : X} (hx : x ∉ U) :
    extendFunction U f g x = f x := by simp only [extendFunction, dif_neg hx]

attribute [local instance 100] Classical.propDecidable in
/-- The homotopy extension is continuous. -/
theorem OpenHomotopyExtension.continuous_extendFunction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (U : TopologicalSpace.Opens X) (f : X → Y) (g : U → Y)
    (hf : Continuous f) (hg : Continuous g) {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U)
    (hfixed : ∀ x : U, (x : X) ∉ K → g x = f x) : Continuous (extendFunction U f g) := by
  have hU : ContinuousOn (extendFunction U f g) U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (U : Set X).domRestrict (extendFunction U f g) = g :=
      funext (extendFunction_of_mem U f g)
    rw [heq]
    exact hg
  have haway : ContinuousOn (extendFunction U f g) Kᶜ := by
    apply hf.continuousOn.congr
    intro x hx
    by_cases hxU : x ∈ U
    · rw [extendFunction, dif_pos hxU]
      exact hfixed ⟨x, hxU⟩ hx
    · exact extendFunction_of_not_mem U f g hxU
  have hcover : (U : Set X) ∪ Kᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inl (hKU hx)
    · exact Or.inr hx
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hU.union_of_isOpen haway U.isOpen hK.isOpen_compl

/-- A homotopy on `U` fixed off a closed set extends to the whole space. -/
theorem OpenHomotopyExtension.exists_extended_homotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (U : TopologicalSpace.Opens X) (f : C(X, Y)) (H : C(unitInterval × U, Y))
    {K : Set X} (hK : IsClosed K) (hKU : K ⊆ U) (hzero : ∀ x : U, H (0, x) = f x)
    (hfixed : ∀ t (x : U), (x : X) ∉ K → H (t, x) = f x) :
    ∃ g : C(X, Y),
      ∃ G : f.Homotopy g, (∀ t (x : U), G (t, x) = H (t, x)) ∧ (∀ t x, x ∉ K → G (t, x) = f x) := by
  let V : TopologicalSpace.Opens (unitInterval × X) :=
    ⟨Prod.snd ⁻¹' U, U.isOpen.preimage continuous_snd⟩
  let L : V → Y := fun z => H (z.val.1, ⟨z.val.2, z.property⟩)
  have hL : Continuous L :=
    H.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  let T : C(unitInterval × X, Y) :=
    ⟨extendFunction V (fun z => f z.2) L,
      continuous_extendFunction V _ L (f.continuous.comp continuous_snd) hL
        (hK.preimage continuous_snd) (fun _ hz => hKU hz)
        (fun z hz => hfixed z.val.1 ⟨z.val.2, z.property⟩ hz)⟩
  have hlocal (t) (x : U) : T (t, x) = H (t, x) :=
    extendFunction_of_mem V (fun z : unitInterval × X => f z.2) L ⟨(t, x), x.property⟩
  have houtside (t) (x : X) (hx : x ∉ K) : T (t, x) = f x := by
    by_cases hxU : x ∈ U
    · exact (hlocal t ⟨x, hxU⟩).trans (hfixed t ⟨x, hxU⟩ hx)
    · exact extendFunction_of_not_mem V (fun z : unitInterval × X => f z.2) L (x := (t, x)) hxU
  let g : C(X, Y) := T.comp ⟨fun x => (1, x), continuous_const.prodMk continuous_id⟩
  refine
    ⟨g, { toContinuousMap := T, map_zero_left := ?_, map_one_left := fun _ => rfl }, hlocal,
      houtside⟩
  intro x
  by_cases hx : x ∈ U
  · exact (hlocal 0 ⟨x, hx⟩).trans (hzero ⟨x, hx⟩)
  · exact houtside 0 x (fun h => hx (hKU h))

/-- A `C¹` image has Hausdorff dimension at most the domain's. -/
theorem dimH_image_le_of_contDiffOn_isOpen {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s) : dimH (f '' s) ≤ dimH s := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro x hx
  obtain ⟨C, U, hU, hL⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨C, U, mem_nhdsWithin_of_mem_nhds hU, hL⟩

/-- A chart image has Hausdorff dimension at most the domain's. -/
theorem dimH_image_chart_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] {f : M → F} {s : Set M} (hs : IsOpen s)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) (x : M) :
    dimH (f '' ((modelChartPartialDiffeomorph (I := I) x).source ∩ s)) ≤ Module.finrank ℝ E := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let V : Set E := c.target ∩ c.symm ⁻¹' s
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hs
  have hfc : ContDiffOn ℝ ∞ (f ∘ c.symm) V :=
    (hf.comp (c.contMDiffOn_invFun.mono Set.inter_subset_left) Set.inter_subset_right).contDiffOn
  have himage : f '' (c.source ∩ s) = (f ∘ c.symm) '' V := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      refine ⟨c y, ⟨c.map_source' hyc, ?_⟩, ?_⟩
      · change c.symm (c y) ∈ s
        have hc : c.symm (c y) = y := c.left_inv' hyc
        rwa [hc]
      · exact congrArg f (c.left_inv' hyc)
    · rintro ⟨y, ⟨hyc, hys⟩, rfl⟩
      exact ⟨c.symm y, ⟨c.map_target' hyc, hys⟩, rfl⟩
  change dimH (f '' (c.source ∩ s)) ≤ _
  rw [himage]
  exact
    (dimH_image_le_of_contDiffOn_isOpen hV (hfc.of_le (by simp))).trans
      ((dimH_mono (Set.subset_univ V)).trans_eq (Real.dimH_univ_eq_finrank E))

/-- A smooth image of a manifold has Hausdorff dimension at most the domain's. -/
theorem dimH_image_manifold_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M] {f : M → F} {s : Set M}
    (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s) : dimH (f '' s) ≤ Module.finrank ℝ E := by
  let U : M → Set M := fun x ↦ (modelChartPartialDiffeomorph (I := I) x).source
  have hU : ∀ x, IsOpen (U x) := fun x ↦ (modelChartPartialDiffeomorph (I := I) x).open_source
  have hcover : (Set.univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩
  obtain ⟨t, htcount, ht⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have himage : f '' s ⊆ ⋃ x ∈ t, f '' (U x ∩ s) := by
    rintro z ⟨y, hys, rfl⟩
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Set.mem_iUnion₂.mpr ⟨x, hxt, y, ⟨hyx, hys⟩, rfl⟩
  apply (dimH_mono himage).trans
  rw [dimH_bUnion htcount]
  exact iSup_le (fun x ↦ iSup_le (fun _ ↦ dimH_image_chart_le hs hf x))

/-- The complement of a lower-dimensional smooth image is dense. -/
theorem dense_compl_manifold_image {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {H M : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M] [FiniteDimensional ℝ F] {f : M → F}
    {s : Set M} (hs : IsOpen s) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f s)
    (hd : Module.finrank ℝ E < Module.finrank ℝ F) : Dense (f '' s)ᶜ :=
  dense_compl_of_dimH_lt_finrank ((dimH_image_manifold_le hs hf).trans_lt (Nat.cast_lt.mpr hd))

/-- A smooth map from a lower-dimensional manifold is not surjective. -/
theorem not_surjective_contMDiff_of_dim_lt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [LindelofSpace M]
    [FiniteDimensional ℝ F] {G N : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    [J.Boundaryless] [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [Nonempty N]
    {f : M → N} (hf : ContMDiff I J ∞ f) (hd : Module.finrank ℝ E < Module.finrank ℝ F) :
    ¬Function.Surjective f := by
  intro hsurj
  let y : N := Classical.choice inferInstance
  let d := modelChartPartialDiffeomorph (I := J) y
  let s : Set M := f ⁻¹' d.source
  have hs : IsOpen s := d.open_source.preimage hf.continuous
  have hdf : ContMDiffOn I 𝓘(ℝ, F) ∞ (d ∘ f) s :=
    d.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ h ↦ h)
  have himage : (d ∘ f) '' s = d.target := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact d.map_source' hx
    · intro hz
      obtain ⟨x, hx⟩ := hsurj (d.symm z)
      refine ⟨x, ?_, ?_⟩
      · change f x ∈ d.source
        rw [hx]
        exact d.map_target' hz
      · change d (f x) = z
        rw [hx]
        exact d.right_inv' hz
  have hne : (interior d.target).Nonempty := by
    rw [d.open_target.interior_eq]
    exact ⟨d y, d.map_source' (mem_extChartAt_source y)⟩
  have hdim := dimH_image_manifold_le hs hdf
  rw [himage, Real.dimH_of_nonempty_interior hne] at hdim
  exact
    (not_le_of_gt (Nat.cast_lt.mpr hd : (Module.finrank ℝ E : ℝ≥0∞) < Module.finrank ℝ F)) hdim

/-- A continuous map into a higher-dimensional space has a smooth nonvanishing approximation. -/
theorem exists_smooth_nonzero_approx {B H M F : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : Module.finrank ℝ B < Module.finrank ℝ F) :
    ∃ g : C(M, F), ContMDiff I 𝓘(ℝ, F) ∞ g ∧ (∀ x, g x ≠ 0) ∧ ∀ x, Dist.dist (g x) (f x) < ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨h, hh, -⟩ :=
    f.continuous.exists_contMDiff_approx I (⊤ : ℕ∞) (ε := fun _ ↦ ε / 2) continuous_const
      (fun _ ↦ hhalf)
  have hdense : Dense (Set.range h)ᶜ := by
    simpa only [Set.image_univ] using
      dense_compl_manifold_image isOpen_univ h.contMDiff.contMDiffOn hd
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.mp (hdense (0 : F)) (ε / 2) hhalf
  have haNorm : ‖a‖ < ε / 2 := by simpa only [dist_zero_left, dist_zero_right] using hdist
  let g : C(M, F) := ⟨fun x ↦ h x - a, h.contMDiff.continuous.sub continuous_const⟩
  refine ⟨g, h.contMDiff.sub contMDiff_const, ?_, ?_⟩
  · intro x hx
    have he : h x = a := sub_eq_zero.mp hx
    exact ha ⟨x, he⟩
  · intro x
    have hnorm : ‖h x - a - f x‖ ≤ ‖h x - f x‖ + ‖a‖ := by
      have he : h x - a - f x = (h x - f x) - a := by abel
      rw [he]
      exact norm_sub_le _ _
    change Dist.dist (h x - a) (f x) < ε
    rw [dist_eq_norm]
    have hhx : ‖h x - f x‖ < ε / 2 := by simpa only [dist_eq_norm] using hh x
    linarith

/-! ### The zero-avoidance cutoff -/

/-- The cutoff progress between levels `l` and `u`. -/
noncomputable def RealIntervalProgress.progress (l u t : ℝ) : ℝ :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((t - l) / (u - l))

/-- The progress cutoff is continuous. -/
theorem RealIntervalProgress.continuous_progress (l u : ℝ) : Continuous (progress l u) :=
  continuous_subtype_val.comp
    (continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _))

/-- The progress is zero below `l`. -/
theorem RealIntervalProgress.progress_before {l u t : ℝ} (hlu : l ≤ u) (ht : t ≤ l) :
    progress l u t = 0 := by
  have h :=
    Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) zero_le_one
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu))
  exact congrArg Subtype.val h

/-- The progress is one above `u`. -/
theorem RealIntervalProgress.progress_after {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) :
    progress l u t = 1 := by
  have hr : 1 ≤ (t - l) / (u - l) := by
    apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
    simpa only [one_mul] using sub_le_sub_right ht l
  exact congrArg Subtype.val (Set.projIcc_of_right_le zero_le_one hr)

/-- The blend weight keeping a perturbed map nonzero. -/
noncomputable def ZeroAvoidanceCutoff.weight {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) : C(X, ℝ) :=
  ⟨fun x ↦ 1 - RealIntervalProgress.progress ε (2 * ε) ‖f x‖,
    continuous_const.sub
      ((RealIntervalProgress.continuous_progress ε (2 * ε)).comp f.continuous.norm)⟩

/-- The weight lies in `[0, 1]`. -/
theorem ZeroAvoidanceCutoff.weight_bounds {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (x : X) : 0 ≤ weight f ε x ∧ weight f ε x ≤ 1 := by
  have hp : RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ∈ Set.Icc (0 : ℝ) 1 :=
    (Set.projIcc (0 : ℝ) 1 zero_le_one ((‖f x‖ - ε) / (2 * ε - ε))).property
  change
    0 ≤ 1 - RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ∧
      1 - RealIntervalProgress.progress ε (2 * ε) ‖f x‖ ≤ 1
  constructor <;> linarith [hp.1, hp.2]

/-- The weight is one where the original map is small. -/
theorem ZeroAvoidanceCutoff.weight_small {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : ‖f x‖ ≤ ε) :
    weight f ε x = 1 := by
  simp only [weight, ContinuousMap.coe_mk,
    RealIntervalProgress.progress_before (by linarith : ε ≤ 2 * ε) hx, sub_zero]

/-- The weight is zero where the original map is large. -/
theorem ZeroAvoidanceCutoff.weight_large {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] (f : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X} (hx : 2 * ε ≤ ‖f x‖) :
    weight f ε x = 0 := by
  simp only [weight, ContinuousMap.coe_mk,
    RealIntervalProgress.progress_after (by linarith : ε < 2 * ε) hx, sub_self]

/-- The blend of the original and perturbed maps. -/
noncomputable def ZeroAvoidanceCutoff.blend {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) : C(X, F) :=
  ⟨fun x ↦ f x + weight f ε x • (g x - f x),
    f.continuous.add ((weight f ε).continuous.smul (g.continuous.sub f.continuous))⟩

/-- Where the original is small the blend is the original. -/
theorem ZeroAvoidanceCutoff.blend_small {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X}
    (hx : ‖f x‖ ≤ ε) : blend f g ε x = g x := by
  change f x + weight f ε x • (g x - f x) = g x
  rw [weight_small f ε hε hx, one_smul]
  abel

/-- Where the original is large the blend is the perturbation. -/
theorem ZeroAvoidanceCutoff.blend_large {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) {x : X}
    (hx : 2 * ε ≤ ‖f x‖) : blend f g ε x = f x := by
  change f x + weight f ε x • (g x - f x) = f x
  rw [weight_large f ε hε hx, zero_smul, add_zero]

/-- The blend stays within the perturbation distance. -/
theorem ZeroAvoidanceCutoff.dist_blend_le {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (x : X) :
    Dist.dist (blend f g ε x) (f x) ≤ Dist.dist (g x) (f x) := by
  simp only [dist_eq_norm]
  change ‖f x + weight f ε x • (g x - f x) - f x‖ ≤ ‖g x - f x‖
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_bounds f ε x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_bounds f ε x).2

/-- The blend is nonzero. -/
theorem ZeroAvoidanceCutoff.blend_ne_zero {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hg : ∀ x, g x ≠ 0) (hclose : ∀ x, Dist.dist (g x) (f x) < ε) (x : X) : blend f g ε x ≠ 0 := by
  by_cases hx : ‖f x‖ ≤ ε
  · rw [blend_small f g ε hε hx]
    exact hg x
  · intro hz
    have hh := (dist_blend_le f g ε x).trans_lt (hclose x)
    rw [hz, dist_zero_left] at hh
    exact hx hh.le

/-- The blend as a homotopy between the two maps. -/
noncomputable def ZeroAvoidanceCutoff.homotopy {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε) :
    ContinuousMap.HomotopyRel f (blend f g ε) {x | 2 * ε ≤ ‖f x‖}
    where
  toFun p := f p.2 + (p.1 : ℝ) • (blend f g ε p.2 - f p.2)
  continuous_toFun :=
    (f.continuous.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((blend f g ε).continuous.comp continuous_snd).sub (f.continuous.comp continuous_snd)))
  map_zero_left x := by simp
  map_one_left
    x := by
    change f x + (1 : ℝ) • (blend f g ε x - f x) = blend f g ε x
    rw [one_smul]
    abel
  prop' t x
    hx := by
    change f x + (t : ℝ) • (blend f g ε x - f x) = f x
    rw [blend_large f g ε hε hx, sub_self, smul_zero, add_zero]

/-- The homotopy stays within the perturbation distance. -/
theorem ZeroAvoidanceCutoff.homotopy_dist_lt {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : C(X, F)) (ε : ℝ) (hε : 0 < ε)
    (hclose : ∀ x, Dist.dist (g x) (f x) < ε) (t : (unitInterval)) (x : X) :
    Dist.dist (homotopy f g ε hε (t, x)) (f x) < ε := by
  rw [dist_eq_norm]
  change ‖f x + (t : ℝ) • (blend f g ε x - f x) - f x‖ < ε
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1]
  calc
    (t : ℝ) * ‖blend f g ε x - f x‖ ≤ ‖blend f g ε x - f x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) t.2.2
    _ ≤ Dist.dist (g x) (f x) := by simpa only [dist_eq_norm] using dist_blend_le f g ε x
    _ < ε := hclose x

/-- A map into higher dimensions is homotopic to a nearby nonvanishing map. -/
theorem exists_nonzero_homotopy_small {B H M F : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : Module.finrank ℝ B < Module.finrank ℝ F) :
    ∃ g : C(M, F),
      (∀ x, g x ≠ 0) ∧
        ∃ G : ContinuousMap.HomotopyRel f g {x | 2 * ε ≤ ‖f x‖},
          ∀ t x, Dist.dist (G (t, x)) (f x) < ε := by
  obtain ⟨h, -, hnonzero, hclose⟩ := exists_smooth_nonzero_approx (I := I) f ε hε hd
  refine
    ⟨ZeroAvoidanceCutoff.blend f h ε, ZeroAvoidanceCutoff.blend_ne_zero f h ε hε hnonzero hclose,
      ZeroAvoidanceCutoff.homotopy f h ε hε, ?_⟩
  exact ZeroAvoidanceCutoff.homotopy_dist_lt f h ε hε hclose

/-! ### Belt-avoiding circles and nullhomotopies -/

/-- A circle in the new interior can be homotoped off the belt. -/
theorem SurgeryBoundaryPair.exists_belt_avoiding_circle {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup P]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) (hdim : 1 < Module.finrank ℝ N)
    (g : C(Hemisphere.Sphere 1, Y)) :
    ∃ g' : C(Hemisphere.Sphere 1, Y),
      (∀ x, g' x ∉ Set.range d.beltSphere) ∧ g.Homotopic g' := by
  let U : TopologicalSpace.Opens (Hemisphere.Sphere 1) :=
    ⟨g ⁻¹' d.NewInterior, d.isOpen_newInterior.preimage g.continuous⟩
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let e := d.newInteriorHomeomorph
  let coord : C(U, PuncturedHandle.OpenUnitBall N × PuncturedHandle.UnitSphere P) :=
    ⟨fun x => e.symm ⟨g x, x.property⟩,
      e.symm.continuous.comp ((g.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  let normal : C(U, N) := ⟨fun x => (coord x).1, continuous_subtype_val.comp coord.continuous.fst⟩
  have hparam (x : U) : d.newPiece (⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2) = g x :=
    congrArg (fun y : d.NewInterior => (y : Y)) (e.apply_symm_apply ⟨g x, x.property⟩)
  obtain ⟨q, hq, G, hclose⟩ :=
    exists_nonzero_homotopy_small (I := 𝓡 1) normal (1 / 8) (by norm_num)
      (by simpa only [finrank_euclideanSpace_fin] using hdim)
  have hnorm (t) (x : U) : ‖G (t, x)‖ < 1 := by
    by_cases hx : 1 / 4 ≤ ‖normal x‖
    · rw [G.eq_fst t
          (show x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} from
            by
            change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
            linarith)]
      exact (coord x).1.property
    · have hdist : ‖G (t, x) - normal x‖ < 1 / 8 := by simpa only [dist_eq_norm] using hclose t x
      have hbound := norm_add_le (G (t, x) - normal x) (normal x)
      rw [sub_add_cancel] at hbound
      linarith
  let H : C(unitInterval × U, Y) :=
    ⟨fun z => (e (⟨G z, hnorm z.1 z.2⟩, (coord z.2).2) : Y),
      continuous_subtype_val.comp
        (e.continuous.comp
          ((G.continuous.subtype_mk _).prodMk (coord.continuous.snd.comp continuous_snd)))⟩
  have hreturn (t) (x : U) (hx : G (t, x) = normal x) : H (t, x) = g x := by
    have hu : (⟨G (t, x), hnorm t x⟩ : PuncturedHandle.OpenUnitBall N) = (coord x).1 :=
      Subtype.ext hx
    change (e (⟨G (t, x), _⟩, (coord x).2) : Y) = _
    rw [hu]
    exact hparam x
  have hzero (x : U) : H (0, x) = g x := hreturn 0 x (G.apply_zero x)
  let K₀ : Set Y :=
    d.newPiece ''
      {p : PuncturedHandle.UnitBall N × PuncturedHandle.UnitSphere P |
        ‖(p.1 : N)‖ ≤ 1 / 2}
  have hK₀ : IsClosed K₀ :=
    d.newPiece_closed.isClosedMap _
      (isClosed_le (continuous_subtype_val.comp continuous_fst).norm continuous_const)
  have hK₀U : K₀ ⊆ d.NewInterior := by
    rintro _ ⟨p, hp, rfl⟩
    apply (d.newPiece_mem_newInterior_iff p).mpr
    exact hp.trans_lt (by norm_num)
  let K : Set (Hemisphere.Sphere 1) := g ⁻¹' K₀
  have hK : IsClosed K := hK₀.preimage g.continuous
  have hKU : K ⊆ U := fun _ hx => hK₀U hx
  have hfixed (t) (x : U) (hx : (x : Hemisphere.Sphere 1) ∉ K) : H (t, x) = g x := by
    have hlarge : 1 / 2 < ‖normal x‖ := by
      by_contra! hh
      apply hx
      exact ⟨(⟨(coord x).1, (coord x).1.property.le⟩, (coord x).2), hh, hparam x⟩
    have hsafe : x ∈ {x | 2 * (1 / 8 : ℝ) ≤ ‖normal x‖} := by
      change 2 * (1 / 8 : ℝ) ≤ ‖normal x‖
      linarith
    exact hreturn t x (G.eq_fst t hsafe)
  obtain ⟨g', G', hlocal, houtside⟩ :=
    OpenHomotopyExtension.exists_extended_homotopy U g H hK hKU hzero hfixed
  refine ⟨g', ?_, ⟨G'⟩⟩
  intro x hxB
  by_cases hx : x ∈ U
  · have heq : g' x = H (1, ⟨x, hx⟩) := (G'.apply_one x).symm.trans (hlocal 1 ⟨x, hx⟩)
    rw [heq] at hxB
    have hzero' : G (1, ⟨x, hx⟩) = 0 := (d.newInteriorHomeomorph_mem_belt_iff _).mp hxB
    rw [G.apply_one] at hzero'
    exact hq ⟨x, hx⟩ hzero'
  · have heq : g' x = g x := (G'.apply_one x).symm.trans (houtside 1 x (fun h => hx (hKU h)))
    rw [heq] at hxB
    obtain ⟨v, hv⟩ := hxB
    apply hx
    change g x ∈ d.NewInterior
    rw [← hv]
    exact d.beltSphere_mem_newInterior v

/-- Loops avoiding the belt are nullhomotopic. -/
theorem SurgeryBoundaryPair.circle_nullhomotopies_of_beltComplement {N P R X Y : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup P]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
    (d : SurgeryBoundaryPair N P R X Y) (hdim : 1 < Module.finrank ℝ N)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  intro g
  obtain ⟨g', havoid, hgg'⟩ := d.exists_belt_avoiding_circle hdim g
  let g₀ : C(Hemisphere.Sphere 1, d.NewComplement) :=
    ⟨fun x => ⟨g' x, havoid x⟩, g'.continuous.subtype_mk _⟩
  let inc : C(d.NewComplement, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨q, hq⟩ := hnull g₀
  have hh : (inc.comp g₀).Homotopic (ContinuousMap.const _ (q : Y)) :=
    (ContinuousMap.Homotopic.refl inc).comp hq
  exact ⟨q, hgg'.trans hh⟩

/-- Loops in the new boundary are nullhomotopic. -/
theorem SurgeryBoundaryPair.newBoundary_circle_nullhomotopies {N F R X Y G H : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace R]
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X]
    (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] (hn : 0 < n)
    (d : SurgeryBoundaryPair N F R X Y) (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, Y), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hnormal : 1 < Module.finrank ℝ N := by
    rw [show Module.finrank ℝ N = n + 1 from Fact.out]
    omega
  exact
    d.circle_nullhomotopies_of_beltComplement hnormal
      (d.beltComplement_circle_nullhomotopies_of_sphere_dimension n hattach hdim hnull)

attribute [local instance 100] Classical.propDecidable in
/-- Loops in the surgery new boundary are nullhomotopic. -/
theorem ManifoldMorse.SignedMorseChart.surgery_newBoundary_circle_nullhomotopies
    {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [TopologicalSpace R] [TopologicalSpace Y] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p) (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ ManifoldMorse.criticalPoints E f)
    (d :
      SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
        { x : M // f x = f p - ρ ^ 2 } Y)
    (hpiece :
      ∀ z,
        (d.oldPiece z : M) =
          c.normHandleMap ρ hρ hblock (PuncturedHandle.sphereToBall z.1, z.2))
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p - ρ ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  have hattach := c.contMDiff_surgeryAttachingSphere n hf ρ hρ hblock hreg d hpiece
  apply d.newBoundary_circle_nullhomotopies n hn hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

/-! ### Morse surgery data -/

attribute [local instance 100] Classical.propDecidable in
/-- The surgery data of a signed Morse chart: attaching and belt spheres with levels. -/
structure ManifoldMorse.MorseSurgeryData (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ)
    (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : SignedMorseChart (E := E) f p
  block :
    Metric.closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
        Metric.closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆
      chart.splitChart.target
  attachmentHomeomorph :
    ↥({x : M | f x ≤ f p - radius ^ 2} ∪
          Set.range (chart.attachingHandleMap radius radius_pos block)) ≃ₜ
      { x : M // f x ≤ f p + radius ^ 2 }
  attachment_frontier :
    ∀ x,
      f (attachmentHomeomorph x) = f p + radius ^ 2 ↔
        x.val ∈
          frontier
            ({y : M | f y ≤ f p - radius ^ 2} ∪
              Set.range (chart.attachingHandleMap radius radius_pos block))
  attachment_fixed : ∀ x, f x.val = f p + radius ^ 2 → (attachmentHomeomorph x).val = x.val
  attachment_model_orbits :
    chart.FollowsModelBoundaryOrbits radius radius_pos block attachmentHomeomorph
  surgery :
    SurgeryBoundaryPair chart.NegativeCoordinates chart.PositiveCoordinates
      { x : M //
        f x = f p - radius ^ 2 ∧
          x ∈
            frontier
              ({y | f y ≤ f p - radius ^ 2} ∪
                Set.range (chart.normHandleMap radius radius_pos block)) }
      { x : M // f x = f p - radius ^ 2 } { x : M // f x = f p + radius ^ 2 }
  oldExterior_eq : ∀ r, (surgery.oldExterior r : M) = r.val
  newExterior_eq :
    ∀ r, (surgery.newExterior r : M) = (attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩).val
  oldPiece_eq :
    ∀ z,
      (surgery.oldPiece z : M) =
        chart.normHandleMap radius radius_pos block (PuncturedHandle.sphereToBall z.1, z.2)
  newPiece_eq :
    ∀ z,
      (surgery.newPiece z : M) =
        (attachmentHomeomorph
            ⟨chart.normHandleMap radius radius_pos block
                (z.1, PuncturedHandle.sphereToBall z.2),
              Or.inr
                ⟨chart.handleBallCoordinates (z.1, PuncturedHandle.sphereToBall z.2),
                  rfl⟩⟩).val
  belt_eq : surgery.beltSphere = chart.beltCoreMap radius radius_pos block
  lower_regular : ∀ x, f x = f p - radius ^ 2 → x ∉ criticalPoints E f
  upper_regular : ∀ x, f x = f p + radius ^ 2 → x ∉ criticalPoints E f

/-- The lower level of the surgery data. -/
abbrev ManifoldMorse.MorseSurgeryData.LowerLevel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :=
  { x : M // f x = f p - d.radius ^ 2 }

/-- The upper level of the surgery data. -/
abbrev ManifoldMorse.MorseSurgeryData.UpperLevel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :=
  { x : M // f x = f p + d.radius ^ 2 }

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map computes the sphere inclusion. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) :
    d.surgery.attachingSphere = d.chart.attachingCoreMap d.radius d.radius_pos d.block :=
  d.chart.attachingSphere_eq_attachingCoreMap d.radius d.radius_pos d.block d.surgery
    d.oldPiece_eq

attribute [local instance 100] Classical.propDecidable in
/-- The attaching sphere map is a closed embedding. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.surgery.attachingSphere := by
  rw [d.attaching_eq]
  exact d.chart.attachingCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
/-- The belt sphere map is a closed embedding. -/
theorem ManifoldMorse.MorseSurgeryData.belt_isClosedEmbedding {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] :
    Topology.IsClosedEmbedding d.surgery.beltSphere := by
  rw [d.belt_eq]
  exact d.chart.beltCoreMap_isClosedEmbedding d.radius d.radius_pos d.block

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map is smooth. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_smooth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.attachingSphere := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact d.chart.contMDiff_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular

attribute [local instance 100] Classical.propDecidable in
/-- The belt map is smooth. -/
theorem ManifoldMorse.MorseSurgeryData.belt_smooth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.surgery.beltSphere := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.contMDiff_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map's derivative is injective. -/
theorem ManifoldMorse.MorseSurgeryData.attaching_derivative_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)]
    (u : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    Function.Injective
      (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.attachingSphere u) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  rw [d.attaching_eq]
  exact
    d.chart.injective_mfderiv_attachingCoreMap n hf d.radius d.radius_pos d.block d.lower_regular
      u

attribute [local instance 100] Classical.propDecidable in
/-- The belt map's derivative is injective. -/
theorem ManifoldMorse.MorseSurgeryData.belt_derivative_injective {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere v) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  rw [d.belt_eq]
  exact d.chart.injective_mfderiv_beltCoreMap n hf d.radius d.radius_pos d.block d.upper_regular v

attribute [local instance 100] Classical.propDecidable in
/-- Loops in the upper level are nullhomotopic. -/
theorem ManifoldMorse.MorseSurgeryData.upper_circle_nullhomotopies {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p - d.radius ^ 2 }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, { x : M // f x = f p + d.radius ^ 2 }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
  d.chart.surgery_newBoundary_circle_nullhomotopies n hn hf d.radius d.radius_pos d.block
    d.lower_regular d.surgery d.oldPiece_eq hdim hnull

attribute [local instance 100] Classical.propDecidable in
/-- Morse surgery data exists below a level. -/
theorem ManifoldMorse.exists_morseSurgeryData_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : MorseSurgeryData E f p,
      d.radius < ε ∧
        ∀ x ∈ criticalPoints E f,
          f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p := by
  obtain ⟨ρ, hρ, hρε, c, hblock, e, he, hfixed, hlevel, hlower, hupper, horbits, hband⟩ :=
    exists_morse_boundary_attachment_with_model_orbits_lt hf hm hp hunique hε
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := he
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e he
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e he hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, hband⟩

/-! ### Surgery windows -/

/-- The standard sphere parametrization by hemisphere coordinates. -/
def SphereCoordinates.standardParametrization (N : Type*) [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] [FiniteDimensional ℝ N] :
    Diffeomorph (𝓡 n) (𝓡 n) (Hemisphere.Sphere n) (Metric.sphere (0 : N) 1) ∞ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b := (stdOrthonormalBasis ℝ N).reindex (finCongr (Fact.out : Module.finrank ℝ N = n + 1))
  exact SphereCoordinates.ofLinearIsometry b.repr.symm

attribute [local instance 100] Classical.propDecidable in
/-- The attaching sphere transported by the flow. -/
def ManifoldMorse.MorseSurgeryData.transportedAttachingSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) : C(Hemisphere.Sphere n, d.UpperLevel) :=
  ⟨fun x =>
    e.symm
      (d'.surgery.attachingSphere
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x)),
    e.symm.continuous.comp
      (d'.surgery.attachingSphere.continuous.comp
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates
            n).continuous)⟩

attribute [local instance 100] Classical.propDecidable in
/-- The transported attaching sphere computes the flow. -/
theorem ManifoldMorse.MorseSurgeryData.transportedAttachingSphere_apply {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) (x : Hemisphere.Sphere n) :
    e (d.transportedAttachingSphere d' n e x) =
      d'.surgery.attachingSphere
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x) :=
  e.apply_symm_apply _

attribute [local instance 100] Classical.propDecidable in
/-- The range of the transported attaching sphere. -/
theorem ManifoldMorse.MorseSurgeryData.range_transportedAttachingSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) :
    Set.range (d.transportedAttachingSphere d' n e) =
      e ⁻¹' Set.range d'.surgery.attachingSphere := by
  let s := SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨s x, (d.transportedAttachingSphere_apply d' n e x).symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := s.surjective z
    refine ⟨x, e.injective ?_⟩
    rw [d.transportedAttachingSphere_apply d' n e]
    exact (congrArg d'.surgery.attachingSphere hx).trans hz

attribute [local instance 100] Classical.propDecidable in
/-- The transported attaching sphere is smooth. -/
theorem ManifoldMorse.MorseSurgeryData.transportedAttachingSphere_smooth {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∀ e :
      Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) d.UpperLevel
        d'.LowerLevel ∞,
      ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞
        (d.transportedAttachingSphere d' n e.toHomeomorph) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  intro e
  exact
    e.symm.contMDiff.comp
      ((d'.attaching_smooth hf n).comp
        (SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates
            n).contMDiff)

/-- A smooth band bridge of the surgery data exists. -/
theorem ManifoldMorse.MorseSurgeryData.exists_smoothBandBridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (d' : ManifoldMorse.MorseSurgeryData E f q) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (hgap : f p + d.radius ^ 2 ≤ f q - d'.radius ^ 2)
    (hband :
      ∀ x,
        f x ∈ Set.Icc (f p + d.radius ^ 2) (f q - d'.radius ^ 2) →
          x ∉ ManifoldMorse.criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI := RegularLevel.chartedSpace hf d'.lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) d.UpperLevel
          d'.LowerLevel ∞,
        D '' {x : M | f x ≤ f p + d.radius ^ 2} = {x : M | f x ≤ f q - d'.radius ^ 2} ∧
          ∀ x : d.UpperLevel, (e x : M) = D x := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.chartedSpace hf d'.lower_regular
  obtain ⟨D, hlevel, hsublevel⟩ :=
    RegularLevel.exists_ambient_regularBand_transport hf hgap hband
  obtain ⟨e, he⟩ :=
    RegularLevel.exists_levelDiffeomorph_of_ambient hf d.upper_regular d'.lower_regular D
      hlevel
  exact ⟨D, e, hsublevel, he⟩

attribute [local instance 100] Classical.propDecidable in
/-- A pair of surgery windows around a critical point, with lower and upper levels. -/
structure ManifoldMorse.SurgeryWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) where
  finite : (criticalPoints E f).Finite
  distinct : Set.InjOn f (criticalPoints E f)
  data : ∀ p : criticalPoints E f, MorseSurgeryData E f p.val
  isolated :
    ∀ (p : criticalPoints E f) (x : M),
      x ∈ criticalPoints E f →
        f x ∈ Set.Icc (f p - (data p).radius ^ 2) (f p + (data p).radius ^ 2) → x = p.val
  separated :
    ∀ p q : criticalPoints E f, f p < f q → f p + (data p).radius ^ 2 < f q - (data q).radius ^ 2

/-- The lower level of the surgery windows. -/
def ManifoldMorse.SurgeryWindows.lower {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    ℝ :=
  f p - (S.data p).radius ^ 2

/-- The upper level of the surgery windows. -/
def ManifoldMorse.SurgeryWindows.upper {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    ℝ :=
  f p + (S.data p).radius ^ 2

/-- The lower level lies below the critical value. -/
theorem ManifoldMorse.SurgeryWindows.lower_lt_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    S.lower p < f p := by
  dsimp [ManifoldMorse.SurgeryWindows.lower]
  nlinarith [(S.data p).radius_pos]

/-- The critical value lies below the upper level. -/
theorem ManifoldMorse.SurgeryWindows.value_lt_upper {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p : ManifoldMorse.criticalPoints E f) :
    f p < S.upper p := by
  dsimp [ManifoldMorse.SurgeryWindows.upper]
  nlinarith [(S.data p).radius_pos]

/-- The upper window lies below the lower bound. -/
theorem ManifoldMorse.SurgeryWindows.upper_lt_lower {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) : S.upper p < S.lower q :=
  S.separated p q hpq

/-- The band between the levels is regular. -/
theorem ManifoldMorse.SurgeryWindows.regular_between {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (p q : ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ x, f x ∈ Set.Icc (S.upper p) (S.lower q) → x ∉ ManifoldMorse.criticalPoints E f := by
  intro x hx hcrit
  exact
    hconsecutive ⟨x, hcrit⟩
      ⟨(S.value_lt_upper p).trans_le hx.1, hx.2.trans_lt (S.lower_lt_value q)⟩

attribute [local instance 100] Classical.propDecidable in
/-- A band bridge between the windows exists. -/
theorem ManifoldMorse.SurgeryWindows.exists_bandBridge {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper p} = {x : M | f x ≤ S.lower q} ∧
          ∀ x : (S.data p).UpperLevel, (b x : M) = D x :=
  (S.data p).exists_smoothBandBridge (S.data q) hf (S.upper_lt_lower p q hpq).le
    (S.regular_between p q hconsecutive)

attribute [local instance 100] Classical.propDecidable in
/-- Surgery windows exist around a Morse critical point. -/
theorem ManifoldMorse.nonempty_surgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hinj : Set.InjOn f (criticalPoints E f)) :
    Nonempty (SurgeryWindows E f) := by
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii (finite_criticalPoints hf hm) hinj
  have hex :
    ∀ p : criticalPoints E f,
      ∃ d : MorseSurgeryData E f p.val,
        d.radius < r p ∧
          ∀ x ∈ criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      exists_morseSurgeryData_lt hf hm p.property (fun x hx hfx => hinj hx p.property hfx) (hr p)
  choose d hd hisolated using hex
  refine
    ⟨{  finite := finite_criticalPoints hf hm
        distinct := hinj
        data := d
        isolated := hisolated
        separated := ?_ }⟩
  intro p q hpq
  have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)
    nlinarith
  have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)
    nlinarith
  linarith [hgap p q hpq]

attribute [local instance 100] Classical.propDecidable in
/-- Surgery windows adapted to a descent field. -/
structure AdaptedWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ) extends
    ManifoldMorse.SurgeryWindows E f where
  field : (x : M) → TangentSpace 𝓘(ℝ, E) x
  flow : Flow ℝ M
  smooth :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, field x⟩ : TangentBundle 𝓘(ℝ, E) M))
  integral : ∀ x, IsMIntegralCurve (fun t => flow t x) field
  zero : ∀ x ∈ ManifoldMorse.criticalPoints E f, field x = 0
  descent : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (field x) < 0
  model_germ :
    ∀ (p : ManifoldMorse.criticalPoints E f) z,
      z ∈
          Metric.closedBall (0 : (data p).chart.NegativeCoordinates) (2 * (data p).radius) ×ˢ
            Metric.closedBall (0 : (data p).chart.PositiveCoordinates) (2 * (data p).radius) →
        ∀ᶠ y in 𝓝 ((data p).chart.splitChart.symm z), field y = (data p).chart.descentField y

