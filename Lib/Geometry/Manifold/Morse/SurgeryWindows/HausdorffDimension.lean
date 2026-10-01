/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Flow.Compact

/-!
# Hausdorff dimension of smooth images

A smooth map `f : X → F` from a finite-dimensional manifold, restricted to an open set `s`, has
image of Hausdorff dimension at most `dim X` (`GeneralPosition.dimH_image_manifold_le`); hence
the complement of `f '' s` is dense when `dim X < dim F`
(`GeneralPosition.dense_compl_manifold_image`). The proof covers `X` by countably many
extended charts, in each of which `f` is locally Lipschitz, and applies Mathlib's
`dimH_image_le_of_locally_lipschitzOn` and `dense_compl_of_dimH_lt_finrank`.

The root-namespace versions `dimH_image_chart_le`, `dimH_image_manifold_le` and
`dense_compl_manifold_image` state the same bounds for boundaryless models through
`modelChartPartialDiffeomorph`; `not_surjective_contMDiff_of_dim_lt` deduces that a smooth map
into a manifold of larger dimension is not surjective (the easy case of Sard's theorem,
cf. Milnor, *Topology from the differentiable viewpoint*, §2–3).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

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

