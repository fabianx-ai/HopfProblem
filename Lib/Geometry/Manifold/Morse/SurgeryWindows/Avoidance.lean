/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.HausdorffDimension
public import Lib.Geometry.Manifold.Morse.Existence

/-!
# Avoiding a lower-dimensional image by a small perturbation

General position for two smooth maps `f : X → N` and `g : Y → N` with
`dim X + dim Y < dim N`: `f` can be moved by a smooth homotopy relative to a closed set `C`
on which it already misses `g`, to a smooth map whose range is disjoint from the range of `g`
(`GeneralPosition.exists_disjoint_smooth_map_homotopicRel`, for compact `X` and `Y`).
The perturbation is built from finitely many chart patches
(`GeneralPosition.MapAvoidancePatch`), each a bump function times a small vector added in a
chart of `N`; a single small vector exists because the "bad" vectors form the image of a smooth
map of `X × Y` of dimension smaller than `dim N`, whose complement is dense
(`exists_small_localized_image_avoidance`,
`ChartMapPerturbation.exists_small_avoiding_parameter`).
Cf. Hirsch, *Differential Topology*, Ch. 3 (transversality), and Guillemin–Pollack,
*Differential Topology*, Ch. 2.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

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

/-- A chart of `N` with a smooth compactly supported cutoff on `X` vanishing on `C`: the data of one
  local perturbation of maps `X → N` relative to `C`. -/
structure GeneralPosition.MapAvoidancePatch {E G H K X N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace K] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N] [ChartedSpace K N]
    (C : Set X) where
  /-- The chart of the target in which the map is perturbed. -/
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  /-- The bump function on the source that scales the perturbation vector. -/
  cutoff : X → ℝ
  /-- The cutoff is smooth. -/
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  /-- The cutoff has compact support. -/
  compact : HasCompactSupport cutoff
  /-- The cutoff vanishes on `C`, so the perturbation is relative to `C`. -/
  fixed : ∀ x ∈ C, cutoff x = 0

/-- A patch is compatible with `f` when `f` maps the support of the cutoff into the chart's
  source. -/
def GeneralPosition.MapAvoidancePatch.Compatible {E G H K X N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace K] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace N]
    [ChartedSpace K N] {C : Set X} (p : GeneralPosition.MapAvoidancePatch I J (N := N) C)
    (f : X → N) : Prop :=
  Set.MapsTo f (tsupport p.cutoff) p.chart.source

/-- One patch step: a smooth `f` compatible with all patches is homotopic rel `C` to a smooth map,
  still compatible, that misses the range of `g` wherever `f` did or the cutoff of patch `i` is
  nonzero. -/
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

/-- Every point outside the closed set `C` has a patch compatible with `f` whose cutoff is nonzero
  there. -/
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

