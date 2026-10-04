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
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Lib.Geometry.Manifold.Transversality.Basic
public import Lib.Geometry.Manifold.LocalDiffeomorph
/-!
# Transversality by an ambient diffeomorphism

`NativeTransversality.At I I' J f g x y` (from `Lib.Geometry.Manifold.Transversality.Basic`)
says that at a common value `f x = g y` the differentials of `f` and `g` span the tangent space.
It forces `dim N ≤ dim X + dim Y` (`MorseRearrangement.native_transverse_dimension_bound`), so
when `dim X + dim Y < dim N` everywhere-transverse maps have disjoint ranges
(`disjoint_ranges_of_native_transverse_dimension`); a dummy factor can be ignored
(`native_transverse_of_ignored_factor`).

A `NativeTransversality.Patch J X` is a compact core in `X`, a chart of `N`, a compactly
supported cutoff in the chart and an open plateau on which the cutoff is `1`; it is
`Compatible` with `f` when `f` maps the core into the plateau, and every point of a compact
`X` has one (`exists_patch_at`). In a patch, translating by a small vector `a` in the chart
through `SupportedDiffeomorph.bumpFamily` gives a diffeomorphism `e` of `N`, isotopic to the
identity, with `e ∘ f` transverse to `g` at the points of the plateau
(`ChartMapPerturbation.exists_ambient_transverse_plateau`, using the density of good translations
`TransverseCoordinates.dense_native_translations`). Transversality on a compact set is open, so
the patches are handled one after another (`exists_patch_step`,
`exists_finite_patch_diffeomorph`). Hence, for `X`, `Y` compact and
`dim X + dim Y = dim N`, there is a diffeomorphism `e` of `N` isotopic to the identity with
`e ∘ f` transverse to `g` (`exists_ambient_transverse_diffeomorph`), and for
`dim X + dim Y < dim N` one with `range (e ∘ f)` disjoint from `range g`
(`MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension`).

Textbook: the transversality theorem by perturbation and its use for general position
(Guillemin–Pollack, *Differential Topology*, Ch. 2 §3; Milnor, *Lectures on the h-cobordism
theorem*, §4 and §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

@[expose] public noncomputable section

/-! ### Transversality for rearrangement -/

/-- A dimension bound making a map transverse to an ignored factor. -/
theorem MorseRearrangement.native_transverse_dimension_bound {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] [FiniteDimensional ℝ D]
    [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N} {x : X} {y : Y}
    (ht : NativeTransversality.At I I' J f g x y) (hxy : g y = f x) :
    Module.finrank ℝ G ≤ Module.finrank ℝ D + Module.finrank ℝ Z := by
  let L : (D × Z) →L[ℝ] G := by
    exact (mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)
  have hL : Function.Surjective L := ht hxy
  have hh := LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hL
  simpa only [Module.finrank_prod] using hh

/-- Under the transverse dimension bound the ranges can be made disjoint. -/
theorem MorseRearrangement.disjoint_ranges_of_native_transverse_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace K] {I : ModelWithCorners ℝ D H}
    {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] [TopologicalSpace N]
    [ChartedSpace K N] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] {f : X → N} {g : Y → N}
    (ht : ∀ x y, NativeTransversality.At I I' J f g x y)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    Disjoint (Set.range f) (Set.range g) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  exact (not_le_of_gt hdim) (native_transverse_dimension_bound (ht x y) (hy.trans hx.symm))

/-- Transversality when the target factor is ignored. -/
theorem MorseRearrangement.native_transverse_of_ignored_factor {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [TopologicalSpace N] [ChartedSpace K N] {R H'' W : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R] [TopologicalSpace H'']
    {I'' : ModelWithCorners ℝ R H''} [TopologicalSpace W] [ChartedSpace H'' W] {f : X → N}
    {g : Y → N} {x : X} {y : Y} (w : W) (hf : MDifferentiableAt I J f x)
    (ht : NativeTransversality.At (I.prod I'') I' J (f ∘ Prod.fst) g (x, w) y) :
    NativeTransversality.At I I' J f g x y := by
  intro hxy
  have hsurj := ht hxy
  have hd :
    (mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G) =
      (mfderiv I J f x : D →L[ℝ] G).comp (ContinuousLinearMap.fst ℝ D R) := by
    rw [mfderiv_comp (x, w) hf mdifferentiableAt_fst, mfderiv_fst]
    rfl
  change
    Function.Surjective
      ((mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G).coprod
        (mfderiv I' J g y : Z →L[ℝ] G)) at hsurj
  rw [hd] at hsurj
  intro v
  obtain ⟨⟨⟨a, b⟩, c⟩, hh⟩ := hsurj v
  exact ⟨(a, c), hh⟩

/-- A chart map can be perturbed to a transverse plateau. -/
theorem ChartMapPerturbation.exists_ambient_transverse_plateau
    {D Z G F H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [TopologicalSpace N]
    [ChartedSpace K N] [T2Space N] [LindelofSpace (X × Y)]
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {g : Y → N} {β : F → ℝ}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ c.target)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F,
      ‖a‖ < ε ∧
        ∃ e : Diffeomorph J J N N ∞,
          (∀ y, e y = SupportedDiffeomorph.bumpFamily c.symm β (a, y)) ∧
            (∀ y ∉ c.symm '' tsupport β, e y = y) ∧
              SupportedDiffeomorph.IsotopicToIdentity e ∧
                ∀ x,
                  f x ∈ c.source →
                    (β =ᶠ[𝓝 (c (f x))] fun _ => 1) →
                      ∀ y,
                        g y = e (f x) →
                          Function.Surjective
                            ((mfderiv I J (e ∘ f) x : D →L[ℝ] G).coprod
                              (mfderiv I' J g y : Z →L[ℝ] G)) := by
  let U : Set X := f ⁻¹' c.source
  let V : Set Y := g ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hV : IsOpen V := c.open_source.preimage hg.continuous
  have hcf : ContMDiffOn I 𝓘(ℝ, F) ∞ (c ∘ f) U :=
    c.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ hx => hx)
  have hcg : ContMDiffOn I' 𝓘(ℝ, F) ∞ (c ∘ g) V :=
    c.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
  have hdense := TransverseCoordinates.dense_native_translations hU hV hcf hcg hdim
  obtain ⟨δ, hδ, hdiff, -, hsource⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily c.symm hβ hcompact hsupport
  obtain ⟨η, hη, hisotopy⟩ :=
    SupportedDiffeomorph.exists_radius_bumpFamily_isotopy c.symm hβ hcompact hsupport
  obtain ⟨a, ha, hnorm⟩ := hdense.exists_dist_lt 0 (lt_min hε (lt_min hδ hη))
  have hn : ‖a‖ < Min.min ε (Min.min δ η) := by simpa only [dist_zero_left] using hnorm
  have haδ := (lt_min_iff.mp (lt_min_iff.mp hn).2).1
  have haη := (lt_min_iff.mp (lt_min_iff.mp hn).2).2
  obtain ⟨e, he⟩ := hdiff a haδ
  have hsrc := hsource a haδ
  refine ⟨a, (lt_min_iff.mp hn).1, e, he, ?_, hisotopy a haη e he, ?_⟩
  · intro y hy
    rw [he]
    exact SupportedDiffeomorph.bumpFamily_fixed_outside c.symm β a hy
  · intro x hfx hx y hxy
    have hnew : e (f x) ∈ c.source := by
      rw [he]
      exact SupportedDiffeomorph.bumpFamily_mem_target c.symm β a hsrc hfx
    have hgy : g y ∈ c.source := hxy ▸ hnew
    have hcfAt := hcf.contMDiffAt (hU.mem_nhds hfx)
    have hevent : c ∘ (e ∘ f) =ᶠ[𝓝 x] fun z => c (f z) + a := by
      filter_upwards [hU.mem_nhds hfx, hx.comp_tendsto hcfAt.continuousAt] with z hz hβz
      change β (c (f z)) = 1 at hβz
      change c (e (f z)) = c (f z) + a
      rw [he]
      have hh := SupportedDiffeomorph.bumpFamily_coordinates c.symm β a hsrc hz
      change
        c (SupportedDiffeomorph.bumpFamily c.symm β (a, f z)) =
          c (f z) + β (c (f z)) • a at hh
      exact hh.trans (by rw [hβz, one_smul])
    have hcross : (c ∘ g) y = (c ∘ f) x + a := by
      change c (g y) = c (f x) + a
      rw [hxy]
      exact hevent.eq_of_nhds
    have ht := ha x hfx y hgy hcross
    have hderiv := mfderiv_eq_of_translation_germ (hcfAt.mdifferentiableAt (by simp)) hevent
    apply
      transverse_of_chart c ((e.contMDiff.comp hf).mdifferentiableAt (by simp))
        (hg.mdifferentiableAt (by simp)) hxy hnew
    rw [hderiv]
    exact ht

/-- A compact-core chart patch for local transversality constructions. -/
structure NativeTransversality.Patch {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] (J : ModelWithCorners ℝ G K) [TopologicalSpace N]
    [ChartedSpace K N] (X : Type*) [TopologicalSpace X] where
  core : Set X
  core_compact : IsCompact core
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : G → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.target
  plateau : Set N
  plateau_open : IsOpen plateau
  plateau_source : plateau ⊆ chart.source
  plateau_one : ∀ y ∈ plateau, cutoff =ᶠ[𝓝 (chart y)] fun _ => 1

/-- Compatibility of a patch with a map: the chart covers the core. -/
def NativeTransversality.Patch.Compatible {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X]
    (p : NativeTransversality.Patch J X (N := N)) (f : X → N) : Prop :=
  Set.MapsTo f p.core p.plateau

/-- Every point of a compact space admits a patch around its image. -/
theorem NativeTransversality.exists_patch_at {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] {X : Type*} [TopologicalSpace X] [FiniteDimensional ℝ G] [J.Boundaryless]
    [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N} (hf : Continuous f) (x : X) :
    ∃ p : Patch J X (N := N), p.Compatible f ∧ x ∈ interior p.core := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source' hcx))
  obtain ⟨β, hβ, hsupport, W, hW, hcenter, -, hone⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {c (f x)}) (U :=
      Metric.ball (c (f x)) r) isClosed_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (c (f x)) r).of_isClosed_subset (isClosed_tsupport β)
      (hsupport.trans Metric.ball_subset_closedBall)
  let O : Set N := c.source ∩ c ⁻¹' W
  have hO : IsOpen O := c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source hW
  have hfx : f x ∈ O := ⟨hcx, hcenter (Set.mem_singleton _)⟩
  obtain ⟨C, hC, -, hxC, hCO⟩ :=
    exists_compact_closed_between (isCompact_singleton (x := x)) (hO.preimage hf)
      (Set.singleton_subset_iff.mpr hfx)
  let p : Patch J X (N := N) :=
    { core := C
      core_compact := hC
      chart := c
      cutoff := β
      cutoff_smooth := hβ
      cutoff_compact := hcompact
      cutoff_support := hsupport.trans hball
      plateau := O
      plateau_open := hO
      plateau_source := Set.inter_subset_left
      plateau_one := by
        intro y hy
        filter_upwards [hW.mem_nhds hy.2] with z hz
        exact hone hz }
  exact ⟨p, hCO, hxC (Set.mem_singleton x)⟩

/-- One step of the finite transversality patch construction. -/
theorem NativeTransversality.exists_patch_step {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] (p : ι → Patch J X (N := N)) (i : ι)
    {f : X → N} {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {C : Set X}
    (hC : IsCompact C) (htrans : ∀ x ∈ C, ∀ y, At I I' J f g x y) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
        (∀ x ∈ C ∪ (p i).core, ∀ y, At I I' J (e ∘ f) g x y) ∧
          (∀ y ∉ (p i).chart.symm '' tsupport (p i).cutoff, e y = y) ∧
            SupportedDiffeomorph.IsotopicToIdentity e := by
  let A : G × X → N := fun q =>
    SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
        (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
        (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily (p i).chart.symm
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support
  have hA : ContMDiffOn (𝓘(ℝ, G).prod I) J ∞ A (Metric.ball (0 : G) δ ×ˢ Set.univ) := by
    intro q hq
    have hsmall : ‖q.1‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hq.1
    have hpair :
      ContMDiffAt (𝓘(ℝ, G).prod I) (𝓘(ℝ, G).prod J) ∞ (fun r : G × X => (r.1, f r.2)) q :=
      contMDiffAt_fst.prodMk (hf.comp contMDiff_snd).contMDiffAt
    exact ((hsmooth (q.1, f q.2) hsmall).comp q hpair).contMDiffWithinAt
  have hzero : (fun x => A (0, x)) = f := by
    funext x
    exact SupportedDiffeomorph.bumpFamily_zero _ _ _
  have hregular :
    ∀ᶠ a in 𝓝 (0 : G), ∀ z ∈ C ×ˢ (Set.univ : Set Y), At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply
      eventually_on_compact Metric.isOpen_ball hA hg hdim (hC.prod isCompact_univ)
        (Metric.mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨a, ha, e, he, hfixed, hisotopy, hnew⟩ :=
    ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim hε
  have hgood :=
    hsmall
      (show a ∈ Metric.ball (0 : G) ε by simpa only [Metric.mem_ball, dist_zero_right] using ha)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hfixed, hisotopy⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, Set.mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

/-- Finitely many patches give a transverse diffeomorphism. -/
theorem NativeTransversality.exists_finite_patch_diffeomorph {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι] (p : ι → Patch J X (N := N)) {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) (s : Finset ι) :
    ∃ e : Diffeomorph J J N N ∞,
      SupportedDiffeomorph.IsotopicToIdentity e ∧
        (∀ j, (p j).Compatible (e ∘ f)) ∧
          ∀ j ∈ s, ∀ x ∈ (p j).core, ∀ y, At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    refine
      ⟨Diffeomorph.refl J N ∞, SupportedDiffeomorph.isotopicToIdentity_refl, hcompatible,
        ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, hiso₁, hc₁, ht₁⟩ := ih
    let C : Set X := ⋃ j ∈ s, (p j).core
    have hC : IsCompact C := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ C, ∀ y, At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, -, hiso₂⟩ :=
      exists_patch_step p i (e₁.contMDiff.comp hf) hg hc₁ hdim hC htrans
    refine ⟨e₁.trans e₂, hiso₁.trans hiso₂, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

/-- An ambient diffeomorphism making the map transverse. -/
theorem NativeTransversality.exists_ambient_transverse_diffeomorph
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [CompactSpace X] [T2Space X] {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞,
      SupportedDiffeomorph.IsotopicToIdentity e ∧ ∀ x y, At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx using fun x : X => exists_patch_at (J := J) hf.continuous x
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover (fun x : X => interior (p x).core)
      (fun _ => isOpen_interior) hcover
  obtain ⟨e, hisotopy, -, ht⟩ :=
    exists_finite_patch_diffeomorph (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim Finset.univ
  refine ⟨e, hisotopy, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

/-- Under the dimension bound an ambient diffeomorphism makes the ranges disjoint. -/
theorem MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    ∃ e : Diffeomorph J J N N ∞,
      SupportedDiffeomorph.IsotopicToIdentity e ∧
        Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' :
    Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) + Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  obtain ⟨e, he, ht⟩ :=
    NativeTransversality.exists_ambient_transverse_diffeomorph hf' hg hdim'
  have htrans : ∀ x y, NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Hemisphere.Sphere d := Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, he, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩
