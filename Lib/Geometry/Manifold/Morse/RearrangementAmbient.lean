/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.AlgebraicTopology.SingularHomology.LocalDegreeNeighborhoods

/-!
# Ambient patches for rearrangement

This file contains the geometric ingredient of the reordering of the critical points of a Morse
function by index (Milnor, *Lectures on the h-cobordism theorem*, §4); the combinatorial
ingredient, the inversion count, is `Lib/Combinatorics/IndexDisorder.lean`.

**General position by a compactly supported ambient isotopy.**  For smooth maps `f : X → N`,
`g : Y → N` of compact manifolds, `f` can be moved by a diffeomorphism `e` of `N`, isotopic to
the identity through an isotopy supported in a compact subset of a prescribed open set and fixing
a prescribed closed set, so that `e ∘ f` is transverse to `g` when `dim X + dim Y = dim N`, and
has image disjoint from that of `g` when `dim X + dim Y < dim N`
(`exists_supported_ambient_transverse_in_open`, `exists_supported_ambient_disjoint_in_open`,
`exists_supported_ambient_disjoint_fixing_closed`, `exists_whole_family_avoidance`).  This is
general position by isotopy, Hirsch, *Differential Topology*, Ch. 3.  It is proved patch by patch
(`exists_ambient_patch_in_open`, `exists_relative_ambient_patch_step`,
`exists_finite_relative_patch_diffeomorph`), the patches being composed by
`compose_supported_ambient_isotopies`; a finite family of sources is replaced by a single source
through the iterated disjoint union `sheetSum`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §4.
* [M. Hirsch, *Differential Topology*][hirsch76], Ch. 3 (general position by isotopy).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- A compactly supported bump in a chart gives, for all small enough translation vectors `a`,
a supported relative isotopy of the bump diffeomorphism: it is supported in the image of the
support of the bump and fixes any set `C` disjoint from that image. -/
theorem MorseRearrangement.exists_radius_supported_bump_preparation {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source)
    {C : Set M} (hC : ∀ y ∈ C, y ∉ Φ '' tsupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∀ e : Diffeomorph J J M M ∞,
              (∀ y, e y = SupportedDiffeomorph.bumpFamily Φ β (a, y)) →
                Nonempty
                  (SupportedDiffeomorph.SupportedRelativeIsotopy e (Φ '' tsupport β) C) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    SupportedDiffeomorph.exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  have hone : ∀ y, A (1, y) = e y := by
    intro y
    rw [he]
    by_cases hy : y ∈ Φ.target
    · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
      have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
      rw [hpoint] at hh
      change A (1, y) = SupportedDiffeomorph.extendMap Φ (fun x => x + β x • a) y
      rw [SupportedDiffeomorph.extendMap_of_mem Φ _ hy]
      exact hh
    · have hnot : y ∉ Φ '' tsupport β := by
        rintro ⟨x, hx, rfl⟩
        exact hy (Φ.map_source' (hsupport hx))
      rw [hfix 1 y hnot, SupportedDiffeomorph.bumpFamily_fixed_outside Φ β a hnot]
  refine
    ⟨{  family := A
        smooth := hA
        zero := hzero
        one := hone
        slices := ?_
        fixedOutside := hfix
        fixedOn := fun t y hy => hfix t y (hC y hy) }⟩
  intro t
  obtain ⟨d, hd⟩ := hdiff t
  exact ⟨d, fun y => (hd y).symm⟩

/-- The image in `N` of the support of the cutoff of a patch is compact. -/
theorem MorseRearrangement.ambient_patch_support_compact {G K N X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] [TopologicalSpace X]
    (p : NativeTransversality.Patch J X (N := N)) :
    IsCompact (p.chart.symm '' tsupport p.cutoff) :=
  p.cutoff_compact.isCompact.image_of_continuousOn
    (p.chart.contMDiffOn_invFun.continuousOn.mono p.cutoff_support)

/-- Every point of a compact source has a patch compatible with `f`, containing it in the
interior of its core, and with support contained in a prescribed open neighbourhood of its
image. -/
theorem MorseRearrangement.exists_ambient_patch_in_open {G K N X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] [TopologicalSpace X] [FiniteDimensional ℝ G]
    [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N}
    (hf : Continuous f) {U : Set N} (hU : IsOpen U) (x : X) (hfxU : f x ∈ U) :
    ∃ p : NativeTransversality.Patch J X (N := N),
      p.Compatible f ∧ x ∈ interior p.core ∧ p.chart.symm '' tsupport p.cutoff ⊆ U := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  let V : Set G := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcv : c (f x) ∈ V :=
    ⟨c.map_source' hcx, by
      change c.symm (c (f x)) ∈ U
      have heq : c.symm (c (f x)) = f x := c.left_inv' hcx
      rw [heq]
      exact hfxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcv)
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
  let p : NativeTransversality.Patch J X (N := N) :=
    { core := C
      core_compact := hC
      chart := c
      cutoff := β
      cutoff_smooth := hβ
      cutoff_compact := hcompact
      cutoff_support := hsupport.trans (hball.trans Set.inter_subset_left)
      plateau := O
      plateau_open := hO
      plateau_source := Set.inter_subset_left
      plateau_one := by
        intro y hy
        filter_upwards [hW.mem_nhds hy.2] with z hz
        exact hone hz }
  refine ⟨p, hCO, hxC (Set.mem_singleton x), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hball (hsupport hz)).2

/-- One patch of the general-position induction: if `f` is already transverse to `g` on a
compact set `B`, there is a diffeomorphism `e` of `N`, supported in the patch `p i` and fixing a
set `C` disjoint from that patch, making `e ∘ f` transverse to `g` on `B ∪ (p i).core` while
keeping all patches compatible.  The dimension hypothesis is `dim X + dim Y = dim N`. -/
theorem MorseRearrangement.exists_relative_ambient_patch_step {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι]
    (p : ι → NativeTransversality.Patch J X (N := N)) (i : ι) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {B : Set X}
    (hB : IsCompact B) (htrans : ∀ x ∈ B, ∀ y, NativeTransversality.At I I' J f g x y)
    {C : Set N} (hC : ∀ y ∈ C, y ∉ (p i).chart.symm '' tsupport (p i).cutoff) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
        (∀ x ∈ B ∪ (p i).core, ∀ y, NativeTransversality.At I I' J (e ∘ f) g x y) ∧
          Nonempty
            (SupportedDiffeomorph.SupportedRelativeIsotopy e
              ((p i).chart.symm '' tsupport (p i).cutoff) C) := by
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
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ z ∈ B ×ˢ (Set.univ : Set Y),
        NativeTransversality.At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply
      NativeTransversality.eventually_on_compact Metric.isOpen_ball hA hg hdim
        (hB.prod isCompact_univ) (Metric.mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨η, hη, hisotopy⟩ :=
    exists_radius_supported_bump_preparation (p i).chart.symm (p i).cutoff_smooth
      (p i).cutoff_compact (p i).cutoff_support hC
  obtain ⟨a, ha, e, he, -, -, hnew⟩ :=
    ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim (lt_min hε hη)
  have hgood :=
    hsmall
      (show a ∈ Metric.ball (0 : G) ε by
        simpa only [Metric.mem_ball, dist_zero_right] using (lt_min_iff.mp ha).1)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hisotopy a (lt_min_iff.mp ha).2 e he⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, Set.mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

/-- Two supported relative isotopies fixing the same set compose: the composite diffeomorphism
is supported in the union of the two supports and still fixes that set. -/
def MorseRearrangement.compose_supported_ambient_isotopies {G K N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] {e d : Diffeomorph J J N N ∞} {K₁ K₂ C : Set N}
    (A : SupportedDiffeomorph.SupportedRelativeIsotopy e K₁ C)
    (B : SupportedDiffeomorph.SupportedRelativeIsotopy d K₂ C) :
    SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K₁ ∪ K₂) C
    where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = d (e x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)), B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

/-- Iterating `exists_relative_ambient_patch_step` over a finite set of patches: there is a
diffeomorphism `e` of `N`, isotopic to the identity through an isotopy supported in a compact
subset of `U` and fixing `Uᶜ`, keeping all patches compatible and making `e ∘ f` transverse to
`g` on the core of every patch in the given finite set. -/
theorem MorseRearrangement.exists_finite_relative_patch_diffeomorph
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [LindelofSpace (X × Y)] {ι : Type*}
    [Finite ι] (p : ι → NativeTransversality.Patch J X (N := N)) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {U : Set N}
    (hsupport : ∀ j, (p j).chart.symm '' tsupport (p j).cutoff ⊆ U) (s : Finset ι) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            (∀ j, (p j).Compatible (e ∘ f)) ∧
              ∀ j ∈ s,
                ∀ x ∈ (p j).core, ∀ y, NativeTransversality.At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    let A : SupportedDiffeomorph.SupportedRelativeIsotopy (Diffeomorph.refl J N ∞) ∅ Uᶜ :=
      { family := Prod.snd
        smooth := contMDiff_snd
        zero := fun _ => rfl
        one := fun _ => rfl
        slices := fun _ => ⟨Diffeomorph.refl J N ∞, fun _ => rfl⟩
        fixedOutside := fun _ _ _ => rfl
        fixedOn := fun _ _ _ => rfl }
    refine ⟨Diffeomorph.refl J N ∞, ∅, isCompact_empty, Set.empty_subset _, ⟨A⟩, hcompatible, ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, C₁, hC₁, hC₁U, ⟨A₁⟩, hc₁, ht₁⟩ := ih
    let B : Set X := ⋃ j ∈ s, (p j).core
    have hB : IsCompact B := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ B, ∀ y, NativeTransversality.At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, ⟨A₂⟩⟩ :=
      exists_relative_ambient_patch_step (C := Uᶜ) p i (e₁.contMDiff.comp hf) hg hc₁ hdim hB
        htrans (fun y hy hys => hy (hsupport i hys))
    refine
      ⟨e₁.trans e₂, C₁ ∪ ((p i).chart.symm '' tsupport (p i).cutoff),
        hC₁.union (ambient_patch_support_compact (p i)), Set.union_subset hC₁U (hsupport i),
        ⟨compose_supported_ambient_isotopies A₁ A₂⟩, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

/-- General position by ambient isotopy: for `f : X → N` with `X` compact and image in an open
`U`, and `dim X + dim Y = dim N`, there is a diffeomorphism `e` of `N`, isotopic to the identity
through an isotopy supported in a compact subset of `U` and fixing `Uᶜ`, with `e ∘ f` transverse
to `g` everywhere (Hirsch, *Differential Topology*, Ch. 3). -/
theorem MorseRearrangement.exists_supported_ambient_transverse_in_open
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [CompactSpace X] [T2Space X] {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {U : Set N}
    (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            ∀ x y, NativeTransversality.At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx hs using fun x : X =>
    exists_ambient_patch_in_open (J := J) hf.continuous hU x (hfU (Set.mem_range_self x))
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hscover⟩ :=
    isCompact_univ.elim_finite_subcover (fun x : X => interior (p x).core)
      (fun _ => isOpen_interior) hcover
  obtain ⟨e, C, hC, hCU, hIso, -, ht⟩ :=
    exists_finite_relative_patch_diffeomorph (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim
      (fun i => hs i.1) Finset.univ
  refine ⟨e, C, hC, hCU, hIso, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hscover (Set.mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

/-- Same statement below the transversality dimension: if `dim X + dim Y < dim N`, the ambient
isotopy can be chosen so that the images of `e ∘ f` and `g` are disjoint. -/
theorem MorseRearrangement.exists_supported_ambient_disjoint_in_open
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {U : Set N}
    (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
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
  have hf'U : Set.range f' ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact hfU (Set.mem_range_self x.1)
  obtain ⟨e, C, hC, hCU, hIso, ht⟩ :=
    exists_supported_ambient_transverse_in_open hf' hg hdim' hU hf'U
  have htrans : ∀ x y, NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Hemisphere.Sphere d := Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, C, hC, hCU, hIso, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

/-- Disjunction by an ambient isotopy fixing a prescribed closed set `C` disjoint from the
image of `f`, again when `dim X + dim Y < dim N`. -/
theorem MorseRearrangement.exists_supported_ambient_disjoint_fixing_closed
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {C : Set N}
    (hC : IsClosed C) (hfC : Disjoint (Set.range f) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧
        K ⊆ Cᶜ ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy e K C) ∧
            Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  have hfU : Set.range f ⊆ Cᶜ := fun _ hx hy => Set.disjoint_left.mp hfC hx hy
  obtain ⟨e, K, hK, hKU, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_in_open hf hg hdim hC.isOpen_compl hfU
  refine ⟨e, K, hK, hKU, ?_, hdisj⟩
  simpa only [compl_compl] using hIso

/-- The union of the images of all members of a family except the `i`-th. -/
def MorseRearrangement.otherSheetImages {ι X N : Type*} (a : ι → X → N) (i : ι) : Set N :=
  ⋃ j : { j : ι // j ≠ i }, Set.range (a j.val)

/-- A value of the `j`-th member of a family, `j ≠ i`, lies in `otherSheetImages a i`. -/
theorem MorseRearrangement.mem_otherSheetImages {ι X N : Type*} (a : ι → X → N) (i j : ι)
    (hji : j ≠ i) (x : X) : a j x ∈ otherSheetImages a i :=
  Set.mem_iUnion.mpr ⟨⟨j, hji⟩, Set.mem_range_self x⟩

universe u

/-- The disjoint union of `n` copies of `X`, defined by recursion on `n`. -/
def MorseRearrangement.sheetSum (X : Type u) : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => X ⊕ sheetSum X n

/-- `sheetSum X n` carries the disjoint-union topology. -/
instance MorseRearrangement.sheetSumTopology {X : Type*} [TopologicalSpace X] :
    (n : ℕ) → TopologicalSpace (sheetSum X n)
  | 0 => inferInstanceAs (TopologicalSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumTopology (X := X) n
    inferInstanceAs (TopologicalSpace (X ⊕ sheetSum X n))

/-- A finite disjoint union of compact spaces is compact. -/
instance MorseRearrangement.sheetSumCompact {X : Type*} [TopologicalSpace X]
    [CompactSpace X] : (n : ℕ) → CompactSpace (sheetSum X n)
  | 0 => inferInstanceAs (CompactSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumCompact (X := X) n
    inferInstanceAs (CompactSpace (X ⊕ sheetSum X n))

/-- A finite disjoint union of Hausdorff spaces is Hausdorff. -/
instance MorseRearrangement.sheetSumT2 {X : Type*} [TopologicalSpace X] [T2Space X] :
    (n : ℕ) → T2Space (sheetSum X n)
  | 0 => inferInstanceAs (T2Space PEmpty)
  | n + 1 =>
    let _ := sheetSumT2 (X := X) n
    inferInstanceAs (T2Space (X ⊕ sheetSum X n))

/-- A finite disjoint union of second-countable spaces is second countable. -/
instance MorseRearrangement.sheetSumSecondCountable {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] : (n : ℕ) → SecondCountableTopology (sheetSum X n)
  | 0 => inferInstanceAs (SecondCountableTopology PEmpty)
  | n + 1 =>
    let _ := sheetSumSecondCountable (X := X) n
    inferInstanceAs (SecondCountableTopology (X ⊕ sheetSum X n))

/-- A finite disjoint union of charted spaces on `H` is a charted space on `H`. -/
instance MorseRearrangement.sheetSumChartedSpace {X : Type*} [TopologicalSpace X] {H : Type*}
    [TopologicalSpace H] [ChartedSpace H X] : (n : ℕ) → ChartedSpace H (sheetSum X n)
  | 0 => ChartedSpace.empty H PEmpty
  | n + 1 =>
    let _ := sheetSumChartedSpace (X := X) (H := H) n
    inferInstanceAs (ChartedSpace H (X ⊕ sheetSum X n))

/-- A finite disjoint union of smooth manifolds is a smooth manifold. -/
instance MorseRearrangement.sheetSumIsManifold {X : Type*} [TopologicalSpace X] {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [ChartedSpace H X] [IsManifold I ∞ X] : (n : ℕ) → IsManifold I ∞ (sheetSum X n)
  | 0 =>
    let _ : ChartedSpace H PEmpty := sheetSumChartedSpace (X := X) 0
    inferInstanceAs (IsManifold I ∞ PEmpty)
  | n + 1 =>
    let _ := sheetSumIsManifold (X := X) (I := I) n
    inferInstanceAs (IsManifold I ∞ (X ⊕ sheetSum X n))

/-- The map out of `sheetSum X n` assembled from a family of `n` maps `X → N`. -/
def MorseRearrangement.sheetSumMap {X : Type*} {N : Type*} :
    (n : ℕ) → (Fin n → X → N) → sheetSum X n → N
  | 0, _, x => x.elim
  | n + 1, a, x => Sum.elim (a 0) (sheetSumMap n (fun i => a i.succ)) x

/-- The image of the assembled map is the union of the images of the family. -/
theorem MorseRearrangement.range_sheetSumMap {X : Type*} [TopologicalSpace X] {N : Type*}
    (n : ℕ) (a : Fin n → X → N) : Set.range (sheetSumMap n a) = ⋃ i, Set.range (a i) := by
  induction n with
  | zero =>
    ext y
    simp only [Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro ⟨x, _⟩
      exact x.elim
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    ext y
    constructor
    · rintro ⟨x, hx⟩
      rcases x with x | x
      · exact Set.mem_iUnion.mpr ⟨0, ⟨x, hx⟩⟩
      · have hy : y ∈ Set.range (sheetSumMap n (fun i => a i.succ)) := ⟨x, hx⟩
        rw [ih] at hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion.mpr ⟨i.succ, hi⟩
    · intro hy
      obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hy
      cases i using Fin.cases with
      | zero => exact ⟨Sum.inl x, hx⟩
      | succ
        i =>
        have hy' : y ∈ ⋃ i : Fin n, Set.range (a i.succ) := Set.mem_iUnion.mpr ⟨i, ⟨x, hx⟩⟩
        rw [← ih] at hy'
        obtain ⟨z, hz⟩ := hy'
        exact ⟨Sum.inr z, hz⟩

/-- The assembled map is smooth when each member of the family is. -/
theorem MorseRearrangement.contMDiff_sheetSumMap {X : Type*} [TopologicalSpace X]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {G K N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] (n : ℕ) (a : Fin n → X → N) (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ContMDiff I J ∞ (sheetSumMap n a) := by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih => exact (ha 0).sumElim (ih (fun i => a i.succ) (fun i => ha i.succ))

/-- A finite family of smooth maps `X → N` is the assembly of a single smooth map out of a
finite disjoint union of copies of `X`, with the same image. -/
theorem MorseRearrangement.exists_sheetSumMap_for_finite_family {X : Type*}
    [TopologicalSpace X] {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {G K N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] {ι : Type*} [Finite ι] (a : ι → X → N)
    (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ∃ (n : ℕ) (b : sheetSum X n → N), ContMDiff I J ∞ b ∧ Set.range b = ⋃ i, Set.range (a i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let a' : Fin (Fintype.card ι) → X → N := fun j => a (e.symm j)
  refine
    ⟨Fintype.card ι, sheetSumMap (Fintype.card ι) a',
      contMDiff_sheetSumMap _ a' (fun j => ha (e.symm j)), ?_⟩
  rw [range_sheetSumMap]
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨e.symm j, hj⟩
  · intro hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨e i, ?_⟩
    simpa only [a', e.symm_apply_apply] using hi

/-- Simultaneous disjunction: a finite family of smooth maps `a j : X → N`, all with image
disjoint from a closed set `C`, can be moved by a single ambient isotopy fixing `C` so that every
`e ∘ a j` has image disjoint from that of `g`, provided `dim X + dim Y < dim N`. -/
theorem MorseRearrangement.exists_whole_family_avoidance {ι D Z G H H' K X Y N : Type*}
    [Finite ι] [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] (a : ι → X → N)
    (ha : ∀ j, ContMDiff I J ∞ (a j)) {g : Y → N} (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {C : Set N}
    (hC : IsClosed C) (haC : ∀ j, Disjoint (Set.range (a j)) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧
        K ⊆ Cᶜ ∧
          Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy e K C) ∧
            ∀ j, Disjoint (Set.range (e ∘ a j)) (Set.range g) := by
  obtain ⟨n, b, hb, hbrange⟩ := exists_sheetSumMap_for_finite_family a ha
  have hbC : Disjoint (Set.range b) C := by
    apply Set.disjoint_left.mpr
    intro z hz hzC
    rw [hbrange] at hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (haC j) hj hzC
  obtain ⟨e, K, hK, hKC, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_fixing_closed hb hg hdim hC hbC
  refine ⟨e, K, hK, hKC, hIso, ?_⟩
  intro j
  apply Set.disjoint_left.mpr
  intro z hz hzg
  obtain ⟨x, hx⟩ := hz
  have hx' : a j x ∈ Set.range b := by
    rw [hbrange]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩
  obtain ⟨w, hw⟩ := hx'
  apply Set.disjoint_left.mp hdisj _ hzg
  refine ⟨w, ?_⟩
  change e (b w) = z
  rw [hw]
  exact hx


end
