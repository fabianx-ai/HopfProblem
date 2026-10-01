/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs
import Lib.Geometry.Manifold.Whitney.RankThreeModel.Model

/-!
# Graph motions of the rank-three model and their transport to a manifold

A graph motion of the rank-three model (`RankThreeWhitneyModel.GraphMotion h U`) is a compactly
supported smooth ambient isotopy of the model, supported in `U`, preserving the horizontal and
normal coordinates, which pushes the lower sheet onto the graph of a height function lying above
the parabolic arc; one exists over every open neighbourhood of the zero section of the bigon
(`RankThreeWhitneyModel.nonempty_graphMotion`, obtained from the Whitney pair model through
`expand`/`collapse`), and after it the two model sheets are disjoint. Transported through a chart
`Φ` and extended by the identity, it gives a compactly supported ambient isotopy of the manifold,
supported in the target of `Φ`, whose time-one map pushes the image of the model lower sheet off the
image of the model upper sheet (`RankThreeWhitneyModel.exists_supported_native_bigon_cancellation`).

Milnor, *Lectures on the h-cobordism theorem*, §6 (the isotopy of Whitney's lemma).

## Tags

Whitney trick, isotopy, compact support
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- A graph motion of the rank-three model: the analogue of `WhitneyPairModel.GraphMotion` in the
model with the two normal directions. -/
structure RankThreeWhitneyModel.GraphMotion (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph height 1 s

/-- A graph motion of the rank-three model exists over any open neighbourhood of the zero section of
the bigon. -/
theorem RankThreeWhitneyModel.nonempty_graphMotion {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : ∀ p ∈ WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ U) :
    Nonempty (GraphMotion h U) := by
  let V : Set WhitneyPairModel.Space := collapse ⁻¹' U
  have hV : IsOpen V := hU.preimage collapse.continuous
  have hKV :
    Set.MapsTo WhitneyPairModel.bigonEmbedding (WhitneyPairModel.bigon h) V := by
    intro p hp
    change collapse (p, 0) ∈ U
    rw [collapse_zero]
    exact hKU p hp
  obtain ⟨g⟩ := WhitneyPairModel.nonempty_graphMotionData hh hV hKV
  obtain ⟨a⟩ := g.nonempty_graphMotion
  let A : ℝ × Space → Space := fun p => collapse (a.family (p.1, expand p.2))
  have hA : ContDiff ℝ ∞ A :=
    collapse.contDiff.comp
      (a.smooth.comp (contDiff_fst.prodMk (expand.contDiff.comp contDiff_snd)))
  refine
    ⟨{  height := g.height
        nonneg_height := g.nonneg_height
        above := g.above
        support := collapse '' a.support
        compact_support := a.compact_support.image collapse.continuous
        support_subset := ?_
        family := A
        smooth := hA
        initial := ?_
        diffeomorph := ?_
        fixed := ?_
        horizontal := ?_
        normal := ?_
        tracking := ?_ }⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact a.support_subset hz
  · intro z
    change collapse (a.family (0, expand z)) = z
    rw [a.initial, collapse_expand]
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hn : ∀ z, (d z).2 = z.2 := by
      intro z
      rw [hd]
      exact a.normal t z
    refine
      ⟨FiberRestriction.restrict normalInclude normalProject normalProject_include d hn, ?_⟩
    intro z
    change collapse (d (expand z)) = collapse (a.family (t, expand z))
    rw [hd]
  · intro t z hz
    have hz' : expand z ∉ a.support := fun hs => hz ⟨expand z, hs, collapse_expand z⟩
    change collapse (a.family (t, expand z)) = z
    rw [a.fixed t _ hz', collapse_expand]
  · intro t z
    change (a.family (t, expand z)).1.1 = z.1.1
    rw [a.horizontal]
    rfl
  · intro t z
    change normalProject (a.family (t, expand z)).2 = z.2
    rw [a.normal]
    exact normalProject_include z.2
  · intro s
    have he : expand (firstSheet (s, 0)) = WhitneyPairModel.firstSheet (s, 0) :=
      expand_zero (s, 0)
    change collapse (a.family (1, expand (firstSheet (s, 0)))) = verticalGraph g.height 1 s
    rw [he, a.tracking, collapse_verticalGraph]

/-- After the rank-three graph motion the lower sheet has been pushed off the upper sheet. -/
theorem RankThreeWhitneyModel.GraphMotion.firstSheet_ne_secondSheet {h : ℝ}
    {U : Set RankThreeWhitneyModel.Space} (a : RankThreeWhitneyModel.GraphMotion h U)
    (hh : 0 < h) (p : RankThreeWhitneyModel.LowerSheet)
    (q : RankThreeWhitneyModel.UpperSheet) :
    a.family (1, RankThreeWhitneyModel.firstSheet p) ≠
      RankThreeWhitneyModel.secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : RankThreeWhitneyModel.Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : RankThreeWhitneyModel.Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : a.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [RankThreeWhitneyModel.verticalGraph,
      RankThreeWhitneyModel.secondSheet, one_mul] using
      congrArg (fun z : RankThreeWhitneyModel.Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ a.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (a.above q.1 habs).ne ht.symm


/-- The graph motion of the rank-three model, transported through a chart: a compactly supported
ambient isotopy of the manifold, supported in the target of the chart, whose time-one map pushes
the image of the model lower sheet off the image of the model upper sheet. -/
theorem RankThreeWhitneyModel.GraphMotion.exists_native_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) J
        RankThreeWhitneyModel.Space M ∞)
    {h : ℝ} (a : RankThreeWhitneyModel.GraphMotion h Φ.source) (hh : 0 < h) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint
                      ((fun y => A (1, y)) '' RankThreeWhitneyModel.nativeFirstSheet Φ)
                      (RankThreeWhitneyModel.nativeSecondSheet Φ h) := by
  have hsource : ∀ t, Set.MapsTo (fun z => a.family (t, z)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    intro z hz
    change a.family (t, z) ∈ Φ.source
    rw [← hd z]
    exact SupportedDiffeomorph.mapsTo_source Φ d.toEquiv a.support_subset hdfix hz
  let A : ℝ × M → M := fun p =>
    SupportedDiffeomorph.extendMap Φ (fun z => a.family (p.1, z)) p.2
  have hcompact : IsCompact (Φ '' a.support) :=
    a.compact_support.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono a.support_subset)
  have htarget : Φ '' a.support ⊆ Φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Φ.map_source' (a.support_subset hz)
  have hfamily :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RankThreeWhitneyModel.Space))
      𝓘(ℝ, RankThreeWhitneyModel.Space) ∞ a.family := by
    exact a.smooth.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  refine
    ⟨Φ '' a.support, hcompact, htarget, A,
      SupportedDiffeomorph.contMDiff_extendFamily Φ hfamily a.compact_support
        a.support_subset a.fixed hsource,
      ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun z => a.family (0, z)) = id := funext a.initial
    change SupportedDiffeomorph.extendMap Φ (fun z => a.family (0, z)) y = y
    rw [hzero]
    exact SupportedDiffeomorph.extendMap_id Φ y
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    refine ⟨SupportedDiffeomorph.extension Φ d a.compact_support a.support_subset hdfix, ?_⟩
    intro y
    change
      SupportedDiffeomorph.extendMap Φ (fun z => a.family (t, z)) y =
        SupportedDiffeomorph.extendMap Φ d y
    exact
      congrArg
        (fun f : RankThreeWhitneyModel.Space → RankThreeWhitneyModel.Space =>
          SupportedDiffeomorph.extendMap Φ f y)
        (funext (fun z => (hd z).symm))
  · intro t y hy
    exact SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (a.fixed t) hy
  · rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨x, hx, hxy⟩ := hy₁
    obtain ⟨z, ⟨⟨p, hp⟩, hz⟩, hzx⟩ := hx
    obtain ⟨w, ⟨⟨q, hq⟩, hw⟩, hwy⟩ := hy₂
    have hleft : A (1, Φ z) = y := by rw [hzx]; exact hxy
    have hcomm : A (1, Φ z) = Φ (a.family (1, z)) :=
      SupportedDiffeomorph.extendMap_chart Φ (fun v => a.family (1, v)) hz
    have heq : a.family (1, z) = w :=
      Φ.toPartialEquiv.injOn (hsource 1 hz) hw (hcomm.symm.trans (hleft.trans hwy.symm))
    apply a.firstSheet_ne_secondSheet hh p q
    rw [hp, hq]
    exact heq

/-- The same cancellation with an explicit compact support inside the target of the chart. -/
theorem RankThreeWhitneyModel.exists_supported_native_bigon_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) {h : ℝ} (hh : 0 < h)
    (hsource : ∀ p ∈ WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ Φ.source) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint ((fun y => A (1, y)) '' nativeFirstSheet Φ)
                      (nativeSecondSheet Φ h) := by
  obtain ⟨a⟩ := nonempty_graphMotion hh Φ.open_source hsource
  exact a.exists_native_cancellation Φ hh


end
