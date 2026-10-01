/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetParametrizedChart

/-!
# Compatible charts of a tubular bigon

A rank-three compatible chart (`TubularBigon.RankThreeCompatibleChart`) of a tubular bigon with
sheets `S`, `T` is a chart in the coordinates of the rank-three model, containing a product
neighbourhood of the bigon and extending its tubular map on the zero section, which meets `S`
exactly in the model lower sheet and `T` exactly in the model upper sheet. Restricting a
sheet-parametrised chart to its recognition neighbourhood gives one, so one exists for closed
sheets when the two corner intersection signs are opposite
(`TubularBigon.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs`). In such a chart the
images of the model sheets are the parts of `S` and `T` in its target, and `S ∩ T` meets the target
exactly in the two corners `a 0`, `a 1` of the bigon
(`TubularBigon.RankThreeCompatibleChart.intersection_in_target_eq`).

This is the standard neighbourhood of a Whitney disc: Milnor, *Lectures on the h-cobordism
theorem*, §6 (Whitney's lemma).

## Tags

Whitney trick, Whitney disc, chart
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- A compatible chart of a rank-three tubular bigon: a chart in the rank-three model coordinates
which meets the two sheets exactly in the two model sheets. -/
structure TubularBigon.RankThreeCompatibleChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  first_sheet :
    ∀ z ∈ chart.source, chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet
  second_sheet :
    ∀ z ∈ chart.source, chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h)

/-- Restricting a sheet-parametrised chart to the recognition neighbourhood gives a compatible
chart. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.nonempty_rankThreeCompatibleChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) : Nonempty (TubularBigon.RankThreeCompatibleChart tube) := by
  obtain ⟨U, hU, hKU, hUsource, hfirst, hsecond⟩ := c.exists_open_full_sheet_neighborhood hS hT
  have hlocal :
    IsLocalDiffeomorphOn 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E) ∞ c.chart U := fun z =>
    ⟨c.chart, hUsource z.property, fun _ _ => rfl⟩
  let Φ :=
    partialDiffeomorphOfInjectiveLocal hU (c.chart.toPartialEquiv.injOn.mono hUsource)
      hlocal
  have hzero :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      Φ.source :=
    hKU
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset
      (WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzero
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := c.zero_section
        target_subset := ?_
        first_sheet := hfirst
        second_sheet := hsecond }⟩
  intro y hy
  change y ∈ c.chart '' U at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact c.target_subset (c.chart.map_source' (hUsource hz))

/-- The Whitney condition gives a compatible chart: if the two corner intersection signs are
opposite, a rank-three compatible chart exists. -/
theorem TubularBigon.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeCompatibleChart tube) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeCompatibleChart hS hT

/-- In a compatible chart, the image of the model lower sheet is the part of the first sheet in the
target. -/
theorem TubularBigon.RankThreeCompatibleChart.nativeFirstSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    RankThreeWhitneyModel.nativeFirstSheet c.chart = S ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.first_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.first_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ S
    rw [hzy]
    exact hy.1

/-- In a compatible chart, the image of the model upper sheet is the part of the second sheet in the
target. -/
theorem TubularBigon.RankThreeCompatibleChart.nativeSecondSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    RankThreeWhitneyModel.nativeSecondSheet c.chart h = T ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.second_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.second_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ T
    rw [hzy]
    exact hy.1


/-- In the target of a compatible chart the two sheets meet exactly at the two corners `a 0` and `a
1` of the bigon. -/
theorem TubularBigon.RankThreeCompatibleChart.intersection_in_target_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    (S ∩ T) ∩ c.chart.target = {a 0, a 1} := by
  have hc0 : c.chart (RankThreeWhitneyModel.firstSheet (-1, 0)) = a 0 := by
    calc
      c.chart (RankThreeWhitneyModel.firstSheet (-1, 0)) = tube.map (-1, 0) :=
        c.zero_section (-1, 0)
      _ = a 0 := by simpa using tube.lower 0 (by simp)
  have hc1 : c.chart (RankThreeWhitneyModel.firstSheet (1, 0)) = a 1 := by
    calc
      c.chart (RankThreeWhitneyModel.firstSheet (1, 0)) = tube.map (1, 0) :=
        c.zero_section (1, 0)
      _ = a 1 := by
        have he := tube.lower 1 (by simp)
        norm_num at he
        exact he
  have hcorner :
    ∀ s : ℝ,
      s = -1 ∨ s = 1 →
        c.chart (RankThreeWhitneyModel.firstSheet (s, 0)) ∈ (S ∩ T) ∩ c.chart.target := by
    intro s hs
    have hb : (s, (0 : ℝ)) ∈ WhitneyPairModel.bigon h := by
      rcases hs with rfl | rfl <;> simp [WhitneyPairModel.bigon]
    have hsource : RankThreeWhitneyModel.firstSheet (s, 0) ∈ c.chart.source :=
      c.source_contains ⟨hb, Metric.mem_closedBall_self c.radius_pos.le⟩
    refine
      ⟨⟨(c.first_sheet _ hsource).mpr ⟨(s, 0), rfl⟩, (c.second_sheet _ hsource).mpr ?_⟩,
        c.chart.map_source' hsource⟩
    refine ⟨(s, 0), ?_⟩
    rcases hs with rfl | rfl <;>
      simp [RankThreeWhitneyModel.firstSheet, RankThreeWhitneyModel.secondSheet]
  ext y
  change y ∈ (S ∩ T) ∩ c.chart.target ↔ y = a 0 ∨ y = a 1
  constructor
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    have hlo : c.chart.symm y ∈ Set.range RankThreeWhitneyModel.firstSheet := by
      apply (c.first_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ S
      rw [hzy]
      exact hy.1.1
    have hhi : c.chart.symm y ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
      apply (c.second_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ T
      rw [hzy]
      exact hy.1.2
    obtain ⟨p, hp⟩ := hlo
    obtain ⟨q, hq⟩ := hhi
    obtain ⟨hst, hu, _, hends⟩ :=
      (RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff tube.height_pos p q).mp
        (hp.trans hq.symm)
    have hpq : p = (q.1, 0) := Prod.ext hst hu
    rw [hpq] at hp
    have hycorner : y = c.chart (RankThreeWhitneyModel.firstSheet (q.1, 0)) :=
      hzy.symm.trans (congrArg c.chart hp.symm)
    rcases hends with hm | hp
    · left
      rw [hm] at hycorner
      exact hycorner.trans hc0
    · right
      rw [hp] at hycorner
      exact hycorner.trans hc1
  · rintro (rfl | rfl)
    · rw [← hc0]
      exact hcorner (-1) (Or.inl rfl)
    · rw [← hc1]
      exact hcorner 1 (Or.inr rfl)


end
