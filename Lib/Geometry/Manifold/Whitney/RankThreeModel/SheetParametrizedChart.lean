/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.RankThreeModel.CorrectedCoordinates
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRecognition

/-!
# Sheet-parametrised charts of a tubular bigon

A rank-three sheet-parametrised chart (`TubularBigon.RankThreeSheetParametrizedChart`) is a chart
of the tubular neighbourhood in the coordinates of the rank-three model which on the model lower
and upper sheets is the strip chart of the first and second sheet, read in the retimed parameter.
The corrected coordinates of a tangent-adapted chart give one
(`TubularBigon.RankThreeTangentAdaptedChart.nonempty_rankThreeSheetParametrizedChart`), hence one
exists when the two corner intersection signs are opposite
(`TubularBigon.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs`). Such a chart
meets the two sheets exactly in the model sheets near every model sheet point
(`eventually_lower_mem_iff`, `eventually_upper_mem_iff`) and, for closed sheets, on an open
neighbourhood of the zero section of the bigon (`exists_open_full_sheet_neighborhood`).
`TubularBigon.SheetParametrizedChart` is the same notion in the Whitney pair model.

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

Whitney trick, chart, submanifold
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- A sheet-parametrised chart of a rank-three tubular bigon: a chart in the coordinates of the
rank-three model which on the two model sheets is the strip chart of the corresponding sheet,
read in the retimed parameter. -/
structure TubularBigon.RankThreeSheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : RankThreeWhitneyModel.LowerSheet,
      RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : RankThreeWhitneyModel.UpperSheet,
      RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
          e.chart.source
  lower :
    ∀ q : RankThreeWhitneyModel.LowerSheet,
      RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        chart (RankThreeWhitneyModel.firstSheet q) =
          d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : RankThreeWhitneyModel.UpperSheet,
      RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        chart (RankThreeWhitneyModel.secondSheet h q) =
          e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)

/-- The corrected coordinates of a tangent-adapted chart give a sheet-parametrised chart. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.nonempty_rankThreeSheetParametrizedChart
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Nonempty (TubularBigon.RankThreeSheetParametrizedChart tube d e) := by
  have hinj :
    Set.InjOn c.correctedCoordinates
      (WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)}) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩ ⟨q, w⟩ ⟨hq, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [c.correctedCoordinates_zero, c.correctedCoordinates_zero] at heq
    exact Prod.ext (congrArg (fun v : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3) => v.1) heq) rfl
  have hlocal :
    ∀
      p ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      IsLocalDiffeomorphAt 𝓘(ℝ, RankThreeWhitneyModel.Space)
        𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) ∞ c.correctedCoordinates p := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      isLocalDiffeomorphAt_of_contMDiffOn (D := RankThreeWhitneyModel.Space) (E :=
        (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) (M := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3))
        c.isOpen_nonlinearDomain (c.nonlinearDomain_contains_zero hp)
        c.contDiffOn_correctedCoordinates.contMDiffOn
    rw [mfderiv_eq_fderiv, (c.hasFDerivAt_correctedCoordinates_zero hp).fderiv]
    exact
      FrameField.isInvertible_shearedBlock (c.base p) (c.normal p)
        (c.normal_invertible p (c.contains hp))
  have hzeroDomain :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      c.nonlinearDomain := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.nonlinearDomain_contains_zero hp
  obtain ⟨χ, hzeroχ, hχD, hχ⟩ :=
    exists_partialDiffeomorph_near_compact
      ((WhitneyPairModel.isCompact_bigon tube.height_pos).prod isCompact_singleton) hinj
      hlocal c.isOpen_nonlinearDomain hzeroDomain
  let Φ := χ.trans tube.chart
  have hzeroΦ :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      Φ.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hp, rfl⟩, ?_⟩
    change χ (p, 0) ∈ tube.chart.source
    rw [hχ, c.correctedCoordinates_zero]
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, hsource⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset
      (WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzeroΦ
  have hformula (p : RankThreeWhitneyModel.Space) :
    Φ p = tube.chart (c.correctedCoordinates p) := by
    change tube.chart (χ p) = tube.chart (c.correctedCoordinates p)
    rw [hχ]
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        target_subset := fun _ hy => hy.1
        lower_source := fun q hq => (c.lower_native_parameters (hχD hq.1)).1
        upper_source := fun q hq => (c.upper_native_parameters (hχD hq.1)).1
        lower := ?_
        upper := ?_ }⟩
  · intro p
    rw [hformula, c.correctedCoordinates_zero, tube.zero_section]
  · intro q hq
    rw [hformula, c.correctedCoordinates_lower_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.lower_native_parameters (hχD hq.1)).2
  · intro q hq
    rw [hformula, c.correctedCoordinates_upper_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.upper_native_parameters (hχD hq.1)).2

/-- The Whitney condition gives a sheet-parametrised chart: if the two corner intersection signs are
opposite, a rank-three sheet-parametrised chart exists. -/
theorem TubularBigon.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs
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
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeSheetParametrizedChart tube d e) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeSheetParametrizedChart

/-- In a sheet-parametrised chart, the model lower sheet lands in the first sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.lower_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    c.chart (RankThreeWhitneyModel.firstSheet q) ∈ S := by
  rw [c.lower q hq]
  exact (d.sheet _ (c.lower_source q hq)).mpr rfl

/-- In a sheet-parametrised chart, the model upper sheet lands in the second sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.upper_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    c.chart (RankThreeWhitneyModel.secondSheet h q) ∈ T := by
  rw [c.upper q hq]
  exact (e.sheet _ (c.upper_source q hq)).mpr rfl


/-- Near a point of the model lower sheet, a sheet-parametrised chart meets the first sheet exactly
in the model lower sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.eventually_lower_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (RankThreeWhitneyModel.firstSheet q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart d.chart d.sheet
    RankThreeWhitneyModel.contDiff_firstSheet.continuous
    WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    WhitneyPairModel.sheetTimeInverse_leftInverse
    WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.lower_source q hq, c.lower q hq⟩) hq

/-- Near a point of the model upper sheet, a sheet-parametrised chart meets the second sheet exactly
in the model upper sheet. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.eventually_upper_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      StripNormalData RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      StripNormalData RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (RankThreeWhitneyModel.secondSheet h q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h)) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart e.chart e.sheet
    (RankThreeWhitneyModel.contDiff_secondSheet h).continuous
    WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    WhitneyPairModel.sheetTimeInverse_leftInverse
    WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.upper_source q hq, c.upper q hq⟩) hq

/-- The sheet-parametrised chart in the planar model: the variant of
`RankThreeSheetParametrizedChart` whose two sheet directions are planes. -/
structure TubularBigon.SheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 4)
    (d :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData WhitneyPairModel.Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T
        l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, WhitneyPairModel.Space) 𝓘(ℝ, E) WhitneyPairModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.firstSheet q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.secondSheet h q ∈ chart.source →
        (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          e.chart.source
  lower :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.firstSheet q ∈ chart.source →
        chart (WhitneyPairModel.firstSheet q) =
          d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : WhitneyPairModel.Sheet,
      WhitneyPairModel.secondSheet h q ∈ chart.source →
        chart (WhitneyPairModel.secondSheet h q) =
          e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0)


/-- A sheet-parametrised chart has an open neighbourhood of the zero section of the bigon on which
it meets the two sheets exactly in the two model sheets. -/
theorem TubularBigon.RankThreeSheetParametrizedChart.exists_open_full_sheet_neighborhood
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
    (hT : IsClosed T) :
    ∃ U : Set RankThreeWhitneyModel.Space,
      IsOpen U ∧
        WhitneyPairModel.bigon h ×ˢ
              {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
            U ∧
          U ⊆ c.chart.source ∧
            (∀ z ∈ U, c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet) ∧
              ∀ z ∈ U,
                c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
  have hzero :
    WhitneyPairModel.bigon h ×ˢ
        {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)} ⊆
      c.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩
  have hfirst :
    ∀
      z ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      c.chart z ∈ S ↔ z ∈ Set.range RankThreeWhitneyModel.firstSheet := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_first_iff hp).trans
        (RankThreeWhitneyModel.zero_mem_firstSheet_iff p).symm
  have hsecond :
    ∀
      z ∈
        WhitneyPairModel.bigon h ×ˢ
          {(0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)},
      c.chart z ∈ T ↔ z ∈ Set.range (RankThreeWhitneyModel.secondSheet h) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_second_iff hp).trans
        (RankThreeWhitneyModel.zero_mem_secondSheet_iff h p).symm
  obtain ⟨U, hU, hKU, hUsource, hUS⟩ :=
    SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range RankThreeWhitneyModel.firstSheet) hS hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.lower_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_lower_mem_iff hz)
      hfirst
  obtain ⟨V, hV, hKV, -, hVT⟩ :=
    SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range (RankThreeWhitneyModel.secondSheet h)) hT hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.upper_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_upper_mem_iff hz)
      hsecond
  exact
    ⟨U ∩ V, hU.inter hV, fun z hz => ⟨hKU hz, hKV hz⟩, fun _ hz => hUsource hz.1, fun z hz =>
      hUS z hz.1, fun z hz => hVT z hz.2⟩


end
