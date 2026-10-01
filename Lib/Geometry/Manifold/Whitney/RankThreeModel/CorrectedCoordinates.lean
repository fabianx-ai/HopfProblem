/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetCorrection
import Lib.Geometry.Manifold.Whitney.RankThreeModel.TangentAdaptedChart

/-!
# Corrected coordinates of a tangent-adapted chart

For a rank-three tangent-adapted chart `c` of a tubular bigon, `c.shearedCoordinates` is the model
map of its base and normal blocks and `c.correctedCoordinates` is that map corrected along the two
model sheets (`RankThreeWhitneyModel.correctedSheetMap`) towards the retimed strip transitions of
the two sheets. The corrected coordinates agree with the sheared ones on the zero section, have the
same derivative there (`hasFDerivAt_correctedCoordinates_zero`), are smooth on an open domain
containing the zero section of the bigon (`contDiffOn_correctedCoordinates`,
`nonlinearDomain_contains_zero`), and on that domain carry the model lower and upper sheets to the
strip charts of the two sheets (`correctedCoordinates_lower_of_mem_domain`,
`correctedCoordinates_upper_of_mem_domain`).

These are the coordinates in which the two sheets are straightened along the Whitney disc; cf.
Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

Whitney trick, chart, inverse function theorem
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- The sheared coordinates of a tangent-adapted chart: the model map of its base and normal
blocks. -/
def TubularBigon.RankThreeTangentAdaptedChart.shearedCoordinates {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  FrameField.shearedMap c.base c.normal

/-- The corrected coordinates: the sheared coordinates corrected along the two sheets to agree with
the two retimed sheet transitions. -/
def TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  RankThreeWhitneyModel.correctedSheetMap c.shearedCoordinates
    (d.retimedSheetTransition tube.chart) (e.retimedSheetTransition tube.chart) h

/-- The corrected coordinates are the identity on the zero section. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_zero {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) (p : ℝ × ℝ) :
    c.correctedCoordinates (p, 0) = (p, 0) := by
  rw [correctedCoordinates, RankThreeWhitneyModel.correctedSheetMap_zero]
  exact FrameField.shearedMap_zero c.base c.normal p

/-- At a point of the bigon, the sheared coordinates have the sheared block as derivative. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_shearedCoordinates_zero
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    HasFDerivAt c.shearedCoordinates (FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) :=
  FrameField.hasFDerivAt_shearedMap_zero
    ((c.smooth_base.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))
    ((c.smooth_normal.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))

/-- The restriction of the sheared coordinates to the lower sheet has the retimed lower sheet
differential as derivative. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_lower {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ RankThreeWhitneyModel.firstSheet)
      ((d.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.lowerBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : RankThreeWhitneyModel.Lower))
      (RankThreeWhitneyModel.hasFDerivAt_firstSheet (2 * t - 1, 0))
  rwa [WhitneyPairModel.lowerBoundaryArc, c.lower_model_tangent ht] at hd

/-- The restriction of the sheared coordinates to the upper sheet has the retimed upper sheet
differential as derivative. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_upper {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ RankThreeWhitneyModel.secondSheet h)
      ((e.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.upperBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : RankThreeWhitneyModel.Upper))
      (RankThreeWhitneyModel.hasFDerivAt_secondSheet h (2 * t - 1, 0))
  rwa [c.upper_model_tangent ht] at hd

/-- The corrected coordinates have the same derivative as the sheared ones at every point of the
bigon. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_correctedCoordinates_zero
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    HasFDerivAt c.correctedCoordinates (FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) := by
  have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have hRlo :=
    d.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.lower_chart_center_mem_target d ht)
  have hRhi :=
    e.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.upper_chart_center_mem_target e ht)
  have hGlo := c.hasFDerivAt_sheared_lower ht
  have hGhi := c.hasFDerivAt_sheared_upper ht
  rw [htime] at hRlo hRhi hGlo hGhi
  exact
    RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero
      (c.hasFDerivAt_shearedCoordinates_zero hp) hRlo hGlo hRhi hGhi

/-- Along the lower boundary arc, the retimed lower sheet transition and the sheared coordinates of
the lower sheet have the same germ. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.retimed_lower_center_germ {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.lower_sheetTransition_center_germ d ht).comp_tendsto htime] with s hs
  change
    d.sheetTransition tube.chart (WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      FrameField.shearedMap c.base c.normal ((s, 0), 0)
  rw [WhitneyPairModel.sheetTimeCoordinates_apply, FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [WhitneyPairModel.lowerBoundaryArc, hlin]

/-- Along the upper boundary arc, the retimed upper sheet transition and the sheared coordinates of
the upper sheet have the same germ. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.retimed_upper_center_germ {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => e.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.upper_sheetTransition_center_germ e ht).comp_tendsto htime] with s hs
  change
    e.sheetTransition tube.chart (WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      FrameField.shearedMap c.base c.normal ((s, h * (1 - s ^ 2)), 0)
  rw [WhitneyPairModel.sheetTimeCoordinates_apply, FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [WhitneyPairModel.upperBoundaryArc, hlin]

/-- The domain of the sheared coordinates: the points whose base coordinate lies in the domain of
the chart blocks. -/
def TubularBigon.RankThreeTangentAdaptedChart.shearedDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.Space :=
  Prod.fst ⁻¹' c.domain

/-- The domain of the correction along the lower sheet. -/
def TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.LowerSheet :=
  d.retimedDomain tube.chart ∩ RankThreeWhitneyModel.firstSheet ⁻¹' c.shearedDomain

/-- The domain of the correction along the upper sheet. -/
def TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.UpperSheet :=
  e.retimedDomain tube.chart ∩ RankThreeWhitneyModel.secondSheet h ⁻¹' c.shearedDomain

/-- The interior of the set of times at which both sheet transitions agree with the sheared
coordinates on the centre lines. -/
def TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : Set ℝ :=
  interior
    {s |
      d.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
        e.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}

/-- The domain on which the corrected coordinates are defined and smooth: the correction domain
intersected with the matching times. -/
def TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set RankThreeWhitneyModel.Space :=
  RankThreeWhitneyModel.correctionDomain c.shearedDomain c.lowerCorrectionDomain
      c.upperCorrectionDomain ∩
    (fun p : RankThreeWhitneyModel.Space => p.1.1) ⁻¹' c.centerMatchingTimes

/-- The domain of the sheared coordinates is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_shearedDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.shearedDomain :=
  c.open_domain.preimage continuous_fst

/-- The lower correction domain is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_lowerCorrectionDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.lowerCorrectionDomain :=
  (d.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage RankThreeWhitneyModel.contDiff_firstSheet.continuous)

/-- The upper correction domain is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_upperCorrectionDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.upperCorrectionDomain :=
  (e.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage
      (RankThreeWhitneyModel.contDiff_secondSheet h).continuous)

/-- The domain of the corrected coordinates is open. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.isOpen_nonlinearDomain {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.nonlinearDomain :=
  (RankThreeWhitneyModel.isOpen_correctionDomain c.isOpen_shearedDomain
        c.isOpen_lowerCorrectionDomain c.isOpen_upperCorrectionDomain).inter
    (isOpen_interior.preimage (by fun_prop))

/-- The corrected coordinates are smooth on their domain. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.contDiffOn_correctedCoordinates
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
    ContDiffOn ℝ ∞ c.correctedCoordinates c.nonlinearDomain := by
  have hG : ContDiffOn ℝ ∞ c.shearedCoordinates c.shearedDomain :=
    FrameField.contDiffOn_shearedMap c.smooth_base c.smooth_normal
  exact
    (RankThreeWhitneyModel.contDiffOn_correctedSheetMap hG
          ((d.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp RankThreeWhitneyModel.contDiff_firstSheet.contDiffOn (fun _ hp => hp.2))
          ((e.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp (RankThreeWhitneyModel.contDiff_secondSheet h).contDiffOn
            (fun _ hp => hp.2))).mono
      Set.inter_subset_left

/-- Every parameter of `[0, 1]`, read as a boundary-arc time, is a matching time. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes_contains {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 2 * t - 1 ∈ c.centerMatchingTimes :=
  mem_interior_iff_mem_nhds.mpr
    ((c.retimed_lower_center_germ ht).and (c.retimed_upper_center_germ ht))

/-- The centre of the lower sheet at a parameter of `[0, 1]` lies in the lower correction domain. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain_contains_center
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : RankThreeWhitneyModel.Lower)) ∈ c.lowerCorrectionDomain := by
  refine
    ⟨d.retimedDomain_contains_center tube.chart ht (tube.lower_chart_center_mem_target d ht), ?_⟩
  exact c.contains (tube.lowerBoundaryArc_mem_bigon ht)

/-- The centre of the upper sheet at a parameter of `[0, 1]` lies in the upper correction domain. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain_contains_center
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : RankThreeWhitneyModel.Upper)) ∈ c.upperCorrectionDomain := by
  refine
    ⟨e.retimedDomain_contains_center tube.chart ht (tube.upper_chart_center_mem_target e ht), ?_⟩
  exact c.contains (tube.upperBoundaryArc_mem_bigon ht)

/-- The zero section over the bigon lies in the domain of the corrected coordinates. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain_contains_zero
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ WhitneyPairModel.bigon h) :
    (p, (0 : RankThreeWhitneyModel.Lower × RankThreeWhitneyModel.Upper)) ∈
      c.nonlinearDomain := by
  have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have hlo := c.lowerCorrectionDomain_contains_center ht
  have hhi := c.upperCorrectionDomain_contains_center ht
  have hmatch := c.centerMatchingTimes_contains ht
  rw [htime] at hlo hhi hmatch
  exact ⟨⟨c.contains hp, ⟨hlo, hlo⟩, ⟨hhi, hhi⟩⟩, hmatch⟩

/-- A point of the lower sheet in the domain has its retimed parameter in the source of the lower
strip chart, with image in the target of the tubular chart. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.lower_native_parameters {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
        d.chart.source ∧
      d.chart (WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.1.1.1

/-- A point of the upper sheet in the domain has its retimed parameter in the source of the upper
strip chart, with image in the target of the tubular chart. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.upper_native_parameters {E M : Type*}
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    (WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
        e.chart.source ∧
      e.chart (WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.2.1.1

/-- On the lower sheet the corrected coordinates are the retimed lower sheet transition: the chart
is sheet-parametrised there. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_lower_of_mem_domain
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.LowerSheet}
    (hq : RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (RankThreeWhitneyModel.firstSheet q) =
      d.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact RankThreeWhitneyModel.correctedSheetMap_lower q hm.1

/-- On the upper sheet the corrected coordinates are the retimed upper sheet transition: the chart
is sheet-parametrised there. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_upper_of_mem_domain
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
    (c : TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : RankThreeWhitneyModel.UpperSheet}
    (hq : RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (RankThreeWhitneyModel.secondSheet h q) =
      e.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact RankThreeWhitneyModel.correctedSheetMap_upper q hm.2


end
