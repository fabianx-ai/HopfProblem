/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.RankThreeModel.Model
import Lib.Geometry.Manifold.Whitney.RankThreeModel.SheetRetiming

/-!
# Tangent-adapted charts of a tubular bigon

A tubular bigon is an embedding of the planar bigon whose lower and upper boundary arcs run along
two sheets `S` and `T`, with a tubular chart around it. A rank-three tangent-adapted chart
(`TubularBigon.RankThreeTangentAdaptedChart`) is a chart of the tubular neighbourhood in the
coordinates of the rank-three model whose differential along the bigon is a sheared block equal to
the sheet differential of `S` along the lower arc and of `T` along the upper arc. If the two corner
intersection signs of the bigon are opposite, such a chart exists
(`TubularBigon.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs`), and along the two
boundary arcs its differential, composed with the model sheet derivatives, is the retimed sheet
differential (`lower_model_tangent`, `upper_model_tangent`).
`TubularBigon.TangentAdaptedChart` is the same notion in the Whitney pair model, whose two sheet
directions are planes.

The opposite-sign hypothesis is the orientation condition of Whitney's lemma that lets the normal
frames along the two arcs be joined across the disc: Milnor, *Lectures on the h-cobordism
theorem*, §6.

## Tags

Whitney trick, tubular neighbourhood, adapted chart
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- A tangent-adapted chart of a rank-three tubular bigon: a chart of the tubular neighbourhood in
the coordinates of the rank-three model whose differential along the bigon is a sheared block
matching the two sheet differentials on the two boundary arcs. -/
structure TubularBigon.RankThreeTangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map) where
  base : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        FrameField.shearedBlock (base (WhitneyPairModel.upperBoundaryArc h t))
            (normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      RankThreeWhitneyModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (FrameField.shearedBlock (base p) (normal p))
        (p, 0)

/-- The Whitney condition gives a tangent-adapted chart: if the two corner intersection signs are
opposite, a rank-three tangent-adapted chart exists. -/
theorem TubularBigon.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeTangentAdaptedChart tube d e) := by
  obtain ⟨W, hW, hlo, O, hO, hKO, C, hC, hhi, hframe⟩ :=
    tube.exists_rankThree_adapted_frame_of_opposite_corner_signs d e hsign
  obtain ⟨Dlo, hDlo, hIDlo, hBlo⟩ :=
    d.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.lower_chart_center_mem_target d ht)
  obtain ⟨Dhi, hDhi, hIDhi, hBhi⟩ :=
    e.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.upper_chart_center_mem_target e ht)
  have htime (t y : ℝ) : WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    WhitneyPairModel.arcTime (WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have htimeK :
    Set.MapsTo WhitneyPairModel.arcTime (WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  let U := O ∩ WhitneyPairModel.arcTime ⁻¹' (Dlo ∩ Dhi)
  have hU : IsOpen U :=
    hO.inter ((hDlo.inter hDhi).preimage WhitneyPairModel.contDiff_arcTime.continuous)
  have hKU : WhitneyPairModel.bigon h ⊆ U := fun p hp =>
    ⟨hKO hp, hIDlo (htimeK hp), hIDhi (htimeK hp)⟩
  let A : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ)) :=
    fun p =>
    (d.sheetBaseFrame tube.chart (WhitneyPairModel.arcTime p)).coprod
      (e.sheetBaseFrame tube.chart (WhitneyPairModel.arcTime p))
  let N :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    fun p => (W p).coprod (C p)
  have hA : ContDiffOn ℝ ∞ A U :=
    FrameField.contDiffOn_coprod
      (hBlo.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.1))
      (hBhi.comp WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
  have hN : ContDiffOn ℝ ∞ N U :=
    FrameField.contDiffOn_coprod hW.contDiffOn (hC.mono Set.inter_subset_left)
  have hiN : ∀ p ∈ U, (N p).IsInvertible := fun p hp =>
    FrameField.isInvertible_coprod_of_bijective _ _ (hframe p hp.1)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        FrameField.shearedBlock (A (2 * t - 1, 0)) (N (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u) := by
    intro t ht u
    have hWt : W (2 * t - 1, 0) = d.normalFrame tube.chart t := by
      have hg := (hlo t ht).eq_of_nhds
      dsimp only [Function.comp_apply] at hg
      rwa [htime] at hg
    rw [d.sheetDifferential_transverse_eq tube.chart ht (tube.lower_chart_center_mem_target d ht),
      FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, add_zero, zero_add, htime, hWt]
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        FrameField.shearedBlock (A (WhitneyPairModel.upperBoundaryArc h t))
            (N (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v) := by
    intro t ht v
    rw [e.sheetDifferential_transverse_eq tube.chart ht (tube.upper_chart_center_mem_target e ht),
      FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, zero_add, htq, hhi t ht]
  have hz :
    WhitneyPairModel.bigon h ×ˢ {(0 : EuclideanSpace ℝ (Fin 3))} ⊆ tube.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, Φ, hsource, hformula, htarget, -, hderiv⟩ :=
    FrameField.exists_sheared_tubular_chart tube.chart
      (WhitneyPairModel.isCompact_bigon tube.height_pos) hU hKU hz hA hN
      (fun p hp => hiN p (hKU hp))
  refine
    ⟨{  base := A
        normal := N
        domain := U
        open_domain := hU
        contains := hKU
        smooth_base := hA
        smooth_normal := hN
        normal_invertible := hiN
        lower_transverse := hlow
        upper_transverse := hupp
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        coordinates := hformula
        target_subset := htarget
        transition_derivative := hderiv }⟩
  intro p
  rw [hformula, FrameField.shearedMap_zero, tube.zero_section]

/-- The tangent-adapted chart in the planar model: the variant of `RankThreeTangentAdaptedChart`
whose two sheet directions are planes. -/
structure TubularBigon.TangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
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
  base : (ℝ × ℝ) → ((WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((WhitneyPairModel.Plane × WhitneyPairModel.Plane) →L[ℝ]
        EuclideanSpace ℝ (Fin 4))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : WhitneyPairModel.Plane,
        FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : WhitneyPairModel.Plane,
        FrameField.shearedBlock (base (WhitneyPairModel.upperBoundaryArc h t))
            (normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, WhitneyPairModel.Space) 𝓘(ℝ, E) WhitneyPairModel.Space M ∞
  source_contains : WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (FrameField.shearedBlock (base p) (normal p))
        (p, 0)


/-- Along the lower boundary arc, the sheared block of a tangent-adapted chart restricts to the
retimed sheet differential of the lower sheet. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.lower_model_tangent {E M : Type*}
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
    (FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))).comp
        RankThreeWhitneyModel.firstSheetDerivative =
      (d.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc : d.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, 0), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.lower_sheetDifferential_arc d ht]
    ext <;> simp [smul_eq_mul]
  change
    FrameField.shearedBlock _ _ (RankThreeWhitneyModel.firstSheetDerivative v) =
      d.sheetDifferential tube.chart t (WhitneyPairModel.halfTimeDerivative v)
  rw [WhitneyPairModel.halfTimeDerivative_apply]
  calc
    FrameField.shearedBlock _ _ (RankThreeWhitneyModel.firstSheetDerivative v) =
        FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            ((v.1, 0), 0) +
          FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            (0, (v.2, 0)) := by
      rw [← map_add]
      congr 1
      simp only [RankThreeWhitneyModel.firstSheetDerivative_apply, Prod.mk_add_mk, add_zero,
        zero_add]
    _ =
        d.sheetDifferential tube.chart t (v.1 / 2, 0) +
          d.sheetDifferential tube.chart t (0, v.2) := by
      rw [FrameField.shearedBlock_horizontal, c.lower_transverse t ht, harc]
    _ = d.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

/-- Along the upper boundary arc, the sheared block of a tangent-adapted chart restricts to the
retimed sheet differential of the upper sheet. -/
theorem TubularBigon.RankThreeTangentAdaptedChart.upper_model_tangent {E M : Type*}
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
    (FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t))).comp
        (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1)) =
      (e.sheetDifferential tube.chart t).comp WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc :
    e.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.upper_sheetDifferential_arc e ht]
    ext <;> simp [smul_eq_mul]
    ring
  change
    FrameField.shearedBlock _ _
        (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
      e.sheetDifferential tube.chart t (WhitneyPairModel.halfTimeDerivative v)
  rw [WhitneyPairModel.halfTimeDerivative_apply]
  calc
    FrameField.shearedBlock _ _
          (RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
        FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t))
            ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) +
          FrameField.shearedBlock (c.base (WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v.2)) := by
      rw [← map_add]
      congr 1
      simp only [RankThreeWhitneyModel.secondSheetDerivative_apply, Prod.mk_add_mk,
        add_zero, zero_add]
    _ =
        e.sheetDifferential tube.chart t (v.1 / 2, 0) +
          e.sheetDifferential tube.chart t (0, v.2) := by
      rw [FrameField.shearedBlock_horizontal, c.upper_transverse t ht, harc]
    _ = e.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp


end
