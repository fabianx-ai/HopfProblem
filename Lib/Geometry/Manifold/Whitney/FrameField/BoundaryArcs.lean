/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.AnnularExtension
import Lib.Geometry.Manifold.Whitney.FrameField.Complement

/-!
# The boundary arcs of a tubular bigon

The standard planar bigon of height `h` is bounded by the lower arc `t ↦ (2t - 1, 0)` and the
upper arc `t ↦ (2t - 1, h (1 - (2t - 1)²))`, `t ∈ [0, 1]`
(`WhitneyPairModel.lowerBoundaryArc`, `WhitneyPairModel.upperBoundaryArc`), with their velocities.
For a tubular bigon (`TubularBigon`) and the strip normal data of a sheet along one arc, this file
shows that the arcs stay in the bigon and in the chart source, that the strip chart and the tubular
chart agree along the centre line, computes the sheet differential on the unit tangent, and shows
that the normal frame of each sheet is smooth near `[0, 1]` and injective on it
(`TubularBigon.lower_sheetFrame`, `TubularBigon.upper_sheetFrame`), completed by a smooth field of
orthogonal complements when the dimensions add up
(`TubularBigon.upper_sheetFrame_complement_of_finrank`).

These are the boundary data of the framing problem of the Whitney disc, cf. Milnor, *Lectures on
the h-cobordism theorem*, §6.

## Tags

Whitney trick, bigon, normal frame
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- The lower boundary arc of the standard planar bigon: the segment `t ↦ (2 t - 1, 0)`, `t ∈ [0,
1]`. -/
def WhitneyPairModel.lowerBoundaryArc (t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, 0)

/-- The upper boundary arc of the standard planar bigon of height `h`: the parabolic arc `t ↦ (2 t -
1, h (1 - (2 t - 1)^2))`, `t ∈ [0, 1]`. -/
def WhitneyPairModel.upperBoundaryArc (h t : ℝ) : ℝ × ℝ :=
  (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))

/-- The lower boundary arc has constant velocity `(2, 0)`. -/
theorem WhitneyPairModel.hasDerivAt_lowerBoundaryArc (t : ℝ) :
    HasDerivAt lowerBoundaryArc (2, 0) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  exact hs.prodMk (hasDerivAt_const t (0 : ℝ))

/-- The upper boundary arc has velocity `(2, -4 h (2 t - 1))` at time `t`. -/
theorem WhitneyPairModel.hasDerivAt_upperBoundaryArc (h t : ℝ) :
    HasDerivAt (upperBoundaryArc h) (2, -4 * h * (2 * t - 1)) t := by
  have hs : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hy : HasDerivAt (fun s : ℝ => h * (1 - (2 * s - 1) ^ 2)) (-4 * h * (2 * t - 1)) t := by
    convert HasDerivAt.const_mul h ((hasDerivAt_const t (1 : ℝ)).sub (hs.pow 2)) using 1 <;>
      first
      | rfl
      | ring
  exact hs.prodMk hy

/-- The lower boundary arc stays inside the bigon on the parameter interval `[0, 1]`. -/
theorem TubularBigon.lowerBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WhitneyPairModel.lowerBoundaryArc t ∈ WhitneyPairModel.bigon h := by
  have hf :
    WhitneyPairModel.lowerBoundaryArc t ∈ frontier (WhitneyPairModel.bigon h) :=
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
  exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

/-- The upper boundary arc stays inside the bigon on the parameter interval `[0, 1]`. -/
theorem TubularBigon.upperBoundaryArc_mem_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    WhitneyPairModel.upperBoundaryArc h t ∈ WhitneyPairModel.bigon h := by
  have hf :
    WhitneyPairModel.upperBoundaryArc h t ∈ frontier (WhitneyPairModel.bigon h) :=
    (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inr rfl⟩
  exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1

/-- The zero section over a point of the lower boundary arc lies in the source of the tubular chart
of a tubular bigon. -/
theorem TubularBigon.lowerBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (WhitneyPairModel.lowerBoundaryArc t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.lowerBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

/-- The zero section over a point of the upper boundary arc lies in the source of the tubular chart
of a tubular bigon. -/
theorem TubularBigon.upperBoundaryArc_zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (WhitneyPairModel.upperBoundaryArc h t, 0) ∈ tube.chart.source :=
  tube.source_contains
    ⟨tube.upperBoundaryArc_mem_bigon ht, Metric.mem_closedBall_self tube.radius_pos.le⟩

/-- Along the lower sheet, the centre line of a strip chart lands in the target of the tubular chart
of the bigon. -/
theorem TubularBigon.lower_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.lower_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [WhitneyPairModel.lowerStripCoordinates_lower, d.center t] at hg
  have hp := tube.chart.map_source' (tube.lowerBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, WhitneyPairModel.lowerBoundaryArc, hg] at hp
  exact hp

/-- Along the upper sheet, the centre line of a strip chart lands in the target of the tubular chart
of the bigon. -/
theorem TubularBigon.upper_chart_center_mem_target {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.upper_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [WhitneyPairModel.upperStripCoordinates_upper, d.center t] at hg
  have hp := tube.chart.map_source' (tube.upperBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, WhitneyPairModel.upperBoundaryArc, hg] at hp
  exact hp

/-- Near each parameter `t ∈ [0, 1]`, the transition from the strip chart of the lower sheet to the
tubular chart of the bigon carries the centre line onto the lower boundary arc, with vanishing
normal component. -/
theorem TubularBigon.lower_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (WhitneyPairModel.lowerBoundaryArc s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (WhitneyPairModel.hasDerivAt_lowerBoundaryArc t).continuousAt
    (tube.lowerBoundaryArc_zero_mem_source ht)
    (WhitneyPairModel.lowerStripCoordinates_lower h) (tube.lower_germ t ht)

/-- Near each parameter `t ∈ [0, 1]`, the transition from the strip chart of the upper sheet to the
tubular chart of the bigon carries the centre line onto the upper boundary arc, with vanishing
normal component. -/
theorem TubularBigon.upper_sheetTransition_center_germ {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t] fun s =>
      (WhitneyPairModel.upperBoundaryArc h s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (WhitneyPairModel.hasDerivAt_upperBoundaryArc h t).continuousAt
    (tube.upperBoundaryArc_zero_mem_source ht)
    (WhitneyPairModel.upperStripCoordinates_upper h) (tube.upper_germ t ht)

/-- The differential of the lower sheet transition sends the unit tangent of the centre line to the
velocity `((2, 0), 0)` of the lower boundary arc. -/
theorem TubularBigon.lower_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, 0), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.lower_chart_center_mem_target d ht)
    (WhitneyPairModel.hasDerivAt_lowerBoundaryArc t)
    (tube.lower_sheetTransition_center_germ d ht)

/-- The differential of the upper sheet transition sends the unit tangent of the centre line to the
velocity `((2, -4 h (2 t - 1)), 0)` of the upper boundary arc. -/
theorem TubularBigon.upper_sheetDifferential_arc {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l h n)
    (d : StripNormalData A B (E := E) T l) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, -4 * h * (2 * t - 1)), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.upper_chart_center_mem_target d ht)
    (WhitneyPairModel.hasDerivAt_upperBoundaryArc h t)
    (tube.upper_sheetTransition_center_germ d ht)


/-- Along the lower sheet of a tubular bigon, the normal frame of the strip chart is smooth on a
neighbourhood of `[0, 1]` and injective at every parameter of `[0, 1]`. -/
theorem TubularBigon.lower_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : (ℝ × ℝ) → M} {n : ℕ} (tube : TubularBigon (E := E) S T a b k.map l h n)
    (d : StripNormalData A B (E := E) S k.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ WhitneyPairModel.bigon h := by
    intro t ht
    have hf : (2 * t - 1, 0) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inl rfl⟩
    exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, 0), 0) ∈ tube.chart.source := fun t ht =>
    tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.lower t ht] at hp
    rw [← d.center t, k.center t ht]
    exact hp
  · intro t ht
    have hkt : (t, (0 : ℝ)) ∈ k.domain :=
      k.contains_strip ⟨ht, ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (WhitneyPairModel.lowerStripCoordinates h) (2 * t - 1, 0)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (k.smooth.contMDiffAt (k.open_domain.mem_nhds hkt)) tube.zero_section (hsource t ht)
        (WhitneyPairModel.contDiff_lowerStripCoordinates tube.height_pos.ne').contDiffAt
        (WhitneyPairModel.lowerStripCoordinates_lower h t) hcs (tube.lower_germ t ht)

/-- Along the upper sheet of a tubular bigon, the normal frame of the strip chart is smooth on a
neighbourhood of `[0, 1]` and injective at every parameter of `[0, 1]`. -/
theorem TubularBigon.upper_sheetFrame {E M A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} {l : CleanStripPatch (E := E) T S b k₀ k₁}
    {k : (ℝ × ℝ) → M} {n : ℕ} (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) :
    (∃ U : Set ℝ,
        IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (d.normalFrame tube.chart t) := by
  have hpoint :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ WhitneyPairModel.bigon h := by
    intro t ht
    have hf :
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (WhitneyPairModel.bigon h) :=
      (WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
        ⟨t, ht, Or.inr rfl⟩
    exact ((WhitneyPairModel.mem_frontier_bigon_iff h _).mp hf).1
  have hsource :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ((2 * t - 1, h * (1 - (2 * t - 1) ^ 2)), 0) ∈ tube.chart.source :=
    fun t ht => tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.upper t ht] at hp
    rw [← d.center t, l.center t ht]
    exact hp
  · intro t ht
    have hlt : (t, (0 : ℝ)) ∈ l.domain :=
      l.contains_strip ⟨ht, ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩⟩
    have hcs :
      Function.Surjective
        (fderiv ℝ (WhitneyPairModel.upperStripCoordinates h)
          (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates tube.height_pos.ne'
          (2 * t - 1))
    exact
      d.injective_normalFrame_of_strip_germ tube.chart ht
        (l.smooth.contMDiffAt (l.open_domain.mem_nhds hlt)) tube.zero_section (hsource t ht)
        (WhitneyPairModel.contDiff_upperStripCoordinates tube.height_pos.ne').contDiffAt
        (WhitneyPairModel.upperStripCoordinates_upper h t) hcs (tube.upper_germ t ht)

/-- When the sheet directions and the chosen complement fill the normal fibre by dimension count,
the normal frame along the upper sheet extends to a smooth field of complements `C t`,
orthogonal to the frame on `[0, 1]`, with `normalFrame t ⊞ C t` bijective. -/
theorem TubularBigon.upper_sheetFrame_complement_of_finrank {E M A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ} [FiniteDimensional ℝ A]
    {l : CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M} {n : ℕ}
    (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) (m : ℕ) (hdim : Module.finrank ℝ A + m = n) :
    ∃ V : Set ℝ,
      IsOpen V ∧
        Set.Icc (0 : ℝ) 1 ⊆ V ∧
          ContDiffOn ℝ ∞ (d.normalFrame tube.chart) V ∧
            ∃ C : ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)),
              ContDiffOn ℝ ∞ C V ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1, (C t).range = (d.normalFrame tube.chart t).rangeᗮ) ∧
                  ∀ t ∈ V, Function.Bijective ((d.normalFrame tube.chart t).coprod (C t)) := by
  obtain ⟨⟨U, hU, hIU, hs⟩, hi⟩ := tube.upper_sheetFrame d
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  have hdim' : Module.finrank ℝ A + m = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨W, hW, hIW, C, hC, hr, hc⟩ :=
    FrameField.exists_smooth_complement_near_starConvex_on hU hs
      CompactIccSpace.isCompact_Icc hstar (by simp) hIU hi m hdim'
  exact
    ⟨W ∩ U, hW.inter hU, fun t ht => ⟨hIW ht, hIU ht⟩, hs.mono Set.inter_subset_right, C,
      hC.mono Set.inter_subset_left, hr, fun t ht => hc t ht.1⟩

end
