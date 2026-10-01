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
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Homogeneity of manifolds

Every point of an open set of a manifold has a neighbourhood in it each of whose points is the image
of the given point under a diffeomorphism that is the identity outside the open set; in a chart the
diffeomorphism is the time-one map of a compactly supported isotopy.

## Main results

* `SupportedDiffeomorph.exists_supported_pointMoving`
* `SupportedDiffeomorph.exists_open_pointMoving`

## References

* cf. J. Milnor, *Topology from the Differentiable Viewpoint*, §4 (homogeneity lemma).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section


/-- Homogeneity in a chart: points close enough to a given point of a chart can be moved onto its
image by a compactly supported isotopy of the manifold that is the identity outside the chart.
-/
theorem SupportedDiffeomorph.exists_supported_pointMoving {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {x : E}
    (hx : x ∈ Φ.source) :
    ∃ ε : ℝ,
      0 < ε ∧
        Metric.ball x ε ⊆ Φ.source ∧
          ∀ y ∈ Metric.ball x ε,
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
                (∀ z, A (0, z) = z) ∧
                  (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ z, A (t, z) = d z) ∧
                    (∀ t z, z ∉ Φ.target → A (t, z) = z) ∧ A (1, Φ x) = Φ y := by
  obtain ⟨β, hβsupport, hβcompact, hβsmooth, -, hβx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Φ.open_source.mem_nhds hx)
  obtain ⟨δ, hδ, hmove⟩ := exists_small_supported_bump_isotopy Φ hβsmooth hβcompact hβsupport
  obtain ⟨ρ, hρ, hρsource⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hx)
  refine ⟨Min.min δ ρ, lt_min hδ hρ, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hρsource
  · intro y hy
    have hnear : ‖y - x‖ < δ := by
      simpa only [dist_eq_norm] using
        (show Dist.dist y x < Min.min δ ρ from hy).trans_le (min_le_left _ _)
    obtain ⟨A, hA, hzero, hdiff, hfix, hend⟩ := hmove (y - x) hnear
    refine ⟨A, hA, hzero, hdiff, ?_, ?_⟩
    · intro t z hz
      apply hfix t z
      rintro ⟨q, hq, rfl⟩
      exact hz (Φ.map_source' (hβsupport hq))
    · have hterminal := hend x hx
      rw [hβx, one_smul] at hterminal
      have hxy : x + (y - x) = y := by abel
      exact hterminal.trans (congrArg Φ hxy)

/-- Homogeneity of a manifold: every point of an open set has a neighbourhood in it each of whose
points is the image of that point under a diffeomorphism that is the identity outside the open
set.
-/
theorem SupportedDiffeomorph.exists_open_pointMoving {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M,
      IsOpen V ∧
        x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := modelChartPartialDiffeomorph (I := J) x
  let Φ := PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := exists_supported_pointMoving Φ hxΦ
  refine
    ⟨Φ '' Metric.ball (c x) ε,
      Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
      ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, _, _, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))
