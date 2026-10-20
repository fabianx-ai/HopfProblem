/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.RankThreeModel.CompatibleChart
import Lib.Geometry.Manifold.Whitney.RankThreeModel.ModelGraphMotion
import Lib.Geometry.Manifold.Whitney.RankThreeModel.IntersectionRemoval

/-!
# Whitney's lemma in the rank-three model

`TubularBigon.exists_rankThree_relative_cancellation`: let `S`, `T` be closed subsets of a
Hausdorff manifold `M` modelled on `E`, and let a tubular bigon of rank three, with normal data of
the two sheets along its boundary arcs, have opposite intersection signs at its two corners
`a 0`, `a 1`. Then there is a smooth ambient isotopy `A` of `M`, starting at the identity, by
diffeomorphisms, supported in a compact set `K` inside the tubular chart and disjoint from the other
points of `S ∩ T`, whose time-one map satisfies `A₁ '' S ∩ T = (S ∩ T) \ {a 0, a 1}`. The same is
proved first in a compatible chart (`TubularBigon.RankThreeCompatibleChart.exists_cancellation`,
`exists_relative_cancellation`).

This is Whitney's lemma (cancellation of a pair of intersection points of opposite sign) in the
model of two sheets of dimensions `2` and `3` in a manifold of dimension five: Milnor, *Lectures
on the h-cobordism theorem*, §6.

## Tags

Whitney trick, Whitney lemma, handle cancellation
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section


/-- The Whitney cancellation in a compatible chart: a compactly supported ambient isotopy whose
time-one map removes exactly the two intersection points `a 0`, `a 1` from the intersection of
the two sheets. -/
theorem TubularBigon.RankThreeCompatibleChart.exists_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) [T2Space M] :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, hdisjoint⟩ :=
    RankThreeWhitneyModel.exists_supported_native_bigon_cancellation c.chart tube.height_pos
      (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)
  rw [c.nativeFirstSheet_eq, c.nativeSecondSheet_eq] at hdisjoint
  obtain ⟨d, hd⟩ := hdiff 1
  have hdfix : ∀ y ∉ c.chart.target, d y = y := by
    intro y hy
    exact (hd y).symm.trans (hfix 1 y (fun h => hy (hKsource h)))
  have hdeq : (fun y => A (1, y)) = d := funext hd
  have hdisjoint' : Disjoint (d '' (S ∩ c.chart.target)) (T ∩ c.chart.target) := by
    rw [← hdeq]
    exact hdisjoint
  have hinter : (d '' S) ∩ T = (S ∩ T) \ c.chart.target :=
    SupportedDiffeomorph.image_inter_eq_diff d.toEquiv hdfix hdisjoint'
  refine ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, ?_⟩
  rw [hdeq, hinter, ← c.intersection_in_target_eq]
  ext y
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

/-- The cancellation of the previous statement with support disjoint from the remaining intersection
points, so that it can be performed relative to them. -/
theorem TubularBigon.RankThreeCompatibleChart.exists_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : TubularBigon.RankThreeCompatibleChart tube) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKt, A, hA⟩ := c.exists_cancellation
  refine ⟨K, hK, hKt, ?_, A, hA⟩
  apply Set.disjoint_left.mpr
  intro y hyK hy
  have hc : y ∈ (S ∩ T) ∩ c.chart.target := ⟨hy.1, hKt hyK⟩
  rw [c.intersection_in_target_eq] at hc
  exact hy.2 hc

/-- The rank-three Whitney lemma: a tubular bigon whose two corner intersection signs are opposite
gives an ambient isotopy, supported away from the other intersection points, whose time-one map
removes exactly those two points from the intersection of the two sheets. -/
theorem TubularBigon.exists_rankThree_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
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
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ tube.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKt, hd, A, hA⟩ := c.exists_relative_cancellation
  exact ⟨K, hK, hKt.trans c.target_subset, hd, A, hA⟩

end
