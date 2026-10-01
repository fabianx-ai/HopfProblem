/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.CleanStrips

/-!
# Fields on a neighbourhood of the boundary of the bigon

Two smooth fields along the lower and upper boundary arcs of the standard bigon that agree near the
two corners are the restrictions of one smooth field on a neighbourhood of the boundary of the bigon
(`WhitneyPairModel.exists_smooth_bigon_boundary_field`); for fields of injective linear maps the
resulting field is injective at every boundary point
(`WhitneyPairModel.exists_injective_bigon_boundary_field`).

Cf. Milnor, *Lectures on the h-cobordism theorem*, §6.

## Tags

Whitney trick, bigon, gluing
-/

open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

/-- Two smooth fields along the two boundary arcs of the bigon, agreeing near the two corners, are
the restrictions of one smooth field defined on a neighbourhood of the boundary of the bigon. -/
theorem WhitneyPairModel.exists_smooth_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ} (hh : 0 < h) {L H : ℝ → F} {D : Set ℝ}
    (hD : IsOpen D) (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D)
    (hH : ContDiffOn ℝ ∞ H D) (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L) :
    ∃ U V : Set (ℝ × ℝ),
      IsOpen U ∧
        IsOpen V ∧
          frontier (bigon h) ⊆ U ∪ V ∧
            Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                ∃ W : (ℝ × ℝ) → F,
                  ContDiffOn ℝ ∞ W (U ∪ V) ∧
                    Set.EqOn W (L ∘ arcTime) U ∧ Set.EqOn W (H ∘ arcTime) V := by
  let P := arcTime ⁻¹' D
  have hP : IsOpen P := hD.preimage contDiff_arcTime.continuous
  have hLP : ContDiffOn ℝ ∞ (L ∘ arcTime) P :=
    hL.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have hHP : ContDiffOn ℝ ∞ (H ∘ arcTime) P :=
    hH.comp contDiff_arcTime.contDiffOn (fun _ hp => hp)
  have htime0 : Filter.Tendsto arcTime (𝓝 ((-1 : ℝ), (0 : ℝ))) (𝓝 (0 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((-1 : ℝ), (0 : ℝ))))
  have htime1 : Filter.Tendsto arcTime (𝓝 ((1 : ℝ), (0 : ℝ))) (𝓝 (1 : ℝ)) := by
    simpa [ContinuousAt, arcTime] using
      (contDiff_arcTime.continuous.continuousAt (x := ((1 : ℝ), (0 : ℝ))))
  have hg0 : (L ∘ arcTime) =ᶠ[𝓝 ((-1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h0.symm.comp_tendsto htime0
  have hg1 : (L ∘ arcTime) =ᶠ[𝓝 ((1 : ℝ), (0 : ℝ))] (H ∘ arcTime) := h1.symm.comp_tendsto htime1
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp hg0
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ := mem_nhds_iff.mp hg1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have hlowP : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) P := by
    intro t ht
    change arcTime (2 * t - 1, 0) ∈ D
    rw [htime]
    exact hID ht
  have huppP : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) P :=
    by
    intro t ht
    change arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ D
    rw [htime]
    exact hID ht
  obtain ⟨U, V, hU, hV, hUP, hVP, hover, hlowU, huppV, hfront⟩ :=
    exists_bigon_boundary_cover hh hP hP (hO₀.union hO₁) (Or.inl hleft) (Or.inr hright) hlowP
      huppP
  have hLH : Set.EqOn (L ∘ arcTime) (H ∘ arcTime) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨W, hW, hWL, hWH⟩ :=
    exists_smooth_open_gluing hU hV (hLP.mono hUP).contMDiffOn (hHP.mono hVP).contMDiffOn
      hLH
  exact ⟨U, V, hU, hV, hfront, hlowU, huppV, W, hW.contDiffOn, hWL, hWH⟩

/-- Version of the previous statement for fields of injective linear maps: the resulting field on a
neighbourhood of the boundary of the bigon has the prescribed germs along the two arcs and is
injective at every boundary point. -/
theorem WhitneyPairModel.exists_injective_bigon_boundary_field {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {h : ℝ} (hh : 0 < h) {L H : ℝ → (A →L[ℝ] F)} {D : Set ℝ} (hD : IsOpen D)
    (hID : Set.Icc (0 : ℝ) 1 ⊆ D) (hL : ContDiffOn ℝ ∞ L D) (hH : ContDiffOn ℝ ∞ H D)
    (h0 : H =ᶠ[𝓝 (0 : ℝ)] L) (h1 : H =ᶠ[𝓝 (1 : ℝ)] L)
    (hiL : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (L t))
    (hiH : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (H t)) :
    ∃ O : Set (ℝ × ℝ),
      IsOpen O ∧
        frontier (bigon h) ⊆ O ∧
          ∃ W : (ℝ × ℝ) → (A →L[ℝ] F),
            ContDiffOn ℝ ∞ W O ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, W =ᶠ[𝓝 (2 * t - 1, 0)] (L ∘ arcTime)) ∧
                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                    W =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))] (H ∘ arcTime)) ∧
                  ∀ p ∈ frontier (bigon h), Function.Injective (W p) := by
  obtain ⟨U, V, hU, hV, hfront, hlow, hupp, W, hW, hWL, hWH⟩ :=
    exists_smooth_bigon_boundary_field hh hD hID hL hH h0 h1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  refine ⟨U ∪ V, hU.union hV, hfront, W, hW, ?_, ?_, ?_⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlow ht)) (fun _ hp => hWL hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (hupp ht)) (fun _ hp => hWH hp)
  · intro p hp
    obtain ⟨t, ht, rfl | rfl⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
    · rw [hWL (hlow ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiL t ht
    · rw [hWH (hupp ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hiH t ht

end
