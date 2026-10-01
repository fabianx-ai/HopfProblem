/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Whitney.CleanStrips.CornerPatch
import Lib.Geometry.Manifold.Whitney.CleanStrips.StripPatch
import Lib.Geometry.Manifold.Whitney.CleanStrips.BigonStripCoordinates

/-!
# A clean embedded neighbourhood of the boundary of the Whitney bigon

Two clean corner patches and two clean strip patches, one along each edge, glue through the lower
and upper strip coordinates of the bigon to a map `f` of a neighbourhood of the frontier of the
bigon into `M`. The file shows that `f` is smooth, an injective immersion on an open neighbourhood
`W` of the frontier and a closed embedding on a compact neighbourhood `C ⊆ W`, restricts to the
two arcs on the edges, and avoids both sheets at every point of the bigon off its frontier
(`exists_clean_bigon_boundary_neighborhood`); `CleanBigonBoundary` packages the result
(`nonempty_cleanBigonBoundary`). Nothing is asserted about the points of the neighbourhood outside
the bigon.

This is the boundary collar of the Whitney disk (Milnor, *Lectures on the h-cobordism theorem*,
§6; the Whitney trick).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §§5–6.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section


/-- Near the left corner of the bigon the lower and the upper strip charts of a Whitney pair give
the same map into `M`, both being the left corner patch in its two coordinate orders.
-/
theorem bigon_strip_maps_left_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (-1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 0 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (-1, 0) = (0, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 0 using 1
    norm_num
  have hk :=
    k.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hx]
        exact (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt)
  have hl :=
    l.left_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0))
        by
        rw [← hy]
        exact (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt)
  have hnear : ∀ᶠ p in 𝓝 ((-1 : ℝ), (0 : ℝ)), WhitneyPairModel.arcTime p ≤ 1 / 3 := by
    have ht : WhitneyPairModel.arcTime (-1, 0) < 1 / 3 := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_lt_const ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp, WhitneyPairModel.lowerStripCoordinates_left h hp,
    WhitneyPairModel.upperStripCoordinates_left hh hp]
  change
    c₀.map (WhitneyPairModel.leftCornerCoordinates h p) =
      c₀.map ((WhitneyPairModel.leftCornerCoordinates h p).swap.swap)
  rw [Prod.swap_swap]

/-- The same agreement near the right corner of the bigon. -/
theorem bigon_strip_maps_right_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : h ≠ 0) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ WhitneyPairModel.lowerStripCoordinates h =ᶠ[𝓝 (1, 0)]
      l.map ∘ WhitneyPairModel.upperStripCoordinates h := by
  have hx : WhitneyPairModel.lowerStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.lowerStripCoordinates_lower h 1 using 1
    norm_num
  have hy : WhitneyPairModel.upperStripCoordinates h (1, 0) = (1, 0) := by
    convert WhitneyPairModel.upperStripCoordinates_upper h 1 using 1
    norm_num
  have hk :=
    k.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.lowerStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_lowerStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hx] at ht
        exact ht)
  have hl :=
    l.right_germ.comp_tendsto
      (show Filter.Tendsto (WhitneyPairModel.upperStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0))
        by
        have ht :=
          (WhitneyPairModel.contDiff_upperStripCoordinates hh).continuous.continuousAt (x :=
            (1, 0))
        rw [ContinuousAt, hy] at ht
        exact ht)
  have hnear : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), 2 / 3 ≤ WhitneyPairModel.arcTime p := by
    have ht : 2 / 3 < WhitneyPairModel.arcTime (1, 0) := by norm_num [WhitneyPairModel.arcTime]
    exact
      ((WhitneyPairModel.contDiff_arcTime.continuous.continuousAt).eventually_const_lt ht).mono
        (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change
    k.map (WhitneyPairModel.lowerStripCoordinates h p) =
      l.map (WhitneyPairModel.upperStripCoordinates h p)
  rw [hkp, hlp]
  change
    c₁.map (StripCoordinates.reverse (WhitneyPairModel.lowerStripCoordinates h p)) =
      c₁.map ((StripCoordinates.reverse (WhitneyPairModel.upperStripCoordinates h p)).swap)
  rw [WhitneyPairModel.lowerStripCoordinates_right h hp,
    WhitneyPairModel.upperStripCoordinates_right hh hp, Prod.swap_swap]

/-- Two smooth maps on open sets that agree on the intersection glue to a map smooth on the union
and restricting to each of them.
-/
theorem exists_smooth_open_gluing {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y] [ChartedSpace F Y] {f g : X → Y} {U V : Set X} (hU : IsOpen U)
    (hV : IsOpen V) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g V) (hfg : Set.EqOn f g (U ∩ V)) :
    ∃ k : X → Y, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k (U ∪ V) ∧ Set.EqOn k f U ∧ Set.EqOn k g V := by
  classical
  let k := U.piecewise f g
  have hkf : Set.EqOn k f U := fun x hx => Set.piecewise_eq_of_mem U f g hx
  have hkg : Set.EqOn k g V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (hkf hxU).trans (hfg ⟨hxU, hx⟩)
    · exact Set.piecewise_eq_of_notMem U f g hxU
  exact
    ⟨k, (hf.congr (fun _ hx => hkf hx)).union_of_isOpen (hg.congr (fun _ hx => hkg hx)) hU hV,
      hkf, hkg⟩

/-- Gluing the two strip patches of a Whitney pair along the corners gives a smooth map on a
neighbourhood of the boundary of the bigon of height `h` which restricts to the given arcs `a`
and `b` on the two edges, and which is the lower strip chart near the lower edge and the upper
strip chart near the upper edge.
-/
theorem exists_smooth_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    ∃ U : Set (ℝ × ℝ),
      ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧
          IsOpen V ∧
            frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V ∧
              Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
                Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V ∧
                  Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain ∧
                    Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain ∧
                      ∃ f : (ℝ × ℝ) → M,
                        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V) ∧
                          Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U ∧
                            Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                  f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) := by
  let Dlo := WhitneyPairModel.lowerStripCoordinates h ⁻¹' k.domain
  let Dhi := WhitneyPairModel.upperStripCoordinates h ⁻¹' l.domain
  have hDlo : IsOpen Dlo :=
    k.open_domain.preimage (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').continuous
  have hDhi : IsOpen Dhi :=
    l.open_domain.preimage (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').continuous
  have hkl :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) Dlo :=
    k.smooth.comp (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  have hlu :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (l.map ∘ WhitneyPairModel.upperStripCoordinates h) Dhi :=
    l.smooth.comp (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne').contMDiff.contMDiffOn
      (fun _ hp => hp)
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ := mem_nhds_iff.mp (bigon_strip_maps_left_germ hh.ne' c₀ c₁ k l)
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ :=
    mem_nhds_iff.mp (bigon_strip_maps_right_germ hh.ne' c₀ c₁ k l)
  have hlowD : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) Dlo := by
    intro t ht
    change WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0) ∈ k.domain
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have huppD :
    Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) Dhi := by
    intro t ht
    change
      WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ l.domain
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  obtain ⟨U, V, hU, hV, hUD, hVD, hover, hlowU, huppV, hfront⟩ :=
    WhitneyPairModel.exists_bigon_boundary_cover hh hDlo hDhi (hO₀.union hO₁) (Or.inl hleft)
      (Or.inr hright) hlowD huppD
  have hfg :
    Set.EqOn (k.map ∘ WhitneyPairModel.lowerStripCoordinates h)
      (l.map ∘ WhitneyPairModel.upperStripCoordinates h) (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨f, hf, hflo, hfhi⟩ := exists_smooth_open_gluing hU hV (hkl.mono hUD) (hlu.mono hVD) hfg
  refine
    ⟨U, V, hU, hV, hfront, hlowU, huppV, fun _ hp => hUD hp, fun _ hp => hVD hp, f, hf, hflo,
      hfhi, ?_, ?_⟩
  · intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  · intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht


/-- The map glued from the two strip patches is an immersion at every point of the frontier of the
bigon.
-/
theorem injective_mfderiv_of_mem_frontier_bigon {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∀ p ∈ frontier (WhitneyPairModel.bigon h),
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  intro p hp
  obtain ⟨t, ht, rfl | rfl⟩ := (WhitneyPairModel.mem_frontier_bigon_iff_exists_time hh p).mp hp
  · exact
      injective_mfderiv_of_eqOn_cleanStripPatch_comp k
        (WhitneyPairModel.contDiff_lowerStripCoordinates hh.ne') hU hflo hmapU (hlowU ht)
        (WhitneyPairModel.injective_fderiv_lowerStripCoordinates hh.ne' _)
  · exact
      injective_mfderiv_of_eqOn_cleanStripPatch_comp l
        (WhitneyPairModel.contDiff_upperStripCoordinates hh.ne') hV hfhi hmapV (huppV ht)
        (WhitneyPairModel.injective_fderiv_upperStripCoordinates hh.ne' _)

/-- The glued map is injective and an immersion on some open neighbourhood of the frontier of the
bigon, hence an embedding there.
-/
theorem exists_embedded_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    (hfront : frontier (WhitneyPairModel.bigon h) ⊆ U ∪ V)
    (hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U)
    (huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V)
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V))
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        frontier (WhitneyPairModel.bigon h) ⊆ W ∧
          W ⊆ U ∪ V ∧
            Set.InjOn f W ∧ ∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p) := by
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t := by
    intro t ht
    rw [hflo (hlowU ht)]
    change k.map (WhitneyPairModel.lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [WhitneyPairModel.lowerStripCoordinates_lower]
    exact k.center t ht
  have hupp : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t := by
    intro t ht
    rw [hfhi (huppV ht)]
    change
      l.map (WhitneyPairModel.upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) =
        b t
    rw [WhitneyPairModel.upperStripCoordinates_upper]
    exact l.center t ht
  have hinj :=
    WhitneyPairModel.injOn_frontier_bigon_of_arcs hh k.center_injOn l.center_injOn hlow hupp
      (strip_center_coincidences_of_corner_overlap k l hover)
  have hi :=
    injective_mfderiv_of_mem_frontier_bigon hh k l hU hV hlowU huppV hmapU hmapV hflo hfhi
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  exact
    ManifoldImmersion.exists_open_embedded_immersive_neighborhood (hU.union hV) hf hcompact hfront
      hinj hi


/-- The map glued from the two strip patches avoids both sheets on the interior of the bigon; the
bigon meets the two sheets only in its two edges.
-/
theorem bigon_boundary_map_avoids_sheets {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁) {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hmapU : Set.MapsTo (WhitneyPairModel.lowerStripCoordinates h) U k.domain)
    (hmapV : Set.MapsTo (WhitneyPairModel.upperStripCoordinates h) V l.domain)
    (hflo : Set.EqOn f (k.map ∘ WhitneyPairModel.lowerStripCoordinates h) U)
    (hfhi : Set.EqOn f (l.map ∘ WhitneyPairModel.upperStripCoordinates h) V) {p : ℝ × ℝ}
    (hp : p ∈ U ∪ V) (hpi : p ∈ interior (WhitneyPairModel.bigon h)) : f p ∉ S ∪ T := by
  rcases hp with hpU | hpV
  · rw [hflo hpU]
    have hc := WhitneyPairModel.lowerStripCoordinates_interior hh hpi
    exact k.avoids_sheets (hmapU hpU) hc.1 hc.2.ne'
  · rw [hfhi hpV]
    have hc := WhitneyPairModel.upperStripCoordinates_interior hh hpi
    change l.map (WhitneyPairModel.upperStripCoordinates h p) ∉ S ∪ T
    rw [Set.union_comm]
    exact l.avoids_sheets (hmapV hpV) hc.1 hc.2.ne'

/-- A clean embedded neighbourhood of the boundary of the Whitney bigon of height `h`: an immersed
injective map defined on an open set containing a compact neighbourhood of the frontier of the
bigon, a closed embedding there, restricting to the arcs `a` and `b` on the two edges, given
near the edges by the strip charts `k` and `l`, and avoiding the sheets `S` and `T` at every point
of the bigon off its frontier. Only the bigon side is constrained: nothing is asserted about the
points of the neighbourhood outside the bigon.
-/
structure CleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M)
    (h : ℝ) where
  height_pos : 0 < h
  map : (ℝ × ℝ) → M
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : Set.InjOn map domain
  derivative_injective : ∀ p ∈ domain, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ domain ∩ interior (WhitneyPairModel.bigon h), map p ∉ S ∪ T
  closed_neighborhood : Set (ℝ × ℝ)
  compact_neighborhood : IsCompact closed_neighborhood
  closed_closed_neighborhood : IsClosed closed_neighborhood
  boundary_covered : frontier (WhitneyPairModel.bigon h) ⊆ interior closed_neighborhood
  neighborhood_subset : closed_neighborhood ⊆ domain
  closed_embedding : Topology.IsClosedEmbedding (fun p : closed_neighborhood => map p)
  clean :
    ∀ p ∈ WhitneyPairModel.bigon h ∩ closed_neighborhood,
      p ∉ frontier (WhitneyPairModel.bigon h) → map p ∉ S ∪ T
  lower : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Set.Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ WhitneyPairModel.lowerStripCoordinates h
  upper_germ :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
        l ∘ WhitneyPairModel.upperStripCoordinates h

/-- Existence of a clean embedded neighbourhood of the bigon boundary: two clean corner patches and
two clean strip patches for the arcs `a` and `b` glue to a map `f` which is smooth, injective and
an immersion on an open set `W`, is a closed embedding on a compact neighbourhood `C ⊆ W` of the
frontier of the bigon, restricts to `a` and `b` on the two edges, agrees near the edges with the
strip charts `k` and `l`, and avoids the sheets `S` and `T` at every point of `W` in the interior
of the bigon and at every point of the bigon in `C` off its frontier.  Only the bigon side is
constrained: nothing is asserted about the points of `W` outside the bigon.
-/
theorem exists_clean_bigon_boundary_neighborhood {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∃ f : (ℝ × ℝ) → M,
      ∃ W : Set (ℝ × ℝ),
        IsOpen W ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W ∧
            Set.InjOn f W ∧
              (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
                (∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T) ∧
                  ∃ C : Set (ℝ × ℝ),
                    IsCompact C ∧
                      IsClosed C ∧
                        frontier (WhitneyPairModel.bigon h) ⊆ interior C ∧
                          C ⊆ W ∧
                            Topology.IsClosedEmbedding (fun p : C => f p) ∧
                              (∀ p ∈ WhitneyPairModel.bigon h ∩ C,
                                  p ∉ frontier (WhitneyPairModel.bigon h) → f p ∉ S ∪ T) ∧
                                (∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                      f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) ∧
                                    (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, 0)]
                                          k.map ∘ WhitneyPairModel.lowerStripCoordinates h) ∧
                                      (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                        f =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
                                          l.map ∘ WhitneyPairModel.upperStripCoordinates h) := by
  obtain ⟨U, V, hU, hV, hfront, hlowU, huppV, hmapU, hmapV, f, hf, hflo, hfhi, hlow, hupp⟩ :=
    exists_smooth_bigon_boundary_neighborhood hh c₀ c₁ k l
  obtain ⟨W, hW, hfrontW, hWUV, hinj, hi⟩ :=
    exists_embedded_bigon_boundary_neighborhood hh k l hover hU hV hfront hlowU huppV hmapU hmapV
      hf hflo hfhi
  have hclean : ∀ p ∈ W ∩ interior (WhitneyPairModel.bigon h), f p ∉ S ∪ T := fun p hp =>
    bigon_boundary_map_avoids_sheets hh k l hmapU hmapV hflo hfhi (hWUV hp.1) hp.2
  have hcompact : IsCompact (frontier (WhitneyPairModel.bigon h)) :=
    (WhitneyPairModel.isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((WhitneyPairModel.mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCclosed, hfrontC, hCW⟩ := exists_compact_closed_between hcompact hW hfrontW
  have hemb : Topology.IsClosedEmbedding (fun p : C => f p) := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hc : Continuous (fun p : C => f p) :=
      continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono (hCW.trans hWUV))
    apply hc.isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj (hCW p.property) (hCW q.property) hpq)
  refine
    ⟨f, W, hW, hf.mono hWUV, hinj, hi, hclean, C, hC, hCclosed, hfrontC, hCW, hemb, ?_, hlow,
      hupp, ?_, ?_⟩
  · intro p hp hnot
    apply hclean p ⟨hCW hp.2, ?_⟩
    by_contra hni
    apply hnot
    rw [frontier, (WhitneyPairModel.isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hni⟩
  · intro t ht
    exact Filter.mem_of_superset (hU.mem_nhds (hlowU ht)) (fun _ hp => hflo hp)
  · intro t ht
    exact Filter.mem_of_superset (hV.mem_nhds (huppV ht)) (fun _ hp => hfhi hp)

/-- The same statement packaged as the nonemptiness of `CleanBigonBoundary`. -/
theorem nonempty_cleanBigonBoundary {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {h : ℝ} (hh : 0 < h) {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀) (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover :
      ∀ p ∈ k.domain,
        ∀ q ∈ l.domain,
          k.map p = l.map q →
            p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    Nonempty (CleanBigonBoundary (E := E) S T a b k.map l.map h) := by
  obtain
    ⟨f, W, hW, hf, hinj, hi, havoid, C, hC, hCc, hfront, hCW, hemb, hclean, hlow, hupp, hlowg,
      huppg⟩ :=
    exists_clean_bigon_boundary_neighborhood hh c₀ c₁ k l hover
  exact
    ⟨{  height_pos := hh
        map := f
        domain := W
        open_domain := hW
        smooth := hf
        injective := hinj
        derivative_injective := hi
        interior_avoids := havoid
        closed_neighborhood := C
        compact_neighborhood := hC
        closed_closed_neighborhood := hCc
        boundary_covered := hfront
        neighborhood_subset := hCW
        closed_embedding := hemb
        clean := hclean
        lower := hlow
        upper := hupp
        lower_germ := hlowg
        upper_germ := huppg }⟩

end
