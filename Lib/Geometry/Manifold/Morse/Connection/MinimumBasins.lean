/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Geometry.Manifold.Morse.Rearrangement

/-!
# Density of the forward basins of the minima

For the flow of a descent field adapted to surgery windows (`AdaptedWindows E f`) on a compact
manifold, the forward basin of a critical point of positive index is the flow image of a
codimension `≥ 1` coordinate plane, hence meagre:
`native_positive_plane_piece_nowhereDense` (from the general facts
`compact_partial_chart_image_nowhereDense` and `interior_zero_product_empty`) and
`nonminimum_forward_basin_meagre`. By the Baire category theorem the union of the forward
basins of the minima (index `0`) is dense: `dense_minimum_forward_basins`.

The belt passage of a handle (`BeltPassage.upper`, `BeltPassage.lower`) is carried by the flow
(`flow_belt_passage`, `belt_passage_forward_limit_iff`), so a branch of the attaching sphere
landing in a minimum basin yields belt branches landing there as well
(`exists_positive_belt_branch_in_minimum_basin`,
`exists_two_sided_belt_branch_in_minimum_basin`).

cf. Milnor, *Lectures on the h-cobordism theorem*, §4 (the stable manifold of a critical point of
index `λ` is a `λ`-cell).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff NNReal

noncomputable section

/-! ### Belt passage -/

attribute [local instance 100] Classical.propDecidable in
/-- The flow belt passage through the adapted windows. -/
theorem AdaptedWindows.flow_belt_passage {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    S.flow (BeltPassage.time s)
        ((S.data q).chart.splitChart.symm
          (BeltPassage.upper (S.data q).radius s u.val v.val)) =
      (S.data q).chart.splitChart.symm
        (BeltPassage.lower (S.data q).radius s u.val v.val) := by
  let d := S.data q
  let z := BeltPassage.upper d.radius s u.val v.val
  have htime := BeltPassage.time_nonneg hs
  have hstay (t : ℝ) (ht : t ∈ Set.uIcc 0 (BeltPassage.time s)) :
    MorseHandle.descentFlow t z ∈
      Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
        Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    rw [Set.uIcc_of_le htime] at ht
    exact
      BeltPassage.descentFlow_mem_block d.radius_pos hs hs₁
        (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property) ht
  have hz : z ∈ d.chart.splitChart.target := by
    have hh := d.block (hstay 0 Set.left_mem_uIcc)
    simpa only [MorseHandle.descentFlow.map_zero_apply] using hh
  have hcoords : d.chart.splitChart (d.chart.splitChart.symm z) = z :=
    d.chart.splitChart.right_inv' hz
  have hflow :=
    d.chart.flow_eq_descentModel_of_mem_uIcc (S.smooth.of_le (by simp)) S.flow S.integral (x :=
      d.chart.splitChart.symm z) (d.chart.splitChart.map_target' hz) (t :=
      BeltPassage.time s) (fun t ht => by rw [hcoords]; exact d.block (hstay t ht))
      (fun t ht => by rw [hcoords]; exact S.model_germ q _ (hstay t ht))
  change
    S.flow (BeltPassage.time s) (d.chart.splitChart.symm z) =
      d.chart.splitChart.symm
        (MorseHandle.descentFlow (BeltPassage.time s)
          (d.chart.splitChart (d.chart.splitChart.symm z))) at hflow
  rw [hcoords, BeltPassage.descentFlow_time d.radius hs u.val v.val] at hflow
  exact hflow

attribute [local instance 100] Classical.propDecidable in
/-- The belt passage's forward limit characterization. -/
theorem AdaptedWindows.belt_passage_forward_limit_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} (S : AdaptedWindows E f) (q : ManifoldMorse.criticalPoints E f) {s : ℝ}
    (hs : 0 < s) (hs₁ : s ≤ 1) (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (p : M) :
    Filter.Tendsto
        (fun t =>
          S.flow t
            ((S.data q).chart.splitChart.symm
              (BeltPassage.upper (S.data q).radius s u.val v.val)))
        Filter.atTop (𝓝 p) ↔
      Filter.Tendsto
        (fun t =>
          S.flow t
            ((S.data q).chart.splitChart.symm
              (BeltPassage.lower (S.data q).radius s u.val v.val)))
        Filter.atTop (𝓝 p) := by
  rw [← S.flow_belt_passage q hs hs₁ u v]
  exact (MorseCancellation.flow_time_atTop_limit_iff S.flow (BeltPassage.time s) _ p).symm

/-! ### Nowhere-dense critical pieces -/

/-- A compact partial chart image is nowhere dense. -/
theorem MorseCancellation.compact_partial_chart_image_nowhereDense {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] [T2Space X] (e : OpenPartialHomeomorph X A) {K : Set A}
    (hK : IsCompact K) (hKt : K ⊆ e.target) (hKi : interior K = ∅) :
    IsNowhereDense (e.symm '' K) := by
  have hclosed : IsClosed (e.symm '' K) :=
    (hK.image_of_continuousOn (e.symm.continuousOn.mono hKt)).isClosed
  apply hclosed.isNowhereDense_iff.mpr
  have hsource : e.symm '' K ⊆ e.source := by
    rintro x ⟨z, hz, rfl⟩
    exact e.map_target (hKt hz)
  have hopen : IsOpen (e '' interior (e.symm '' K)) :=
    e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hsource)
  have hsub : e '' interior (e.symm '' K) ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := interior_subset hx
    rw [← hzx, e.right_inv (hKt hz)]
    exact hz
  have hinto : e '' interior (e.symm '' K) ⊆ interior K := hopen.subset_interior_iff.mpr hsub
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := hinto (Set.mem_image_of_mem e hx)
  exact (Set.eq_empty_iff_forall_notMem.mp hKi) _ hh

/-- A zero-dimensional product has empty interior. -/
theorem MorseCancellation.interior_zero_product_empty {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [Nontrivial A] [TopologicalSpace B] (s : Set B) :
    interior (({0} : Set A) ×ˢ s) = ∅ := by
  rw [interior_prod_eq, interior_singleton, Set.empty_prod]

/-- The native positive plane piece is nowhere dense. -/
theorem MorseCancellation.native_positive_plane_piece_nowhereDense {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (c : ManifoldMorse.SignedMorseChart (E := E) f p)
    (hindex : 0 < Module.finrank ℝ c.NegativeCoordinates) {r : ℝ}
    (hblock :
      ({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target) :
    IsNowhereDense
      (c.splitChart.symm ''
        (({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) r)) :=
  by
  let : Nontrivial c.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  exact
    compact_partial_chart_image_nowhereDense c.splitChart.toOpenPartialHomeomorph
      (isCompact_singleton.prod (ProperSpace.isCompact_closedBall _ _)) hblock
      (interior_zero_product_empty _)

/-! ### The native Morse index -/

/-- The non-minimum forward basin is meagre. -/
theorem AdaptedWindows.nonminimum_forward_basin_meagre {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hindex : 0 < MorseCancellation.nativeMorseIndex E f p) :
    IsMeagre {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ :=
    MorseCancellation.exists_descending_morse_basin_block c hf (S.smooth.of_le (by simp)) S.flow
      S.integral S.zero S.descent (S.critical_model_germ p)
  let K :=
    c.splitChart.symm ''
      (({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) (r / 2))
  have hKt :
    ({0} : Set c.NegativeCoordinates) ×ˢ Metric.closedBall (0 : c.PositiveCoordinates) (r / 2) ⊆
      c.splitChart.target := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha0 : a = 0 := ha
    subst a
    exact
      hblock
        ⟨Metric.mem_closedBall_self hr.le,
          Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ r) hb⟩
  have hi : 0 < Module.finrank ℝ c.NegativeCoordinates := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart c] at hindex
  have hK : IsNowhereDense K := MorseCancellation.native_positive_plane_piece_nowhereDense c hi hKt
  have hcover :
    {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} ⊆
      ⋃ n : ℕ, S.flow (-(n : ℝ)) '' K := by
    intro x hx
    have hlim : Filter.Tendsto (fun n : ℕ => S.flow (n : ℝ) x) Filter.atTop (𝓝 p.val) :=
      hx.comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hs, hn, hp⟩ :=
      (hlim.eventually
          (MorseCancellation.morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
    have hnew : Filter.Tendsto (fun t => S.flow t (S.flow (n : ℝ) x)) Filter.atTop (𝓝 p.val) :=
      (MorseCancellation.flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
    have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
      ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp.trans (half_lt_self hr))).1).mp hnew
    have hmem : S.flow (n : ℝ) x ∈ K := by
      refine ⟨c.splitChart (S.flow (n : ℝ) x), ?_, c.splitChart.left_inv' hs⟩
      exact ⟨Set.mem_singleton_iff.mpr hz, mem_closedBall_zero_iff.mpr hp.le⟩
    exact
      Set.mem_iUnion.mpr
        ⟨n, S.flow (n : ℝ) x, hmem, (S.flow.toHomeomorph (n : ℝ)).symm_apply_apply x⟩
  apply IsMeagre.mono hcover
  apply isMeagre_iUnion
  intro n
  exact ((S.flow.toHomeomorph (-(n : ℝ))).isInducing.isNowhereDense_image hK).isMeagre

/-! ### Minimum basins -/

/-- The minimum forward basins are dense. -/
theorem AdaptedWindows.dense_minimum_forward_basins {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    Dense
      {x : M |
        ∃ p : ManifoldMorse.criticalPoints E f,
          MorseCancellation.nativeMorseIndex E f p = 0 ∧
            Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
  let : Finite (ManifoldMorse.criticalPoints E f) := S.finite.to_subtype
  let I :=
    { p : ManifoldMorse.criticalPoints E f // 0 < MorseCancellation.nativeMorseIndex E f p }
  let B := ⋃ p : I, {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val.val)}
  have hm : IsMeagre B :=
    isMeagre_iUnion (fun p : I => S.nonminimum_forward_basin_meagre hf p.val p.property)
  have hd : Dense Bᶜ := dense_of_mem_residual hm
  apply hd.mono
  intro x hx
  obtain ⟨r, hr, p, hp, -, hlim, -⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x
  have hi : MorseCancellation.nativeMorseIndex E f p = 0 := by
    by_contra hi
    apply hx
    exact Set.mem_iUnion.mpr ⟨(⟨⟨p, hp⟩, Nat.pos_of_ne_zero hi⟩ : I), hlim⟩
  exact ⟨⟨p, hp⟩, hi, hlim⟩

attribute [local instance 100] Classical.propDecidable in
/-- A positive belt branch in the minimum basin exists. -/
theorem AdaptedWindows.exists_positive_belt_branch_in_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranch :
      Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          ∀ s : ℝ,
            0 < s →
              s < ε →
                Filter.Tendsto
                  (fun t =>
                    S.flow t
                      ((S.data q).chart.splitChart.symm
                        (BeltPassage.upper (S.data q).radius s u.val v.val)))
                  Filter.atTop (𝓝 p.val) := by
  let d := S.data q
  have h0target : BeltPassage.lower d.radius 0 u.val v.val ∈ d.chart.splitChart.target := by
    rw [BeltPassage.lower_zero]
    apply d.block
    constructor
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos,
        mem_sphere_zero_iff_norm.mp u.property, mul_one]
      linarith [d.radius_pos]
    · exact Metric.mem_closedBall_self (by linarith [d.radius_pos])
  have h0value :
    d.chart.splitChart.symm (BeltPassage.lower d.radius 0 u.val v.val) =
      (d.surgery.attachingSphere u).val := by
    rw [BeltPassage.lower_zero, d.attaching_eq, d.chart.attachingCoreMap_coe]
  have hc :
    ContinuousAt
      (fun s : ℝ => d.chart.splitChart.symm (BeltPassage.lower d.radius s u.val v.val))
      0 :=
    (d.chart.splitChart.contMDiffOn_invFun.continuousOn.continuousAt
          (d.chart.splitChart.open_target.mem_nhds h0target)).comp
      (f := fun s : ℝ => BeltPassage.lower d.radius s u.val v.val)
      (BeltPassage.contDiff_lower d.radius u.val v.val).continuous.continuousAt
  have hbasin :
    d.chart.splitChart.symm (BeltPassage.lower d.radius 0 u.val v.val) ∈
      {x : M | Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)} := by
    rw [h0value]
    exact hbranch
  have hnear := hc.tendsto.eventually ((S.isOpen_minimum_forward_basin hf p hp).mem_nhds hbasin)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨Min.min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro s hs hsε
  have hs₁ : s ≤ 1 := (hsε.trans_le (min_le_right _ _)).le
  apply (S.belt_passage_forward_limit_iff q hs hs₁ u v p.val).mpr
  apply hδsub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
  exact hsε.trans_le (min_le_left _ _)

attribute [local instance 100] Classical.propDecidable in
/-- A two-sided belt branch in the minimum basin exists. -/
theorem AdaptedWindows.exists_two_sided_belt_branch_in_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε ≤ 1 ∧
          ∀ s : ℝ,
            0 < |s| →
              |s| < ε →
                Filter.Tendsto
                  (fun t =>
                    S.flow t
                      ((S.data q).chart.splitChart.symm
                        (BeltPassage.upper (S.data q).radius s u.val v.val)))
                  Filter.atTop (𝓝 p.val) := by
  let u' : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1 :=
    ⟨-u.val,
      mem_sphere_zero_iff_norm.mpr
        (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp u.property)⟩
  obtain ⟨εp, hεp, hεp1, hplus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u v (hbranches u)
  obtain ⟨εn, hεn, -, hminus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u' v (hbranches u')
  refine ⟨Min.min εp εn, lt_min hεp hεn, (min_le_left _ _).trans hεp1, ?_⟩
  intro s hs hsmall
  by_cases hpos : 0 < s
  · apply hplus s hpos
    rw [abs_of_pos hpos] at hsmall
    exact hsmall.trans_le (min_le_left _ _)
  · have hneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (abs_pos.mp hs)
    have heq :
      BeltPassage.upper (S.data q).radius s u.val v.val =
        BeltPassage.upper (S.data q).radius (-s) u'.val v.val := by
      simpa only [neg_neg] using BeltPassage.upper_neg (S.data q).radius (-s) u.val v.val
    rw [heq]
    apply hminus (-s) (neg_pos.mpr hneg)
    rw [abs_of_neg hneg] at hsmall
    exact hsmall.trans_le (min_le_right _ _)

end
