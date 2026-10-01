/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# Homeomorphisms onto the unit disc escape to the boundary circle

Let `e : U ≃ₜ 𝔻` be a homeomorphism from a set `U ⊆ ℂ` onto the open unit disc. Preimages of the
closed discs `‖w‖ ≤ r < 1` are compact, so `‖e z‖ → 1` whenever `z` leaves every compact subset of
`U`: along a filter converging to a point outside `U`, along the cocompact filter, as `‖z‖ → ∞` or
`Im z → ∞`, and, for a continuous boundary chart `φ` of the closed upper half-plane that sends the
open half-plane into `U` and a real point outside `U`, along `φ` as one approaches the real axis.

This is the elementary half of the boundary behaviour of a conformal map onto the disc (Ahlfors,
*Complex Analysis*, Ch. 6 §1; Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.1).

## Main results

* `RiemannMapping.isCompact_discHomeomorph_preimage_closedBall`
* `RiemannMapping.tendsto_norm_discHomeomorph_of_notMem`
* `RiemannBoundary.tendsto_norm_discHomeomorph_of_cocompact`
* `RiemannBoundary.tendsto_norm_discHomeomorph_in_boundary_chart`
-/

open Set Function Filter Topology

noncomputable section

/-- For a homeomorphism `e : U ≃ₜ 𝔻` and `r < 1`, the set of points of `U` with `‖e z‖ ≤ r` is
compact. -/
theorem RiemannMapping.isCompact_discHomeomorph_preimage_closedBall {U : Set ℂ}
    (e : U ≃ₜ Metric.ball (0 : ℂ) 1) {r : ℝ} (hr : r < 1) :
    IsCompact
      ((Subtype.val : U → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))) := by
  apply IsCompact.image _ continuous_subtype_val
  apply e.isCompact_preimage.mpr
  apply
    Topology.IsInducing.subtypeVal.isCompact_preimage' (ProperSpace.isCompact_closedBall _ _) ?_
  simpa only [Subtype.range_coe] using Metric.closedBall_subset_ball hr

/-- For a homeomorphism `e : U ≃ₜ 𝔻`, if `z i → a` with `a ∉ U`, then `‖e (z i)‖ → 1`. -/
theorem RiemannMapping.tendsto_norm_discHomeomorph_of_notMem {U : Set ℂ}
    (e : U ≃ₜ Metric.ball (0 : ℂ) 1) {α : Type*} {l : Filter α} {z : α → U} {a : ℂ} (ha : a ∉ U)
    (hz : Filter.Tendsto (fun i => (z i : ℂ)) l (𝓝 a)) :
    Filter.Tendsto (fun i => ‖(e (z i) : ℂ)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ :=
      (Subtype.val : U → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))
    have hK : IsCompact K := isCompact_discHomeomorph_preimage_closedBall e hr
    have haK : a ∉ K := by
      rintro ⟨w, _, hwa⟩
      exact ha (hwa ▸ w.property)
    have hevent : ∀ᶠ i in l, (z i : ℂ) ∉ K :=
      hz.eventually (hK.isClosed.isOpen_compl.mem_nhds haK)
    filter_upwards [hevent] with i hi
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨z i, ?_, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hle
  · intro r hr
    apply Filter.Eventually.of_forall
    intro i
    have hi : ‖(e (z i) : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (e (z i)).property
    exact hi.trans hr

/-- The disc-coordinate norm tends to `1` along cocompact filters. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_cocompact {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto z l (Filter.cocompact ℂ))
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ :=
      (Subtype.val : D → ℂ) ''
        (e ⁻¹' ((Subtype.val : Metric.ball (0 : ℂ) 1 → ℂ) ⁻¹' Metric.closedBall 0 r))
    have hK : IsCompact K := RiemannMapping.isCompact_discHomeomorph_preimage_closedBall e hr
    have hesc : ∀ᶠ i in l, z i ∉ K := hz.eventually hK.compl_mem_cocompact
    filter_upwards [hesc, hmem] with i hi him
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨⟨z i, him⟩, ?_, rfl⟩
    have hh := he ⟨z i, him⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, ← hh] using hle
  · intro r hr
    filter_upwards [hmem] with i hi
    have hh := he ⟨z i, hi⟩
    have hb : ‖f (z i)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, ← hh] using (e ⟨z i, hi⟩).property
    exact hb.trans hr

/-- The disc norm tends to `1` as the norm tends to infinity. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_norm_atTop {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto (fun i => ‖z i‖) l Filter.atTop)
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_cocompact e he _ hmem
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hz

/-- The disc norm tends to `1` as the imaginary part tends to infinity. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_of_im_atTop {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {α : Type*}
    {l : Filter α} {z : α → ℂ} (hz : Filter.Tendsto (fun i => (z i).im) l Filter.atTop)
    (hmem : ∀ᶠ i in l, z i ∈ D) : Filter.Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) :=
  tendsto_norm_discHomeomorph_of_norm_atTop e he
    (Filter.tendsto_atTop_mono (fun i => Complex.im_le_norm (z i)) hz) hmem

/-- If `f` restricts to a homeomorphism `D ≃ₜ 𝔻` and `a ∉ D`, then `‖f z‖ → 1` as `z → a` within
`D`. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_nhdsWithin_of_notMem {D : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) {a : ℂ}
    (ha : a ∉ D) : Filter.Tendsto (fun z => ‖f z‖) (𝓝[D] a) (𝓝 1) := by
  have hz :
    Filter.Tendsto (Subtype.val : D → ℂ) (Filter.comap (Subtype.val : D → ℂ) (𝓝[D] a)) (𝓝 a) :=
    Filter.tendsto_comap.mono_right nhdsWithin_le_nhds
  have ht := RiemannMapping.tendsto_norm_discHomeomorph_of_notMem e ha hz
  apply (Filter.tendsto_comap'_iff (i := (Subtype.val : D → ℂ)) ?_).mp
  · simpa only [Function.comp_def, he] using ht
  · simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : D ∈ 𝓝[D] a)

/-- Let `f` restrict to a homeomorphism `D ≃ₜ 𝔻` and let `φ` be continuous on `U ∩ {Im z ≥ 0}` (`U`
open) and map `U ∩ {Im z > 0}` into `D`. If `x ∈ U` is real and `φ x ∉ D`, then `‖f (φ z)‖ → 1` as
`z → x` from the upper half-plane. -/
theorem RiemannBoundary.tendsto_norm_discHomeomorph_in_boundary_chart {D U : Set ℂ}
    (e : D ≃ₜ Metric.ball (0 : ℂ) 1) {f φ : ℂ → ℂ} (he : ∀ z : D, f z = (e z : ℂ)) (hU : IsOpen U)
    (hφ : ContinuousOn φ (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hside : Set.MapsTo φ (U ∩ {z : ℂ | 0 < z.im}) D) {x : ℝ} (hx : (x : ℂ) ∈ U)
    (hout : φ (x : ℂ) ∉ D) :
    Filter.Tendsto (fun z => ‖f (φ z)‖) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 1) := by
  apply (tendsto_norm_discHomeomorph_nhdsWithin_of_notMem e he hout).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc := hφ (x : ℂ) ⟨hx, by simp⟩
    apply hc.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Filter.tendsto_id.mono_right nhdsWithin_le_nhds
    · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
      exact ⟨hz, le_of_lt hu⟩
  · have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) := mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hu
    exact hside ⟨hz, hu⟩
