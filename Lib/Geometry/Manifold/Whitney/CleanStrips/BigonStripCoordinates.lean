/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Lib.Geometry.Manifold.Whitney.CleanStrips.StripModel

/-!
# Strip coordinates on the Whitney bigon

Facts about the planar model `WhitneyPairModel` of the bigon of height `h > 0`, bounded by the
lower edge `t ↦ (2t - 1, 0)` and the upper edge `t ↦ (2t - 1, h (1 - (2t - 1)²))`:

* the lower and upper strip charts `lowerStripCoordinates h`, `upperStripCoordinates h` are
  immersions along the respective edges, and the edge exchange is an immersion everywhere;
* the frontier of the bigon is the union of the two edges, and a map restricting to two
  injective arcs on the edges that meet only at their common endpoints is injective on it;
* both strip charts carry the interior of the bigon into the open strip `(0, 1) × (0, ∞)`.

These are the coordinates in which the Whitney disk is built from two strips along its edges
(Milnor, *Lectures on the h-cobordism theorem*, §6).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- The lower strip chart of the bigon has horizontal derivative `(1/2, 0)` on the lower edge, the
arc parameter running at half speed.
-/
theorem WhitneyPairModel.lowerStripCoordinates_horizontal_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0) = (1 / 2, 0) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_horizontalSlice hf
  have heq : (fun x : ℝ => lowerStripCoordinates h (x, 0)) = fun x => ((x + 1) / 2, 0) := by
    funext x
    simp [lowerStripCoordinates, arcTime]
  rw [heq] at hd
  exact
    hd.unique (((hasDerivAt_id s).add_const 1).div_const 2 |>.prodMk (hasDerivAt_const s (0 : ℝ)))

/-- The vertical derivative of the lower strip chart of the bigon on the lower edge, in terms of the
corner sign and the corner scale.
-/
theorem WhitneyPairModel.lowerStripCoordinates_vertical_derivative {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) :
    fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1) =
      (cornerSign ((s + 1) / 2) * (1 / (4 * h * cornerScale ((s + 1) / 2))),
        1 / (4 * h * cornerScale ((s + 1) / 2))) := by
  have hf : DifferentiableAt ℝ (lowerStripCoordinates h) (s, 0) :=
    (contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp)
  have hd := StripCoordinates.hasDerivAt_verticalSlice hf
  have hdiv :
    HasDerivAt (fun u : ℝ => u / (4 * h * cornerScale ((s + 1) / 2)))
      (1 / (4 * h * cornerScale ((s + 1) / 2))) 0 :=
    (hasDerivAt_id 0).div_const _
  have hfirst := (HasDerivAt.const_mul (cornerSign ((s + 1) / 2)) hdiv).const_add ((s + 1) / 2)
  exact hd.unique (hfirst.prodMk hdiv)

/-- The lower strip chart of the bigon is an immersion along the lower edge. -/
theorem WhitneyPairModel.injective_fderiv_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (lowerStripCoordinates h) (s, 0)) := by
  let L := fderiv ℝ (lowerStripCoordinates h) (s, 0)
  have hhor : ((2 : ℝ) • L) (1, 0) = (1, 0) := by
    change (2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (1, 0)) = (1, 0)
    rw [lowerStripCoordinates_horizontal_derivative hh]
    norm_num
  have hnorm : (((2 : ℝ) • L) (0, 1)).2 ≠ 0 := by
    change ((2 : ℝ) • (fderiv ℝ (lowerStripCoordinates h) (s, 0) (0, 1))).2 ≠ 0
    rw [lowerStripCoordinates_vertical_derivative hh]
    change (2 : ℝ) * (1 / (4 * h * cornerScale ((s + 1) / 2))) ≠ 0
    exact
      mul_ne_zero (by norm_num)
        (one_div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne'))
  have hi :=
    StripCoordinates.injective_plane_of_horizontal_and_normal ((2 : ℝ) • L) hhor hnorm
  intro x y hxy
  exact hi (congrArg (fun z : ℝ × ℝ => (2 : ℝ) • z) hxy)

/-- The edge exchange of the bigon is an immersion (indeed a diffeomorphism) everywhere. -/
theorem WhitneyPairModel.injective_fderiv_exchangeEdges (h : ℝ) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (exchangeEdges h) p) := by
  have heq : exchangeEdges h ∘ exchangeEdges h = id := funext (exchangeEdges_involutive h)
  have hd :
    (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [←
      fderiv_comp p ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))
        ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp)),
      heq, fderiv_id]
  intro x y hxy
  have he := congrArg (fderiv ℝ (exchangeEdges h) (exchangeEdges h p)) hxy
  change
    ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p)) x =
      ((fderiv ℝ (exchangeEdges h) (exchangeEdges h p)).comp (fderiv ℝ (exchangeEdges h) p))
        y at he
  rw [hd] at he
  exact he

/-- The upper strip chart of the bigon is an immersion along the upper edge. -/
theorem WhitneyPairModel.injective_fderiv_upperStripCoordinates {h : ℝ} (hh : h ≠ 0)
    (s : ℝ) : Function.Injective (fderiv ℝ (upperStripCoordinates h) (s, h * (1 - s ^ 2))) := by
  rw [upperStripCoordinates,
    fderiv_comp _ ((contDiff_lowerStripCoordinates hh).contDiffAt.differentiableAt (by simp))
      ((contDiff_exchangeEdges h).contDiffAt.differentiableAt (by simp))]
  have heq : exchangeEdges h (s, h * (1 - s ^ 2)) = (s, 0) := by
    simp only [exchangeEdges, sub_self]
  rw [heq]
  exact (injective_fderiv_lowerStripCoordinates hh s).comp (injective_fderiv_exchangeEdges h _)

/-- The frontier of the bigon is exactly the union of the two parametrised edges `t ↦ (2t - 1, 0)`
and `t ↦ (2t - 1, h (1 - (2t - 1)²))` over `t ∈ [0, 1]`.
-/
theorem WhitneyPairModel.mem_frontier_bigon_iff_exists_time {h : ℝ} (hh : 0 < h)
    (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔
      ∃ t ∈ Set.Icc (0 : ℝ) 1, p = (2 * t - 1, 0) ∨ p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
  constructor
  · intro hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    refine ⟨t, ht, ?_⟩
    rcases hpedge with hpzero | hpupper
    · exact Or.inl (Prod.ext hbase hpzero)
    · right
      apply Prod.ext hbase
      rw [← hbase]
      exact hpupper
  · rintro ⟨t, ht, rfl | rfl⟩
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨lowerArc_mem_bigon hh.le ?_, Or.inl rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · apply (mem_frontier_bigon_iff h _).mpr
      refine ⟨upperArc_mem_bigon hh.le ?_, Or.inr rfl⟩
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]

/-- A map on the plane restricting to two injective arcs on the two edges of the bigon, which meet
only at the two shared endpoints, is injective on the frontier of the bigon.
-/
theorem WhitneyPairModel.injOn_frontier_bigon_of_arcs {M : Type*} {h : ℝ} (hh : 0 < h)
    {f : (ℝ × ℝ) → M} {a b : ℝ → M} (ha : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hb : Set.InjOn b (Set.Icc (0 : ℝ) 1))
    (hlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t)
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    Set.InjOn f (frontier (bigon h)) := by
  have hcross {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (heq : a t = b s) : (2 * t - 1, (0 : ℝ)) = (2 * s - 1, h * (1 - (2 * s - 1) ^ 2)) := by
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  intro p hp q hq heq
  obtain ⟨t, ht, hp'⟩ := (mem_frontier_bigon_iff_exists_time hh p).mp hp
  obtain ⟨s, hs, hq'⟩ := (mem_frontier_bigon_iff_exists_time hh q).mp hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · rw [hlower t ht, hlower s hs] at heq
    rw [ha ht hs heq]
  · rw [hlower t ht, hupper s hs] at heq
    exact hcross ht hs heq
  · rw [hupper t ht, hlower s hs] at heq
    exact (hcross hs ht heq.symm).symm
  · rw [hupper t ht, hupper s hs] at heq
    rw [hb ht hs heq]

/-- The interpolated strip time `t + (2β - 1) z / (4 h J)` of an interior point of the bigon again
lies strictly between `0` and `1`.
-/
theorem WhitneyPairModel.interpolated_strip_time_mem_Ioo {h t β z J : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hJ : 0 < J)
    (hJdef : J = (1 - β) * (1 - t) + β * t) (hz : 0 < z) (hzupper : z < 4 * h * t * (1 - t)) :
    t + (2 * β - 1) * (z / (4 * h * J)) ∈ Set.Ioo (0 : ℝ) 1 := by
  let H := 4 * h * t * (1 - t)
  have hH : 0 < H := mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
  let θ := z / H
  let e := t * β / J
  have hθ0 : 0 < θ := div_pos hz hH
  have hθ1 : θ < 1 := (div_lt_one hH).mpr hzupper
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg ht.1.le hβ.1) hJ.le
  have he1 : e ≤ 1 := by
    apply (div_le_one hJ).mpr
    rw [hJdef]
    have hr := mul_nonneg (sub_nonneg.mpr hβ.2) (sub_nonneg.mpr ht.2.le)
    nlinarith
  have hid : t + (2 * β - 1) * (z / (4 * h * J)) = (1 - θ) * t + θ * e := by
    dsimp [θ, e, H]
    field_simp [hh.ne', ht.1.ne', (sub_pos.mpr ht.2).ne', hJ.ne']
    rw [hJdef]
    ring
  rw [hid]
  constructor
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) ht.1) (mul_nonneg hθ0.le he0)
  · have hpos : 0 < (1 - θ) * (1 - t) + θ * (1 - e) :=
      add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hθ1) (sub_pos.mpr ht.2))
        (mul_nonneg hθ0.le (sub_nonneg.mpr he1))
    nlinarith

/-- The lower strip chart carries the interior of the bigon into the open strip: the time lies in
`(0, 1)` and the height is positive.
-/
theorem WhitneyPairModel.lowerStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (lowerStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (lowerStripCoordinates h p).2 := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  have hheight : 0 < h * (1 - p.1 ^ 2) := hp0.trans hphi
  have hsq : p.1 ^ 2 < 1 := by
    have hpos : 0 < 1 - p.1 ^ 2 := (mul_pos_iff_of_pos_left hh).mp hheight
    linarith
  have ht : arcTime p ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [arcTime]
    constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]
  have hβ : cornerTransition (arcTime p) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hheight_eq : h * (1 - p.1 ^ 2) = 4 * h * arcTime p * (1 - arcTime p) := by
    dsimp [arcTime]
    ring
  have hzupper : p.2 < 4 * h * arcTime p * (1 - arcTime p) := hheight_eq ▸ hphi
  refine ⟨?_, ?_⟩
  · exact interpolated_strip_time_mem_Ioo hh ht hβ (cornerScale_pos _) rfl hp0 hzupper
  · exact div_pos hp0 (mul_pos (mul_pos (by norm_num) hh) (cornerScale_pos _))

/-- The edge exchange preserves the interior of the bigon. -/
theorem WhitneyPairModel.exchangeEdges_mem_interior {h : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) : exchangeEdges h p ∈ interior (bigon h) := by
  obtain ⟨hp0, hphi⟩ := (mem_interior_bigon_iff h p).mp hp
  apply (mem_interior_bigon_iff h _).mpr
  change 0 < h * (1 - p.1 ^ 2) - p.2 ∧ h * (1 - p.1 ^ 2) - p.2 < h * (1 - p.1 ^ 2)
  constructor <;> linarith

/-- The upper strip chart carries the interior of the bigon into the open strip. -/
theorem WhitneyPairModel.upperStripCoordinates_interior {h : ℝ} (hh : 0 < h) {p : ℝ × ℝ}
    (hp : p ∈ interior (bigon h)) :
    (upperStripCoordinates h p).1 ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < (upperStripCoordinates h p).2 :=
  lowerStripCoordinates_interior hh (exchangeEdges_mem_interior hp)

end
