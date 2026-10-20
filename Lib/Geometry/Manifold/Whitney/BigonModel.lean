/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib

/-!
# The Whitney bigon: explicit strip-coordinate model

`WhitneyPairModel` builds the standard model picture behind the Whitney trick:
two sheets `x ↦ (x, 0)` and `x ↦ (x, h)` in the plane, the bigon they bound
(`bigon h`), and smooth strip coordinates near each corner
(`lowerStripCoordinates`, `upperStripCoordinates`) joined by the corner
transition data (`cornerTransition`, `cornerScale`, `cornerSign`). The model is
deliberately elementary — everything is a concrete map between `ℝ × ℝ` and the
product `Space` — so that later Whitney-disk arguments can cite exact smooth
charts instead of an existence statement.

## Main definitions and results

* `WhitneyPairModel.bigon` : the bigon bounded by the two sheets; closed,
  star-convex, and compact for `0 < h` (`isClosed_bigon`, `starConvex_bigon`,
  `isCompact_bigon`), with interior/frontier characterizations
  (`mem_interior_bigon_iff`, `mem_frontier_bigon_iff`) and boundary cover
  (`exists_bigon_boundary_cover`).
* `bigonReflection` / `exchangeEdges_involutive` : the sheet-swapping symmetry.
* `leftCornerCoordinates`, `rightCornerCoordinates`, `cornerTransition`,
  `cornerScale`, `cornerSign` : smooth corner charts and their exchange
  behaviour (`leftCornerCoordinates_exchange`).
* `lowerStripCoordinates`, `upperStripCoordinates` : smooth strip coordinates
  (`contDiff_lowerStripCoordinates`, `contDiff_upperStripCoordinates`) agreeing
  with the sheets on their sides (`lowerStripCoordinates_lower`, …).
* `StripCoordinates.reverse` : orientation-reversing model map, smooth
  (`contDiff_reverse`).

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §6
  (Theorem 6.6, the Whitney lemma this model serves).

## Twin

No Mathlib counterpart exists.

## Tags

Whitney trick, bigon, strip coordinates, model
-/

open Set Function Filter Manifold Topology
open scoped ContDiff


@[expose] public noncomputable section

/-- Partial derivative in the second variable: if `F : ℝ × ℝ → E` is differentiable at `(t, s)`,
then the vertical slice `u ↦ F (t, u)` has derivative `fderiv ℝ F (t, s) (0, 1)` at `s`.
-/
theorem StripCoordinates.hasDerivAt_verticalSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℝ × ℝ) → E} {t s : ℝ} (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (t, u)) (fderiv ℝ F (t, s) (0, 1)) s := by
  have hi : HasDerivAt (fun u : ℝ => (t, u)) (0, 1) s :=
    (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  exact hF.hasFDerivAt.comp_hasDerivAt s hi

/-- The Euclidean plane `ℝ²`, used as the normal fibre of each of the two sheets in the model. -/
abbrev WhitneyPairModel.Plane :=
  EuclideanSpace ℝ (Fin 2)

/-- The ambient model space of the Whitney picture: the bigon plane `ℝ × ℝ` together with the normal
fibres of the two sheets.
-/
abbrev WhitneyPairModel.Space :=
  (ℝ × ℝ) × (Plane × Plane)

/-- The model of a single sheet: an arc parameter together with the sheet's own plane of tangent
directions.
-/
abbrev WhitneyPairModel.Sheet :=
  ℝ × Plane

/-- The first sheet of the model, embedded along the horizontal edge `y = 0` of the bigon with its
tangent plane in the first normal factor.
-/
def WhitneyPairModel.firstSheet (p : Sheet) : Space :=
  ((p.1, 0), (p.2, 0))

/-- The second sheet of the model, embedded along the parabolic edge `y = h (1 - x²)` of the bigon
with its tangent plane in the second normal factor.
-/
def WhitneyPairModel.secondSheet (h : ℝ) (p : Sheet) : Space :=
  ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

/-- The model Whitney bigon of height `h`: the region of the plane bounded below by the segment
`y = 0` and above by the parabolic arc `y = h (1 - x²)`. This is the model disc of Milnor's
Whitney lemma (h-cobordism theorem, §6).
-/
def WhitneyPairModel.bigon (h : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h}

/-- The inclusion of the bigon plane into the ambient model space at zero normal coordinates. -/
def WhitneyPairModel.bigonEmbedding : (ℝ × ℝ) → Space := fun p => (p, (0, 0))

/-- The bigon is a closed subset of the plane. -/
theorem WhitneyPairModel.isClosed_bigon (h : ℝ) : IsClosed (bigon h) :=
  (isClosed_le continuous_const continuous_snd).inter
    (isClosed_le (show Continuous (fun p : ℝ × ℝ => h * p.1 ^ 2 + p.2) by fun_prop)
      continuous_const)

/-- For nonnegative height the origin, the midpoint of the lower edge, belongs to the bigon. -/
theorem WhitneyPairModel.zero_mem_bigon {h : ℝ} (hh : 0 ≤ h) : (0 : ℝ × ℝ) ∈ bigon h := by
  exact ⟨le_rfl, by simpa using hh⟩

/-- For positive height the bigon is contained in the rectangle `[-1, 1] × [0, h]`. -/
theorem WhitneyPairModel.bigon_subset_rectangle {h : ℝ} (hh : 0 < h) :
    bigon h ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) h := by
  intro p hp
  rcases hp with ⟨ht, hupper⟩
  have hsq : p.1 ^ 2 ≤ 1 := by nlinarith
  have hheight : p.2 ≤ h := by nlinarith [sq_nonneg p.1]
  exact ⟨⟨by nlinarith, by nlinarith⟩, ht, hheight⟩

/-- For positive height the bigon is compact. -/
theorem WhitneyPairModel.isCompact_bigon {h : ℝ} (hh : 0 < h) : IsCompact (bigon h) :=
  (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc).of_isClosed_subset
    (isClosed_bigon h) (bigon_subset_rectangle hh)

/-- A point lies in the interior of the bigon exactly when both defining inequalities are strict,
that is `0 < y` and `y < h (1 - x²)`.
-/
theorem WhitneyPairModel.mem_interior_bigon_iff (h : ℝ) (p : ℝ × ℝ) :
    p ∈ interior (bigon h) ↔ 0 < p.2 ∧ p.2 < h * (1 - p.1 ^ 2) := by
  constructor
  · intro hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    have hd (a : ℝ) : Dist.dist (p.1, p.2 + a) p = |a| := by simp [Prod.dist_eq]
    have hm : (p.1, p.2 + (-ε / 2)) ∈ Metric.ball p ε := by
      change Dist.dist (p.1, p.2 + (-ε / 2)) p < ε
      rw [hd, abs_of_neg (by linarith)]
      linarith
    have hp' : (p.1, p.2 + ε / 2) ∈ Metric.ball p ε := by
      change Dist.dist (p.1, p.2 + ε / 2) p < ε
      rw [hd, abs_of_pos (by linarith)]
      linarith
    have hlo := (hball hm).1
    have hhi := (hball hp').2
    change 0 ≤ p.2 + (-ε / 2) at hlo
    change h * p.1 ^ 2 + (p.2 + ε / 2) ≤ h at hhi
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    let U : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ h * q.1 ^ 2 + q.2 < h}
    have hU : IsOpen U :=
      (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (show Continuous (fun q : ℝ × ℝ => h * q.1 ^ 2 + q.2) by fun_prop)
          continuous_const)
    have hpU : p ∈ U := ⟨hlo, by nlinarith⟩
    exact
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hU.mem_nhds hpU) (fun _ hq => ⟨hq.1.le, hq.2.le⟩))

/-- A point lies on the frontier of the bigon exactly when it lies in the bigon and on one of its
two edges, `y = 0` or `y = h (1 - x²)`.
-/
theorem WhitneyPairModel.mem_frontier_bigon_iff (h : ℝ) (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔ p ∈ bigon h ∧ (p.2 = 0 ∨ p.2 = h * (1 - p.1 ^ 2)) := by
  rw [frontier, (isClosed_bigon h).closure_eq, Set.mem_sdiff, mem_interior_bigon_iff]
  constructor
  · rintro ⟨hp, hnot⟩
    refine ⟨hp, ?_⟩
    by_cases ht : p.2 = 0
    · exact Or.inl ht
    · right
      have hlo : 0 < p.2 := lt_of_le_of_ne hp.1 (Ne.symm ht)
      have hhi : ¬p.2 < h * (1 - p.1 ^ 2) := fun hlt => hnot ⟨hlo, hlt⟩
      have hupper := hp.2
      change h * p.1 ^ 2 + p.2 ≤ h at hupper
      nlinarith
  · rintro ⟨hp, ht | ht⟩
    · exact ⟨hp, fun hstrict => hstrict.1.ne' ht⟩
    · exact ⟨hp, fun hstrict => hstrict.2.ne ht⟩

/-- For nonnegative height the bigon is star-convex about the origin. -/
theorem WhitneyPairModel.starConvex_bigon {h : ℝ} (hh : 0 ≤ h) :
    StarConvex ℝ (0 : ℝ × ℝ) (bigon h) := by
  rw [starConvex_zero_iff]
  intro p hp a ha₀ ha₁
  rcases hp with ⟨ht, hupper⟩
  change 0 ≤ a * p.2 ∧ h * (a * p.1) ^ 2 + a * p.2 ≤ h
  refine ⟨mul_nonneg ha₀ ht, ?_⟩
  calc
    h * (a * p.1) ^ 2 + a * p.2 = a * (h * p.1 ^ 2 + p.2) - (a * (1 - a)) * (h * p.1 ^ 2) := by
      ring
    _ ≤ a * (h * p.1 ^ 2 + p.2) :=
      (sub_le_self _
        (mul_nonneg (mul_nonneg ha₀ (sub_nonneg.mpr ha₁)) (mul_nonneg hh (sq_nonneg _))))
    _ ≤ a * h := (mul_le_mul_of_nonneg_left hupper ha₀)
    _ ≤ h := by nlinarith

/-- Every point `(s, 0)` of the lower edge with `|s| ≤ 1` lies in the bigon. -/
theorem WhitneyPairModel.lowerArc_mem_bigon {h s : ℝ} (hh : 0 ≤ h) (hs : |s| ≤ 1) :
    (s, 0) ∈ bigon h := by
  have habs := abs_le.mp hs
  refine ⟨le_rfl, ?_⟩
  change h * s ^ 2 + 0 ≤ h
  have hsq : s ^ 2 ≤ 1 := by nlinarith
  simpa only [mul_one, add_zero] using mul_le_mul_of_nonneg_left hsq hh

/-- Every point `(s, h (1 - s²))` of the upper edge with `|s| ≤ 1` lies in the bigon. -/
theorem WhitneyPairModel.upperArc_mem_bigon {h s : ℝ} (hh : 0 ≤ h) (hs : |s| ≤ 1) :
    (s, h * (1 - s ^ 2)) ∈ bigon h := by
  have habs := abs_le.mp hs
  refine ⟨mul_nonneg hh (by nlinarith), ?_⟩
  change h * s ^ 2 + h * (1 - s ^ 2) ≤ h
  nlinarith

/-- Given open sets `D` and `E` containing the lower and upper edge of the bigon and an open set `O`
containing the two corners `(±1, 0)`, the frontier of the bigon is covered by two open sets
`U ⊆ D` and `V ⊆ E` that still contain the respective edges and whose intersection lies in `O`.
This is the two-set cover of the bigon boundary used to separate the corner charts from the edge
charts.
-/
theorem WhitneyPairModel.exists_bigon_boundary_cover {h : ℝ} (hh : 0 < h)
    {D E O : Set (ℝ × ℝ)} (hD : IsOpen D) (hE : IsOpen E) (hO : IsOpen O) (hleft : (-1, 0) ∈ O)
    (hright : (1, 0) ∈ O) (hlower : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) D)
    (hupper : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) E) :
    ∃ U : Set (ℝ × ℝ),
      ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧
          IsOpen V ∧
            U ⊆ D ∧
              V ⊆ E ∧
                U ∩ V ⊆ O ∧
                  Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
                    Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1)
                        V ∧
                      frontier (bigon h) ⊆ U ∪ V := by
  let B : Set (ℝ × ℝ) := {p | p.2 < h * (1 - p.1 ^ 2) / 2}
  let T : Set (ℝ × ℝ) := {p | h * (1 - p.1 ^ 2) / 2 < p.2}
  have hB : IsOpen B := isOpen_lt continuous_snd (by fun_prop)
  have hT : IsOpen T := isOpen_lt (by fun_prop) continuous_snd
  let U := D ∩ (O ∪ B)
  let V := E ∩ (O ∪ T)
  have hU : IsOpen U := hD.inter (hO.union hB)
  have hV : IsOpen V := hE.inter (hO.union hT)
  have hheight {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < h * (1 - (2 * t - 1) ^ 2) := by
    calc
      0 < 4 * h * t * (1 - t) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
      _ = h * (1 - (2 * t - 1) ^ 2) := by ring
  have hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U := by
    intro t ht
    refine ⟨hlower ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (by simpa using hleft)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (by convert hright using 1; norm_num)
    right
    have hh' := hheight ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    change (0 : ℝ) < h * (1 - (2 * t - 1) ^ 2) / 2
    linarith
  have huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V :=
    by
    intro t ht
    refine ⟨hupper ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (by simpa using hleft)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (by convert hright using 1; norm_num)
    right
    have hh' := hheight ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    change h * (1 - (2 * t - 1) ^ 2) / 2 < h * (1 - (2 * t - 1) ^ 2)
    linarith
  refine ⟨U, V, hU, hV, Set.inter_subset_left, Set.inter_subset_left, ?_, hlowU, huppV, ?_⟩
  · intro p hp
    rcases hp.1.2 with hpO | hpB
    · exact hpO
    rcases hp.2.2 with hpO | hpT
    · exact hpO
    have hpB' : p.2 < h * (1 - p.1 ^ 2) / 2 := hpB
    have hpT' : h * (1 - p.1 ^ 2) / 2 < p.2 := hpT
    exact (lt_asymm hpB' hpT').elim
  · intro p hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    rcases hpedge with hpzero | hpupper
    · left
      have heq : p = (2 * t - 1, 0) := Prod.ext hbase hpzero
      rw [heq]
      exact hlowU ht
    · right
      have heq : p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
        apply Prod.ext hbase
        rw [← hbase]
        exact hpupper
      rw [heq]
      exact huppV ht

/-- The affine arc parameter `x ↦ (x + 1) / 2`, carrying the base interval `[-1, 1]` of the bigon to
`[0, 1]`.
-/
def WhitneyPairModel.arcTime (p : ℝ × ℝ) : ℝ :=
  (p.1 + 1) / 2

/-- The corner chart at the left corner `(-1, 0)`: the arc parameter shifted by the normalised
height, paired with that normalised height.
-/
def WhitneyPairModel.leftCornerCoordinates (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (arcTime p - p.2 / (4 * h * (1 - arcTime p)), p.2 / (4 * h * (1 - arcTime p)))

/-- The arc parameter is smooth. -/
theorem WhitneyPairModel.contDiff_arcTime : ContDiff ℝ ∞ arcTime := by
  unfold arcTime
  fun_prop

/-- The reflection `(x, y) ↦ (-x, y)` of the plane, a linear symmetry of the bigon exchanging its
two corners.
-/
def WhitneyPairModel.bigonReflection : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

/-- The reflection acts by negating the first coordinate. -/
theorem WhitneyPairModel.bigonReflection_apply (p : ℝ × ℝ) :
    bigonReflection p = (-p.1, p.2) :=
  rfl

/-- The reflection reverses the arc parameter: `arcTime (bigonReflection p) = 1 - arcTime p`. -/
theorem WhitneyPairModel.arcTime_bigonReflection (p : ℝ × ℝ) :
    arcTime (bigonReflection p) = 1 - arcTime p := by
  dsimp [arcTime, bigonReflection]
  ring

/-- The corner chart at the right corner `(1, 0)`, obtained from the left-corner chart by the
reflection of the bigon.
-/
def WhitneyPairModel.rightCornerCoordinates (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  leftCornerCoordinates h ∘ bigonReflection

/-- Exchanging the two edges of the bigon swaps the two left-corner coordinates: the chart sends
`(x, h (1 - x²) - y)` to the swap of its value at `(x, y)`.
-/
theorem WhitneyPairModel.leftCornerCoordinates_exchange {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≠ 1) :
    leftCornerCoordinates h (p.1, h * (1 - p.1 ^ 2) - p.2) = (leftCornerCoordinates h p).swap := by
  have hd : 4 * h * (1 - arcTime p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hp))
  have hheight : h * (1 - p.1 ^ 2) = arcTime p * (4 * h * (1 - arcTime p)) := by
    dsimp [arcTime]
    ring
  have hv :
    (h * (1 - p.1 ^ 2) - p.2) / (4 * h * (1 - arcTime p)) =
      arcTime p - p.2 / (4 * h * (1 - arcTime p)) := by
    rw [sub_div, hheight, mul_div_cancel_right₀ _ hd]
  apply Prod.ext
  · change arcTime p - (h * (1 - p.1 ^ 2) - p.2) / (4 * h * (1 - arcTime p)) = _
    rw [hv]
    dsimp [leftCornerCoordinates]
    ring
  · exact hv

/-- Reversal of the strip parameter, `(t, s) ↦ (1 - t, s)`. -/
def StripCoordinates.reverse (p : ℝ × ℝ) : ℝ × ℝ :=
  (1 - p.1, p.2)

/-- Reversal of the strip parameter is smooth. -/
theorem StripCoordinates.contDiff_reverse : ContDiff ℝ ∞ reverse :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

/-- Reversal carries the right end `(1, 0)` of the strip to the left end `(0, 0)`. -/
theorem StripCoordinates.reverse_one_zero : reverse (1, 0) = (0, 0) := by
  simp only [reverse, sub_self]

/-- Reversal preserves vertical partial derivatives: the derivative of `H ∘ reverse` at `(1, 0)` in
the direction `(0, 1)` equals that of `H` at `(0, 0)`.
-/
theorem StripCoordinates.vertical_derivative_reverse {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : (ℝ × ℝ) → B} (hH : DifferentiableAt ℝ H (0, 0)) :
    fderiv ℝ (H ∘ reverse) (1, 0) (0, 1) = fderiv ℝ H (0, 0) (0, 1) := by
  have houter : DifferentiableAt ℝ H (reverse (1, 0)) := by
    rw [reverse_one_zero]
    exact hH
  have hcomp : DifferentiableAt ℝ (H ∘ reverse) (1, 0) :=
    houter.comp (1, 0) (contDiff_reverse.contDiffAt.differentiableAt (by simp))
  have hleft := hasDerivAt_verticalSlice hcomp
  have hright := hasDerivAt_verticalSlice hH
  have heq : (fun s : ℝ => (H ∘ reverse) (1, s)) = fun s => H (0, s) := by
    funext s
    simp only [Function.comp_apply, reverse, sub_self]
  rw [heq] at hleft
  exact hleft.unique hright

/-- The smooth transition function `t ↦ smoothTransition (3 t - 1)`, which vanishes for `t ≤ 1/3`
and equals `1` for `t ≥ 2/3`; it interpolates between the left-corner and the right-corner
chart.
-/
def WhitneyPairModel.cornerTransition (t : ℝ) : ℝ :=
  Real.smoothTransition (3 * t - 1)

/-- The interpolated distance to the opposite corner, `(1 - β t) (1 - t) + β t · t` for the
transition `β`; it equals `1 - t` near the left corner and `t` near the right one.
-/
def WhitneyPairModel.cornerScale (t : ℝ) : ℝ :=
  (1 - cornerTransition t) * (1 - t) + cornerTransition t * t

/-- The interpolated corner sign `2 β t - 1`, equal to `-1` near the left corner and to `1` near the
right one.
-/
def WhitneyPairModel.cornerSign (t : ℝ) : ℝ :=
  2 * cornerTransition t - 1

/-- The corner transition function is smooth. -/
theorem WhitneyPairModel.contDiff_cornerTransition : ContDiff ℝ ∞ cornerTransition := by
  unfold cornerTransition
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- The corner transition vanishes on `t ≤ 1/3`, the region of the left corner. -/
theorem WhitneyPairModel.cornerTransition_zero {t : ℝ} (ht : t ≤ 1 / 3) :
    cornerTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The corner transition is `1` on `2/3 ≤ t`, the region of the right corner. -/
theorem WhitneyPairModel.cornerTransition_one {t : ℝ} (ht : 2 / 3 ≤ t) :
    cornerTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The corner scale is strictly positive, so it may be divided by. -/
theorem WhitneyPairModel.cornerScale_pos (t : ℝ) : 0 < cornerScale t := by
  by_cases hlo : t ≤ 1 / 3
  · simp only [cornerScale, cornerTransition_zero hlo, sub_zero, one_mul, MulZeroClass.zero_mul,
      add_zero]
    linarith
  by_cases hhi : 2 / 3 ≤ t
  · simp only [cornerScale, cornerTransition_one hhi, sub_self, MulZeroClass.zero_mul, one_mul,
      zero_add]
    linarith
  have h0 : 0 ≤ cornerTransition t := Real.smoothTransition.nonneg _
  have h1 : cornerTransition t ≤ 1 := Real.smoothTransition.le_one _
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < 1 - t := by linarith
  by_cases hβ : cornerTransition t = 0
  · simp only [cornerScale, hβ, sub_zero, one_mul, MulZeroClass.zero_mul, add_zero]
    exact ht1
  · exact
      add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr h1) ht1.le)
        (mul_pos (lt_of_le_of_ne h0 (Ne.symm hβ)) ht0)

/-- The corner scale is smooth. -/
theorem WhitneyPairModel.contDiff_cornerScale : ContDiff ℝ ∞ cornerScale := by
  exact
    ((contDiff_const.sub contDiff_cornerTransition).mul (contDiff_const.sub contDiff_id)).add
      (contDiff_cornerTransition.mul contDiff_id)

/-- The corner sign is smooth. -/
theorem WhitneyPairModel.contDiff_cornerSign : ContDiff ℝ ∞ cornerSign :=
  (contDiff_const.mul contDiff_cornerTransition).sub contDiff_const

/-- The reflection `(x, y) ↦ (x, h (1 - x²) - y)` of the bigon in its two edges, exchanging the
lower and the upper edge and fixing the corners.
-/
def WhitneyPairModel.exchangeEdges (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, h * (1 - p.1 ^ 2) - p.2)

/-- The edge exchange is smooth. -/
theorem WhitneyPairModel.contDiff_exchangeEdges (h : ℝ) : ContDiff ℝ ∞ (exchangeEdges h) := by
  unfold exchangeEdges
  fun_prop

/-- The edge exchange is an involution. -/
theorem WhitneyPairModel.exchangeEdges_involutive (h : ℝ) :
    Function.Involutive (exchangeEdges h) := by
  intro p
  apply Prod.ext <;> dsimp [exchangeEdges]
  ring

/-- The strip chart along the lower edge of the bigon: the arc parameter corrected by the corner
sign times the normalised height, paired with that height. It agrees with the left-corner chart
near the left corner and with the reversed right-corner chart near the right one.
-/
def WhitneyPairModel.lowerStripCoordinates (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (arcTime p + cornerSign (arcTime p) * (p.2 / (4 * h * cornerScale (arcTime p))),
    p.2 / (4 * h * cornerScale (arcTime p)))

/-- The strip chart along the upper edge of the bigon, the lower strip chart precomposed with the
edge exchange.
-/
def WhitneyPairModel.upperStripCoordinates (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  lowerStripCoordinates h ∘ exchangeEdges h

/-- For nonzero height the lower strip chart is smooth. -/
theorem WhitneyPairModel.contDiff_lowerStripCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ ∞ (lowerStripCoordinates h) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 / (4 * h * cornerScale (arcTime p))) :=
    contDiff_snd.div (contDiff_const.mul (contDiff_cornerScale.comp contDiff_arcTime))
      (fun p => mul_ne_zero (mul_ne_zero (by norm_num) hh) (cornerScale_pos _).ne')
  exact (contDiff_arcTime.add ((contDiff_cornerSign.comp contDiff_arcTime).mul hd)).prodMk hd

/-- For nonzero height the upper strip chart is smooth. -/
theorem WhitneyPairModel.contDiff_upperStripCoordinates {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ ∞ (upperStripCoordinates h) :=
  (contDiff_lowerStripCoordinates hh).comp (contDiff_exchangeEdges h)

/-- The lower strip chart straightens the lower edge: it carries the parametrisation
`t ↦ (2 t - 1, 0)` to `t ↦ (t, 0)`.
-/
theorem WhitneyPairModel.lowerStripCoordinates_lower (h t : ℝ) :
    lowerStripCoordinates h (2 * t - 1, 0) = (t, 0) := by
  simp only [lowerStripCoordinates, arcTime, zero_div, MulZeroClass.mul_zero, add_zero]
  congr 1
  ring

/-- The upper strip chart straightens the upper edge: it carries the parametrisation
`t ↦ (2 t - 1, h (1 - (2 t - 1)²))` to `t ↦ (t, 0)`.
-/
theorem WhitneyPairModel.upperStripCoordinates_upper (h t : ℝ) :
    upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = (t, 0) := by
  simp only [upperStripCoordinates, Function.comp_apply, exchangeEdges, sub_self]
  exact lowerStripCoordinates_lower h t

/-- Near the left corner the lower strip chart coincides with the left-corner chart. -/
theorem WhitneyPairModel.lowerStripCoordinates_left (h : ℝ) {p : ℝ × ℝ}
    (hp : arcTime p ≤ 1 / 3) : lowerStripCoordinates h p = leftCornerCoordinates h p := by
  simp [lowerStripCoordinates, cornerSign, cornerScale, cornerTransition_zero hp,
    leftCornerCoordinates, sub_eq_add_neg]

/-- Near the left corner the upper strip chart is the swap of the left-corner chart. -/
theorem WhitneyPairModel.upperStripCoordinates_left {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≤ 1 / 3) : upperStripCoordinates h p = (leftCornerCoordinates h p).swap := by
  have htime : arcTime (exchangeEdges h p) = arcTime p := rfl
  have hp' : arcTime p ≠ 1 := by linarith
  change lowerStripCoordinates h (exchangeEdges h p) = _
  rw [lowerStripCoordinates_left h (htime ▸ hp)]
  exact leftCornerCoordinates_exchange hh hp'

/-- Near the right corner the reversed lower strip chart coincides with the right-corner chart. -/
theorem WhitneyPairModel.lowerStripCoordinates_right (h : ℝ) {p : ℝ × ℝ}
    (hp : 2 / 3 ≤ arcTime p) :
    StripCoordinates.reverse (lowerStripCoordinates h p) = rightCornerCoordinates h p := by
  have hden : 1 - arcTime (bigonReflection p) = arcTime p := by
    rw [arcTime_bigonReflection]
    ring
  simp only [lowerStripCoordinates, cornerSign, cornerScale, cornerTransition_one hp, sub_self,
    MulZeroClass.zero_mul, one_mul, zero_add]
  norm_num only [mul_one, sub_self, sub_zero]
  change
    (1 - (arcTime p + 1 * (p.2 / (4 * h * arcTime p))), p.2 / (4 * h * arcTime p)) =
      leftCornerCoordinates h (bigonReflection p)
  simp only [leftCornerCoordinates]
  rw [hden, arcTime_bigonReflection]
  simp only [bigonReflection_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- Near the right corner the reversed upper strip chart is the swap of the right-corner chart. -/
theorem WhitneyPairModel.upperStripCoordinates_right {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : 2 / 3 ≤ arcTime p) :
    StripCoordinates.reverse (upperStripCoordinates h p) =
      (rightCornerCoordinates h p).swap := by
  have htime : arcTime (exchangeEdges h p) = arcTime p := rfl
  change StripCoordinates.reverse (lowerStripCoordinates h (exchangeEdges h p)) = _
  rw [lowerStripCoordinates_right h (htime ▸ hp)]
  have heq :
    bigonReflection (exchangeEdges h p) =
      ((bigonReflection p).1, h * (1 - (bigonReflection p).1 ^ 2) - (bigonReflection p).2) := by
    simp only [bigonReflection_apply, exchangeEdges, neg_sq]
  change leftCornerCoordinates h (bigonReflection (exchangeEdges h p)) = _
  rw [heq]
  apply leftCornerCoordinates_exchange hh
  rw [arcTime_bigonReflection]
  linarith

