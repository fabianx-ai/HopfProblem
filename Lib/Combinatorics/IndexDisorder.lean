/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib

/-!
# The weighted inversion count of a height function

For a finite type `X` with an injective height `h : X → ℝ` and weights `w : X → ℕ`,
`IndexDisorder.upperValueRank h x` is the number of points of `X` above `x` and
`IndexDisorder.finiteIndexDisorder h w = ∑ x, w x * upperValueRank h x` is the weighted
inversion count.  Exchanging the heights of two consecutive points whose weights are inverted
strictly decreases this count (`IndexDisorder.finiteIndexDisorder_swap_lt`), and an inverted
pair which is consecutive exists whenever the weights are not monotone for the height order
(`IndexDisorder.exists_adjacent_index_inversion`).  Together these run the induction that
reorders a finite family by weight, keeping the count as the induction measure.

`IndexDisorder.beforeValueRank` is the mirror count (the number of points below `x`) with the
corresponding exchange lemma `IndexDisorder.beforeValueRank_exchange_lt`.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §4 (the inversion count in the
  proof of Theorem 4.8, self-indexing: the critical points are reordered by index one adjacent
  inversion at a time).
-/

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The number of points of a finite set whose height exceeds that of `x`. -/
def IndexDisorder.upperValueRank {X : Type*} [Fintype X] (h : X → ℝ) (x : X) : ℕ :=
  (Finset.univ.filter (fun y => h x < h y)).card

/-- The weighted inversion count `∑ x, w x * upperValueRank h x` of a height function `h` with
weights `w`.  This is the quantity whose decrease drives Milnor's reordering induction
(*Lectures on the h-cobordism theorem*, Theorem 4.8). -/
def IndexDisorder.finiteIndexDisorder {X : Type*} [Fintype X] (h : X → ℝ)
    (w : X → ℕ) : ℕ :=
  ∑ x, w x * upperValueRank h x

/-- `upperValueRank` is invariant under reindexing by an equivalence. -/
theorem IndexDisorder.upperValueRank_comp_equiv {X : Type*} [Fintype X] {Y : Type*}
    [Fintype Y] (h : Y → ℝ) (e : X ≃ Y) (x : X) :
    upperValueRank (h ∘ e) x = upperValueRank h (e x) := by
  classical
  unfold upperValueRank
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-- `finiteIndexDisorder` is invariant under reindexing by an equivalence. -/
theorem IndexDisorder.finiteIndexDisorder_comp_equiv {X : Type*} [Fintype X]
    {Y : Type*} [Fintype Y] (h : Y → ℝ) (w : Y → ℕ) (e : X ≃ Y) :
    finiteIndexDisorder (h ∘ e) (w ∘ e) = finiteIndexDisorder h w := by
  classical
  unfold finiteIndexDisorder
  calc
    _ = ∑ x, w (e x) * upperValueRank h (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [upperValueRank_comp_equiv]
      rfl
    _ = _ := e.sum_comp (fun y => w y * upperValueRank h y)

/-- If `p` is immediately below `q` in an injective height function, then exactly one more
point lies above `p` than above `q`. -/
theorem IndexDisorder.upperValueRank_consecutive {X : Type*} [Fintype X] {h : X → ℝ}
    (hi : Function.Injective h) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) :
    upperValueRank h p = upperValueRank h q + 1 := by
  classical
  have hset :
    Finset.univ.filter (fun x => h p < h x) =
      Insert.insert q (Finset.univ.filter (fun x => h q < h x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxq : x = q
      · exact Or.inl hxq
      · apply Or.inr
        by_contra hnot
        have hlt : h x < h q := lt_of_le_of_ne (le_of_not_gt hnot) (fun heq => hxq (hi heq))
        exact hconsecutive x ⟨hx, hlt⟩
    · rintro (rfl | hx)
      · exact hpq
      · exact hpq.trans hx
  unfold upperValueRank
  rw [hset, Finset.card_insert_of_notMem (by simp)]

attribute [local instance 100] Classical.propDecidable in
/-- A sum over a finite type splits off the two distinct terms `p` and `q`. -/
theorem IndexDisorder.sum_erase_two_nat {X : Type*} [Fintype X] (v : X → ℕ) {p q : X}
    (hpq : p ≠ q) : ∑ x, v x = (∑ x ∈ (Finset.univ.erase p).erase q, v x) + v p + v q := by
  classical
  have hp := Finset.sum_erase_add (s := Finset.univ) v (Finset.mem_univ p)
  have hq :=
    Finset.sum_erase_add (s := Finset.univ.erase p) v
      (by simp [Ne.symm hpq] : q ∈ Finset.univ.erase p)
  omega

attribute [local instance 100] Classical.propDecidable in
/-- Transposing two values in a weighted sum changes it by exchanging the two crossed terms. -/
theorem IndexDisorder.weighted_sum_swap_identity {X : Type*} [Fintype X] (w v : X → ℕ)
    {p q : X} (hpq : p ≠ q) :
    (∑ x, w x * v (Equiv.swap p q x)) + w p * v p + w q * v q =
      (∑ x, w x * v x) + w p * v q + w q * v p := by
  classical
  have hnew := sum_erase_two_nat (fun x => w x * v (Equiv.swap p q x)) hpq
  have hold := sum_erase_two_nat (fun x => w x * v x) hpq
  have hrest :
    (∑ x ∈ (Finset.univ.erase p).erase q, w x * v (Equiv.swap p q x)) =
      ∑ x ∈ (Finset.univ.erase p).erase q, w x * v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxq := (Finset.mem_erase.mp hx).1
    have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq]
  rw [hrest] at hnew
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hnew
  omega

attribute [local instance 100] Classical.propDecidable in
/-- Exchanging the heights of two consecutive points whose weights are inverted strictly
decreases the inversion count.  This is the induction step of Milnor's proof of Theorem 4.8. -/
theorem IndexDisorder.finiteIndexDisorder_swap_lt {X : Type*} [Fintype X] {h : X → ℝ}
    (hi : Function.Injective h) (w : X → ℕ) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) (hw : w q < w p) :
    finiteIndexDisorder (h ∘ Equiv.swap p q) w < finiteIndexDisorder h w := by
  classical
  have hne : p ≠ q := fun heq => (ne_of_lt hpq) (congrArg h heq)
  have hrank := upperValueRank_consecutive hi hpq hconsecutive
  have hid := weighted_sum_swap_identity w (upperValueRank h) hne
  have hnew :
    finiteIndexDisorder (h ∘ Equiv.swap p q) w = ∑ x, w x * upperValueRank h (Equiv.swap p q x) :=
    by
    unfold finiteIndexDisorder
    apply Finset.sum_congr rfl
    intro x _
    rw [upperValueRank_comp_equiv]
  rw [hrank] at hid
  simp only [Nat.mul_add, Nat.mul_one] at hid
  change _ < ∑ x, w x * upperValueRank h x
  rw [hnew]
  omega

/-- If the weights are not monotone along the height, there is a consecutive pair `p`, `q` with
`h p < h q` and `w q < w p`: an adjacent inversion. -/
theorem IndexDisorder.exists_adjacent_index_inversion {X : Type*} [Finite X]
    {h : X → ℝ} (hi : Function.Injective h) (w : X → ℕ) (hnot : ¬∀ x y, h x < h y → w x ≤ w y) :
    ∃ p q, h p < h q ∧ (∀ x, ¬(h p < h x ∧ h x < h q)) ∧ w q < w p := by
  classical
  let := Fintype.ofFinite X
  let _ : LinearOrder X := LinearOrder.lift' h hi
  let _ : LocallyFiniteOrder X := Fintype.toLocallyFiniteOrder
  have hnotmono : ¬Monotone w := by
    intro hm
    apply hnot
    intro x y hxy
    exact hm (show x ≤ y from hxy.le)
  have hnotadj : ¬∀ x y : X, x ⋖ y → w x ≤ w y := by
    intro hadj
    exact hnotmono ((monotone_iff_forall_covBy w).mpr hadj)
  simp only [Classical.not_forall, not_le] at hnotadj
  obtain ⟨p, q, hcover, hweights⟩ := hnotadj
  exact ⟨p, q, hcover.lt, fun x hx => hcover.2 hx.1 hx.2, hweights⟩

/-- If some point lies strictly between `p` and `q`, there is one lying immediately below
`q`. -/
theorem IndexDisorder.exists_consecutive_below_of_intermediate {X : Type*} [Finite X]
    {h : X → ℝ} {p q : X} (hintermediate : ∃ x, h p < h x ∧ h x < h q) :
    ∃ r, h p < h r ∧ h r < h q ∧ ∀ x, ¬(h r < h x ∧ h x < h q) := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨w, hpw, hwq⟩ := hintermediate
  let K := Finset.univ.filter (fun x => h x < h q)
  have hw : w ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwq⟩
  obtain ⟨r, hr, hmax⟩ := K.exists_max_image h ⟨w, hw⟩
  refine ⟨r, hpw.trans_le (hmax w hw), (Finset.mem_filter.mp hr).2, ?_⟩
  intro x hx
  exact (not_lt_of_ge (hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩))) hx.1

/-- The number of points of a finite set whose height is below that of `q`. -/
def IndexDisorder.beforeValueRank {X : Type*} [Fintype X] (h : X → ℝ) (q : X) : ℕ :=
  upperValueRank (fun x => -h x) q

attribute [local instance 100] Classical.propDecidable in
/-- Exchanging the heights of a consecutive pair `p < q` strictly decreases the number of
points below `q`. -/
theorem IndexDisorder.beforeValueRank_exchange_lt {X : Type*} [Fintype X]
    {h g : X → ℝ} (hi : Function.Injective h) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) (hgp : g p = h q) (hgq : g q = h p)
    (hothers : ∀ x, x ≠ p → x ≠ q → g x = h x) : beforeValueRank g q < beforeValueRank h q := by
  classical
  have hform : (fun x => -g x) = (fun x => -h x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_left, hgp]
    by_cases hxq : x = q
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_right, hgq]
    simp only [Function.comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq,
      hothers x hxp hxq]
  have hnew : beforeValueRank g q = beforeValueRank h p := by
    unfold beforeValueRank
    rw [hform, upperValueRank_comp_equiv, Equiv.swap_apply_right]
  have hneg : Function.Injective (fun x => -h x) := fun x y hxy => hi (neg_injective hxy)
  have hgap : beforeValueRank h q = beforeValueRank h p + 1 := by
    apply upperValueRank_consecutive hneg (neg_lt_neg hpq)
    intro x hx
    exact hconsecutive x ⟨neg_lt_neg_iff.mp hx.2, neg_lt_neg_iff.mp hx.1⟩
  omega

end
