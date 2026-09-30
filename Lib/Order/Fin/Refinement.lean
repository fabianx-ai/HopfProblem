module
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
/-!
# Finite weak-list refinement

Textbook j.6 A–C: common distinct cut values, weak rank blocks and local interval containment.
Repeated occurrences share ranks; empty blocks and singleton cut lists are retained.
-/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
universe u v
namespace Fin

-- A01–A03 literal representations plus the nonempty-cardinality obligation.
/-- j.6.A: the finite union of the two cut-value sets. -/
def commonCutValues {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) : Finset α :=
  Finset.univ.image c ∪ Finset.univ.image d

/-- j.6.A: the number of pieces between distinct common cut values. -/
def commonCutCount {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) : ℕ :=
  (commonCutValues c d).card - 1

/-- j.6.A: each cut list has an initial entry, including zero-piece lists. -/
theorem commonCutValues_nonempty {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) :
    (commonCutValues c d).Nonempty := by
  exact ⟨c 0, by simp [commonCutValues]⟩
/-- j.6.A: the common value count is one more than its piece count. -/
theorem commonCutValues_card {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) :
    (commonCutValues c d).card = commonCutCount c d + 1 := by
  have h := Finset.card_pos.mpr (commonCutValues_nonempty c d)
  unfold commonCutCount
  omega
/-- j.6.A: the increasing enumeration of distinct common cut values. -/
def commonCut {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) :
    Fin (commonCutCount c d+1) → α :=
  (commonCutValues c d).orderEmbOfFin (commonCutValues_card c d)

-- Membership proofs are literal finite-image/union representation only.
/-- j.6.A: the weak rank map of the first list; repeated values share ranks. -/
def commonCutRankLeft {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) :
    Fin (n+1) → Fin (commonCutCount c d+1) :=
  fun i => ((commonCutValues c d).orderIsoOfFin (commonCutValues_card c d)).symm
    ⟨c i, by simp [commonCutValues]⟩

/-- j.6.A: the weak rank map of the second list. -/
def commonCutRankRight {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) :
    Fin (p+1) → Fin (commonCutCount c d+1) :=
  fun i => ((commonCutValues c d).orderIsoOfFin (commonCutValues_card c d)).symm
    ⟨d i, by simp [commonCutValues]⟩

-- A04: actual distinct values and both rank/value equations.
/-- j.6.A: common enumeration and both exact rank-value equations. -/
theorem commonCut_properties {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) :
    StrictMono (commonCut c d) ∧
    Set.range (commonCut c d) = (commonCutValues c d : Set α) ∧
    (∀ i, commonCut c d (commonCutRankLeft c d i) = c i) ∧
    (∀ i, commonCut c d (commonCutRankRight c d i) = d i) := by
  refine ⟨(commonCutValues c d).orderEmbOfFin (commonCutValues_card c d) |>.strictMono,
    Finset.range_orderEmbOfFin _ _, ?_, ?_⟩
  · intro i
    exact congrArg Subtype.val
      (((commonCutValues c d).orderIsoOfFin (commonCutValues_card c d)).apply_symm_apply
        ⟨c i, by simp [commonCutValues]⟩)
  · intro i
    exact congrArg Subtype.val
      (((commonCutValues c d).orderIsoOfFin (commonCutValues_card c d)).apply_symm_apply
        ⟨d i, by simp [commonCutValues]⟩)


-- A05: weak original lists; rank maps are NOT injective.
/-- j.6.A: weak ranks preserve order and the shared endpoints. -/
theorem commonCut_order_endpoints {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) (a b : α)
    (hc : Monotone c) (hd : Monotone d)
    (hc0 : c 0 = a) (hcn : c (Fin.last n) = b)
    (hd0 : d 0 = a) (hdp : d (Fin.last p) = b) :
    commonCut c d 0 = a ∧
    commonCut c d (Fin.last (commonCutCount c d)) = b ∧
    Monotone (commonCutRankLeft c d) ∧
    Monotone (commonCutRankRight c d) ∧
    commonCutRankLeft c d 0 = 0 ∧
    commonCutRankLeft c d (Fin.last n) = Fin.last (commonCutCount c d) ∧
    commonCutRankRight c d 0 = 0 ∧
    commonCutRankRight c d (Fin.last p) = Fin.last (commonCutCount c d) := by
  obtain ⟨hr, hRange, hLeft, hRight⟩ := commonCut_properties c d
  have hBounds (x : α) (hx : x ∈ commonCutValues c d) : a ≤ x ∧ x ≤ b := by
    simp only [commonCutValues, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨hc0 ▸ hc (Fin.zero_le i), hcn ▸ hc (Fin.le_last i)⟩
    · exact ⟨hd0 ▸ hd (Fin.zero_le i), hdp ▸ hd (Fin.le_last i)⟩
  have hMem (j) : commonCut c d j ∈ commonCutValues c d := by
    change commonCut c d j ∈ (commonCutValues c d : Set α)
    rw [← hRange]
    exact Set.mem_range_self j
  have hFirst : commonCut c d 0 = a := by
    apply le_antisymm
    · simpa only [hLeft, hc0] using hr.monotone (Fin.zero_le (commonCutRankLeft c d 0))
    · exact (hBounds _ (hMem 0)).1
  have hLast : commonCut c d (Fin.last (commonCutCount c d)) = b := by
    apply le_antisymm
    · exact (hBounds _ (hMem _)).2
    · simpa only [hLeft, hcn] using hr.monotone (Fin.le_last (commonCutRankLeft c d (Fin.last n)))
  have hL : Monotone (commonCutRankLeft c d) := by
    intro i j hij
    apply hr.le_iff_le.mp
    simpa only [hLeft] using hc hij
  have hR : Monotone (commonCutRankRight c d) := by
    intro i j hij
    apply hr.le_iff_le.mp
    simpa only [hRight] using hd hij
  exact ⟨hFirst, hLast, hL, hR,
    hr.injective ((hLeft 0).trans (hc0.trans hFirst.symm)),
    hr.injective ((hLeft _).trans (hcn.trans hLast.symm)),
    hr.injective ((hRight 0).trans (hd0.trans hFirst.symm)),
    hr.injective ((hRight _).trans (hdp.trans hLast.symm))⟩
/-- j.6.A: equal outer endpoints give a singleton common value list. -/
theorem commonCutCount_eq_zero {α : Type u} [LinearOrder α] {n p : ℕ}
    (c : Fin (n+1) → α) (d : Fin (p+1) → α) (a : α)
    (hc : Monotone c) (hd : Monotone d)
    (hc0 : c 0 = a) (hcn : c (Fin.last n) = a)
    (hd0 : d 0 = a) (hdp : d (Fin.last p) = a) :
    commonCutCount c d = 0 ∧ commonCutValues c d = {a} := by
  have hc' (i : Fin (n+1)) : c i = a :=
    le_antisymm (hcn ▸ hc (Fin.le_last i)) (hc0 ▸ hc (Fin.zero_le i))
  have hd' (i : Fin (p+1)) : d i = a :=
    le_antisymm (hdp ▸ hd (Fin.le_last i)) (hd0 ▸ hd (Fin.zero_le i))
  have hs : commonCutValues c d = {a} := by
    ext x
    simp [commonCutValues, hc', hd', eq_comm]
  exact ⟨by simp [commonCutCount, hs], hs⟩


-- B01 literal consecutive half-open rank blocks and their local lengths.
/-- j.6.B: the half-open block of refined pieces belonging to one old piece. -/
def rankBlock {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j =>
    (ρ i.castSucc).val ≤ j.val ∧ j.val < (ρ i.succ).val)

/-- j.6.B: the length of a consecutive rank block. -/
def rankBlockSize {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (i : Fin n) : ℕ := (ρ i.succ).val - (ρ i.castSucc).val

/-- j.6.B: blocks of different old pieces are disjoint. -/
theorem rankBlock_disjoint {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (hρ : Monotone ρ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (rankBlock ρ) := by
  intro i hi k hk hik
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
  rcases lt_or_gt_of_ne hik with h | h
  · have hidx : i.succ ≤ k.castSucc := by
      change i.val+1 ≤ k.val
      change i.val < k.val at h
      omega
    have hm := hρ hidx
    change (ρ i.succ).val ≤ (ρ k.castSucc).val at hm
    omega
  · have hidx : k.succ ≤ i.castSucc := by
      change k.val+1 ≤ i.val
      change k.val < i.val at h
      omega
    have hm := hρ hidx
    change (ρ k.succ).val ≤ (ρ i.castSucc).val at hm
    omega
/-- j.6.B: endpoint-preserving ranks cover all refined pieces. -/
theorem rankBlock_cover {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (hρ : Monotone ρ) (h0 : ρ 0 = 0) (hn : ρ (Fin.last n) = Fin.last m) :
    (Finset.univ : Finset (Fin n)).biUnion (rankBlock ρ) = Finset.univ := by
  ext j
  simp only [Finset.mem_univ, iff_true]
  let cN : ℕ → ℕ := fun k => if hk : k < n+1 then (ρ ⟨k,hk⟩).val else m
  have hFirst : cN 0 = 0 := by simpa [cN] using congrArg Fin.val h0
  have hLast : cN n = m := by
    simpa [cN, Fin.last] using congrArg Fin.val hn
  have hj : j.val ∈ Set.Ico (cN 0) (cN n) := by
    rw [hFirst, hLast]
    exact ⟨Nat.zero_le _, j.isLt⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (Ico_subset_biUnion_Ico n cN hj)
  obtain ⟨hk, hj⟩ := Set.mem_iUnion.mp hk
  have hkn := Finset.mem_range.mp hk
  let i : Fin n := ⟨k,hkn⟩
  have hL : ρ ⟨k, Nat.lt_succ_of_lt hkn⟩ = ρ i.castSucc := congrArg ρ (Fin.ext rfl)
  have hR : ρ ⟨k+1, Nat.succ_lt_succ hkn⟩ = ρ i.succ := congrArg ρ (Fin.ext rfl)
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [cN, dif_pos (Nat.lt_succ_of_lt hkn),
    dif_pos (Nat.succ_lt_succ hkn), Set.mem_Ico, hL, hR] using hj
/-- j.6.B: each refined piece belongs to exactly one rank block. -/
theorem rankBlock_unique_owner {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (hρ : Monotone ρ) (h0 : ρ 0 = 0) (hn : ρ (Fin.last n) = Fin.last m)
    (j : Fin m) : ∃! i : Fin n, j ∈ rankBlock ρ i := by
  have hj' : j ∈ (Finset.univ : Finset (Fin n)).biUnion (rankBlock ρ) := by
    rw [rankBlock_cover ρ hρ h0 hn]
    exact Finset.mem_univ j
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj'
  refine ⟨i, hji, ?_⟩
  intro k hjk
  by_contra hki
  exact (Finset.disjoint_left.mp
    (rankBlock_disjoint ρ hρ (Finset.mem_univ k) hi hki)) hjk hji
/-- j.6.B: equal endpoint ranks give an empty block of size zero. -/
theorem rankBlock_empty {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (i : Fin n) (heq : ρ i.castSucc = ρ i.succ) :
    rankBlock ρ i = ∅ ∧ rankBlockSize ρ i = 0 := by
  constructor
  · ext j
    simp [rankBlock, heq]
  · simp [rankBlockSize, heq]
/-- j.6.B: an actual block member forces strictly separated ranks. -/
theorem rankBlock_strict {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (i : Fin n) (j : Fin m) (hj : j ∈ rankBlock ρ i) :
    ρ i.castSucc < ρ i.succ := by
  simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  change (ρ i.castSucc).val < (ρ i.succ).val
  omega
/-- j.6.B: a one-entry rank list forces a zero-piece target. -/
theorem rankTarget_zero_of_source_zero {m : ℕ} (ρ : Fin 1 → Fin (m+1))
    (h0 : ρ 0 = 0) (hn : ρ (Fin.last 0) = Fin.last m) : m = 0 := by
  have he : (0 : Fin 1) = Fin.last 0 := rfl
  have h := congrArg Fin.val (h0.symm.trans ((congrArg ρ he).trans hn))
  simpa using h.symm


-- B02 local finite indexing.
/-- j.6.B: increasing local indices enumerate the actual finite rank block. -/
def rankBlockEquiv {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (hρ : Monotone ρ) (i : Fin n) :
    Fin (rankBlockSize ρ i) ≃ {j : Fin m // j ∈ rankBlock ρ i} := {
  toFun := fun k => ⟨⟨(ρ i.castSucc).val+k.val, by
    have hlo := hρ (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
    have hhi := (ρ i.succ).isLt
    have hk := k.isLt
    change (ρ i.castSucc).val ≤ (ρ i.succ).val at hlo
    unfold rankBlockSize at hk
    omega⟩, by
      simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      have hk := k.isLt
      unfold rankBlockSize at hk
      omega⟩
  invFun := fun j => ⟨j.val.val-(ρ i.castSucc).val, by
    have hj := j.property
    simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    unfold rankBlockSize
    omega⟩
  left_inv := by intro k; apply Fin.ext; simp
  right_inv := by
    intro j
    apply Subtype.ext
    apply Fin.ext
    have hj := j.property
    simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    dsimp
    omega
}
/-- j.6.B: local piece index equals the lower rank plus the local offset. -/
theorem rankBlockEquiv_val {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (hρ : Monotone ρ) (i : Fin n) (k : Fin (rankBlockSize ρ i)) :
    ((rankBlockEquiv ρ hρ i k).val).val = (ρ i.castSucc).val + k.val := rfl
/-- j.6.B: the inclusive last local cut remains a valid global cut. -/
theorem rankBlockCut_bound {n m : ℕ} (ρ : Fin (n+1) → Fin (m+1))
    (hρ : Monotone ρ) (i : Fin n) (k : Fin (rankBlockSize ρ i+1)) :
    (ρ i.castSucc).val + k.val < m+1 := by
  have hlo := hρ (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
  have hhi := (ρ i.succ).isLt
  have hk := k.isLt
  change (ρ i.castSucc).val ≤ (ρ i.succ).val at hlo
  unfold rankBlockSize at hk
  omega


-- C01 literal local cut list; no ordering/geometric parameter on α is needed to form it.
/-- j.6.C: the local cut list attached to a rank block. -/
def rankBlockCuts {α : Type u} {n m : ℕ} (r : Fin (m+1) → α)
    (ρ : Fin (n+1) → Fin (m+1)) (hρ : Monotone ρ) (i : Fin n) :
    Fin (rankBlockSize ρ i+1) → α :=
  fun k => r ⟨(ρ i.castSucc).val+k.val, rankBlockCut_bound ρ hρ i k⟩

/-- j.6.C: the local list has the original block endpoints. -/
theorem rankBlockCuts_endpoints {α : Type u} {n m : ℕ} (r : Fin (m+1) → α)
    (ρ : Fin (n+1) → Fin (m+1)) (hρ : Monotone ρ) (i : Fin n) :
    rankBlockCuts r ρ hρ i 0 = r (ρ i.castSucc) ∧
    rankBlockCuts r ρ hρ i (Fin.last (rankBlockSize ρ i)) = r (ρ i.succ) := by
  constructor
  · apply congrArg r
    apply Fin.ext
    simp [rankBlockCuts]
  · apply congrArg r
    apply Fin.ext
    have hlo := hρ (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
    change (ρ i.castSucc).val ≤ (ρ i.succ).val at hlo
    simp only [rankBlockCuts, Fin.last, rankBlockSize]
    omega
/-- j.6.C: local cuts inherit the weak order of the global list. -/
theorem rankBlockCuts_monotone {α : Type u} [Preorder α] {n m : ℕ}
    (r : Fin (m+1) → α) (hr : Monotone r)
    (ρ : Fin (n+1) → Fin (m+1)) (hρ : Monotone ρ) (i : Fin n) :
    Monotone (rankBlockCuts r ρ hρ i) := by
  intro k l hkl
  apply hr
  change (ρ i.castSucc).val+k.val ≤ (ρ i.castSucc).val+l.val
  exact Nat.add_le_add_left hkl _
/-- j.6.C: local adjacent endpoints are the corresponding global endpoints. -/
theorem rankBlockCuts_adjacent {α : Type u} {n m : ℕ} (r : Fin (m+1) → α)
    (ρ : Fin (n+1) → Fin (m+1)) (hρ : Monotone ρ)
    (i : Fin n) (k : Fin (rankBlockSize ρ i)) :
    rankBlockCuts r ρ hρ i k.castSucc = r (rankBlockEquiv ρ hρ i k).val.castSucc ∧
    rankBlockCuts r ρ hρ i k.succ = r (rankBlockEquiv ρ hρ i k).val.succ := by
  constructor
  · apply congrArg r
    apply Fin.ext
    rfl
  · apply congrArg r
    apply Fin.ext
    simp only [rankBlockCuts, rankBlockEquiv_val, Fin.val_succ]
    omega
/-- j.6.C: each refined closed piece lies in its owning old interval. -/
theorem rankBlock_interval_subset {α : Type u} [Preorder α] {n m : ℕ}
    (r : Fin (m+1) → α) (hr : Monotone r)
    (ρ : Fin (n+1) → Fin (m+1)) (i : Fin n) (j : Fin m)
    (hj : j ∈ rankBlock ρ i) :
    Set.Icc (r j.castSucc) (r j.succ) ⊆
      Set.Icc (r (ρ i.castSucc)) (r (ρ i.succ)) := by
  simp only [rankBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  apply Set.Icc_subset_Icc
  · apply hr
    exact hj.1
  · apply hr
    change j.val+1 ≤ (ρ i.succ).val
    omega
/-- j.6.C: a strict refined piece has a strict containing old interval. -/
theorem rankBlock_strict_interval {α : Type u} [LinearOrder α] {n m : ℕ}
    (r : Fin (m+1) → α) (hr : Monotone r)
    (ρ : Fin (n+1) → Fin (m+1)) (i : Fin n) (j : Fin m)
    (hj : j ∈ rankBlock ρ i) (hstrict : r j.castSucc < r j.succ) :
    r (ρ i.castSucc) < r (ρ i.succ) := by
  have hsub := rankBlock_interval_subset r hr ρ i j hj
  have hl := hsub (show r j.castSucc ∈ Set.Icc (r j.castSucc) (r j.succ) from ⟨le_rfl,hstrict.le⟩)
  have hu := hsub (show r j.succ ∈ Set.Icc (r j.castSucc) (r j.succ) from ⟨hstrict.le,le_rfl⟩)
  exact lt_of_le_of_lt hl.1 (lt_of_lt_of_le hstrict hu.2)


-- C02: ANY inserted weak list, no new curve witness or rank assumption.
/-- j.6.C: inserting weak cuts places every strict new piece inside a strict old piece. -/
theorem exists_strict_piece_containing_of_range_subset
    {α : Type u} [LinearOrder α] {n m : ℕ}
    (c : Fin (n+1) → α) (r : Fin (m+1) → α) (a b : α)
    (hc : Monotone c) (hr : Monotone r)
    (hc0 : c 0 = a) (hcn : c (Fin.last n) = b)
    (hr0 : r 0 = a) (hrm : r (Fin.last m) = b)
    (hvalues : Set.range c ⊆ Set.range r)
    (j : Fin m) (hj : r j.castSucc < r j.succ) :
    ∃ i : Fin n, c i.castSucc < c i.succ ∧
      Set.Icc (r j.castSucc) (r j.succ) ⊆ Set.Icc (c i.castSucc) (c i.succ) := by
  let cN : ℕ → α := fun k => if hk : k < n+1 then c ⟨k,hk⟩ else b
  have hFirst : cN 0 = a := by simpa [cN] using hc0
  have hLast : cN n = b := by simpa [cN, Fin.last] using hcn
  have hLower : a ≤ r j.castSucc := hr0 ▸ hr (Fin.zero_le _)
  have hUpper : r j.succ ≤ b := hrm ▸ hr (Fin.le_last _)
  have ht : r j.castSucc ∈ Set.Ico (cN 0) (cN n) := by
    rw [hFirst, hLast]
    exact ⟨hLower, hj.trans_le hUpper⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (Ico_subset_biUnion_Ico n cN ht)
  obtain ⟨hk, ht⟩ := Set.mem_iUnion.mp hk
  have hkn := Finset.mem_range.mp hk
  let i : Fin n := ⟨k,hkn⟩
  have hL : c ⟨k, Nat.lt_succ_of_lt hkn⟩ = c i.castSucc := congrArg c (Fin.ext rfl)
  have hR : c ⟨k+1, Nat.succ_lt_succ hkn⟩ = c i.succ := congrArg c (Fin.ext rfl)
  have hOld : c i.castSucc ≤ r j.castSucc ∧ r j.castSucc < c i.succ := by
    simpa only [cN, dif_pos (Nat.lt_succ_of_lt hkn),
      dif_pos (Nat.succ_lt_succ hkn), Set.mem_Ico, hL, hR] using ht
  obtain ⟨l, hl⟩ := hvalues (Set.mem_range_self i.succ)
  have hjl : j.succ ≤ l := by
    by_contra hn
    have hlj : l ≤ j.castSucc := by
      change l.val ≤ j.val
      change ¬ j.val+1 ≤ l.val at hn
      omega
    have hh := hr hlj
    rw [hl] at hh
    exact (not_lt_of_ge hh) hOld.2
  have hBound : r j.succ ≤ c i.succ := hl ▸ hr hjl
  exact ⟨i, hOld.1.trans_lt hOld.2, Set.Icc_subset_Icc hOld.1 hBound⟩

end Fin
