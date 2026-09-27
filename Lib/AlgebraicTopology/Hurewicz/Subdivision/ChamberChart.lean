/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Subdivision.CubeClass
import Lib.AlgebraicTopology.Hurewicz.Subdivision.InsertPermutation

/-!
# Chamber charts of the ordered cube

The chamber of the `n`-cube attached to a permutation `e` is the set of points whose
coordinates are ordered by `e`. A *chamber chart* `Hurewicz.NativeSubdivision.NativeChamberChart e`
is a cube self-map satisfying the four face compatibilities of the Duffy map of that
chamber: on the face where the last ordered coordinate is `0` the chart is `0` there, on
the face where the first ordered coordinate is `1` the chart is `1` there, and on the
faces where an inner ordered coordinate is `0` or `1` the chart identifies it with its
neighbour in the order. Any two charts of the same chamber land on a common flat of the
boundary (`NativeChamberChart.sameFlat`), which is what makes their pullbacks homotopic.

The *cut functions* `chamberLower`, `chamberUpper` of a chart at a slot `r` are the two
ordered coordinates adjacent to the slot (with `0` and `1` at the ends); the *cut sequence*
`chamberCutSequence` lists them. Inserting a new coordinate at slot `r` by the convex
combination of the two cuts produces the chart `insertChamberChart e r chart` of the
chamber `insertPermutation e r` of the `(n + 1)`-cube.

This is the recursive description of the Kuhn chambers used to subdivide a based cube
in the proof of the Hurewicz theorem (Hatcher, *Algebraic Topology*, Theorem 4.32).

## Main definitions

* `Hurewicz.NativeSubdivision.NativeChamberChart`
* `Hurewicz.NativeSubdivision.chamberLower`, `Hurewicz.NativeSubdivision.chamberUpper`,
  `Hurewicz.NativeSubdivision.chamberCutSequence`
* `Hurewicz.NativeSubdivision.insertChamberMap`, `Hurewicz.NativeSubdivision.insertChamberChart`

## Main results

* `Hurewicz.NativeSubdivision.NativeChamberChart.sameFlat`
* `Hurewicz.NativeSubdivision.chamberCutSequence_castSucc`, `Hurewicz.NativeSubdivision.chamberCutSequence_succ`
-/

open Set Function Topology

noncomputable section

/-! ### Chamber charts and cut sequences -/

/-- A chart for the `e`-ordered chamber: a cube self-map satisfying the listed
boundary compatibility conditions with the standard ordered Duffy map (the
`sameFlat` property). -/
structure Hurewicz.NativeSubdivision.NativeChamberChart {n : ℕ}
    (e : Equiv.Perm (Fin n)) where
  toContinuousMap : C(NativeCube (Fin n), NativeCube (Fin n))
  zero_last : ∀ u i, i.val + 1 = n → u (e i) = 0 → toContinuousMap u (e i) = 0
  zero_adjacent :
    ∀ u i j, i.val + 1 = j.val → u (e i) = 0 → toContinuousMap u (e i) = toContinuousMap u (e j)
  one_first : ∀ u i, i.val = 0 → u (e i) = 1 → toContinuousMap u (e i) = 1
  one_adjacent :
    ∀ u i j, j.val + 1 = i.val → u (e i) = 1 → toContinuousMap u (e i) = toContinuousMap u (e j)

/-- The lower cut function of a chamber chart at index `r`: the `e`-ordered
coordinate `e ⟨r⟩` of the chart, or `0` when `r = last`. -/
def Hurewicz.NativeSubdivision.chamberLower {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : r.val < n then (ContinuousMap.eval (e ⟨r.val, h⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 0

/-- The upper cut function of a chamber chart at index `r`: the `e`-ordered
coordinate `e ⟨r-1⟩` of the chart, or `1` when `r = 0`. -/
def Hurewicz.NativeSubdivision.chamberUpper {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : 0 < r.val then (ContinuousMap.eval (e ⟨r.val - 1, by omega⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 1

/-- At an index `r < n`, `chamberLower` is the chart's `e ⟨r⟩`-coordinate. -/
theorem Hurewicz.NativeSubdivision.chamberLower_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) : chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  have hr : r.val < n := h ▸ k.isLt
  have hk : (⟨r.val, hr⟩ : Fin n) = k := Fin.ext h
  simp [chamberLower, hr, hk]

/-- At the last index `n`, `chamberLower` is the constant `0`. -/
theorem Hurewicz.NativeSubdivision.chamberLower_last {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = n) :
    chamberLower e r chart u = 0 := by simp [chamberLower, h]

/-- At an index `r > 0`, `chamberUpper` is the chart's `e ⟨r-1⟩`-coordinate. -/
theorem Hurewicz.NativeSubdivision.chamberUpper_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) : chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  have hr : 0 < r.val := by omega
  have hk : (⟨r.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
  simp [chamberUpper, hr, hk]

/-- At index `0`, `chamberUpper` is the constant `1`. -/
theorem Hurewicz.NativeSubdivision.chamberUpper_first {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = 0) :
    chamberUpper e r chart u = 1 := by simp [chamberUpper, h]

/-- On the face where the chart's `e 0`-coordinate is `0`, the lower cut at index
`1` vanishes. -/
theorem Hurewicz.NativeSubdivision.chamberLower_zero_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) (hu : u (e k) = 0) :
    chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : r.val < n
  · let j : Fin n := ⟨r.val, hr⟩
    rw [chamberLower_of_rank e r chart u j rfl]
    exact (chart.zero_adjacent u k j (by simpa [j] using h.symm) hu).symm
  · have hn : r.val = n := by omega
    rw [chamberLower_last e r chart u hn]
    exact (chart.zero_last u k (by omega) hu).symm

/-- On the face where the chart's `e ⟨n-1⟩`-coordinate is `1`, the upper cut at
index `n` is `1`. -/
theorem Hurewicz.NativeSubdivision.chamberUpper_one_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) (hu : u (e k) = 1) :
    chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : 0 < r.val
  · let j : Fin n := ⟨r.val - 1, by omega⟩
    rw [chamberUpper_of_rank e r chart u j (by dsimp [j]; omega)]
    exact (chart.one_adjacent u k j (by dsimp [j]; omega) hu).symm
  · have hz : r.val = 0 := by omega
    rw [chamberUpper_first e r chart u hz]
    exact (chart.one_first u k (by omega) hu).symm

/-- The old coordinates of a chamber chart: the `Fin m` restriction of a
`Fin n` chart point. -/
def Hurewicz.NativeSubdivision.chamberOldCoordinates {n : ℕ} :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin n))
    where
  toFun u k := u k.castSucc
  continuous_toFun := continuous_pi fun _ => continuous_apply _

/-- The map inserting a cut value into the `e`-chamber chart at the cut index,
extending a `Fin m` chamber chart to `Fin (m+1)`. -/
def Hurewicz.NativeSubdivision.insertChamberMap {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin (n + 1)))
    where
  toFun
    u :=
    Fin.lastCases
      (Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)))
      (chart.toContinuousMap (chamberOldCoordinates u))
  continuous_toFun := by
    apply continuous_pi
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.lastCases_last]
      exact
        Set.Icc.continuous_convexComb_prod.comp
          (((chamberLower e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
            (((chamberUpper e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
              (continuous_apply (Fin.last n))))
    · simp only [Fin.lastCases_castSucc]
      exact
        (continuous_apply j).comp
          (chart.toContinuousMap.continuous.comp chamberOldCoordinates.continuous)

/-- On `castSucc` indices, `insertChamberMap` agrees with the original chart. -/
@[simp]
theorem Hurewicz.NativeSubdivision.insertChamberMap_apply_castSucc {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    insertChamberMap e r chart u k.castSucc = chart.toContinuousMap (chamberOldCoordinates u) k :=
  by simp [insertChamberMap]

/-- On the last index, `insertChamberMap` applies the cut function. -/
@[simp]
theorem Hurewicz.NativeSubdivision.insertChamberMap_apply_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) :
    insertChamberMap e r chart u (Fin.last n) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) := by
  simp [insertChamberMap]

/-- A `Fin (m+2)` index is `0`, a `castSucc`, or the last index. -/
theorem Hurewicz.NativeSubdivision.chamberSuccAbove_val_cases {n : ℕ} (r : Fin (n + 1))
    (i : Fin n) :
    ((r.succAbove i).val = i.val ∧ i.val < r.val) ∨
      ((r.succAbove i).val = i.val + 1 ∧ r.val ≤ i.val) := by
  by_cases h : i.castSucc < r
  · exact Or.inl ⟨congrArg Fin.val (Fin.succAbove_of_castSucc_lt r i h), h⟩
  · exact
      Or.inr
        ⟨congrArg Fin.val (Fin.succAbove_of_le_castSucc r i (le_of_not_gt h)), le_of_not_gt h⟩

/-- The upper cut at `r.succ` equals the lower cut at `r.castSucc`. -/
theorem Hurewicz.NativeSubdivision.chamberUpper_succ_eq_lower_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin m) (u : NativeCube (Fin m)) :
    chamberUpper e j.succ chart u = chamberLower e j.castSucc chart u := by
  rw [chamberUpper_of_rank e j.succ chart u j rfl,
    chamberLower_of_rank e j.castSucc chart u j rfl]

/-- The sequence of cut functions of a chamber chart: `0`, then the upper cuts in
reverse order. -/
def Hurewicz.NativeSubdivision.chamberCutSequence {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) : Fin (m + 2) → C(NativeCube (Fin m), (unitInterval)) :=
  Fin.cons (ContinuousMap.const _ 0) (fun j : Fin (m + 1) => chamberUpper e j.rev chart)

/-- The `j.succ` entry of the cut sequence is the upper cut at `j.rev`. -/
theorem Hurewicz.NativeSubdivision.chamberCutSequence_succ {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.succ u = chamberUpper e j.rev chart u := by
  simp [chamberCutSequence]

/-- The last entry of the cut sequence is the constant `1`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.chamberCutSequence_last {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart (Fin.last (m + 1)) u = 1 := by
  change chamberUpper e (Fin.last m).rev chart u = 1
  rw [Fin.rev_last]
  exact chamberUpper_first e 0 chart u rfl

/-- The `castSucc` entries of the cut sequence agree with the reversed upper cuts
and consecutive entries match at shared faces. -/
theorem Hurewicz.NativeSubdivision.chamberCutSequence_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.castSucc u = chamberLower e j.rev chart u := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change 0 = chamberLower e (0 : Fin (m + 1)).rev chart u
    rw [Fin.rev_zero]
    exact (chamberLower_last e (Fin.last m) chart u rfl).symm
  · change chamberUpper e k.castSucc.rev chart u = chamberLower e k.succ.rev chart u
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact chamberUpper_succ_eq_lower_castSucc e chart k.rev u

/-- Summing over the cut sequence equals summing in reverse order (`Fin.revPerm`). -/
theorem Hurewicz.NativeSubdivision.chamberCuts_sum_rev {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (m + 1) → A) : ∑ j : Fin (m + 1), f j.rev = ∑ j : Fin (m + 1), f j :=
  Equiv.sum_comp Fin.revPerm f

/-! ### Inserted chamber charts -/

/-- The inserted chamber map at cut value `0` agrees on the last face with the
lower cut. -/
theorem Hurewicz.NativeSubdivision.insertChamberMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val + 1 = n + 1)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) = 0 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_zero]
    exact chamberLower_last e r chart (chamberOldCoordinates u) (by omega)
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.zero_last (chamberOldCoordinates u) k (by omega) hu

/-- The inserted chamber map at cut value `0` agrees on adjacent faces. -/
theorem Hurewicz.NativeSubdivision.insertChamberMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_zero]
      exact chamberLower_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_zero_face e r chart (chamberOldCoordinates u) k hr hu,
        chamberUpper_of_rank e r chart (chamberOldCoordinates u) k hr]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : k.val + 1 = l.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.zero_adjacent (chamberOldCoordinates u) k l hkl hu

/-- The inserted chamber map at cut value `1` agrees on the first face. -/
theorem Hurewicz.NativeSubdivision.insertChamberMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val = 0)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) = 1 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_one]
    exact chamberUpper_first e r chart (chamberOldCoordinates u) hi
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.one_first (chamberOldCoordinates u) k (by omega) hu

/-- The inserted chamber map at cut value `1` agrees on adjacent faces. -/
theorem Hurewicz.NativeSubdivision.insertChamberMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : j.val + 1 = i.val)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_one]
      exact chamberUpper_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_of_rank e r chart (chamberOldCoordinates u) k hr,
        chamberUpper_one_face e r chart (chamberOldCoordinates u) k hr hu]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : l.val + 1 = k.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.one_adjacent (chamberOldCoordinates u) k l hkl hu

/-- The chamber chart on `Fin (n+1)` obtained by inserting the cut index into the
`e`-chart. -/
def Hurewicz.NativeSubdivision.insertChamberChart {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : NativeChamberChart (insertPermutation e r)
    where
  toContinuousMap := insertChamberMap e r chart
  zero_last := insertChamberMap_zero_last e r chart
  zero_adjacent := insertChamberMap_zero_adjacent e r chart
  one_first := insertChamberMap_one_first e r chart
  one_adjacent := insertChamberMap_one_adjacent e r chart

/-- Extensionality for chamber charts: equality of the underlying maps suffices. -/
@[ext]
theorem Hurewicz.NativeSubdivision.NativeChamberChart.ext {n : ℕ} {e : Equiv.Perm (Fin n)}
    {f g : Hurewicz.NativeSubdivision.NativeChamberChart e}
    (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- On the cube boundary, any two charts of the `e`-chamber land on the same flat. -/
theorem Hurewicz.NativeSubdivision.NativeChamberChart.sameFlat {m : ℕ}
    {e : Equiv.Perm (Fin m)} (chart other : Hurewicz.NativeSubdivision.NativeChamberChart e)
    (u : Hurewicz.NativeSubdivision.NativeCube (Fin m)) (hu : u ∈ Cube.boundary (Fin m)) :
    Hurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  let i := e.symm j
  have hei : e i = j := e.apply_symm_apply j
  rcases hj with hj | hj
  · have hi : u (e i) = 0 := hei ▸ hj
    by_cases hilast : i.val + 1 = m
    · exact .zero (e i) (chart.zero_last u i hilast hi) (other.zero_last u i hilast hi)
    · let k : Fin m := ⟨i.val + 1, by have := i.isLt; omega⟩
      have hik : i.val + 1 = k.val := rfl
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.zero_adjacent u i k hik hi)
          (other.zero_adjacent u i k hik hi)
  · have hi : u (e i) = 1 := hei ▸ hj
    by_cases hifirst : i.val = 0
    · exact .one (e i) (chart.one_first u i hifirst hi) (other.one_first u i hifirst hi)
    · let k : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hki : k.val + 1 = i.val := by dsimp [k]; omega
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.one_adjacent u i k hki hi) (other.one_adjacent u i k hki hi)
