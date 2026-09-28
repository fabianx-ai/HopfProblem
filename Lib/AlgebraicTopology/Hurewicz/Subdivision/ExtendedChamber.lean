/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Subdivision.ChamberChart
import Lib.AlgebraicTopology.Hurewicz.Subdivision.Slicing

/-!
# Extended chamber maps and the insertion sum

A chamber chart of the `m`-cube extends to a self-map of the `n`-cube (`m ≤ n`) acting on
the first `m` coordinates and leaving the others unchanged
(`Hurewicz.NativeSubdivision.extendCubeMap`). For an internally based cube
`p : GenLoop (Fin n) X x` the pullback along the extended chart is again a based cube,
the *extended chamber loop* `extendedChamberLoop p hp h chart`, and its class does not
depend on the chart (`nativeClass_extendedChamber_eq`), by the linear homotopy on the
common flat.

The main result is the insertion step: when `m + 1 ≤ n`, the extended chamber loop of a
chart of the `m`-cube chamber `e` is the sum, over the `m + 1` slots `r`, of the extended
chamber loops of the inserted charts `insertChamberChart e r chart`
(`nativeClass_extendedChamber_eq_sum_insertions`). It follows by slicing the coordinate
`chamberCutIndex h` along the extended cut sequence of the chart (`finiteCuts_class`).

This is the induction step of the subdivision of a based cube into its Kuhn chambers in
the proof of the Hurewicz theorem (Hatcher, *Algebraic Topology*, Theorem 4.32).

## Main definitions

* `Hurewicz.NativeSubdivision.cubeRestriction`, `Hurewicz.NativeSubdivision.extendCubeMap`
* `Hurewicz.NativeSubdivision.extendedChamberLoop`, `Hurewicz.NativeSubdivision.extendedChamberHomotopy`
* `Hurewicz.NativeSubdivision.chamberCutIndex`, `Hurewicz.NativeSubdivision.extendedChamberCutSequence`

## Main results

* `Hurewicz.NativeSubdivision.nativeClass_extendedChamber_eq`
* `Hurewicz.NativeSubdivision.nativeClass_extendedChamber_eq_sum_insertions`
-/

open Set Function Topology

noncomputable section

/-! ### Extended chamber maps -/

/-- The restriction of a `Fin n` cube to the `Fin m` coordinates (for `m ≤ n`). -/
def Hurewicz.NativeSubdivision.cubeRestriction {m n : ℕ} (h : m ≤ n) :
    C(NativeCube (Fin n), NativeCube (Fin m))
    where
  toFun u i := u (Fin.castLE h i)
  continuous_toFun := continuous_pi fun i => continuous_apply (Fin.castLE h i)

/-- `cubeRestriction h u i = u (Fin.castLE h i)`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.cubeRestriction_apply {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin m) : cubeRestriction h u i = u (Fin.castLE h i) :=
  rfl

/-- Extend a cube self-map on `Fin m` coordinates to `Fin n`, leaving coordinates
`≥ m` unchanged. -/
def Hurewicz.NativeSubdivision.extendCubeMap {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) : C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := if hi : i.val < m then f (cubeRestriction h u) ⟨i.val, hi⟩ else u i
  continuous_toFun := by
    apply continuous_pi
    intro i
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      exact (continuous_apply ⟨i.val, hi⟩).comp (f.continuous.comp (cubeRestriction h).continuous)
    · simpa only [dif_neg hi] using
        (continuous_apply i : Continuous fun u : NativeCube (Fin n) => u i)

/-- On `Fin m` coordinates, `extendCubeMap h f` acts as `f` on the restriction. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendCubeMap_castLE {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin m) :
    extendCubeMap h f u (Fin.castLE h i) = f (cubeRestriction h u) i := by simp [extendCubeMap]

/-- On coordinates `≥ m`, `extendCubeMap h f` is the identity. -/
theorem Hurewicz.NativeSubdivision.extendCubeMap_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) : extendCubeMap h f u i = u i := by simp [extendCubeMap, Nat.not_lt.mpr hi]

/-- Updating a coordinate `≥ m` commutes with restriction. -/
theorem Hurewicz.NativeSubdivision.cubeRestriction_update_outside {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin n) (hi : m ≤ i.val) (v : (unitInterval)) :
    cubeRestriction h (Function.update u i v) = cubeRestriction h u := by
  funext j
  apply Function.update_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  exact (Nat.not_lt.mpr hi) (hv ▸ j.isLt)

/-- `extendCubeMap` commutes with `Function.update` on coordinates `≥ m`. -/
theorem Hurewicz.NativeSubdivision.extendCubeMap_update_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) (v : (unitInterval)) :
    extendCubeMap h f (Function.update u i v) = Function.update (extendCubeMap h f u) i v := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [extendCubeMap_outside h f _ i hi]
  · rw [Function.update_of_ne hj]
    by_cases hjm : j.val < m
    · simp only [extendCubeMap, ContinuousMap.coe_mk, dif_pos hjm]
      rw [cubeRestriction_update_outside h u i hi v]
    · rw [extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm),
        extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm), Function.update_of_ne hj]

/-- `extendCubeMap` at `m = n` is the map itself. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendCubeMap_refl {n : ℕ}
    (f : C(NativeCube (Fin n), NativeCube (Fin n))) : extendCubeMap (le_refl n) f = f := by
  ext u i
  simp [cubeRestriction, extendCubeMap]

/-- `extendCubeMap` of a map preserving zero sends zero to zero. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendCubeMap_zero {n : ℕ} (h : 0 ≤ n)
    (f : C(NativeCube (Fin 0), NativeCube (Fin 0))) : extendCubeMap h f = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro u
  funext i
  exact extendCubeMap_outside h f u i (Nat.zero_le _)

/-- If `f u` and `g u` are on the same flat, their `extendCubeMap` images are on
the same flat. -/
theorem Hurewicz.NativeSubdivision.extendCubeMap_sameFlat {m n : ℕ} (h : m ≤ n)
    (f g : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n))
    (hfg : NativeCubeSameFlat (f (cubeRestriction h u)) (g (cubeRestriction h u))) :
    NativeCubeSameFlat (extendCubeMap h f u) (extendCubeMap h g u) := by
  cases hfg with
  | zero i hf hg => exact .zero (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | one i hf hg => exact .one (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | equal i j hij hf hg =>
    exact
      .equal (Fin.castLE h i) (Fin.castLE h j)
        (fun heq => hij (Fin.ext (congrArg (fun k : Fin n => k.val) heq))) (by simpa using hf)
        (by simpa using hg)

/-- The cut index `Fin.castLE h (Fin.last m)` of an extension `m + 1 ≤ n`. -/
def Hurewicz.NativeSubdivision.chamberCutIndex {m n : ℕ} (h : m + 1 ≤ n) : Fin n :=
  Fin.castLE h (Fin.last m)

/-- The cut index is not a `castLE` image of any `j : Fin m`. -/
theorem Hurewicz.NativeSubdivision.chamberCutIndex_ne_castLE {m n : ℕ} (h : m + 1 ≤ n)
    (j : Fin m) : Fin.castLE (Nat.le_of_succ_le h) j ≠ chamberCutIndex h := by
  intro he
  have hv := congrArg Fin.val he
  exact (Nat.ne_of_lt j.isLt) hv

/-- The old coordinates of an extended chamber chart are the cube restriction of
the extended chart. -/
@[simp]
theorem Hurewicz.NativeSubdivision.chamberOldCoordinates_cubeRestriction {m n : ℕ}
    (h : m + 1 ≤ n) (u : NativeCube (Fin n)) :
    chamberOldCoordinates (cubeRestriction h u) = cubeRestriction (Nat.le_of_succ_le h) u :=
  rfl

/-- `extendCubeMap` of an inserted chamber map inserts the cut at the cut index. -/
theorem Hurewicz.NativeSubdivision.extend_insertChamberMap {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (r : Fin (m + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin n)) :
    extendCubeMap h (insertChamberMap e r chart) u =
      Function.update (extendCubeMap (Nat.le_of_succ_le h) chart.toContinuousMap u)
        (chamberCutIndex h)
        (Set.Icc.convexComb (chamberLower e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (chamberUpper e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (u (chamberCutIndex h))) := by
  funext j
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k.castSucc = j := Fin.ext rfl
    have hk' : Fin.castLE h k.castSucc = Fin.castLE (Nat.le_of_succ_le h) k := Fin.ext rfl
    have hji : j ≠ chamberCutIndex h := by
      rw [← hk, hk']
      exact chamberCutIndex_ne_castLE h k
    rw [Function.update_of_ne hji, ← hk, extendCubeMap_castLE, insertChamberMap_apply_castSucc,
      chamberOldCoordinates_cubeRestriction, hk', extendCubeMap_castLE]
  · by_cases hji : j = chamberCutIndex h
    · subst j
      rw [Function.update_self]
      change extendCubeMap h (insertChamberMap e r chart) u (Fin.castLE h (Fin.last m)) = _
      rw [extendCubeMap_castLE, insertChamberMap_apply_last,
        chamberOldCoordinates_cubeRestriction]
      rfl
    · have hjval : j.val ≠ m := fun he => hji (Fin.ext he)
      have hmj : m + 1 ≤ j.val := by omega
      rw [extendCubeMap_outside h _ u j hmj, Function.update_of_ne hji,
        extendCubeMap_outside (Nat.le_of_succ_le h) _ u j (Nat.le_of_succ_le hmj)]

/-- The cut sequence of an extended chamber chart over `Fin n`, padded by the
extension. -/
def Hurewicz.NativeSubdivision.extendedChamberCutSequence {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) :
    Fin (m + 2) → C(NativeCube (Fin n), (unitInterval)) := fun j =>
  (chamberCutSequence e chart j).comp (cubeRestriction (Nat.le_of_succ_le h))

/-- The first entry of the extended cut sequence is `0`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendedChamberCutSequence_zero {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart 0 u = 0 :=
  rfl

/-- The last entry of the extended cut sequence is `1`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendedChamberCutSequence_last {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart (Fin.last (m + 1)) u = 1 :=
  chamberCutSequence_last e chart _

/-- The `castSucc` entries of the extended cut sequence agree with the original
chamber's cuts. -/
theorem Hurewicz.NativeSubdivision.extendedChamberCutSequence_castSucc {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.castSucc u =
      chamberLower e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_castSucc e chart j _

/-- The `succ` entries of the extended cut sequence. -/
theorem Hurewicz.NativeSubdivision.extendedChamberCutSequence_succ {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.succ u =
      chamberUpper e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_succ e chart j _

/-- The extended chamber maps of two charts land on the same flat on the boundary. -/
theorem Hurewicz.NativeSubdivision.extendedChamberMap_sameFlat {m n : ℕ} (h : m ≤ n)
    {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (extendCubeMap h chart.toContinuousMap u)
      (extendCubeMap h other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k = j := Fin.ext rfl
    apply extendCubeMap_sameFlat
    apply chart.sameFlat other
    refine ⟨k, ?_⟩
    simpa only [cubeRestriction_apply, hk] using hj
  · rcases hj with hj | hj
    · exact
        .zero j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
    · exact
        .one j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)

/-- For internally based `p`, the extended chamber map composed with `p` is based. -/
theorem Hurewicz.NativeSubdivision.extendedChamberMap_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (extendCubeMap h chart.toContinuousMap u) = x := by
  simpa only [nativeCubeBlend_zero] using
    nativeCubeBlend_based p hp (extendedChamberMap_sameFlat h chart chart u hu) 0

/-- The based cube obtained by pulling `p` back along the extended chamber map. -/
def Hurewicz.NativeSubdivision.extendedChamberLoop {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) : GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (extendCubeMap h chart.toContinuousMap)
    (extendedChamberMap_based p hp h chart)

/-- `extendedChamberLoop` evaluated at `u` is `p` of the extended chamber image. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendedChamberLoop_apply {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberLoop p hp h chart u = p (extendCubeMap h chart.toContinuousMap u) :=
  rfl

/-- The extended chamber loop of the degenerate extension. -/
@[simp]
theorem Hurewicz.NativeSubdivision.extendedChamberLoop_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : 0 ≤ n) {e : Equiv.Perm (Fin 0)} (chart : NativeChamberChart e) :
    extendedChamberLoop p hp h chart = p := by
  apply GenLoop.ext
  intro u
  simp

/-- The homotopy between two extended chamber loops of `p`, via the linear homotopy
on the common flat. -/
def Hurewicz.NativeSubdivision.extendedChamberHomotopy {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    (extendedChamberLoop p hp h chart).val.HomotopyRel (extendedChamberLoop p hp h other).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (extendCubeMap h chart.toContinuousMap)
    (extendCubeMap h other.toContinuousMap) (extendedChamberMap_based p hp h chart)
    (extendedChamberMap_based p hp h other) (extendedChamberMap_sameFlat h chart other)

/-- The native class of an extended chamber loop is independent of the chart. -/
theorem Hurewicz.NativeSubdivision.nativeClass_extendedChamber_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp h chart) =
      nativeClass (extendedChamberLoop p hp h other) :=
  nativeClass_homotopic ⟨extendedChamberHomotopy p hp h chart other⟩

/-! ### Cut sequences of extended charts and the insertion sum -/

/-- Each entry of the extended cut sequence is independent of the cut index. -/
theorem Hurewicz.NativeSubdivision.extendedChamberCutSequence_independent {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutIndependent (chamberCutIndex h) (extendedChamberCutSequence h e chart j) := by
  intro u v
  change
    chamberCutSequence e chart j
        (cubeRestriction (Nat.le_of_succ_le h) (Function.update u (chamberCutIndex h) v)) =
      chamberCutSequence e chart j (cubeRestriction (Nat.le_of_succ_le h) u)
  rw [cubeRestriction_update_outside (Nat.le_of_succ_le h) u (chamberCutIndex h) (le_refl m) v]

/-- Each entry of the extended cut sequence is based for the extended chamber
loop. -/
theorem Hurewicz.NativeSubdivision.extendedChamberCutSequence_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutBased (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (extendedChamberCutSequence h e chart j) := by
  intro u
  rw [extendedChamberLoop_apply,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  refine Fin.cases ?_ (fun r => ?_) j
  · rw [extendedChamberCutSequence_zero]
    exact p.property _ ⟨chamberCutIndex h, Or.inl (Function.update_self _ _ _)⟩
  · rw [extendedChamberCutSequence_succ]
    by_cases hr : 0 < r.rev.val
    · let k : Fin m := ⟨r.rev.val - 1, by have := r.rev.isLt; omega⟩
      have hk : r.rev.val = k.val + 1 := by
        change r.rev.val = (r.rev.val - 1) + 1
        omega
      rw [chamberUpper_of_rank e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) k hk]
      apply
        hp _ (chamberCutIndex h) (Fin.castLE (Nat.le_of_succ_le h) (e k))
          (chamberCutIndex_ne_castLE h (e k)).symm
      rw [Function.update_self, Function.update_of_ne (chamberCutIndex_ne_castLE h (e k)),
        extendCubeMap_castLE]
    · have hr0 : r.rev.val = 0 := by omega
      rw [chamberUpper_first e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) hr0]
      exact p.property _ ⟨chamberCutIndex h, Or.inr (Function.update_self _ _ _)⟩

/-- The extended chamber loop equals the iterated slice of `p` through the chamber's
cut sequence. -/
theorem Hurewicz.NativeSubdivision.extendedChamberCut_slice_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1)) :
    sliceLoop (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
        (extendedChamberCutSequence h e chart j.castSucc)
        (extendedChamberCutSequence h e chart j.succ)
        (extendedChamberCutSequence_based p hp h e chart j.castSucc)
        (extendedChamberCutSequence_based p hp h e chart j.succ) =
      extendedChamberLoop p hp h (insertChamberChart e j.rev chart) := by
  apply GenLoop.ext
  intro u
  rw [sliceLoop_apply, extendedChamberLoop_apply, extendedChamberCutSequence_castSucc,
    extendedChamberCutSequence_succ,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  exact congrArg p (extend_insertChamberMap h e j.rev chart u).symm

/-- The native class of `p` equals the sum over insertion positions of the chamber
classes. -/
theorem Hurewicz.NativeSubdivision.nativeClass_extendedChamber_eq_sum_insertions {m n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n) {e : Equiv.Perm (Fin m)}
    (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ r : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart)) := by
  have hcut :=
    finiteCuts_class (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (m + 1) (extendedChamberCutSequence h e chart)
      (extendedChamberCutSequence_based p hp h e chart)
      (extendedChamberCutSequence_independent h e chart)
      (extendedChamberCutSequence_zero h e chart) (extendedChamberCutSequence_last h e chart)
  have hrev :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ j : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e j.rev chart)) := by
    simpa only [extendedChamberCut_slice_eq p hp h e chart] using hcut
  exact
    hrev.trans
      (chamberCuts_sum_rev
        (fun r => nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart))))
