/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Subdivision.ChamberChart

/-!
# Duffy maps of the ordered chambers

The *Duffy cube* of a permutation `e` sends `u` to the cumulative products of the
coordinates of `u` taken in the order `e`: the `e i`-th coordinate of
`Hurewicz.NativeSubdivision.nativeDuffyCube e u` is `prefixProduct u (i + 1) = ∏_{k ≤ i} u k`.
Its image consists of `e`-ordered points, so it is a chart of the chamber `e`; the
*ordered Duffy map* `nativeOrderedDuffyMap e` is the Duffy cube precomposed with the
coordinate permutation `e`, and `orderedDuffyChart e` records it as a
`NativeChamberChart e`. Every chamber chart shares a flat with it on the boundary
(`NativeChamberChart.commonOrderedDuffy`).

For an internally based cube `p`, the pullback along any cube self-map that shares a flat
with the ordered Duffy map has class `sign e • nativeClass (nativeDuffyCubeLoop p hp e)`
(`nativeClass_commonOrderedDuffy`), by the linear homotopy and the sign of a permuted
cube.

The cumulative-product map from the cube onto a simplex is Duffy's transformation
(cf. M. G. Duffy, *Quadrature over a pyramid or cube of integrands with a singularity at
a vertex*, 1982); here it serves as the canonical chart of a Kuhn chamber in this
development's proof of the Hurewicz theorem (statement: Hatcher, *Algebraic Topology*,
Theorem 4.32; the argument is recorded in `Lib/docs/C.md`).

## Main definitions

* `Hurewicz.NativeSubdivision.prefixProduct`
* `Hurewicz.NativeSubdivision.nativeDuffyCube`, `Hurewicz.NativeSubdivision.nativeDuffyCubeLoop`
* `Hurewicz.NativeSubdivision.nativeOrderedDuffyMap`, `Hurewicz.NativeSubdivision.orderedDuffyChart`

## Main results

* `Hurewicz.NativeSubdivision.nativeDuffyCube_boundary`
* `Hurewicz.NativeSubdivision.nativeClass_commonOrderedDuffy`
* `Hurewicz.NativeSubdivision.NativeChamberChart.commonOrderedDuffy`
-/

open Set Function Topology

noncomputable section

/-! ### Prefix products and Duffy maps -/

/-- The product of the first `k` coordinates of `u`: `∏ i.val < k, u i`. -/
def Hurewicz.NativeSubdivision.prefixProduct {n : ℕ} (u : NativeCube (Fin n)) (k : ℕ) :
    (unitInterval) :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), u i

/-- The prefix product at `k = 0` is `1`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.prefixProduct_zero {n : ℕ} (u : NativeCube (Fin n)) :
    prefixProduct u 0 = 1 := by simp [prefixProduct]

/-- The prefix product at `k+1` is the prefix product at `k` times `u k`. -/
theorem Hurewicz.NativeSubdivision.prefixProduct_succ {n : ℕ} (u : NativeCube (Fin n))
    (k : ℕ) (hk : k < n) : prefixProduct u (k + 1) = prefixProduct u k * u ⟨k, hk⟩ := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert (by simp)]
  exact mul_comm _ _

/-- If a coordinate `u i = 0` with `i.val < k`, the prefix product at `k` is `0`. -/
theorem Hurewicz.NativeSubdivision.prefixProduct_eq_zero_of_coordinate {n : ℕ}
    (u : NativeCube (Fin n)) (k : ℕ) (i : Fin n) (hik : i.val < k) (hi : u i = 0) :
    prefixProduct u k = 0 :=
  Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩) hi

/-- If `u k = 1`, the prefix product at `k+1` equals that at `k`. -/
theorem Hurewicz.NativeSubdivision.prefixProduct_succ_of_one {n : ℕ}
    (u : NativeCube (Fin n)) (i : Fin n) (hi : u i = 1) :
    prefixProduct u (i.val + 1) = prefixProduct u i.val := by
  rw [prefixProduct_succ u i.val i.isLt, hi, mul_one]

/-- The prefix product is continuous on the cube. -/
theorem Hurewicz.NativeSubdivision.continuous_prefixProduct (n k : ℕ) :
    Continuous (fun u : NativeCube (Fin n) => prefixProduct u k) := by
  unfold prefixProduct
  generalize Finset.univ.filter (fun i : Fin n => i.val < k) = s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (continuous_const : Continuous (fun _ : NativeCube (Fin n) => (1 : (unitInterval))))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact
      ((continuous_subtype_val.comp (continuous_apply i)).mul
            (continuous_subtype_val.comp ih)).subtype_mk
        _

/-- The canonical Duffy cube: `u ↦ i ↦ prefixProduct u (i+1)`, the cumulative
product of coordinates. -/
def Hurewicz.NativeSubdivision.nativeDuffyCubeCanonical (n : ℕ) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := prefixProduct u (i.val + 1)
  continuous_toFun := continuous_pi fun i => continuous_prefixProduct n (i.val + 1)

/-- The `e`-th Duffy cube: `u ↦ i ↦ prefixProduct u ((e.symm i)+1)`, the cumulative
product in the `e`-order. -/
def Hurewicz.NativeSubdivision.nativeDuffyCube {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := nativeDuffyCubeCanonical n u (e.symm i)
  continuous_toFun :=
    continuous_pi fun i =>
      (continuous_apply (e.symm i)).comp (nativeDuffyCubeCanonical n).continuous

/-- `nativeDuffyCube e u i = prefixProduct u ((e.symm i).val + 1)`. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u i = prefixProduct u ((e.symm i).val + 1) :=
  rfl

/-- The `e i`-th coordinate of `nativeDuffyCube e u` is `prefixProduct u (i+1)`. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u (e i) = prefixProduct u (i.val + 1) := by simp [nativeDuffyCube_apply]

/-- If a coordinate `u j = 0` with `j` in the `e`-prefix of `i`, the `i`-th Duffy
coordinate is `0`. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeDuffyCube e u (e j) = 0 := by
  rw [nativeDuffyCube_coordinate]
  exact prefixProduct_eq_zero_of_coordinate u _ i (by omega) hi

/-- If an `e`-prefix coordinate is `0`, the Duffy coordinate is `0`. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeDuffyCube e u (e 0) = 1 := by
  rw [nativeDuffyCube_coordinate, prefixProduct_succ_of_one u 0 hu]
  exact prefixProduct_zero u

/-- If an `e`-prefix coordinate is `1`, adjacent Duffy coordinates coincide. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) : nativeDuffyCube e u (e i.castSucc) = nativeDuffyCube e u (e i.succ) := by
  rw [nativeDuffyCube_coordinate, nativeDuffyCube_coordinate,
    prefixProduct_succ_of_one u i.succ hi]
  rfl

/-- The Duffy cube sends the cube boundary into the boundary-or-diagonal strata. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin n) ∨
      ∃ i j : Fin n, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact Or.inl ⟨e i, Or.inl (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)⟩
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero => exact Or.inl ⟨e 0, Or.inr (nativeDuffyCube_coordinate_zero_of_one e u hi)⟩
      | succ i =>
        exact
          Or.inr
            ⟨e i.castSucc, e i.succ,
              e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this),
              nativeDuffyCube_adjacent_of_one e u i hi⟩

/-- For internally based `p`, the pullback along the Duffy cube is based. -/
theorem Hurewicz.NativeSubdivision.nativeDuffyCube_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

/-- The based cube obtained by pulling `p` back along the `e`-th Duffy cube. -/
def Hurewicz.NativeSubdivision.nativeDuffyCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

/-- The ordered Duffy map of `e`: the Duffy cube precomposed with the coordinate
permutation `permuteCubeCoordinates e`. -/
def Hurewicz.NativeSubdivision.nativeOrderedDuffyMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

/-- The `i`-th coordinate of `nativeOrderedDuffyMap e u` is the prefix product of
the `e`-ordered coordinates. -/
@[simp]
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeOrderedDuffyMap e u (e i) = prefixProduct (fun k => u (e k)) (i.val + 1) := by
  exact nativeDuffyCube_coordinate e (permuteCubeCoordinates e u) i

/-- If an ordered coordinate of `u` is `0`, the corresponding Duffy coordinate is
`0`. -/
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j)
    (hi : u (e i) = 0) : nativeOrderedDuffyMap e u (e j) = 0 :=
  nativeDuffyCube_coordinate_eq_zero e (permuteCubeCoordinates e u) i j hij hi

/-- The ordered Duffy map sends the last-chamber face to the constant `0`. -/
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (_hi : i.val + 1 = n)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = 0 :=
  nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu

/-- The ordered Duffy map respects adjacent faces at `0`. -/
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i.val + 1 = j.val)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu,
    nativeOrderedDuffyMap_coordinate_eq_zero e u i j (by omega) hu]

/-- The ordered Duffy map sends the first-chamber face to the constant `1`. -/
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (hi : i.val = 0)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = 1 := by
  rw [nativeOrderedDuffyMap_coordinate, prefixProduct_succ_of_one (fun k => u (e k)) i hu, hi,
    prefixProduct_zero]

/-- The ordered Duffy map respects adjacent faces at `1`. -/
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hji : j.val + 1 = i.val)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate, nativeOrderedDuffyMap_coordinate,
    prefixProduct_succ_of_one (fun k => u (e k)) i hu, hji]

/-- For internally based `p`, the pullback along the ordered Duffy map is based. -/
theorem Hurewicz.NativeSubdivision.nativeOrderedDuffyMap_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeOrderedDuffyMap e u) = x :=
  nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)

/-- The boundary-relative homotopy between the pullback of `p` along `f` and the
permuted Duffy pullback, given a common flat on the boundary. -/
def Hurewicz.NativeSubdivision.nativeCubeOrderedDuffyHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (nativeOrderedDuffyMap_based p hp e) hfg

/-- The native class of a boundary-flat-common pullback equals the oriented class
of the `e`-th cell simplex. -/
theorem Hurewicz.NativeSubdivision.nativeClass_commonOrderedDuffy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass (nativeDuffyCubeLoop p hp e) := by
  calc
    nativeClass (nativeCubePullbackLoop p f hf) =
        nativeClass (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e) :=
      nativeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp e f hf hfg⟩
    _ = _ := permuteCubeLoop_additiveClass _ e

/-- The ordered Duffy map as a `NativeChamberChart e`. -/
def Hurewicz.NativeSubdivision.orderedDuffyChart {n : ℕ} (e : Equiv.Perm (Fin n)) :
    NativeChamberChart e
    where
  toContinuousMap := nativeOrderedDuffyMap e
  zero_last := nativeOrderedDuffyMap_zero_last e
  zero_adjacent := nativeOrderedDuffyMap_zero_adjacent e
  one_first := nativeOrderedDuffyMap_one_first e
  one_adjacent := nativeOrderedDuffyMap_one_adjacent e

/-- Any `e`-chamber chart lands on the same flat as the ordered Duffy map on the
boundary. -/
theorem Hurewicz.NativeSubdivision.NativeChamberChart.commonOrderedDuffy {n : ℕ}
    {e : Equiv.Perm (Fin n)} (chart : Hurewicz.NativeSubdivision.NativeChamberChart e)
    (u : Hurewicz.NativeSubdivision.NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    Hurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (Hurewicz.NativeSubdivision.nativeOrderedDuffyMap e u) :=
  chart.sameFlat (Hurewicz.NativeSubdivision.orderedDuffyChart e) u hu
