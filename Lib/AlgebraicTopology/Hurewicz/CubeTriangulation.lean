/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
/-!
# The Freudenthal–Kuhn triangulation of a cube

For each permutation `e : Equiv.Perm (Fin n)`, `Hurewicz.CubeTriangulation.cubeSimplex e :
C(SingularChains.Simplex n, CubeN n)` is the affine map onto the ordered chamber
`u (e 0) ≥ u (e 1) ≥ ⋯`; `Hurewicz.CubeTriangulation.exists_cubeSimplex` shows the
chambers cover the cube, and the boundary lemmas identify the shared faces where the
signed sum over permutations cancels.

## Outline of the construction

1. `cubeAffineSimplex` maps a simplex affinely to a list of cube vertices; the Kuhn
   vertices `cubeVertex e k` place `1` on coordinates `i` with `(e.symm i).val < k`.
2. The cumulative coordinates `cubeExtendedCoordinates` and their differences
   `cubeBarycentric` invert the construction on each ordered chamber
   `cubeOrderedRegion e` (`cubeSimplexInverse`).
3. Adjacent-transposition signs: swapping two coordinates changes the orientation
   `cubeOrientation` and identifies shared faces (`cubeSimplex_face_swap`).
4. Every cube point is covered by the chamber of its sorting permutation
   `exists_cubeSimplex`, and overlaps of two chambers factor through the shared face
   (`cubeSimplex_overlap_preimage`), giving signed boundary cancellation.

## Main definitions and results

* `Hurewicz.CubeTriangulation.cubeSimplex`, `cubeOrientation`: the signed Kuhn cells.
* `Hurewicz.CubeTriangulation.cubeSimplexInverse`, `exists_cubeSimplex`: the chamber
  inverse and covering.
* `Hurewicz.CubeTriangulation.cubeSimplex_face_swap`,
  `cubeSimplex_overlap_preimage`: the face identities used in boundary cancellation.

## References

* The construction follows `Lib/docs/C.md`, §3; the simplicial-chain conventions are
  those of [Allen Hatcher, *Algebraic Topology*][hatcher02], §2.1.

## Tags

triangulation, cube, simplex, Kuhn, boundary cancellation
-/


set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

/-- The unit `n`-cube `Fin n → unitInterval`. -/
abbrev Hurewicz.CubeTriangulation.CubeN (n : ℕ) :=
  Fin n → (unitInterval)

/-! ### Affine simplices in the cube -/

/-- The affine simplex in the cube with vertices `v : Fin (m + 1) → CubeN n`:
barycentric coordinates `s` are sent to `∑ j, s j • v j` coordinatewise. -/
def Hurewicz.CubeTriangulation.cubeAffineSimplex {m n : ℕ} (v : Fin (m + 1) → CubeN n) :
    C(SingularChains.Simplex m, CubeN n)
    where
  toFun s
    i :=
    ⟨∑ j, s j * (v j i : ℝ), by
      constructor
      · exact Finset.sum_nonneg fun j _ => mul_nonneg (stdSimplex.zero_le s j) (v j i).property.1
      · calc
          ∑ j, s j * (v j i : ℝ) ≤ ∑ j, s j * 1 :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (v j i).property.2 (stdSimplex.zero_le s j)
          _ = 1 := by simp only [mul_one, stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact
      continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- The `i`-th coordinate of `cubeAffineSimplex v s` is `∑ j, s j * v j i`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeAffineSimplex_coordinate {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (s : SingularChains.Simplex m) (i : Fin n) :
    (cubeAffineSimplex v s i : ℝ) = ∑ j, s j * (v j i : ℝ) :=
  rfl

/-- The `j`-th vertex of the affine cube simplex is `v j`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeAffineSimplex_vertex {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (j : Fin (m + 1)) :
    cubeAffineSimplex v (SingularMayerVietoris.stdVertices m j) = v j := by
  funext i
  apply Subtype.ext
  simp [cubeAffineSimplex_coordinate, SingularMayerVietoris.stdVertices, stdSimplex.vertex,
    Pi.single_apply]

/-- Restricting `cubeAffineSimplex v` to the `i`-th face gives the affine simplex of
the vertices with `v i` dropped. -/
theorem Hurewicz.CubeTriangulation.cubeAffineSimplex_face {m n : ℕ}
    (v : Fin (m + 2) → CubeN n) (i : Fin (m + 2)) :
    (cubeAffineSimplex v).comp (SingularChains.simplexFace m i) =
      cubeAffineSimplex (fun j => v (i.succAbove j)) := by
  ext s k
  change
    (∑ j : Fin (m + 2), SingularChains.simplexFace m i s j * (v j k : ℝ)) =
      ∑ j : Fin (m + 1), s j * (v (i.succAbove j) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [SingularChains.simplexFace_apply_self, MulZeroClass.zero_mul,
    SingularChains.simplexFace_apply_succAbove, zero_add]

/-- If all vertices agree on coordinate `i`, the affine simplex is constant on that
coordinate. -/
theorem Hurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate {m n : ℕ}
    (v : Fin (m + 1) → CubeN n) (i : Fin n) (c : (unitInterval)) (h : ∀ j, v j i = c)
    (s : SingularChains.Simplex m) : cubeAffineSimplex v s i = c := by
  apply Subtype.ext
  simp only [cubeAffineSimplex_coordinate, h, ← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

/-! ### The Kuhn simplex of a permutation -/

/-- The `k`-th vertex of the `e`-th Kuhn simplex: coordinate `i` is `1` if
`(e.symm i).val < k` and `0` otherwise — the first `k` coordinates in the
`e`-ordering are set to `1`. -/
def Hurewicz.CubeTriangulation.cubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) : CubeN n := fun i => if (e.symm i).val < k.val then 1 else 0

/-- The `e`-th Freudenthal–Kuhn simplex of the cube: the affine simplex on the
vertices `cubeVertex e 0, …, cubeVertex e n`, covering the chamber where the
`e`-ordered coordinates are nonincreasing. -/
def Hurewicz.CubeTriangulation.cubeSimplex {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(SingularChains.Simplex n, CubeN n) :=
  cubeAffineSimplex (cubeVertex e)

/-- The `(e i)`-th coordinate of `cubeSimplex e s` is the tail sum of the barycentric
coordinates `s k` over indices `k` with `i.val < k.val` (strictly after `i`). -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_coordinate {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : SingularChains.Simplex n) (i : Fin n) :
    (cubeSimplex e s (e i) : ℝ) = ∑ k : Fin (n + 1), if i.val < k.val then s k else 0 := by
  simp only [cubeSimplex, cubeAffineSimplex_coordinate, cubeVertex, Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

/-- On `cubeSimplex e s`, the `e`-ordered coordinates are nonincreasing. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_antitone {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : SingularChains.Simplex n) : Antitone (fun i => cubeSimplex e s (e i)) := by
  intro i j hij
  change (cubeSimplex e s (e j) : ℝ) ≤ (cubeSimplex e s (e i) : ℝ)
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate]
  apply Finset.sum_le_sum
  intro k _
  by_cases hj : j.val < k.val
  · have hi : i.val < k.val := lt_of_le_of_lt hij hj
    simp only [if_pos hj, if_pos hi, le_refl]
  · simp only [if_neg hj]
    split_ifs
    · exact stdSimplex.zero_le s k
    · exact le_refl 0

/-- The sign `±1` of a permutation `e`, orienting the `e`-th Kuhn cell. -/
def Hurewicz.CubeTriangulation.cubeOrientation {n : ℕ} (e : Equiv.Perm (Fin n)) : ℤ :=
  Equiv.Perm.sign e

/-- The identity permutation has orientation `1`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeOrientation_refl (n : ℕ) :
    cubeOrientation (Equiv.refl (Fin n)) = 1 := by simp [cubeOrientation]

/-- Precomposing with a transposition flips the orientation sign. -/
theorem Hurewicz.CubeTriangulation.cubeOrientation_swap {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (h : i ≠ j) : cubeOrientation ((Equiv.swap i j).trans e) = -cubeOrientation e :=
  by simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h]

/-- The chamber orientations sum to zero: transposing a fixed pair of coordinates reverses
the sign, so the permutation signs cancel in pairs. -/
theorem Hurewicz.CubeTriangulation.cubeOrientation_sum (n : ℕ) :
    ∑ e : Equiv.Perm (Fin (n + 2)), Hurewicz.CubeTriangulation.cubeOrientation e = 0 := by
  have hij : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
  have h :=
    Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (n + 2)) 1))
      (Hurewicz.CubeTriangulation.cubeOrientation (n := n + 2))
  change
    (∑ e : Equiv.Perm (Fin (n + 2)),
        Hurewicz.CubeTriangulation.cubeOrientation ((Equiv.swap 0 1).trans e)) =
      ∑ e : Equiv.Perm (Fin (n + 2)), Hurewicz.CubeTriangulation.cubeOrientation e at h
  simp_rw [Hurewicz.CubeTriangulation.cubeOrientation_swap _ hij] at h
  rw [Finset.sum_neg_distrib] at h
  omega

/-! ### Sorting permutations -/

/-- `u` is sorted by `e` when `u (e 0) ≥ u (e 1) ≥ ⋯`, i.e. `u ∘ e` is antitone. -/
abbrev Hurewicz.CubeTriangulation.SortedCoordinates {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin n → α) (e : Equiv.Perm (Fin n)) : Prop :=
  Antitone (fun i => u (e i))

/-- A permutation sorting the coordinates of `u` in nonincreasing order, chosen via
`Equiv.Perm` sorting of the list of values. -/
def Hurewicz.CubeTriangulation.sortedPermutation {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin n → α) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (u i))

/-- `sortedPermutation u` indeed sorts the coordinates of `u`. -/
theorem Hurewicz.CubeTriangulation.sortedPermutation_sorted {n : ℕ} {α : Type*}
    [LinearOrder α] (u : Fin n → α) : SortedCoordinates u (sortedPermutation u) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (u i))

/-- Every tuple `u : Fin n → α` admits a permutation sorting its coordinates. -/
theorem Hurewicz.CubeTriangulation.exists_sortedPermutation {n : ℕ} {α : Type*}
    [LinearOrder α] (u : Fin n → α) : ∃ e : Equiv.Perm (Fin n), SortedCoordinates u e :=
  ⟨sortedPermutation u, sortedPermutation_sorted u⟩

/-- Two permutations sorting the same tuple produce the same ordered list of values. -/
theorem Hurewicz.CubeTriangulation.sorted_values_eq {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin n → α) {e f : Equiv.Perm (Fin n)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : ∀ i : Fin n, u (e i) = u (f i) :=
  congrFun (Tuple.unique_antitone he hf)

/-! ### Cumulative and barycentric coordinates -/

/-- Telescoping sum: `∑ i : Fin n, (a i.castSucc - a i.succ) = a 0 - a (Fin.last n)`. -/
theorem Hurewicz.CubeTriangulation.sum_fin_differences {n : ℕ} (a : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (a i.castSucc - a i.succ) = a 0 - a (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ a
  have h₁ := Fin.sum_univ_castSucc a
  linarith

/-- The tail of the telescoping sum over `k ≥ i` equals `a i.castSucc - a (Fin.last n)`. -/
theorem Hurewicz.CubeTriangulation.sum_fin_differences_tail (n : ℕ) (a : Fin (n + 1) → ℝ)
    (i : Fin n) :
    ∑ k : Fin n, (if i.val ≤ k.val then a k.castSucc - a k.succ else 0) =
      a i.castSucc - a (Fin.last n) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.val_zero, Nat.zero_le, if_pos, Fin.castSucc_zero] using
        sum_fin_differences a
    | succ i =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_one_le_iff, Nat.not_lt_zero, if_false,
        Nat.lt_succ_iff, zero_add, Fin.castSucc_succ]
      simpa only [Fin.succ_last] using ih (fun k => a k.succ) i

/-- The extended `e`-ordered coordinates of a cube point: `1`, then the coordinates
`u (e i)` in the `e`-order, then `0` — an antitone `Fin (n + 2) → ℝ` on the
ordered chamber. -/
def Hurewicz.CubeTriangulation.cubeExtendedCoordinates {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) : Fin (n + 2) → ℝ :=
  Fin.cons 1 (Fin.snoc (fun i => (u (e i) : ℝ)) 0)

/-- The first extended coordinate is `1`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeExtendedCoordinates_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) : cubeExtendedCoordinates e u 0 = 1 := by
  simp only [cubeExtendedCoordinates, Fin.cons_zero]

/-- The last extended coordinate is `0`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeExtendedCoordinates_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) : cubeExtendedCoordinates e u (Fin.last (n + 1)) = 0 :=
  by
  change cubeExtendedCoordinates e u (Fin.last n).succ = 0
  unfold cubeExtendedCoordinates
  simp only [Fin.cons_succ, Fin.snoc_last]

/-- The inner extended coordinate at `i.succ.castSucc` is `u (e i)`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeExtendedCoordinates_inner {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin n) :
    cubeExtendedCoordinates e u i.castSucc.succ = (u (e i) : ℝ) := by
  simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_castSucc]

/-- Every extended coordinate is nonnegative. -/
theorem Hurewicz.CubeTriangulation.cubeExtendedCoordinates_nonneg {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin (n + 2)) :
    0 ≤ cubeExtendedCoordinates e u i := by
  cases i using Fin.cases with
  | zero => simp only [cubeExtendedCoordinates_zero, zero_le_one]
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_last, le_refl]
    | cast i => simpa only [cubeExtendedCoordinates_inner] using (u (e i)).property.1

/-- Every extended coordinate is at most `1`. -/
theorem Hurewicz.CubeTriangulation.cubeExtendedCoordinates_le_one {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (i : Fin (n + 2)) :
    cubeExtendedCoordinates e u i ≤ 1 := by
  cases i using Fin.cases with
  | zero => simp only [cubeExtendedCoordinates_zero, le_refl]
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp only [cubeExtendedCoordinates, Fin.cons_succ, Fin.snoc_last, zero_le_one]
    | cast i => simpa only [cubeExtendedCoordinates_inner] using (u (e i)).property.2

/-- On the `e`-ordered chamber the extended coordinates are antitone. -/
theorem Hurewicz.CubeTriangulation.cubeExtendedCoordinates_antitone {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : CubeN n) (h : SortedCoordinates u e) :
    Antitone (cubeExtendedCoordinates e u) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => exact cubeExtendedCoordinates_le_one e u j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have hh : i.val + 1 ≤ 0 := (Fin.le_iff_val_le_val).mp hij
      omega
    | succ j =>
      cases j using Fin.lastCases with
      | last =>
        simpa only [Fin.succ_last, cubeExtendedCoordinates_last] using
          cubeExtendedCoordinates_nonneg e u i.succ
      | cast j =>
        cases i using Fin.lastCases with
        | last =>
          have hj : j.val < n := j.isLt
          have hh := (Fin.le_iff_val_le_val).mp hij
          simp only [Fin.val_succ, Fin.val_last, Fin.val_castSucc] at hh
          omega
        | cast
          i =>
          have hh : i ≤ j := by
            simpa only [Fin.succ_le_succ_iff, Fin.castSucc_le_castSucc_iff] using hij
          have hreal : (u (e j) : ℝ) ≤ (u (e i) : ℝ) := h hh
          simpa only [cubeExtendedCoordinates_inner] using hreal

/-- The barycentric coordinates of a cube point in the `e`-th Kuhn cell: consecutive
differences of the extended coordinates, `cubeExtendedCoordinates i -
cubeExtendedCoordinates (i+1)`. -/
def Hurewicz.CubeTriangulation.cubeBarycentric {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) : Fin (n + 1) → ℝ := fun i =>
  cubeExtendedCoordinates e u i.castSucc - cubeExtendedCoordinates e u i.succ

/-- The first barycentric coordinate is `1 - u (e 0)`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeBarycentric_zero {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) :
    cubeBarycentric e u 0 = 1 - (u (e 0) : ℝ) := by
  simp only [cubeBarycentric, Fin.castSucc_zero, cubeExtendedCoordinates, Fin.cons_zero,
    Fin.cons_succ, Fin.snoc_apply_zero]

/-- The last barycentric coordinate is `u (e (Fin.last n))`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeBarycentric_last {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) :
    cubeBarycentric e u (Fin.last (n + 1)) = (u (e (Fin.last n)) : ℝ) := by
  change
    cubeExtendedCoordinates e u (Fin.last n).castSucc.succ -
        cubeExtendedCoordinates e u (Fin.last (n + 2)) =
      _
  simp only [cubeExtendedCoordinates_inner, cubeExtendedCoordinates_last, sub_zero]

/-- The `i.succ.castSucc`-th barycentric coordinate is `u (e i.castSucc) - u (e i.succ)`. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeBarycentric_inner {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : CubeN (n + 1)) (i : Fin n) :
    cubeBarycentric e u i.succ.castSucc = (u (e i.castSucc) : ℝ) - (u (e i.succ) : ℝ) := by
  change
    cubeExtendedCoordinates e u i.castSucc.castSucc.succ -
        cubeExtendedCoordinates e u i.succ.castSucc.succ =
      _
  simp only [cubeExtendedCoordinates_inner]

/-- On the `e`-ordered chamber the barycentric coordinates are nonnegative. -/
theorem Hurewicz.CubeTriangulation.cubeBarycentric_nonneg {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) (h : SortedCoordinates u e) (i : Fin (n + 1)) : 0 ≤ cubeBarycentric e u i :=
  sub_nonneg.mpr (cubeExtendedCoordinates_antitone e u h (Nat.le_succ i.val))

/-- The barycentric coordinates of a cube point sum to `1`. -/
theorem Hurewicz.CubeTriangulation.cubeBarycentric_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) : ∑ i, cubeBarycentric e u i = 1 := by
  unfold cubeBarycentric
  rw [sum_fin_differences]
  simp only [cubeExtendedCoordinates_zero, cubeExtendedCoordinates_last, sub_zero]

/-- The tail sum of the barycentric coordinates from index `i.succ` onward equals the
corresponding extended coordinate `u (e i)`. -/
theorem Hurewicz.CubeTriangulation.cubeBarycentric_tail {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : CubeN n) (i : Fin n) :
    ∑ k : Fin (n + 1), (if i.val < k.val then cubeBarycentric e u k else 0) = (u (e i) : ℝ) := by
  have h := sum_fin_differences_tail (n + 1) (cubeExtendedCoordinates e u) i.succ
  simpa only [Fin.val_succ, Nat.succ_le_iff, cubeBarycentric, Fin.castSucc_succ,
    cubeExtendedCoordinates_inner, cubeExtendedCoordinates_last, sub_zero] using h

/-- The `e 0`-coordinate of `cubeSimplex e s` is `1 - s 0` (the tail sum from index `0`). -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_coordinate_zero {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex (n + 1)) :
    (cubeSimplex e s (e 0) : ℝ) = 1 - s 0 := by
  rw [cubeSimplex_coordinate, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.lt_irrefl, if_false, Fin.val_succ, Nat.zero_lt_succ, if_true,
    zero_add]
  have hs := stdSimplex.sum_eq_one s
  rw [Fin.sum_univ_succ] at hs
  linarith

/-- The `e (Fin.last n)`-coordinate of `cubeSimplex e s` is `s (Fin.last (n+1))`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_coordinate_last {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex (n + 1)) :
    (cubeSimplex e s (e (Fin.last n)) : ℝ) = s (Fin.last (n + 1)) := by
  rw [cubeSimplex_coordinate, Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc, Nat.lt_succ_self, if_true]
  have hz : (∑ k : Fin (n + 1), if n < k.val then s k.castSucc else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (Nat.not_lt.mpr (Nat.le_of_lt_succ k.isLt))
  rw [hz, zero_add]

/-- The difference of adjacent `e`-ordered coordinates of `cubeSimplex e s` is the
barycentric coordinate `s i.succ.castSucc`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_adjacent_difference {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex (n + 1)) (i : Fin n) :
    (cubeSimplex e s (e i.castSucc) : ℝ) - (cubeSimplex e s (e i.succ) : ℝ) = s i.succ.castSucc :=
  by
  rw [cubeSimplex_coordinate, cubeSimplex_coordinate, ← Finset.sum_sub_distrib]
  calc
    ∑ k : Fin (n + 2),
          ((if i.castSucc.val < k.val then s k else 0) -
            (if i.succ.val < k.val then s k else 0)) =
        ∑ k : Fin (n + 2), if k = i.succ.castSucc then s k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i.succ.castSucc
      · subst k
        simp
      · have hv : k.val ≠ i.val + 1 := by
          intro h
          apply hk
          exact Fin.ext h
        by_cases h : i.val < k.val
        · have h' : i.val + 1 < k.val := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, if_pos h, if_pos h', if_neg hk, sub_self]
        · have h' : ¬i.val + 1 < k.val := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, if_neg h, if_neg h', if_neg hk, sub_zero]
    _ = s i.succ.castSucc := by simp

/-! ### The sorted inverse and the covering -/

/-- The `e`-th ordered chamber of the cube: the closed set where the `e`-ordered
coordinates are nonincreasing. -/
def Hurewicz.CubeTriangulation.cubeOrderedRegion {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Set (CubeN n) :=
  {u | SortedCoordinates u e}

/-- The `i`-th coordinate projection of the cube is continuous. -/
theorem Hurewicz.CubeTriangulation.continuous_cubeCoordinate {n : ℕ} (i : Fin n) :
    Continuous (fun u : CubeN n => (u i : ℝ)) :=
  continuous_subtype_val.comp (continuous_apply i)

/-- Each extended coordinate is continuous on the cube. -/
theorem Hurewicz.CubeTriangulation.continuous_cubeExtendedCoordinates {n : ℕ}
    (e : Equiv.Perm (Fin n)) (i : Fin (n + 2)) :
    Continuous (fun u : CubeN n => cubeExtendedCoordinates e u i) := by
  cases i using Fin.cases with
  | zero =>
    simpa only [cubeExtendedCoordinates_zero] using
      (continuous_const : Continuous (fun _ : CubeN n => (1 : ℝ)))
  | succ i =>
    cases i using Fin.lastCases with
    | last =>
      simpa only [Fin.succ_last, cubeExtendedCoordinates_last] using
        (continuous_const : Continuous (fun _ : CubeN n => (0 : ℝ)))
    | cast i => simpa only [cubeExtendedCoordinates_inner] using continuous_cubeCoordinate (e i)

/-- Each barycentric coordinate is continuous on the cube. -/
theorem Hurewicz.CubeTriangulation.continuous_cubeBarycentric {n : ℕ}
    (e : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    Continuous (fun u : CubeN n => cubeBarycentric e u i) :=
  (continuous_cubeExtendedCoordinates e i.castSucc).sub
    (continuous_cubeExtendedCoordinates e i.succ)

/-- The inverse of `cubeSimplex e` on its ordered chamber: a cube point of
`cubeOrderedRegion e` is sent to its barycentric coordinates `cubeBarycentric e u`. -/
def Hurewicz.CubeTriangulation.cubeSimplexInverse {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(↥(cubeOrderedRegion e), SingularChains.Simplex n)
    where
  toFun
    u :=
    ⟨cubeBarycentric e u.val,
      ⟨cubeBarycentric_nonneg e u.val u.property, cubeBarycentric_sum e u.val⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_cubeBarycentric e i).comp continuous_subtype_val

/-- The image of `cubeSimplex e` is `e`-sorted: its `e`-ordered coordinates are
nonincreasing. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_sorted {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : SingularChains.Simplex n) : SortedCoordinates (cubeSimplex e s) e :=
  cubeSimplex_antitone e s

/-- `cubeSimplexInverse` is a right inverse of `cubeSimplex e` on the ordered chamber. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeSimplex_inverse {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : ↥(cubeOrderedRegion e)) : cubeSimplex e (cubeSimplexInverse e u) = u.val := by
  funext k
  obtain ⟨i, rfl⟩ := e.surjective k
  apply Subtype.ext
  rw [cubeSimplex_coordinate]
  exact cubeBarycentric_tail e u.val i

/-- `cubeSimplexInverse` is a left inverse of `cubeSimplex e`: it recovers the simplex
point. -/
@[simp]
theorem Hurewicz.CubeTriangulation.cubeSimplexInverse_simplex {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n) :
    cubeSimplexInverse e ⟨cubeSimplex e s, cubeSimplex_sorted e s⟩ = s := by
  cases n with
  | zero =>
    exact
      (SingularChains.simplexZero_eq_vertex _).trans (SingularChains.simplexZero_eq_vertex s).symm
  | succ n =>
    apply Subtype.ext
    funext i
    change cubeBarycentric e (cubeSimplex e s) i = s i
    cases i using Fin.cases with
    | zero =>
      rw [cubeBarycentric_zero, cubeSimplex_coordinate_zero]
      ring
    | succ i =>
      cases i using Fin.lastCases with
      | last =>
        simpa only [Fin.succ_last, cubeBarycentric_last] using cubeSimplex_coordinate_last e s
      | cast i =>
        simpa only [← Fin.castSucc_succ, cubeBarycentric_inner] using
          cubeSimplex_adjacent_difference e s i

/-- `cubeSimplex e` is injective. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_injective {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Function.Injective (cubeSimplex e) := by
  intro s t h
  have hh :
    (⟨cubeSimplex e s, cubeSimplex_sorted e s⟩ : ↥(cubeOrderedRegion e)) =
      ⟨cubeSimplex e t, cubeSimplex_sorted e t⟩ :=
    Subtype.ext h
  simpa only [cubeSimplexInverse_simplex] using congrArg (cubeSimplexInverse e) hh

/-! ### Boundary faces -/

/-- For `k` not equal to the adjacent-transposition indices, the `k`-th Kuhn vertex is
unchanged by the swap `Equiv.swap i.castSucc i.succ`. -/
theorem Hurewicz.CubeTriangulation.cubeVertex_swap_of_ne {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (k : Fin (n + 2)) (hk : k ≠ i.succ.castSucc) :
    cubeVertex e k = cubeVertex ((Equiv.swap i.castSucc i.succ).trans e) k := by
  funext coord
  change
    (if (e.symm coord).val < k.val then (1 : (unitInterval)) else 0) =
      if ((Equiv.swap i.castSucc i.succ) (e.symm coord)).val < k.val then 1 else 0
  have hk' : k.val ≠ i.val + 1 := by
    intro h
    exact hk (Fin.ext h)
  by_cases h₀ : e.symm coord = i.castSucc
  · rw [h₀, Equiv.swap_apply_left]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h : i.val < k.val ↔ i.val + 1 < k.val := by omega
    simp only [h]
  by_cases h₁ : e.symm coord = i.succ
  · rw [h₁, Equiv.swap_apply_right]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have h : i.val + 1 < k.val ↔ i.val < k.val := by omega
    simp only [h]
  · rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁]

/-- The `i.succ.castSucc`-th face of the `e`-th Kuhn simplex equals the same face of
the simplex of the pre-swapped permutation `(Equiv.swap i.castSucc i.succ).trans e`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_face_swap {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (cubeSimplex e).comp (SingularChains.simplexFace n i.succ.castSucc) =
      (cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e)).comp
        (SingularChains.simplexFace n i.succ.castSucc) := by
  simp only [cubeSimplex, cubeAffineSimplex_face]
  congr 1
  funext j
  exact cubeVertex_swap_of_ne e i _ (Fin.succAbove_ne _ _)

/-- On the zeroth face, the `e 0`-coordinate of the restricted Kuhn simplex is `1`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_face_zero_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex n) :
    cubeSimplex e (SingularChains.simplexFace n 0 s) (e 0) = 1 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (SingularChains.simplexFace n 0)) s (e 0) = 1
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp [cubeVertex]

/-- On the last face, the `e (Fin.last n)`-coordinate of the restricted Kuhn simplex
is `0`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_face_last_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex n) :
    cubeSimplex e (SingularChains.simplexFace n (Fin.last (n + 1)) s) (e (Fin.last n)) = 0 := by
  change
    ((cubeAffineSimplex (cubeVertex e)).comp (SingularChains.simplexFace n (Fin.last (n + 1)))) s
        (e (Fin.last n)) =
      0
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp only [cubeVertex, Equiv.symm_apply_apply, Fin.succAbove_last, Fin.val_castSucc,
    Fin.val_last]
  exact if_neg (Nat.not_lt.mpr (Nat.le_of_lt_succ j.isLt))

/-- The zeroth face of the `e`-th Kuhn simplex maps into the cube-boundary face
`u (e 0) = 1`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex n) :
    cubeSimplex e (SingularChains.simplexFace n 0 s) ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨e 0, Or.inr (cubeSimplex_face_zero_coordinate e s)⟩

/-- The last face of the `e`-th Kuhn simplex maps into the cube-boundary face
`u (e (Fin.last n)) = 0`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_face_last_boundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex n) :
    cubeSimplex e (SingularChains.simplexFace n (Fin.last (n + 1)) s) ∈
      Cube.boundary (Fin (n + 1)) :=
  ⟨e (Fin.last n), Or.inl (cubeSimplex_face_last_coordinate e s)⟩

/-! ### Covering the cube -/

/-- Every cube point lies in some Kuhn cell: `u = cubeSimplex e s` for the sorting
permutation `e` of `u` and `s = cubeSimplexInverse e u`. -/
theorem Hurewicz.CubeTriangulation.exists_cubeSimplex {n : ℕ} (u : CubeN n) :
    ∃ e : Equiv.Perm (Fin n), ∃ s : SingularChains.Simplex n, cubeSimplex e s = u := by
  obtain ⟨e, he⟩ := exists_sortedPermutation u
  exact ⟨e, cubeSimplexInverse e ⟨u, he⟩, cubeSimplex_inverse e ⟨u, he⟩⟩

/-- The cylinder `id × cubeSimplex e` over the `e`-th Kuhn simplex. -/
def Hurewicz.CubeTriangulation.cubeSimplexCylinder {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C((unitInterval) × SingularChains.Simplex n, (unitInterval) × CubeN n) :=
  (ContinuousMap.id (unitInterval)).prodMap (cubeSimplex e)

/-- The covering map `Σ e, unitInterval × Simplex n → unitInterval × CubeN n` of the
cube cylinder by the disjoint union of Kuhn-cell cylinders. -/
def Hurewicz.CubeTriangulation.cubeCylinderCover (n : ℕ) :
    C((Σ _e : Equiv.Perm (Fin n), (unitInterval) × SingularChains.Simplex n),
      (unitInterval) × CubeN n)
    where
  toFun a := cubeSimplexCylinder a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeSimplexCylinder e).continuous

/-- The Kuhn-cell cylinders cover the cube cylinder. -/
theorem Hurewicz.CubeTriangulation.cubeCylinderCover_surjective (n : ℕ) :
    Function.Surjective (cubeCylinderCover n) := by
  rintro ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  exact ⟨⟨e, (r, s)⟩, rfl⟩

/-- The cylinder covering map is a quotient map. -/
theorem Hurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (cubeCylinderCover n) :=
  Topology.IsQuotientMap.of_surjective_continuous (cubeCylinderCover_surjective n)
    (cubeCylinderCover n).continuous

/-! ### Ties, overlaps, and boundary cancellation -/

/-- A point of a Kuhn simplex lies on the outer cube boundary iff its first or last
barycentric coordinate vanishes. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_mem_boundary_iff {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex (n + 1)) :
    cubeSimplex e s ∈ Cube.boundary (Fin (n + 1)) ↔ s 0 = 0 ∨ s (Fin.last (n + 1)) = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    rcases hi with hi | hi
    · right
      have hlast : (cubeSimplex e s (e (Fin.last n)) : ℝ) ≤ (cubeSimplex e s (e j) : ℝ) :=
        cubeSimplex_antitone e s (Fin.le_last j)
      have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
      change (cubeSimplex e s (e j) : ℝ) = 0 at hr
      rw [cubeSimplex_coordinate_last, hr] at hlast
      exact le_antisymm hlast (stdSimplex.zero_le s (Fin.last (n + 1)))
    · left
      have hfirst : (cubeSimplex e s (e j) : ℝ) ≤ (cubeSimplex e s (e 0) : ℝ) :=
        cubeSimplex_antitone e s (Fin.zero_le j)
      have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
      change (cubeSimplex e s (e j) : ℝ) = 1 at hr
      rw [cubeSimplex_coordinate_zero, hr] at hfirst
      linarith [stdSimplex.zero_le s 0]
  · rintro (hs | hs)
    · refine ⟨e 0, Or.inr ?_⟩
      apply Subtype.ext
      change (cubeSimplex e s (e 0) : ℝ) = 1
      rw [cubeSimplex_coordinate_zero, hs, sub_zero]
    · refine ⟨e (Fin.last n), Or.inl ?_⟩
      apply Subtype.ext
      change (cubeSimplex e s (e (Fin.last n)) : ℝ) = 0
      rw [cubeSimplex_coordinate_last, hs]

/-- If adjacent `e`-ordered coordinates of `cubeSimplex e s` are tied, then `s` lies on
face `i.succ.castSucc` of the simplex. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_tie {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (s : SingularChains.Simplex (n + 1)) (i : Fin n)
    (h : cubeSimplex e s (e i.castSucc) = cubeSimplex e s (e i.succ)) : s i.succ.castSucc = 0 := by
  have hd := cubeSimplex_adjacent_difference e s i
  rw [h, sub_self] at hd
  exact hd.symm

/-- Adjacent `e`-ordered coordinates of `cubeSimplex e s` are tied iff `s` has a
vanishing `i.succ.castSucc`-th barycentric coordinate. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_tie_iff {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex (n + 1)) (i : Fin n) :
    cubeSimplex e s (e i.castSucc) = cubeSimplex e s (e i.succ) ↔ s i.succ.castSucc = 0 := by
  refine ⟨cubeSimplex_tie e s i, ?_⟩
  intro hs
  apply Subtype.ext
  have hd := cubeSimplex_adjacent_difference e s i
  rw [hs] at hd
  exact sub_eq_zero.mp hd

/-- If `e` and `f` both sort `cubeSimplex e s`, then `cubeSimplex e s = cubeSimplex f t`
for the corresponding point `t`. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_eq_of_sorted {n : ℕ}
    (e f : Equiv.Perm (Fin n)) (s : SingularChains.Simplex n)
    (hf : SortedCoordinates (cubeSimplex e s) f) : cubeSimplex f s = cubeSimplex e s := by
  funext k
  obtain ⟨i, rfl⟩ := f.surjective k
  apply Subtype.ext
  calc
    (cubeSimplex f s (f i) : ℝ) = ∑ k : Fin (n + 1), if i.val < k.val then s k else 0 :=
      cubeSimplex_coordinate f s i
    _ = (cubeSimplex e s (e i) : ℝ) := (cubeSimplex_coordinate e s i).symm
    _ = (cubeSimplex e s (f i) : ℝ) :=
      congrArg Subtype.val (sorted_values_eq (cubeSimplex e s) (cubeSimplex_sorted e s) hf i)

/-- Points where two Kuhn cells overlap pull back to simplex points lying on the shared
boundary faces. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_overlap_preimage {n : ℕ}
    (e f : Equiv.Perm (Fin n)) (s t : SingularChains.Simplex n)
    (h : cubeSimplex e s = cubeSimplex f t) : s = t := by
  have hf : SortedCoordinates (cubeSimplex e s) f := by
    rw [h]
    exact cubeSimplex_sorted f t
  exact cubeSimplex_injective f ((cubeSimplex_eq_of_sorted e f s hf).trans h)

/-- If `u (e a) = u (e b)`, precomposing `e` with `swap a b` leaves the values `u ∘ e`
unchanged. -/
theorem Hurewicz.CubeTriangulation.coordinate_swap_of_tie {n : ℕ} {α : Type*}
    {u : Fin n → α} {e : Equiv.Perm (Fin n)} {a b : Fin n} (hab : u (e a) = u (e b)) (i : Fin n) :
    u (((Equiv.swap a b).trans e) i) = u (e i) :=
  Equiv.apply_swap_eq_self (v := fun j => u (e j)) hab i

/-- Swapping two tied sorted coordinates preserves `SortedCoordinates u e`. -/
theorem Hurewicz.CubeTriangulation.sortedCoordinates_swap_of_tie {n : ℕ} {α : Type*}
    [LinearOrder α] {u : Fin n → α} {e : Equiv.Perm (Fin n)} (he : SortedCoordinates u e)
    {a b : Fin n} (hab : u (e a) = u (e b)) : SortedCoordinates u ((Equiv.swap a b).trans e) := by
  intro i j hij
  simpa only [coordinate_swap_of_tie hab] using he hij

private theorem Hurewicz.CubeTriangulation.swap_trans_swap_trans_swap_mo1973_8327 {n : ℕ}
    {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) :
    ((Equiv.swap b c).trans (Equiv.swap a b)).trans (Equiv.swap b c) = Equiv.swap a c := by
  simpa only [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left] using
    Equiv.symm_trans_swap_trans a b (Equiv.swap b c)

private theorem Hurewicz.CubeTriangulation.eq_swap_of_sorted_tie_of_lt_mo1973_8328 {n : ℕ}
    {α : Type*} [LinearOrder α] (u : Fin (n + 1) → α) {A : Type*}
    (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap :
      ∀ e,
        SortedCoordinates u e →
          ∀ i : Fin n,
            u (e i.castSucc) = u (e i.succ) → F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    (b : Fin (n + 1)) :
    ∀ (a : Fin (n + 1)) (e : Equiv.Perm (Fin (n + 1))),
      a < b → SortedCoordinates u e → u (e a) = u (e b) → F e = F ((Equiv.swap a b).trans e) := by
  induction b using Fin.induction with
  | zero =>
    intro a e hab
    exact (Fin.not_lt_zero a hab).elim
  | succ b ih =>
    intro a e hab he ht
    obtain rfl | hlt := (Fin.le_castSucc_iff.mpr hab).eq_or_lt
    · exact hswap e he b ht
    have hmid : u (e b.castSucc) = u (e b.succ) :=
      le_antisymm ((he hlt.le).trans ht.le) (he Fin.castSucc_lt_succ.le)
    have hleft : u (e a) = u (e b.castSucc) := ht.trans hmid.symm
    let e₁ := (Equiv.swap b.castSucc b.succ).trans e
    have h₁ : SortedCoordinates u e₁ := sortedCoordinates_swap_of_tie he hmid
    have hv₁ (i : Fin (n + 1)) : u (e₁ i) = u (e i) := coordinate_swap_of_tie hmid i
    have ht₁ : u (e₁ a) = u (e₁ b.castSucc) := by
      rw [hv₁, hv₁]
      exact hleft
    let e₂ := (Equiv.swap a b.castSucc).trans e₁
    have h₂ : SortedCoordinates u e₂ := sortedCoordinates_swap_of_tie h₁ ht₁
    have hv₂ (i : Fin (n + 1)) : u (e₂ i) = u (e₁ i) := coordinate_swap_of_tie ht₁ i
    have ht₂ : u (e₂ b.castSucc) = u (e₂ b.succ) := by
      rw [hv₂, hv₂, hv₁, hv₁]
      exact hmid
    calc
      F e = F e₁ := hswap e he b hmid
      _ = F e₂ := (ih a e₁ hlt h₁ ht₁)
      _ = F ((Equiv.swap b.castSucc b.succ).trans e₂) := (hswap e₂ h₂ b ht₂)
      _ = F ((Equiv.swap a b.succ).trans e) := by
        apply congrArg F
        dsimp only [e₂, e₁]
        rw [← Equiv.trans_assoc, ← Equiv.trans_assoc,
          swap_trans_swap_trans_swap_mo1973_8327 hlt.ne hab.ne]

/-- If `F` on permutations is invariant under swapping adjacent tied sorted
coordinates, then `F` takes the same value on all sorting permutations of `u`. -/
theorem Hurewicz.CubeTriangulation.eq_swap_of_sorted_tie {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin (n + 1) → α) {A : Type*} (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap :
      ∀ e,
        SortedCoordinates u e →
          ∀ i : Fin n,
            u (e i.castSucc) = u (e i.succ) → F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    {e : Equiv.Perm (Fin (n + 1))} (he : SortedCoordinates u e) (a b : Fin (n + 1))
    (hab : u (e a) = u (e b)) : F e = F ((Equiv.swap a b).trans e) := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact eq_swap_of_sorted_tie_of_lt_mo1973_8328 u F hswap b a e hlt he hab
  · simp
  · simpa only [Equiv.swap_comm b a] using
      eq_swap_of_sorted_tie_of_lt_mo1973_8328 u F hswap a b e hgt he hab.symm

private theorem Hurewicz.CubeTriangulation.label_swap_apply_mo1973_8330 {ι β : Type*}
    [DecidableEq ι] (v : ι → β) {a b : ι} (hab : v a = v b) (z : ι) :
    v (Equiv.swap a b z) = v z := by
  by_cases hza : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  by_cases hzb : z = b
  · subst z
    simpa only [Equiv.swap_apply_right] using hab
  rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

/-- Induction principle: a predicate on permutations holds for all permutations
preserving the value tuple `v` if it holds at `1` and is closed under swaps of
value-equal entries. -/
theorem Hurewicz.CubeTriangulation.valuePreservingPermutation_induction {ι β : Type*}
    [DecidableEq ι] [Finite ι] (v : ι → β) {P : Equiv.Perm ι → Prop} (hone : P 1)
    (hswap :
      ∀ (r : Equiv.Perm ι) (a b : ι),
        v a = v b → (∀ i, v (r i) = v i) → P r → P (Equiv.swap a b * r))
    (r : Equiv.Perm ι) (hr : ∀ i, v (r i) = v i) : P r := by
  classical
  let _ := Fintype.ofFinite ι
  suffices h : ∀ k : ℕ, ∀ q : Equiv.Perm ι, q.support.card = k → (∀ i, v (q i) = v i) → P q from
    h _ r rfl hr
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro q hq hvalues
    by_cases hqone : q = 1
    · simpa only [hqone] using hone
    have hmoved : ∃ a, q a ≠ a := by
      by_contra! hn
      exact hqone (Equiv.ext hn)
    obtain ⟨a, ha⟩ := hmoved
    let q' := Equiv.swap a (q a) * q
    have hlt : q'.support.card < k := by
      rw [← hq]
      exact Equiv.Perm.card_support_swap_mul ha
    have hvalues' : ∀ i, v (q' i) = v i := by
      intro i
      change v (Equiv.swap a (q a) (q i)) = v i
      exact (label_swap_apply_mo1973_8330 v (hvalues a).symm (q i)).trans (hvalues i)
    have hstep :=
      hswap q' a (q a) (hvalues a).symm hvalues' (ih q'.support.card hlt q' rfl hvalues')
    simpa only [q', Equiv.swap_mul_self_mul] using hstep

/-- A function on permutations invariant under swaps of value-equal entries of `v` is
constant on all value-preserving permutations. -/
theorem Hurewicz.CubeTriangulation.eq_of_value_preserving_swaps {ι β : Type*}
    [DecidableEq ι] [Finite ι] (v : ι → β) {A : Type*} (G : Equiv.Perm ι → A)
    (hswap :
      ∀ (r : Equiv.Perm ι),
        (∀ i, v (r i) = v i) → ∀ a b, v a = v b → G r = G (Equiv.swap a b * r))
    (r : Equiv.Perm ι) (hr : ∀ i, v (r i) = v i) : G 1 = G r :=
  valuePreservingPermutation_induction v (P := fun q => G 1 = G q) rfl
    (fun q a b hab hq ih => ih.trans (hswap q hq a b hab)) r hr

/-- If `F` on permutations is invariant under adjacent transpositions of tied sorted
coordinates, then `F` is constant on the sorting permutations of `u`. -/
theorem Hurewicz.CubeTriangulation.eq_of_sorted_adjacent {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin (n + 1) → α) {A : Type*} (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap :
      ∀ e,
        SortedCoordinates u e →
          ∀ i : Fin n,
            u (e i.castSucc) = u (e i.succ) → F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    {e f : Equiv.Perm (Fin (n + 1))} (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    F e = F f := by
  have hr : ∀ i, u (e ((f.trans e.symm) i)) = u (e i) := by
    intro i
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using (sorted_values_eq u he hf i).symm
  have hG : F ((1 : Equiv.Perm (Fin (n + 1))).trans e) = F ((f.trans e.symm).trans e) :=
    eq_of_value_preserving_swaps (fun i => u (e i)) (fun r => F (r.trans e))
      (by
        intro r hvalues a b hab
        have hsorted : SortedCoordinates u (r.trans e) := by
          intro i j hij
          change u (e (r j)) ≤ u (e (r i))
          rw [hvalues, hvalues]
          exact he hij
        have ht : u ((r.trans e) (r.symm a)) = u ((r.trans e) (r.symm b)) := by
          simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hab
        have hh := eq_swap_of_sorted_tie u F hswap hsorted (r.symm a) (r.symm b) ht
        refine hh.trans (congrArg F ?_)
        apply Equiv.ext
        intro i
        change e ((r * Equiv.swap (r.symm a) (r.symm b)) i) = e ((Equiv.swap a b * r) i)
        exact
          congrArg (fun q : Equiv.Perm (Fin (n + 1)) => e (q i))
            (Equiv.swap_mul_eq_mul_swap r a b).symm)
      (f.trans e.symm) hr
  simpa only [Equiv.Perm.one_def, Equiv.refl_trans, Equiv.trans_assoc, Equiv.symm_trans_self,
    Equiv.trans_refl] using hG

/-- If `s` lies on the simplex boundary, then `cubeSimplex e s` lies on the cube
boundary or on a shared chamber face where the boundary sum cancels. -/
theorem Hurewicz.CubeTriangulation.cubeSimplex_simplexBoundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : SingularChains.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    cubeSimplex e s ∈ Cube.boundary (Fin (n + 1)) ∨
      ∃ i j : Fin (n + 1), i ≠ j ∧ cubeSimplex e s i = cubeSimplex e s j := by
  obtain ⟨k, hk⟩ := hs
  cases k using Fin.cases with
  | zero => exact Or.inl ((cubeSimplex_mem_boundary_iff e s).mpr (Or.inl hk))
  | succ k =>
    cases k using Fin.lastCases with
    | last =>
      apply Or.inl
      apply (cubeSimplex_mem_boundary_iff e s).mpr
      exact Or.inr (by simpa only [Fin.succ_last] using hk)
    | cast i =>
      apply Or.inr
      refine ⟨e i.castSucc, e i.succ, ?_, ?_⟩
      · intro h
        have hval := congrArg Fin.val (e.injective h)
        simp only [Fin.val_castSucc, Fin.val_succ] at hval
        omega
      · apply (cubeSimplex_tie_iff e s i).mpr
        simpa only [Fin.castSucc_succ] using hk

end Mathoverflow1973
