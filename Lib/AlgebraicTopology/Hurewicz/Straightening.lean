/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.Degree

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

/-!
# Straightening singular simplices

`Hurewicz.normalizationHomotopy x n hpi` is a coherent family of homotopies of singular
`n`-simplices in a simply connected space `X` with basepoint `x` (where `hpi` records
`Subsingleton (π_ k X x)` in the needed range): at time `0` it is the identity
(`Hurewicz.normalizationHomotopy_zero`) and at time `1` it lands in the based simplices
(`Hurewicz.normalizationHomotopy_endpoint`, `Hurewicz.normalizedSimplex`).

The straightening/normalization tower at general degree: for a simply connected space `X`
with basepoint `x`, a coherent family of homotopies `H k` straightening singular
`k`-simplices. The tower is built by recursion: each storey extends the two previous ones over
the next dimension by the homotopy extension property (`extendCoherentSimplexHomotopy`), and
the top storey of each level straightens the simplices whose boundary is already at the
basepoint (`Hurewicz.simplexStraighteningHomotopy`, using `Subsingleton (π_ k X x)`).

The recursion is bundled in `Hurewicz.TowerPair` (two consecutive storeys with their
basepoint and face compatibilities), since the extension step consumes those properties.

## Outline of the construction

1. The edge tower `Hurewicz.edgeTower` and the vertex-then-edge composite
   `Hurewicz.vertexEdgeHomotopy` straighten the low storeys.
2. `Hurewicz.NormalizationState` packages the inductive data, and
   `Hurewicz.normalizationStep`/`Hurewicz.normalizationTower` iterate it.
3. `Hurewicz.normalizedSimplex` and `Hurewicz.normalizedTopSimplex` are the time-`1`
   normalized (based) simplices.
4. `Hurewicz.normalizedSimplex_boundary_relation` and `Hurewicz.classOperator_boundary`
   relate the normalized simplex boundary to the class operator.
5. `Hurewicz.hurewiczInverse` uses the normalization to build the inverse Hurewicz map.

## Main definitions and results

* `Hurewicz.TowerPair`, `Hurewicz.NormalizationState`: the recursion data.
* `Hurewicz.normalizationHomotopy`: the coherent straightening family.
* `Hurewicz.normalizedSimplex`, `Hurewicz.hurewiczInverse`: the normalized simplex and
  the induced inverse on homology classes.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorem 4.32; the argument is
  recorded in `Lib/docs/C.md`, §§8 and 12.

## Tags

Hurewicz theorem, straightening, normalization tower, simplex
-/

/-! ### The tower storeys -/

/-- Two consecutive storeys of a coherent simplex-homotopy tower, with the basepoint and face
compatibilities the extension step consumes. -/
structure Hurewicz.TowerPair {X : Type} [TopologicalSpace X] (x : X) (k : ℕ) where
  /-- The storey-`k` family. -/
  low : SingularChains.SingularSimplex X k → C((unitInterval) × SingularChains.Simplex k, X)
  /-- The storey-`(k + 1)` family. -/
  high :
    SingularChains.SingularSimplex X (k + 1) →
      C((unitInterval) × SingularChains.Simplex (k + 1), X)
  /-- The lower storey starts at the identity. -/
  low_zero : ∀ smp s, low smp (0, s) = smp s
  /-- The higher storey starts at the identity. -/
  high_zero : ∀ smp s, high smp (0, s) = smp s
  /-- Face compatibility between the storeys. -/
  compat : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies k low high

/-- The extension step of a tower pair: the next storey is the coherent extension of the pair
over one dimension up. -/
def Hurewicz.TowerPair.step {X : Type} [TopologicalSpace X] {x : X} {k : ℕ}
    (S : Hurewicz.TowerPair x k) : Hurewicz.TowerPair x (k + 1) where
  low := S.high
  high := Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy S.low S.high S.compat
    S.high_zero
  low_zero := S.high_zero
  high_zero := Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _
  compat := Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _

/-- The edge-straightening tower: storey `0` is stationary, storey `1` is the edge
straightening, and each higher storey extends the previous two. This is the dimension-general
form of `triangleEdgeStraighteningHomotopy` / `tetrahedronEdgeStraighteningHomotopy`. -/
def Hurewicz.edgeTower {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (k : ℕ) → Hurewicz.TowerPair x k
  | 0 =>
    { low := Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy 0
      high := Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy x
      low_zero := fun _smp _s => rfl
      high_zero := Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_zero x
      compat := Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_face x }
  | k + 1 => Hurewicz.TowerPair.step (Hurewicz.edgeTower x k)

/-- The vertex-then-edge normalization at dimension `k`: straighten the vertices first, then
the edges. This is the dimension-general form of the per-degree `vertexEdge*Homotopy`
compositions. -/
def Hurewicz.vertexEdgeHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (k : ℕ) :
    SingularChains.SingularSimplex X k → C((unitInterval) × SingularChains.Simplex k, X) :=
  Hurewicz.composeSimplexHomotopies
    (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy x k) (Hurewicz.edgeTower x k).low
    (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_zero x k)
    (Hurewicz.edgeTower x k).low_zero

/-- At time `0` the vertex-then-edge normalization homotopy is the simplex itself. -/
theorem Hurewicz.vertexEdgeHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (k : ℕ) (smp : SingularChains.SingularSimplex X k)
    (s : SingularChains.Simplex k) : Hurewicz.vertexEdgeHomotopy x k smp (0, s) = smp s :=
  Hurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

/-- The vertex-then-edge normalization is face-compatible between consecutive dimensions. -/
theorem Hurewicz.vertexEdgeHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (k : ℕ) :
    Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies k (Hurewicz.vertexEdgeHomotopy x k)
      (Hurewicz.vertexEdgeHomotopy x (k + 1)) :=
  Hurewicz.composeSimplexHomotopies_face _ _ _ _
    (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_zero x k)
    (Hurewicz.edgeTower x k).low_zero
    (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_zero x (k + 1))
    (Hurewicz.edgeTower x (k + 1)).low_zero
    (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_face x k)
    (Hurewicz.edgeTower x k).compat

/-- The endpoint of the vertex-then-edge normalization at dimension `1` is the constant
loop: after the vertices are moved to the basepoint, every edge is a based loop, which the
edge straightening collapses (simple connectivity). -/
theorem Hurewicz.vertexEdgeHomotopy_one_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 1) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.vertexEdgeHomotopy x 1 smp) 1 =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  apply ContinuousMap.ext
  intro s
  unfold Hurewicz.vertexEdgeHomotopy
  rw [Hurewicz.timeSlice_composeSimplexHomotopies_one]
  have hb := Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased x 1 smp
  exact Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_one x _ (hb 0) (hb 1) s

/-- The endpoint of the vertex-then-edge normalization at dimension `k + 1` is based at `x`
on the whole boundary. -/
theorem Hurewicz.vertexEdgeHomotopy_endpoint_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (k : ℕ)
    (hone :
      ∀ smp,
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.vertexEdgeHomotopy x k smp) 1 =
          ContinuousMap.const (SingularChains.Simplex k) x)
    (smp : SingularChains.SingularSimplex X (k + 1)) (s : SingularChains.Simplex (k + 1))
    (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary (k + 1)) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.vertexEdgeHomotopy x (k + 1) smp) 1 s =
      x :=
  Hurewicz.simplexEndpoint_boundary (Hurewicz.vertexEdgeHomotopy x k)
    (Hurewicz.vertexEdgeHomotopy x (k + 1)) (Hurewicz.vertexEdgeHomotopy_face x k) x
    hone smp s hs

/-! ### The normalization recursion -/

/-- The state of the normalization tower at level `k`: the augmented storey-`k` family (the
normalization composed with the dimension-`k` straightening) and the normalization at storey
`k + 1`, with their basepoint and face compatibilities and the endpoint properties (the
augmented family collapses every simplex to the basepoint at `t = 1`; the next normalization's
endpoint is based at `x` on the boundary). -/

structure Hurewicz.NormalizationState {X : Type} [TopologicalSpace X] (x : X) (k : ℕ) where
  /-- The augmented storey-`k` family. -/
  aug : SingularChains.SingularSimplex X k → C((unitInterval) × SingularChains.Simplex k, X)
  /-- The normalization at storey `k + 1`. -/
  nxt :
    SingularChains.SingularSimplex X (k + 1) →
      C((unitInterval) × SingularChains.Simplex (k + 1), X)
  /-- The augmented family starts at the identity. -/
  aug_zero : ∀ smp s, aug smp (0, s) = smp s
  /-- The next normalization starts at the identity. -/
  nxt_zero : ∀ smp s, nxt smp (0, s) = smp s
  /-- Face compatibility from the augmented family to the next normalization. -/
  compat : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies k aug nxt
  /-- The augmented family collapses every simplex to the basepoint at `t = 1`. -/
  aug_one :
    ∀ smp,
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice (aug smp) 1 =
        ContinuousMap.const (SingularChains.Simplex k) x
  /-- The next normalization's endpoint is based at `x` on the boundary. -/
  nxt_endpoint :
    ∀ (smp : SingularChains.SingularSimplex X (k + 1)) (s : SingularChains.Simplex (k + 1)),
      s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary (k + 1) →
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice (nxt smp) 1 s = x

/-- Composing a coherent family whose endpoint is boundary-based with the dimension-`k`
straightening collapses every simplex to the basepoint at `t = 1` (using
`Subsingleton (π_ k X x)`). -/
theorem Hurewicz.composeSimplexHomotopies_one_straightening {X : Type} [TopologicalSpace X]
    {x : X} {k : ℕ} [Subsingleton (π_ k X x)]
    (H : SingularChains.SingularSimplex X k → C((unitInterval) × SingularChains.Simplex k, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s)
    (hone : ∀ (smp : SingularChains.SingularSimplex X k) (s : SingularChains.Simplex k),
      s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary k →
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1 s = x)
    (smp : SingularChains.SingularSimplex X k) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.composeSimplexHomotopies H (Hurewicz.simplexStraighteningHomotopy k x)
          hH₀ (Hurewicz.simplexStraighteningHomotopy_zero k x) smp) 1 =
      ContinuousMap.const (SingularChains.Simplex k) x := by
  apply ContinuousMap.ext
  intro s
  rw [Hurewicz.timeSlice_composeSimplexHomotopies_one]
  exact Hurewicz.simplexStraighteningHomotopy_one k x _ (hone smp) s

/-- The extension step of the normalization tower: given the state at level `k` and the
triviality of `π_ (k + 1)`, produce the state at level `k + 1`. The next normalization
`N(k + 2)` is the composition of the boundary normalization (the coherent extension of the
state) with the top storey (the coherent extension of the dimension-`(k + 1)` straightening);
the next augmented family is `N(k + 1)` followed by the dimension-`(k + 1)` straightening. -/
def Hurewicz.normalizationStep {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) {k : ℕ} (hpi : Subsingleton (π_ (k + 1) X x))
    (S : Hurewicz.NormalizationState x k) : Hurewicz.NormalizationState x (k + 1) := by
  letI := hpi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Hurewicz.composeSimplexHomotopies S.nxt
      (Hurewicz.simplexStraighteningHomotopy (k + 1) x) S.nxt_zero
      (Hurewicz.simplexStraighteningHomotopy_zero (k + 1) x)
  · exact Hurewicz.composeSimplexHomotopies
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy S.aug S.nxt S.compat
        S.nxt_zero)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
        (Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy k)
        (Hurewicz.simplexStraighteningHomotopy (k + 1) x)
        (Hurewicz.simplexStraighteningHomotopy_face k x)
        (Hurewicz.simplexStraighteningHomotopy_zero (k + 1) x))
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
  · exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _
  · exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _
  · exact Hurewicz.composeSimplexHomotopies_face _ _ _ _ S.nxt_zero
      (Hurewicz.simplexStraighteningHomotopy_zero (k + 1) x)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face S.aug S.nxt S.compat
        S.nxt_zero)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
  · exact Hurewicz.composeSimplexHomotopies_one_straightening S.nxt S.nxt_zero
      S.nxt_endpoint
  · intro smp s hs
    exact Hurewicz.simplexEndpoint_boundary _ _
      (Hurewicz.composeSimplexHomotopies_face _ _ _ _ S.nxt_zero
        (Hurewicz.simplexStraighteningHomotopy_zero (k + 1) x)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face S.aug S.nxt S.compat
          S.nxt_zero)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _))
      x (Hurewicz.composeSimplexHomotopies_one_straightening S.nxt S.nxt_zero
        S.nxt_endpoint) smp s hs

/-- The base of the normalization tower at level `2`: the degree-`2` normalization (vertices,
edges, then the triangle straightening, using `π_2 = 0`), the degree-`3` normalization, and
their compatibilities and endpoint properties. -/
def Hurewicz.normalizationBaseTwo {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (hpi : Subsingleton (π_ 2 X x)) : Hurewicz.NormalizationState x 2 := by
  letI := hpi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Hurewicz.composeSimplexHomotopies (Hurewicz.vertexEdgeHomotopy x 2)
      (Hurewicz.simplexStraighteningHomotopy 2 x)
      (Hurewicz.vertexEdgeHomotopy_zero x 2)
      (Hurewicz.simplexStraighteningHomotopy_zero 2 x)
  · exact Hurewicz.composeSimplexHomotopies (Hurewicz.vertexEdgeHomotopy x 3)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
        (Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy 1)
        (Hurewicz.simplexStraighteningHomotopy 2 x)
        (Hurewicz.simplexStraighteningHomotopy_face 1 x)
        (Hurewicz.simplexStraighteningHomotopy_zero 2 x))
      (Hurewicz.vertexEdgeHomotopy_zero x 3)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
  · exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _
  · exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _
  · exact Hurewicz.composeSimplexHomotopies_face _ _ _ _
      (Hurewicz.vertexEdgeHomotopy_zero x 2)
      (Hurewicz.simplexStraighteningHomotopy_zero 2 x)
      (Hurewicz.vertexEdgeHomotopy_zero x 3)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
      (Hurewicz.vertexEdgeHomotopy_face x 2)
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
  · exact Hurewicz.composeSimplexHomotopies_one_straightening
      (Hurewicz.vertexEdgeHomotopy x 2) (Hurewicz.vertexEdgeHomotopy_zero x 2)
      (Hurewicz.vertexEdgeHomotopy_endpoint_boundary x 1
        (Hurewicz.vertexEdgeHomotopy_one_endpoint x))
  · intro smp s hs
    exact Hurewicz.simplexEndpoint_boundary _ _
      (Hurewicz.composeSimplexHomotopies_face _ _ _ _
        (Hurewicz.vertexEdgeHomotopy_zero x 2)
        (Hurewicz.simplexStraighteningHomotopy_zero 2 x)
        (Hurewicz.vertexEdgeHomotopy_zero x 3)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
        (Hurewicz.vertexEdgeHomotopy_face x 2)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _))
      x (Hurewicz.composeSimplexHomotopies_one_straightening
        (Hurewicz.vertexEdgeHomotopy x 2) (Hurewicz.vertexEdgeHomotopy_zero x 2)
        (Hurewicz.vertexEdgeHomotopy_endpoint_boundary x 1
          (Hurewicz.vertexEdgeHomotopy_one_endpoint x))) smp s hs

/-- The normalization tower, driven to level `k + 2`: the base is `normalizationBaseTwo`; each
step extends the state by one dimension, consuming the triviality of the next homotopy group.
The hypothesis `hpi` is exactly the `(n - 1)`-connectedness input of the Hurewicz theorem at
degree `n = k + 3`. -/
def Hurewicz.normalizationTower {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) :
    (k : ℕ) → (∀ j, 2 ≤ j → j ≤ k + 2 → Subsingleton (π_ j X x)) →
      Hurewicz.NormalizationState x (k + 2)
  | 0, hpi => Hurewicz.normalizationBaseTwo x (hpi 2 (by omega) (by omega))
  | k + 1, hpi =>
    Hurewicz.normalizationStep x (hpi (k + 3) (by omega) (by omega))
      (Hurewicz.normalizationTower x k fun j hj hjk => hpi j hj (by omega))

/-- The normalization homotopy at degree `n`: a coherent family straightening singular
`n`-simplices, starting at the identity and ending at the normalized (boundary-based) simplex.
This is the general-`n` form of the per-degree `normalization*SimplexHomotopy` compositions
(textbook §8). -/
def Hurewicz.normalizationHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (n : ℕ) (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X) :=
  match n with
  | 0 => Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy 0
  | 1 => Hurewicz.vertexEdgeHomotopy x 1
  | 2 => Hurewicz.vertexEdgeHomotopy x 2
  | n + 3 =>
    (Hurewicz.normalizationTower x n fun j hj hj' => hpi j hj (by omega)).nxt

/-- The normalization homotopy starts at the identity. -/
theorem Hurewicz.normalizationHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) (smp : SingularChains.SingularSimplex X n)
    (s : SingularChains.Simplex n) :
    Hurewicz.normalizationHomotopy x n hpi smp (0, s) = smp s := by
  match n with
  | 0 => rfl
  | 1 => exact Hurewicz.vertexEdgeHomotopy_zero x 1 smp s
  | 2 =>
    exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s
  | n + 3 =>
    exact (Hurewicz.normalizationTower x n fun j hj hj' =>
      hpi j hj (by omega)).nxt_zero smp s

/-- The endpoint of the edge straightening of a vertex-based triangle has all vertices at the
basepoint: the tower preserves `VerticesBased` at dimension `2`. -/
theorem Hurewicz.edgeTower_two_verticesBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (τ : SingularChains.SingularSimplex X 2)
    (h : Hurewicz.DegreeTwo.SimplyConnected.VerticesBased x 2 τ) :
    Hurewicz.DegreeTwo.SimplyConnected.VerticesBased x 2
      (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        ((Hurewicz.edgeTower x 2).low τ) 1) := by
  intro j
  obtain ⟨i, j', hj⟩ := Hurewicz.DegreeTwo.SimplyConnected.simplexVertex_exists_face 1 j
  have key := (Hurewicz.edgeTower x 1).compat τ i
  show ((Hurewicz.edgeTower x 2).low τ) (1, stdSimplex.vertex (S := ℝ) j) = x
  rw [← hj]
  have hv := ContinuousMap.ext_iff.mp key (1, stdSimplex.vertex (S := ℝ) j')
  refine hv.trans ?_
  exact Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_one x _
    (by show τ ((SingularChains.simplexFace 1 i) (stdSimplex.vertex (S := ℝ) 0)) = x
        rw [SingularChains.simplexFace_vertex]; exact h _)
    (by show τ ((SingularChains.simplexFace 1 i) (stdSimplex.vertex (S := ℝ) 1)) = x
        rw [SingularChains.simplexFace_vertex]; exact h _) _

/-- The endpoint of the vertex-then-edge normalization of a triangle is based at `x` on the
boundary. -/
theorem Hurewicz.vertexEdgeHomotopy_two_endpoint_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2)
    (s : SingularChains.Simplex 2) (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary 2) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.vertexEdgeHomotopy x 2 smp) 1 s =
      x := by
  obtain ⟨i, t, ht⟩ := Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary_exists_face 1
    (⟨s, hs⟩ : Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary 2)
  have he : SingularChains.simplexFace 1 i t = s := congrArg Subtype.val ht
  rw [← he]
  show (Hurewicz.composeSimplexHomotopies
      (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy x 2)
      ((Hurewicz.edgeTower x 2).low) _ _ smp) (1, SingularChains.simplexFace 1 i t) = x
  rw [Hurewicz.composeSimplexHomotopies_one]
  have key := (Hurewicz.edgeTower x 1).compat
    (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
      (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy x 2 smp) 1) i
  have hv := ContinuousMap.ext_iff.mp key (1, t)
  refine hv.trans ?_
  apply Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_one
  · show (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy x 2 smp) 1)
        ((SingularChains.simplexFace 1 i) (stdSimplex.vertex (S := ℝ) 0)) = x
    rw [SingularChains.simplexFace_vertex]
    exact Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased x 2 smp _
  · show (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy x 2 smp) 1)
        ((SingularChains.simplexFace 1 i) (stdSimplex.vertex (S := ℝ) 1)) = x
    rw [SingularChains.simplexFace_vertex]
    exact Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased x 2 smp _

/-- The normalization homotopy's endpoint is based at `x` on the boundary: the normalized
simplex is a based map `(Δⁿ, ∂Δⁿ) → (X, x)`. -/
theorem Hurewicz.normalizationHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) (smp : SingularChains.SingularSimplex X n)
    (s : SingularChains.Simplex n) (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary n) :
    Hurewicz.normalizationHomotopy x n hpi smp (1, s) = x := by
  match n with
  | 0 =>
    obtain ⟨i, hi⟩ := hs
    exfalso
    have hsum := s.2.2
    have hi0 : i = 0 := Fin.ext (by have := i.2; omega)
    rw [hi0] at hi
    rw [Fin.sum_univ_one] at hsum
    exact one_ne_zero (hsum.symm.trans hi)
  | 1 =>
    show Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.vertexEdgeHomotopy x 1 smp) 1 s = x
    rw [Hurewicz.vertexEdgeHomotopy_one_endpoint x smp]
    rfl
  | 2 =>
    exact Hurewicz.vertexEdgeHomotopy_two_endpoint_boundary x smp s hs
  | n + 3 =>
    exact (Hurewicz.normalizationTower x n fun j hj hj' =>
      hpi j hj (by omega)).nxt_endpoint smp s hs

/-- The normalized simplex: the endpoint of the normalization homotopy, as a based simplex
`(Δⁿ, ∂Δⁿ) → (X, x)`. This is the general-`n` form of the per-degree `normalized*Simplex`
constructions. -/
def Hurewicz.normalizedSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (n : ℕ) (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (smp : SingularChains.SingularSimplex X n) : Hurewicz.SimplexGeometry.BasedSimplex n x :=
  ⟨Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.normalizationHomotopy x n hpi smp) 1,
   fun s hs => Hurewicz.normalizationHomotopy_endpoint x n hpi smp s hs⟩

/-- The endpoint of the straightening of a based simplex is again based. -/
theorem Hurewicz.SimplexGeometry.straighteningHomotopy_one_based {X : Type}
    [TopologicalSpace X] {x : X} {k : ℕ} [Subsingleton (π_ k X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex k x) :
    ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary k,
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice
          (Hurewicz.simplexStraighteningHomotopy k x τ.val) 1 s = x := by
  intro s hs
  show Hurewicz.simplexStraighteningHomotopy k x τ.val (1, s) = x
  rw [Hurewicz.simplexStraighteningHomotopy_boundary k x τ.val 1 s hs]
  exact τ.property s hs

/-- The straightened based simplex: the endpoint of the straightening homotopy. -/
def Hurewicz.SimplexGeometry.straightenedBasedSimplex {X : Type} [TopologicalSpace X]
    {x : X} {k : ℕ} [Subsingleton (π_ k X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex k x) :
    Hurewicz.SimplexGeometry.BasedSimplex k x :=
  ⟨Hurewicz.DegreeTwo.SimplyConnected.timeSlice
      (Hurewicz.simplexStraighteningHomotopy k x τ.val) 1,
    Hurewicz.SimplexGeometry.straighteningHomotopy_one_based τ⟩

/-- The straightening of a based simplex, viewed as a homotopy of based loops: from the
original loop to the straightened one, relative to the boundary. -/
def Hurewicz.SimplexGeometry.basedSimplexLoop_straighteningHomotopy {X : Type}
    [TopologicalSpace X] {x : X} {k : ℕ} [Subsingleton (π_ k X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex k x) :
    (Hurewicz.SimplexGeometry.basedSimplexLoop τ).val.HomotopyRel
      (Hurewicz.SimplexGeometry.basedSimplexLoop
        (Hurewicz.SimplexGeometry.straightenedBasedSimplex τ)).val
      (Cube.boundary (Fin k)) where
  toFun z :=
    Hurewicz.simplexStraighteningHomotopy k x τ.val
      (z.1, Hurewicz.SimplexGeometry.simplexQuotient k z.2)
  continuous_toFun :=
    (Hurewicz.simplexStraighteningHomotopy k x τ.val).continuous.comp
      ((ContinuousMap.id _).prodMap (Hurewicz.SimplexGeometry.simplexQuotient k)).continuous
  map_zero_left u := by
    show Hurewicz.simplexStraighteningHomotopy k x τ.val (0,
        Hurewicz.SimplexGeometry.simplexQuotient k u) = _
    rw [Hurewicz.simplexStraighteningHomotopy_zero k x τ.val]
    rfl
  map_one_left u := rfl
  prop' t u hu := by
    show Hurewicz.simplexStraighteningHomotopy k x τ.val (t,
        Hurewicz.SimplexGeometry.simplexQuotient k u) = _
    rw [Hurewicz.simplexStraighteningHomotopy_boundary k x τ.val t _
      (Hurewicz.SimplexGeometry.simplexQuotient_boundary u hu)]
    rfl

/-- The class of the straightened based simplex equals the class of the original: the
straightening is a homotopy relative to the boundary. -/
theorem Hurewicz.SimplexGeometry.basedSimplexClass_straightening {X : Type}
    [TopologicalSpace X] {x : X} {k : ℕ} [Subsingleton (π_ k X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex k x) :
    Hurewicz.SimplexGeometry.basedSimplexClass
        (Hurewicz.SimplexGeometry.straightenedBasedSimplex τ) =
      Hurewicz.SimplexGeometry.basedSimplexClass τ := by
  unfold Hurewicz.SimplexGeometry.basedSimplexClass
  congr 1
  apply Quotient.sound
  exact ⟨(Hurewicz.SimplexGeometry.basedSimplexLoop_straighteningHomotopy τ).symm⟩

/-! ### The top storey and the class operator -/

/-- The top-storey straightening at dimension `n`: the coherent extension of the
dimension-`n−1` straightening by the stationary family. -/

def Hurewicz.topStorey {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    [Subsingleton (π_ (n + 1) X x)] :
    SingularChains.SingularSimplex X (n + 2) → C((unitInterval) × SingularChains.Simplex (n + 2), X) :=
  Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
    (Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy n)
    (Hurewicz.simplexStraighteningHomotopy (n + 1) x)
    (Hurewicz.simplexStraighteningHomotopy_face n x)
    (Hurewicz.simplexStraighteningHomotopy_zero (n + 1) x)

/-- The top-storey straightening starts at the identity. -/
theorem Hurewicz.topStorey_zero {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    [Subsingleton (π_ (n + 1) X x)] (smp : SingularChains.SingularSimplex X (n + 2))
    (s : SingularChains.Simplex (n + 2)) : Hurewicz.topStorey x n smp (0, s) = smp s :=
  Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

/-- The face compatibility of the top storey: its face restrictions are the dimension-`n`
straightening of the faces. -/
theorem Hurewicz.topStorey_face {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    [Subsingleton (π_ (n + 1) X x)] :
    Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies (n + 1)
      (Hurewicz.simplexStraighteningHomotopy (n + 1) x) (Hurewicz.topStorey x n) :=
  Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _

/-- The tower state one level below a degree: the augmented normalization and the
normalization at the target degree, packaged for the one-off top construction. -/
def Hurewicz.towerBelow {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    {n : ℕ} (hn : 2 ≤ n) (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    Hurewicz.NormalizationState x (n - 1) := by
  match n with
  | 0 => exact absurd hn (by omega)
  | 1 => exact absurd hn (by omega)
  | 2 =>
    exact
      { aug := Hurewicz.vertexEdgeHomotopy x 1
        nxt := Hurewicz.vertexEdgeHomotopy x 2
        aug_zero := Hurewicz.vertexEdgeHomotopy_zero x 1
        nxt_zero := Hurewicz.vertexEdgeHomotopy_zero x 2
        compat := Hurewicz.vertexEdgeHomotopy_face x 1
        aug_one := Hurewicz.vertexEdgeHomotopy_one_endpoint x
        nxt_endpoint := Hurewicz.vertexEdgeHomotopy_two_endpoint_boundary x }
  | m + 3 =>
    exact Hurewicz.normalizationTower x m fun j hj hj' =>
      hpi j hj (by omega)

/-- The one-off top normalization at dimension `n + 1`: the composition of the boundary
normalization (the coherent extension of the tower state) with the self-extension of the top
storey. Used for the boundary relation of the class operator at degree `n`; it never uses the
dimension-`n` straightening (`π_ n` is the answer, not a hypothesis). -/
def Hurewicz.topNormalization {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (n : ℕ) (hn : 2 ≤ n) (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    SingularChains.SingularSimplex X (n + 1) →
      C((unitInterval) × SingularChains.Simplex (n + 1), X) := by
  match n with
  | 0 => exact absurd hn (by omega)
  | 1 => exact absurd hn (by omega)
  | 2 =>
    exact
      Hurewicz.composeSimplexHomotopies
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
          (Hurewicz.towerBelow x hn hpi).aug (Hurewicz.towerBelow x hn hpi).nxt
          (Hurewicz.towerBelow x hn hpi).compat
          (Hurewicz.towerBelow x hn hpi).nxt_zero)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
          (Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy x)
          (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
            (Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy 0)
            (Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy x)
            (Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_face x)
            (Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_zero x))
          (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
          (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _))
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
  | m + 3 =>
    haveI := hpi (m + 2) (by omega) (by omega)
    exact
      Hurewicz.composeSimplexHomotopies
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
          (Hurewicz.towerBelow x hn hpi).aug (Hurewicz.towerBelow x hn hpi).nxt
          (Hurewicz.towerBelow x hn hpi).compat
          (Hurewicz.towerBelow x hn hpi).nxt_zero)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
          (Hurewicz.simplexStraighteningHomotopy (m + 2) x)
          (Hurewicz.topStorey x (m + 1))
          (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
          (Hurewicz.topStorey_zero x (m + 1)))
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _)

/-- The top normalization starts at the identity. -/
theorem Hurewicz.topNormalization_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (hn : 2 ≤ n)
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (smp : SingularChains.SingularSimplex X (n + 1)) (s : SingularChains.Simplex (n + 1)) :
    Hurewicz.topNormalization x n hn hpi smp (0, s) = smp s := by
  match n with
  | 0 => exact absurd hn (by omega)
  | 1 => exact absurd hn (by omega)
  | 2 =>
    show (Hurewicz.composeSimplexHomotopies _ _ _ _ smp) (0, s) = smp s
    exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s
  | m + 3 =>
    show (Hurewicz.composeSimplexHomotopies _ _ _ _ smp) (0, s) = smp s
    exact Hurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

/-- The class operator at degree `n`: the `ℤ`-linear map from singular `n`-chains to
`Additive (π_ n X x)` reading off each simplex's normalized class. This is the general-`n`
form of the per-degree `*SimplexClassOperator`. -/
def Hurewicz.classOperator {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (n : ℕ) [Nontrivial (Fin n)]
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x)) :
    SingularChains.Chains X n →ₗ[ℤ] Additive (π_ n X x) :=
  SingularChains.chainLift X n fun smp =>
    Hurewicz.SimplexGeometry.basedSimplexClass (Hurewicz.normalizedSimplex x n hpi smp)

/-- The class operator on a single simplex is the class of its normalization. -/
@[simp]
theorem Hurewicz.classOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) [Nontrivial (Fin n)]
    (hpi : ∀ j, 2 ≤ j → j < n → Subsingleton (π_ j X x))
    (smp : SingularChains.SingularSimplex X n) :
    Hurewicz.classOperator x n hpi (SingularChains.simplexChain X n smp) =
      Hurewicz.SimplexGeometry.basedSimplexClass
        (Hurewicz.normalizedSimplex x n hpi smp) :=
  SingularChains.chainLift_simplex X n _ smp

/-- The top storey is a homotopy relative to the boundary: on a boundary-based simplex its
value on the boundary is constant (it acts there as the straightening of the constant
faces). -/
theorem Hurewicz.topStorey_relBoundary {X : Type} [TopologicalSpace X] {x : X} {m : ℕ}
    [Subsingleton (π_ (m + 2) X x)] (τ : Hurewicz.SimplexGeometry.BasedSimplex (m + 3) x)
    (r : (unitInterval)) (s : SingularChains.Simplex (m + 3))
    (hs : s ∈ Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary (m + 3)) :
    Hurewicz.topStorey x (m + 1) τ.val (r, s) = τ.val s := by
  obtain ⟨j, t, ht⟩ :=
    Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary_exists_face (m + 2)
      (⟨s, hs⟩ : Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (m + 3))
  have he : SingularChains.simplexFace (m + 2) j t = s := congrArg Subtype.val ht
  rw [← he]
  have hf := Hurewicz.topStorey_face x (m + 1) τ.val j
  have hv :=
    congrArg (fun F : C((unitInterval) × SingularChains.Simplex (m + 2), X) => F (r, t)) hf
  show Hurewicz.topStorey x (m + 1) τ.val
      (r, SingularChains.simplexFace (m + 2) j t) =
    τ.val (SingularChains.simplexFace (m + 2) j t)
  rw [show Hurewicz.topStorey x (m + 1) τ.val
        (r, SingularChains.simplexFace (m + 2) j t) =
        Hurewicz.simplexStraighteningHomotopy (m + 2) x
          (τ.val.comp (SingularChains.simplexFace (m + 2) j)) (r, t) from hv,
    Hurewicz.SimplexGeometry.basedSimplex_face τ j,
    Hurewicz.simplexStraighteningHomotopy_const]
  exact (τ.property _ ⟨j, SingularChains.simplexFace_apply_self (m + 2) j t⟩).symm

/-- The top-storey endpoint of a based simplex, as a based simplex: the endpoint is
boundary-based because the top storey is boundary-stationary. -/
def Hurewicz.SimplexGeometry.topStoreySimplex {X : Type} [TopologicalSpace X] {x : X}
    {m : ℕ} [Subsingleton (π_ (m + 2) X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex (m + 3) x) :
    Hurewicz.SimplexGeometry.BasedSimplex (m + 3) x :=
  ⟨Hurewicz.DegreeTwo.SimplyConnected.timeSlice (Hurewicz.topStorey x (m + 1) τ.val) 1, by
    intro s hs
    show Hurewicz.topStorey x (m + 1) τ.val (1, s) = x
    exact (Hurewicz.topStorey_relBoundary τ 1 s hs).trans (τ.property s hs)⟩

/-- The top storey, viewed as a homotopy of based loops from a based simplex to its
top-storey endpoint, relative to the boundary. -/
def Hurewicz.SimplexGeometry.basedSimplexLoop_topStoreyHomotopy {X : Type}
    [TopologicalSpace X] {x : X} {m : ℕ} [Subsingleton (π_ (m + 2) X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex (m + 3) x) :
    (Hurewicz.SimplexGeometry.basedSimplexLoop τ).val.HomotopyRel
      (Hurewicz.SimplexGeometry.basedSimplexLoop
        (Hurewicz.SimplexGeometry.topStoreySimplex τ)).val
      (Cube.boundary (Fin (m + 3))) where
  toFun z :=
    Hurewicz.topStorey x (m + 1) τ.val
      (z.1, Hurewicz.SimplexGeometry.simplexQuotient (m + 3) z.2)
  continuous_toFun :=
    (Hurewicz.topStorey x (m + 1) τ.val).continuous.comp
      ((ContinuousMap.id _).prodMap
        (Hurewicz.SimplexGeometry.simplexQuotient (m + 3))).continuous
  map_zero_left u := by
    show Hurewicz.topStorey x (m + 1) τ.val
        (0, Hurewicz.SimplexGeometry.simplexQuotient (m + 3) u) = _
    rw [Hurewicz.topStorey_zero]
    rfl
  map_one_left u := rfl
  prop' t u hu := by
    show Hurewicz.topStorey x (m + 1) τ.val
        (t, Hurewicz.SimplexGeometry.simplexQuotient (m + 3) u) = _
    rw [Hurewicz.topStorey_relBoundary τ t _
      (Hurewicz.SimplexGeometry.simplexQuotient_boundary u hu)]
    rfl

/-- The class of the top-storey endpoint equals the class of the original based simplex: the
top storey is a homotopy relative to the boundary. -/
theorem Hurewicz.SimplexGeometry.basedSimplexClass_topStorey {X : Type}
    [TopologicalSpace X] {x : X} {m : ℕ} [Subsingleton (π_ (m + 2) X x)]
    (τ : Hurewicz.SimplexGeometry.BasedSimplex (m + 3) x) :
    Hurewicz.SimplexGeometry.basedSimplexClass
        (Hurewicz.SimplexGeometry.topStoreySimplex τ) =
      Hurewicz.SimplexGeometry.basedSimplexClass τ := by
  unfold Hurewicz.SimplexGeometry.basedSimplexClass
  congr 1
  apply Quotient.sound
  exact ⟨(Hurewicz.SimplexGeometry.basedSimplexLoop_topStoreyHomotopy τ).symm⟩

/-- The normalization one level below the top of the tower is the degree-`n` normalization:
both are the `n`-th normalization tower's next family (the hypotheses differ only by a
proof). -/
theorem Hurewicz.towerBelow_nxt_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ} (hn : 2 ≤ m + 3)
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x)) :
    (Hurewicz.towerBelow x hn hpi).nxt =
      Hurewicz.normalizationHomotopy x (m + 3) hpi := by
  show (Hurewicz.normalizationTower x m _).nxt =
    (Hurewicz.normalizationTower x m _).nxt
  congr 1

/-- The endpoint of the one-off top normalization: the top storey applied to the endpoint of
the boundary normalization (the composition law for composed simplex homotopies). -/
theorem Hurewicz.topNormalization_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ} [Subsingleton (π_ (m + 2) X x)]
    (hn : 2 ≤ m + 3) (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (σ : SingularChains.SingularSimplex X (m + 4)) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.topNormalization x (m + 3) hn hpi σ) 1 =
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
          (Hurewicz.simplexStraighteningHomotopy (m + 2) x)
          (Hurewicz.topStorey x (m + 1))
          (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
          (Hurewicz.topStorey_zero x (m + 1))
          (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
            (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
              (Hurewicz.towerBelow x hn hpi).aug
              (Hurewicz.towerBelow x hn hpi).nxt
              (Hurewicz.towerBelow x hn hpi).compat
              (Hurewicz.towerBelow x hn hpi).nxt_zero σ) 1)) 1 := by
  show Hurewicz.DegreeTwo.SimplyConnected.timeSlice
      (Hurewicz.composeSimplexHomotopies _ _ _ _ σ) 1 = _
  exact Hurewicz.timeSlice_composeSimplexHomotopies_one _ _ _ _ σ

/-- The face relation for the one-off top normalization at the map level: the `i`-th face of
its endpoint is the top storey of the degree-`n` normalization of the `i`-th face. At the
level of based-simplex classes the extra top storey disappears
(`basedSimplexClass_topStorey`). -/
theorem Hurewicz.topNormalization_endpoint_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ} [Subsingleton (π_ (m + 2) X x)]
    (hn : 2 ≤ m + 3) (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (σ : SingularChains.SingularSimplex X (m + 4)) (i : Fin (m + 5)) :
    (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.topNormalization x (m + 3) hn hpi σ) 1).comp
        (SingularChains.simplexFace (m + 3) i) =
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (Hurewicz.topStorey x (m + 1)
          (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
            (Hurewicz.normalizationHomotopy x (m + 3) hpi
              (σ.comp (SingularChains.simplexFace (m + 3) i))) 1)) 1 := by
  rw [Hurewicz.topNormalization_endpoint]
  rw [Hurewicz.DegreeTwo.SimplyConnected.timeSlice_face
    (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face
      (Hurewicz.simplexStraighteningHomotopy (m + 2) x)
      (Hurewicz.topStorey x (m + 1))
      (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
      (Hurewicz.topStorey_zero x (m + 1)))
    _ i 1]
  rw [Hurewicz.DegreeTwo.SimplyConnected.timeSlice_face
    (show Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies (m + 3)
        (Hurewicz.towerBelow x hn hpi).nxt
        (Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
          (Hurewicz.towerBelow x hn hpi).aug
          (Hurewicz.towerBelow x hn hpi).nxt
          (Hurewicz.towerBelow x hn hpi).compat
          (Hurewicz.towerBelow x hn hpi).nxt_zero) from
      Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face _ _ _ _)
    σ i 1]
  rw [Hurewicz.towerBelow_nxt_eq]

/-- The normalized top simplex: the endpoint of the one-off top normalization of an
`(n + 1)`-simplex, as a simplex based on the two-skeleton. Each face restriction is
boundary-collapsed: on the boundary it is the top-storey endpoint of a boundary-based
simplex. This is the general-`n` form of the per-degree `normalized*Simplex` (one degree up)
constructions. -/
def Hurewicz.normalizedTopSimplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (σ : SingularChains.SingularSimplex X (m + 4)) :
    Hurewicz.SimplexGeometry.BasedSimplexBoundary (m + 4) x :=
  Hurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces
    (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
      (Hurewicz.topNormalization x (m + 3) (by omega) hpi σ) 1)
    (fun i s hs => by
      haveI := hpi (m + 2) (by omega) (by omega)
      show (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
          (Hurewicz.topNormalization x (m + 3) _ hpi σ) 1).comp
            (SingularChains.simplexFace (m + 3) i) s = x
      rw [Hurewicz.topNormalization_endpoint_face]
      obtain ⟨j, t, ht⟩ :=
        Hurewicz.DegreeTwo.SimplyConnected.simplexBoundary_exists_face (m + 2)
          (⟨s, hs⟩ : Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (m + 3))
      have he : SingularChains.simplexFace (m + 2) j t = s := congrArg Subtype.val ht
      rw [← he, ← ContinuousMap.comp_apply,
        Hurewicz.DegreeTwo.SimplyConnected.timeSlice_face
          (Hurewicz.topStorey_face x (m + 1)) _ j 1,
        show (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
              (Hurewicz.normalizationHomotopy x (m + 3) hpi
                (σ.comp (SingularChains.simplexFace (m + 3) i))) 1).comp
            (SingularChains.simplexFace (m + 2) j) =
          ContinuousMap.const (SingularChains.Simplex (m + 2)) x from
          Hurewicz.SimplexGeometry.basedSimplex_face
            (Hurewicz.normalizedSimplex x (m + 3) hpi
              (σ.comp (SingularChains.simplexFace (m + 3) i))) j,
        Hurewicz.simplexStraighteningHomotopy_const]
      rfl)

/-- The class-level face relation for the normalized top simplex: the class of its `i`-th
face is the class of the degree-`n` normalization of the `i`-th face of the original
simplex. -/
theorem Hurewicz.normalizedTopSimplex_class_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (σ : SingularChains.SingularSimplex X (m + 4)) (i : Fin (m + 5)) :
    Hurewicz.SimplexGeometry.basedSimplexClass
        (Hurewicz.SimplexGeometry.basedSimplexBoundaryFace
          (Hurewicz.normalizedTopSimplex x hpi σ) i) =
      Hurewicz.SimplexGeometry.basedSimplexClass
        (Hurewicz.normalizedSimplex x (m + 3) hpi
          (σ.comp (SingularChains.simplexFace (m + 3) i))) := by
  haveI := hpi (m + 2) (by omega) (by omega)
  rw [show Hurewicz.SimplexGeometry.basedSimplexBoundaryFace
        (Hurewicz.normalizedTopSimplex x hpi σ) i =
      Hurewicz.SimplexGeometry.topStoreySimplex
        (Hurewicz.normalizedSimplex x (m + 3) hpi
          (σ.comp (SingularChains.simplexFace (m + 3) i))) from
    Subtype.ext (Hurewicz.topNormalization_endpoint_face x (by omega) hpi σ i)]
  exact Hurewicz.SimplexGeometry.basedSimplexClass_topStorey _

/-! ### Boundary relation and the inverse map -/

/-- The boundary relation for the normalized simplex: the signed sum of the classes of the
normalized faces of an `(n + 1)`-simplex vanishes. This is the general-`n` form of the
per-degree `normalized*Simplex_boundary_relation`. -/

theorem Hurewicz.normalizedSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (σ : SingularChains.SingularSimplex X (m + 4)) :
    ∑ i : Fin (m + 5),
        (-1 : ℤ) ^ i.val •
          Hurewicz.SimplexGeometry.basedSimplexClass
            (Hurewicz.normalizedSimplex x (m + 3) hpi
              (σ.comp (SingularChains.simplexFace (m + 3) i))) =
      0 := by
  have h :=
    Hurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := m + 1)
      (Hurewicz.normalizedTopSimplex x hpi σ)
  simpa only [Hurewicz.normalizedTopSimplex_class_face] using h

/-- The class operator vanishes on boundaries: it descends to singular homology. This is the
general-`n` form of the per-degree `*SimplexClassOperator_boundary`. -/
theorem Hurewicz.classOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (b : SingularChains.Chains X (m + 4)) :
    Hurewicz.classOperator x (m + 3) hpi
        (((SingularChains.singularComplex X).d (m + 4) (m + 3)).hom b) =
      0 := by
  have h :
    (Hurewicz.classOperator x (m + 3) hpi).comp
        (((SingularChains.singularComplex X).d (m + 4) (m + 3)).hom) =
      0 := by
    apply SingularChains.chainMap_ext X (m + 4)
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundary_simplex, map_sum, map_zsmul,
      Hurewicz.classOperator_simplex, LinearMap.zero_apply]
    exact Hurewicz.normalizedSimplex_boundary_relation x hpi smp
  exact LinearMap.congr_fun h b

/-- The inverse Hurewicz map at degree `n ≥ 3`: the class operator descended to
singular homology. General-`n` form of the per-degree `hurewiczInverse`. -/
def Hurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x)) :
    SingularMayerVietoris.SingularHomology X (m + 3) →ₗ[ℤ] Additive (π_ (m + 3) X x) :=
  Hurewicz.singularHomologyDesc (m + 3)
    (Hurewicz.classOperator x (m + 3) hpi)
    (Hurewicz.classOperator_boundary x hpi)

/-- The inverse Hurewicz map on a cycle is the class operator on the underlying chain. -/
@[simp]
theorem Hurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) {m : ℕ}
    (hpi : ∀ j, 2 ≤ j → j < m + 3 → Subsingleton (π_ j X x))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) (m + 3)) :
    Hurewicz.hurewiczInverse x hpi
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X)
          (m + 3) c) =
      Hurewicz.classOperator x (m + 3) hpi c.1 :=
  Hurewicz.singularHomologyDesc_cycleClass (m + 3) _ _ c
