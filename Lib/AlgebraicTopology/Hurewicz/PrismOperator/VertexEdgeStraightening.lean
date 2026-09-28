/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.Basic
/-!
# Vertex and edge straightening of singular simplices

In a simply connected space `X` with basepoint `x`, every singular simplex is homotoped, degree
by degree and compatibly with faces, to a simplex whose vertices lie at `x`
(`vertexStraighteningHomotopy`) and then to one whose edges are constant loops at `x`
(`edgeStraighteningHomotopy`); the homotopy extension property of the simplex boundary
(`extendBoundaryHomotopy`) propagates a face-compatible family in degree `n + 1` to degree
`n + 2` (`extendCoherentSimplexHomotopy`).  This is the simplicial form of the straightening
step in the proof of the Hurewicz theorem (Hatcher, Thm 4.32, proof).

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.VertexHomotopyData`: vertex-straightening data in one
  degree; `VertexHomotopyData.next` builds the next degree from it.
* `Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy`: the resulting tower, with
  `vertexStraighteningHomotopy_face` (face compatibility) and
  `vertexStraighteningHomotopy_one_verticesBased`.
* `Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy`: contracting a based edge along
  a chosen nullhomotopy (`chosenNullHomotopy`), fixing the vertices.
* `Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy`: the coherent extension of a
  face-compatible pair of families to the next degree, with `extendCoherentSimplexHomotopy_face`.
-/

open Set Function Topology

noncomputable section

/-! ### Vertex and edge straightening data -/

/-- Vertex-homotopy data in degree `n`: a homotopy for each simplex that is the
identity at time `0`, vertex-based at time `1`, stationary on already-based
simplices, and face-compatible. -/
structure Hurewicz.DegreeTwo.SimplyConnected.VertexHomotopyData {X : Type} [TopologicalSpace X]
    (x : X) (n : ℕ) where
  homotopy : C(SingularChains.Simplex n, X) → C((unitInterval) × SingularChains.Simplex n, X)
  zero :
    ∀ (smp : C(SingularChains.Simplex n, X)) (s : SingularChains.Simplex n),
      homotopy smp (0, s) = smp s
  one_verticesBased : ∀ smp, VerticesBased x n (timeSlice (homotopy smp) 1)
  of_verticesBased :
    ∀ smp,
      VerticesBased x n smp →
        homotopy smp =
          smp.comp
            (ContinuousMap.snd :
              C((unitInterval) × SingularChains.Simplex n, SingularChains.Simplex n))
  face_compatible :
    ∀ smp : C(SingularChains.Simplex (n + 1), X),
      FaceCompatible (fun i => homotopy (smp.comp (SingularChains.simplexFace n i)))

/-- The boundary homotopy of a simplex assembled from vertex homotopy data. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexBoundaryHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X)) :
    C((unitInterval) × SimplexBoundary (n + 1), X) :=
  glueFaceHomotopies (fun i => D.homotopy (smp.comp (SingularChains.simplexFace n i)))
    (D.face_compatible smp)

/-- On the `i`-th face of the boundary, `vertexBoundaryHomotopy` is `D.homotopy` applied to that face. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexBoundaryHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X))
    (i : Fin (n + 2)) (r : (unitInterval)) (s : SingularChains.Simplex n) :
    vertexBoundaryHomotopy D smp (r, simplexFaceBoundary n i s) =
      D.homotopy (smp.comp (SingularChains.simplexFace n i)) (r, s) :=
  glueFaceHomotopies_face _ _ i r s

/-- At time `0`, `vertexBoundaryHomotopy` is `smp` on the boundary. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexBoundaryHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X))
    (s : SimplexBoundary (n + 1)) : vertexBoundaryHomotopy D smp (0, s) = smp s.val :=
  glueFaceHomotopies_zero _ _ smp (fun i t => D.zero (smp.comp (SingularChains.simplexFace n i)) t)
    s

/-- The one-step vertex homotopy: stationary on already vertex-based simplices, otherwise the extension of `vertexBoundaryHomotopy`. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X)) :
    C((unitInterval) × SingularChains.Simplex (n + 1), X) := by
  classical
    exact
    if VerticesBased x (n + 1) smp then
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × SingularChains.Simplex (n + 1), SingularChains.Simplex (n + 1)))
    else
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp)

/-- On an already vertex-based simplex, the vertex step is stationary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) (h : VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × SingularChains.Simplex (n + 1), SingularChains.Simplex (n + 1))) := by
  classical simp only [vertexStepHomotopy, if_pos h]

/-- On a non-vertex-based simplex, the vertex step is `extendBoundaryHomotopy` of `vertexBoundaryHomotopy D smp`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_of_not_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) (h : ¬VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp) := by classical simp only [vertexStepHomotopy, if_neg h]

/-- At time `0` the vertex step homotopy is the simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X))
    (s : SingularChains.Simplex (n + 1)) : vertexStepHomotopy D smp (0, s) = smp s := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h]
    exact extendBoundaryHomotopy_bottom _ _ _ s

/-- On the `i`-th face, the vertex step evaluates to `D.homotopy` of that face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_face_apply {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval))
    (s : SingularChains.Simplex n) :
    vertexStepHomotopy D smp (r, SingularChains.simplexFace n i s) =
      D.homotopy (smp.comp (SingularChains.simplexFace n i)) (r, s) := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h, D.of_verticesBased _ (h.face i)]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h, extendBoundaryHomotopy_face]
    exact vertexBoundaryHomotopy_face D smp i r s

/-- The face homotopies `D.homotopy` are face-compatible with the vertex step `vertexStepHomotopy D`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) :
    FaceCompatibleHomotopies n D.homotopy (vertexStepHomotopy D) := by
  intro smp i
  ext u
  exact vertexStepHomotopy_face_apply D smp i u.1 u.2

/-- At time `1` the vertex step lands on vertex-based simplices. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) :
    VerticesBased x (n + 1) (timeSlice (vertexStepHomotopy D smp) 1) := by
  intro k
  obtain ⟨i, j, hij⟩ := simplexVertex_exists_face n k
  change vertexStepHomotopy D smp (1, stdSimplex.vertex k) = x
  rw [← hij, vertexStepHomotopy_face_apply]
  exact D.one_verticesBased (smp.comp (SingularChains.simplexFace n i)) j

/-- The vertex step homotopies are face-compatible across simplices. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_faceCompatible {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 2), X)) :
    FaceCompatible
      (fun i => vertexStepHomotopy D (smp.comp (SingularChains.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij r u
  rw [vertexStepHomotopy_face_apply, vertexStepHomotopy_face_apply,
    SingularChains.singularSimplex_face_face smp hij]

/-- The `VertexHomotopyData` in degree `n` induces vertex data in degree `n+1`
(via `vertexStepHomotopy`). -/
def Hurewicz.DegreeTwo.SimplyConnected.VertexHomotopyData.next {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : Hurewicz.DegreeTwo.SimplyConnected.VertexHomotopyData x n) :
    Hurewicz.DegreeTwo.SimplyConnected.VertexHomotopyData x (n + 1)
    where
  homotopy := Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy D
  zero := Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_zero D
  one_verticesBased := Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_one_verticesBased D
  of_verticesBased := Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_of_verticesBased D
  face_compatible := Hurewicz.DegreeTwo.SimplyConnected.vertexStepHomotopy_faceCompatible D

/-- The edge path of a simplex along edge `(i,j)` in the chosen base paths. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedEdgePath {X : Type} [TopologicalSpace X] (x : X)
    (smp : C(SingularChains.Simplex 1, X)) (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) : Path x x :=
  (SingularChains.simplexPath smp).cast h₀.symm h₁.symm

/-- The based edge path of a constant configuration is constant. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedEdgePath_const {X : Type} [TopologicalSpace X]
    (x : X) :
    basedEdgePath x (ContinuousMap.const (SingularChains.Simplex 1) x) rfl rfl = Path.refl x := by
  apply Path.ext
  funext t
  rfl

/-- The chosen path from a vertex value to the basepoint `x` (using
`SimplyConnectedSpace`). -/
def Hurewicz.DegreeTwo.SimplyConnected.chosenBasePath {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x y : X) : Path y x := by
  classical exact if h : y = x then (Path.refl x).cast h rfl else PathConnectedSpace.somePath y x

/-- The chosen base path at `x` itself is the constant path. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.chosenBasePath_self {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : chosenBasePath x x = Path.refl x := by
  simp [chosenBasePath]

/-- The chosen nullhomotopy of a based edge loop. -/
def Hurewicz.DegreeTwo.SimplyConnected.chosenNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (p : Path x x) : p.Homotopy (Path.refl x) := by
  classical
    exact
    if h : p = Path.refl x then (Path.Homotopy.refl (Path.refl x)).cast h.symm rfl
    else Classical.choice (SimplyConnectedSpace.paths_homotopic p (Path.refl x))

/-- The chosen nullhomotopy of the constant loop is stationary. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.chosenNullHomotopy_refl {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    chosenNullHomotopy x (Path.refl x) = Path.Homotopy.refl (Path.refl x) := by
  simp [chosenNullHomotopy]
  rfl

/-- The homotopy contracting a `0`-simplex to `x` along `chosenBasePath`. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 0, X)) :
    C((unitInterval) × SingularChains.Simplex 0, X) :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).toContinuousMap.comp
    (ContinuousMap.fst : C((unitInterval) × SingularChains.Simplex 0, (unitInterval)))

/-- At time `0`, `vertexHomotopy` is the given `0`-simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 0, X))
    (s : SingularChains.Simplex 0) : vertexHomotopy x smp (0, s) = smp s := by
  change chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) 0 = smp s
  rw [Path.source, SingularChains.simplexZero_eq_vertex s]

/-- At time `1`, `vertexHomotopy` lands at the basepoint. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 0, X))
    (s : SingularChains.Simplex 0) : vertexHomotopy x smp (1, s) = x :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).target

/-- The vertex homotopy at the basepoint is stationary. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    vertexHomotopy x (ContinuousMap.const (SingularChains.Simplex 0) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex 0) x := by
  ext t
  change chosenBasePath x x t.1 = x
  rw [chosenBasePath_self]
  rfl

/-- The homotopy contracting an edge to the basepoint, relative to its endpoints. -/
def Hurewicz.DegreeTwo.SimplyConnected.edgeNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) :
    C((unitInterval) × SingularChains.Simplex 1, X) :=
  (chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)).toContinuousMap.comp
    ((ContinuousMap.id (unitInterval)).prodMap
      ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩)

/-- At time `0`, `edgeNullHomotopy` is the edge itself. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeNullHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) (h₀ h₁)
    (s : SingularChains.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (0, s) = smp s := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (0, stdSimplexHomeomorphUnitInterval s) =
      smp s
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change smp (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = smp s
  rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]

/-- At time `1`, `edgeNullHomotopy` is constant at `x`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeNullHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) (h₀ h₁)
    (s : SingularChains.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (1, s) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (1, stdSimplexHomeomorphUnitInterval s) = x
  rw [ContinuousMap.HomotopyWith.apply_one]
  rfl

/-- `edgeNullHomotopy` sends vertex `0` to `x` for all times. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeNullHomotopy_vertex_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (h₀ h₁) (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero]
  exact Path.Homotopy.source _ t

/-- `edgeNullHomotopy` sends vertex `1` to `x` for all times. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeNullHomotopy_vertex_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) (h₀ h₁)
    (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_one]
  exact Path.Homotopy.target _ t

/-- The edge nullhomotopy of the constant edge is stationary. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeNullHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    edgeNullHomotopy x (ContinuousMap.const (SingularChains.Simplex 1) x) rfl rfl =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex 1) x := by
  ext t
  change
    chosenNullHomotopy x
        (basedEdgePath x (ContinuousMap.const (SingularChains.Simplex 1) x) rfl rfl)
        (t.1, stdSimplexHomeomorphUnitInterval t.2) =
      x
  rw [basedEdgePath_const, chosenNullHomotopy_refl]
  rfl

/-- The initial vertex-homotopy data built from `chosenBasePath`. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexInitialData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : VertexHomotopyData x 0
    where
  homotopy := vertexHomotopy x
  zero := vertexHomotopy_zero x
  one_verticesBased smp i := vertexHomotopy_one x smp (stdSimplex.vertex i)
  of_verticesBased smp
    h := by
    have hs : smp = ContinuousMap.const (SingularChains.Simplex 0) x := verticesBased_zero_iff.mp h
    rw [hs, vertexHomotopy_const]
    rfl
  face_compatible
    smp :=
    faceCompatible_zero (fun i => vertexHomotopy x (smp.comp (SingularChains.simplexFace 0 i)))

/-- The vertex-straightening data for simplices: the recursive tower of vertex
homotopies. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : (n : ℕ) → VertexHomotopyData x n
  | 0 => vertexInitialData x
  | n + 1 => (vertexStraighteningData x n).next

/-- The homotopy straightening the vertices of a simplex to the basepoint. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : C(SingularChains.Simplex n, X)) :
    C((unitInterval) × SingularChains.Simplex n, X) :=
  (vertexStraighteningData x n).homotopy smp

/-- At time `0`, `vertexStraighteningHomotopy` is the simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) (s : SingularChains.Simplex n) :
    vertexStraighteningHomotopy x n smp (0, s) = smp s :=
  (vertexStraighteningData x n).zero smp s

/-- The time-`0` slice of the vertex-straightening homotopy is the simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_timeSlice_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) :
    timeSlice (vertexStraighteningHomotopy x n smp) 0 = smp := by
  ext s
  exact vertexStraighteningHomotopy_zero x n smp s

/-- Vertex straightening is face-compatible across consecutive degrees. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    FaceCompatibleHomotopies n (vertexStraighteningHomotopy x n)
      (vertexStraighteningHomotopy x (n + 1)) :=
  vertexStepHomotopy_face (vertexStraighteningData x n)

/-- The `i`-th face of a time slice of the degree `n + 1` straightening is the time slice of the degree `n` straightening of that face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_timeSlice_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval)) :
    (timeSlice (vertexStraighteningHomotopy x (n + 1) smp) r).comp
        (SingularChains.simplexFace n i) =
      timeSlice (vertexStraighteningHomotopy x n (smp.comp (SingularChains.simplexFace n i))) r :=
  timeSlice_face (vertexStraighteningHomotopy_face x n) smp i r

/-- At time `1` the vertex-straightened simplex is vertex-based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) :
    VerticesBased x n (timeSlice (vertexStraighteningHomotopy x n smp) 1) :=
  (vertexStraighteningData x n).one_verticesBased smp

/-- On an already vertex-based simplex the straightening is stationary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) (h : VerticesBased x n smp) :
    vertexStraighteningHomotopy x n smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × SingularChains.Simplex n, SingularChains.Simplex n)) :=
  (vertexStraighteningData x n).of_verticesBased smp h

/-- Time slices of the vertex straightening of an already-based simplex are the
simplex itself. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_timeSlice_of_verticesBased
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) (h : VerticesBased x n smp) (r : (unitInterval)) :
    timeSlice (vertexStraighteningHomotopy x n smp) r = smp := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n smp h]
  rfl

/-- The vertex straightening of the constant simplex is stationary. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    vertexStraighteningHomotopy x n (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n _ (verticesBased_const x n)]
  rfl

/-- The stationary homotopy of a simplex (constant in time). -/
def Hurewicz.DegreeTwo.SimplyConnected.stationarySimplexHomotopy {X : Type} [TopologicalSpace X]
    (n : ℕ) (smp : C(SingularChains.Simplex n, X)) :
    C((unitInterval) × SingularChains.Simplex n, X) :=
  smp.comp
    (ContinuousMap.snd : C((unitInterval) × SingularChains.Simplex n, SingularChains.Simplex n))

/-- The homotopy straightening the edges of a simplex to basepoint loops, keeping
the vertices fixed. -/
def Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) :
    C((unitInterval) × SingularChains.Simplex 1, X) := by
  classical
    exact
    if h :
        smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
          smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x then
      edgeNullHomotopy x smp h.1 h.2
    else stationarySimplexHomotopy 1 smp

/-- At time `0`, `edgeStraighteningHomotopy` is the simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (s : SingularChains.Simplex 1) : edgeStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · exact edgeNullHomotopy_zero x smp _ _ s
  · rfl

/-- At time `1`, `edgeStraighteningHomotopy` has based edges. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_one {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) (s : SingularChains.Simplex 1) :
    edgeStraighteningHomotopy x smp (1, s) = x := by
  classical
  have h :
    smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
      smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x :=
    ⟨h₀, h₁⟩
  rw [edgeStraighteningHomotopy, dif_pos h]
  exact edgeNullHomotopy_one x smp _ _ s

/-- The edge straightening fixes each vertex. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_vertex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (i : Fin 2) (t : (unitInterval)) :
    edgeStraighteningHomotopy x smp (t, stdSimplex.vertex (S := ℝ) i) =
      smp (stdSimplex.vertex (S := ℝ) i) := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · rename_i h
    fin_cases i
    · exact (edgeNullHomotopy_vertex_zero x smp h.1 h.2 t).trans h.1.symm
    · exact (edgeNullHomotopy_vertex_one x smp h.1 h.2 t).trans h.2.symm
  · rfl

/-- The edge straightening of the constant simplex is stationary. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    edgeStraighteningHomotopy x (ContinuousMap.const (SingularChains.Simplex 1) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex 1) x := by
  classical
  simp only [edgeStraighteningHomotopy, ContinuousMap.const_apply]
  exact edgeNullHomotopy_const x

/-- The `i`-th face of the edge straightening agrees with the edge straightening
of the face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.edgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 0 (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change
    edgeStraighteningHomotopy x smp (t, SingularChains.simplexFace 0 i s) =
      smp (SingularChains.simplexFace 0 i s)
  rw [SingularChains.simplexZero_eq_vertex s, SingularChains.simplexFace_vertex]
  exact edgeStraighteningHomotopy_vertex x smp _ t

/-- The face restrictions of `H'` on a degree `n + 2` simplex are pairwise compatible. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.nextFaceHomotopies_compatible {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 2)) :
    FaceCompatible (fun i => H' (smp.comp (SingularChains.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij t s
  have hi :=
    congrArg (fun F : C((unitInterval) × SingularChains.Simplex n, X) => F (t, s))
      (h (smp.comp (SingularChains.simplexFace (n + 1) j.succ)) i)
  have hj :=
    congrArg (fun F : C((unitInterval) × SingularChains.Simplex n, X) => F (t, s))
      (h (smp.comp (SingularChains.simplexFace (n + 1) i.castSucc)) j)
  change
    H' (smp.comp (SingularChains.simplexFace (n + 1) j.succ))
        (t, SingularChains.simplexFace n i s) =
      H
        ((smp.comp (SingularChains.simplexFace (n + 1) j.succ)).comp
          (SingularChains.simplexFace n i))
        (t, s) at hi
  change
    H' (smp.comp (SingularChains.simplexFace (n + 1) i.castSucc))
        (t, SingularChains.simplexFace n j s) =
      H
        ((smp.comp (SingularChains.simplexFace (n + 1) i.castSucc)).comp
          (SingularChains.simplexFace n j))
        (t, s) at hj
  rw [hi, hj]
  change
    H (smp.comp ((SingularChains.simplexFace (n + 1) j.succ).comp (SingularChains.simplexFace n i)))
        (t, s) =
      H
        (smp.comp
          ((SingularChains.simplexFace (n + 1) i.castSucc).comp (SingularChains.simplexFace n j)))
        (t, s)
  rw [SingularChains.simplexFace_comp hij]

/-- The coherent boundary homotopy of a simplex assembled from face-compatible
data. -/
def Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 2)) :
    C((unitInterval) × SimplexBoundary (n + 2), X) :=
  glueFaceHomotopies (fun i => H' (smp.comp (SingularChains.simplexFace (n + 1) i)))
    (nextFaceHomotopies_compatible H H' h smp)

/-- On the `i`-th face boundary, `coherentFaceBoundaryHomotopy` evaluates to `H'` of that face. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy_face {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 2))
    (i : Fin (n + 3)) (t : (unitInterval)) (s : SingularChains.Simplex (n + 1)) :
    coherentFaceBoundaryHomotopy H H' h smp (t, simplexFaceBoundary (n + 1) i s) =
      H' (smp.comp (SingularChains.simplexFace (n + 1) i)) (t, s) :=
  glueFaceHomotopies_face _ _ i t s

/-- At time `0` the coherent boundary homotopy is the simplex. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X (n + 2)) (b : SimplexBoundary (n + 2)) :
    coherentFaceBoundaryHomotopy H H' h smp (0, b) = smp b.val :=
  glueFaceHomotopies_zero _ _ smp
    (fun i s => h₀ (smp.comp (SingularChains.simplexFace (n + 1) i)) s) b

/-- The extension of a coherent boundary homotopy to the whole simplex cylinder,
using the homotopy extension property. -/
def Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X (n + 2)) :
    C((unitInterval) × SingularChains.Simplex (n + 2), X) :=
  extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
    (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)

/-- At time `0` the extended coherent homotopy is the simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X (n + 2)) (s : SingularChains.Simplex (n + 2)) :
    extendCoherentSimplexHomotopy H H' h h₀ smp (0, s) = smp s :=
  extendBoundaryHomotopy_bottom _ _ _ s

/-- The extended degree `n + 2` family is face-compatible with `H'`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy_face {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s) :
    FaceCompatibleHomotopies (n + 1) H' (extendCoherentSimplexHomotopy H H' h h₀) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change
    extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
        (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)
        (t, SingularChains.simplexFace (n + 1) i s) =
      _
  rw [extendBoundaryHomotopy_face]
  exact coherentFaceBoundaryHomotopy_face H H' h smp i t s
