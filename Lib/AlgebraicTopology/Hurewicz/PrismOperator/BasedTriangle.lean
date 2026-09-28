/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.Basic
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.VertexEdgeStraightening
/-!
# Based triangles and the normalized `2`-cycle

A based triangle is a singular `2`-simplex sending the boundary of the standard triangle to the
basepoint `x`; through the quotient `I × I → Δ²` collapsing two sides (`triangleQuotient`) it
defines a based square `basedTriangleLoop τ` and hence a class
`basedTriangleClass τ ∈ Additive (π_ 2 X x)`.  In a simply connected space every singular
`2`-simplex is straightened, first at the vertices and then along the edges, to a based triangle
`normalizedTriangle x smp`, and the endpoint operator of the straightening turns a `2`-cycle
into the homologous normalized cycle `normalizedTwoCycle x c` (`normalizedTwoCycle_class`).
This is the step of the proof of Hatcher, Thm 4.32, that represents a homology class by based
simplices.

## Main definitions

* `Hurewicz.DegreeTwo.SimplyConnected.BasedTriangle`, `triangleQuotient`, `basedTriangleLoop`,
  `basedTriangleClass`.
* `Hurewicz.DegreeTwo.SimplyConnected.triangleEdgeStraighteningHomotopy`,
  `tetrahedronEdgeStraighteningHomotopy`: edge straightening in degrees `2` and `3`.
* `Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangle`, `normalizedTetrahedronMap`,
  `normalizedTwoChain`, `normalizedTwoCycle`, `normalizedTwoCycle_class`.
-/

open Set Function Topology

noncomputable section

/-! ### Based triangles and the triangle quotient -/

/-- The boundary of the `2`-simplex as a subset: the union of its three edges. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleBoundary : Set (SingularChains.Simplex 2) :=
  {s | ∃ i, s i = 0}

/-- A based triangle at `x`: a `2`-simplex map sending `triangleBoundary` to `x`. -/
def Hurewicz.DegreeTwo.SimplyConnected.BasedTriangle {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(SingularChains.Simplex 2, X) // ∀ s ∈ triangleBoundary, τ s = x }

/-- The quotient map `I × I → Simplex 2` sending `(a, b)` to `![1 - a, a - min a b, min a b]`. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient :
    C((unitInterval) × (unitInterval), SingularChains.Simplex 2)
    where
  toFun
    z :=
    ⟨![1 - (z.1 : ℝ), (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ), Min.min (z.1 : ℝ) (z.2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr z.1.property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min z.1.property.1 z.2.property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

/-- `triangleQuotient z 0 = 1 - z.1`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_zero
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 0 = 1 - (z.1 : ℝ) :=
  rfl

/-- `triangleQuotient z 1 = z.1 - min z.1 z.2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_one
    (z : (unitInterval) × (unitInterval)) :
    triangleQuotient z 1 = (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

/-- `triangleQuotient z 2 = min z.1 z.2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_two
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 2 = Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

/-- The quotient `(Fin 2 → I) → Simplex 2`, i.e. `triangleQuotient ∘ (t ↦ (t 0, t 1))`. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleCubeQuotient :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 2) :=
  triangleQuotient.comp ⟨fun t => (t 0, t 1), by fun_prop⟩

/-- `triangleCubeQuotient` sends the square boundary into the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleCubeQuotient_boundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : triangleCubeQuotient t ∈ triangleBoundary := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · refine ⟨2, ?_⟩
      change t 0 = 0 at hi
      change Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 1).property.1]
    · refine ⟨2, ?_⟩
      change t 1 = 0 at hi
      change Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_right (t 0).property.1]
  · fin_cases i
    · refine ⟨0, ?_⟩
      change t 0 = 1 at hi
      change 1 - (t 0 : ℝ) = 0
      simp [hi]
    · refine ⟨1, ?_⟩
      change t 1 = 1 at hi
      change (t 0 : ℝ) - Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 0).property.2]

/-- The based square loop `τ ∘ triangleCubeQuotient`. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTriangleLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp triangleCubeQuotient, fun t ht => τ.property _ (triangleCubeQuotient_boundary t ht)⟩

/-- The square map of `basedTriangleLoop τ` is `τ ∘ triangleQuotient`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareMap_basedTriangleLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    Hurewicz.DegreeTwo.squareMap (basedTriangleLoop τ) = τ.val.comp triangleQuotient := by
  ext z
  change
    τ.val
        (triangleQuotient
          (Hurewicz.DegreeTwo.squareCoordinates z 0, Hurewicz.DegreeTwo.squareCoordinates z 1)) =
      _
  rw [Hurewicz.DegreeTwo.squareCoordinates_zero, Hurewicz.DegreeTwo.squareCoordinates_one]
  rfl

/-- The `π_2`-class `⟦basedTriangleLoop τ⟧` of a based triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTriangleClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : Additive (π_ 2 X x) :=
  Additive.ofMul (⟦basedTriangleLoop τ⟧ : π_ 2 X x)

/-- The constant based triangle at `x`. -/
def Hurewicz.DegreeTwo.SimplyConnected.constantBasedTriangle {X : Type} [TopologicalSpace X] (x : X) :
    BasedTriangle x :=
  ⟨ContinuousMap.const (SingularChains.Simplex 2) x, fun _ _ => rfl⟩

/-- The edge-straightening homotopy of a triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) : C((unitInterval) × SingularChains.Simplex 2, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x) smp

/-- At time `0` the triangle edge straightening is the triangle. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (s : SingularChains.Simplex 2) :
    triangleEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

/-- Triangle edge straightening is face-compatible with `edgeStraighteningHomotopy`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 1 (edgeStraighteningHomotopy x)
      (triangleEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x)

/-- The edge-straightening homotopy of a tetrahedron (`3`-simplex). -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) : C((unitInterval) × SingularChains.Simplex 3, X) :=
  extendCoherentSimplexHomotopy (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x) smp

/-- At time `0` the tetrahedron edge straightening is the tetrahedron. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) (s : SingularChains.Simplex 3) :
    tetrahedronEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

/-- Tetrahedron edge straightening is face-compatible with `triangleEdgeStraighteningHomotopy`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 2 (triangleEdgeStraighteningHomotopy x)
      (tetrahedronEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x)

/-- For vertex-based `smp`, every face of the time-`1` endpoint is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleEdgeStraighteningHomotopy_one_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (h : VerticesBased x 2 smp) (i : Fin 3) :
    (timeSlice (triangleEdgeStraighteningHomotopy x smp) 1).comp (SingularChains.simplexFace 1 i) =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  rw [timeSlice_face (triangleEdgeStraighteningHomotopy_face x)]
  ext s
  exact
    edgeStraighteningHomotopy_one x (smp.comp (SingularChains.simplexFace 1 i)) (h.face i 0)
      (h.face i 1) s

/-- For vertex-based `smp`, the time-`1` endpoint is `x` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleEdgeStraighteningHomotopy_one_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (h : VerticesBased x 2 smp)
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    timeSlice (triangleEdgeStraighteningHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 1 (⟨s, hs⟩ : SimplexBoundary 2)
  have he : SingularChains.simplexFace 1 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(SingularChains.Simplex 1, X) => f t)
      (triangleEdgeStraighteningHomotopy_one_face x smp h i)

/-- The time-`1` endpoint of the edge straightening: a boundary-based triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.edgeStraightenedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2)
    (h : VerticesBased x 2 smp) : BasedTriangle x :=
  ⟨timeSlice (triangleEdgeStraighteningHomotopy x smp) 1,
    triangleEdgeStraighteningHomotopy_one_boundary x smp h⟩

/-- The vertex normalization of a simplex: its time-`1` slice under the vertex
straightening. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexNormalizedSimplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : SingularChains.SingularSimplex X n) :
    SingularChains.SingularSimplex X n :=
  timeSlice (vertexStraighteningHomotopy x n smp) 1

/-- The vertex normalization is vertex-based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexNormalizedSimplex_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : SingularChains.SingularSimplex X n) :
    VerticesBased x n (vertexNormalizedSimplex x n smp) :=
  vertexStraighteningHomotopy_one_verticesBased x n smp

/-- The faces of the vertex normalization are the vertex normalizations of the
faces. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexNormalizedSimplex_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : SingularChains.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (vertexNormalizedSimplex x (n + 1) smp).comp (SingularChains.simplexFace n i) =
      vertexNormalizedSimplex x n (smp.comp (SingularChains.simplexFace n i)) :=
  vertexStraighteningHomotopy_timeSlice_face x n smp i 1

/-- The vertex normalization of an already vertex-based simplex is the simplex
itself. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexNormalizedSimplex_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : SingularChains.SingularSimplex X n) (h : VerticesBased x n smp) :
    vertexNormalizedSimplex x n smp = smp :=
  vertexStraighteningHomotopy_timeSlice_of_verticesBased x n smp h 1

/-- The normalized triangle: vertex- then edge-straightened. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2) :
    BasedTriangle x :=
  edgeStraightenedTriangle x (vertexNormalizedSimplex x 2 smp)
    (vertexNormalizedSimplex_verticesBased x 2 smp)

/-- Normalizing an already vertex-based triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangle_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (h : VerticesBased x 2 smp) :
    normalizedTriangle x smp = edgeStraightenedTriangle x smp h := by
  apply Subtype.ext
  change
    timeSlice (triangleEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 2 smp)) 1 =
      timeSlice (triangleEdgeStraighteningHomotopy x smp) 1
  rw [vertexNormalizedSimplex_of_verticesBased x 2 smp h]

/-- The normalized tetrahedron map: vertex- then edge-straightened `3`-simplex. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedronMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) :
    SingularChains.SingularSimplex X 3 :=
  timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1

/-- The `i`-th face of the normalized tetrahedron map is the normalized triangle of the `i`-th face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedronMap_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) (i : Fin 4) :
    (normalizedTetrahedronMap x smp).comp (SingularChains.simplexFace 2 i) =
      (normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i))).val := by
  change
    (timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1).comp
        (SingularChains.simplexFace 2 i) =
      _
  rw [timeSlice_face (tetrahedronEdgeStraighteningHomotopy_face x), vertexNormalizedSimplex_face]
  rfl

/-- On the `i`-th face, the normalized tetrahedron map sends the triangle boundary to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedronMap_face_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) (i : Fin 4) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) :
    normalizedTetrahedronMap x smp (SingularChains.simplexFace 2 i s) = x := by
  have hf :=
    congrArg (fun f : C(SingularChains.Simplex 2, X) => f s)
      (normalizedTetrahedronMap_face x smp i)
  exact hf.trans ((normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i))).property s hs)

/-- The normalized `2`-chain: `simplexEndpointOperator` at time `1` of the
straightening. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTwoChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : SingularChains.Chains X 2 →ₗ[ℤ] SingularChains.Chains X 2 :=
  SingularChains.chainLift X 2 fun smp =>
    SingularChains.simplexChain X 2 (normalizedTriangle x smp).val

/-- `normalizedTwoChain` sends a simplex generator to the simplex chain of its normalized triangle. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTwoChain_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2) :
    normalizedTwoChain x (SingularChains.simplexChain X 2 smp) =
      SingularChains.simplexChain X 2 (normalizedTriangle x smp).val :=
  SingularChains.chainLift_simplex X 2 _ smp

/-- `normalizedTwoChain` agrees with the vertex-then-edge normalization. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTwoChain_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    normalizedTwoChain x =
      (simplexEndpointOperator 2 (triangleEdgeStraighteningHomotopy x) 1).comp
        (simplexEndpointOperator 2 (vertexStraighteningHomotopy x 2) 1) := by
  apply SingularChains.chainMap_ext X 2
  intro smp
  simp only [normalizedTwoChain_simplex, LinearMap.comp_apply, simplexEndpointOperator_simplex]
  rfl

/-- The degree-`2` cycle obtained by straightening along `vertexStraighteningHomotopy`. -/
def Hurewicz.DegreeTwo.SimplyConnected.vertexNormalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  straightenedTwoCycle (vertexStraighteningHomotopy x 1) (vertexStraighteningHomotopy x 2)
    (vertexStraighteningHomotopy_face x 1) c

/-- The vertex-normalized `2`-cycle is homologous to `c`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.vertexNormalizedTwoCycle_class {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (vertexNormalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c :=
  straightenedTwoCycle_class _ _ (vertexStraighteningHomotopy_face x 1)
    (vertexStraighteningHomotopy_timeSlice_zero x 2) c

/-- The fully normalized cycle: `vertexNormalizedTwoCycle` followed by edge straightening. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  straightenedTwoCycle (edgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy_face x) (vertexNormalizedTwoCycle x c)

/-- The underlying chain of `normalizedTwoCycle c`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTwoCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    (normalizedTwoCycle x c).val = normalizedTwoChain x c.val := by
  rw [normalizedTwoChain_eq]
  rfl

/-- The normalized `2`-cycle is homologous to `c`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTwoCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (normalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c := by
  have h₀ : ∀ smp, timeSlice (triangleEdgeStraighteningHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleEdgeStraighteningHomotopy_zero x smp s
  exact
    (straightenedTwoCycle_class _ _ (triangleEdgeStraighteningHomotopy_face x) h₀
          (vertexNormalizedTwoCycle x c)).trans
      (vertexNormalizedTwoCycle_class x c)
