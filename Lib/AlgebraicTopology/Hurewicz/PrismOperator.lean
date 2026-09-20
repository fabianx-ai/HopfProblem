/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
/-!
# Simplex homotopies and the degree-two Hurewicz theorem

The file builds the prism operator on singular chains —
`Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator n H` takes a simplex-indexed
family `H : SingularSimplex X n → C(I × Simplex n, X)` and sends an `n`-chain to an
`(n+1)`-chain by `chainLift` of `simplexPrism n (H smp)`. For face-compatible families
in consecutive degrees, its boundary is the difference of the endpoint operators minus
the lower-degree prism applied to the boundary. The ordinary `prismOperator` gives
`∂(prism c) = H₁# c - H₀# c - prism(∂c)` for a single homotopy `H`.
The file then proves the degree-two Hurewicz theorem: `Hurewicz.degreeTwoLinearEquiv x` is a `ℤ`-linear equivalence
`Additive (π_ 2 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2` whenever `X`
is `SimplyConnectedSpace`.

## Outline of the construction

1. The evaluation map `Hurewicz.DegreeTwo.evaluation` and the square chain
   `squareChain`/`squareHomologyClass` assign a homology class to a based square;
   `hurewiczMap` is the resulting `ℤ`-linear map `π_2 → H_2`.
2. `timeSlice`, `prismOperator`, and `simplexPrismOperator` implement the prism
   construction and its boundary identity.
3. Coherent vertex/edge normalization (`VertexHomotopyData`,
   `edgeStraighteningHomotopy`, `extendCoherentSimplexHomotopy`) straightens
   simplices relative to their boundaries.
4. The based-triangle class `basedTriangleClass` and the square subdivision
   (`subdivision_class`, `squareNormalization_homotopic`) compare the square class
   with sums of triangle classes.
5. `secondHomologyDesc`, `triangleClassOperator`, and `hurewiczInverse` construct
   the inverse map, and `hurewiczInverse_comp_hurewiczMap` /
   `hurewiczMap_comp_hurewiczInverse` give the round trips.
6. `Hurewicz.composeSimplexHomotopies` and the `Hurewicz.*_const` lemmas compose
   coherent homotopy families for the general straightening construction.

## Main definitions and results

* `Hurewicz.DegreeTwo.hurewiczMap`: the degree-two Hurewicz map `π_2 → H_2`.
* `Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator_boundary`: the prism
  boundary identity.
* `Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse`, `hurewiczPi2Equiv`: the inverse.
* `Hurewicz.degreeTwoLinearEquiv`: the degree-two Hurewicz equivalence for
  simply connected `X`.

## References

* [Allen Hatcher, *Algebraic Topology*][hatcher02], Theorems 2.10 and 4.32;
  recorded in `Lib/docs/C.md`, §§6, 8, 12–13.

## Tags

Hurewicz, prism operator, simplex, homotopy, simply connected
-/


open Set Function Filter Manifold Topology

noncomputable section

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Evaluating `crossProductTriangle` at the degenerate zero simplex on the left
equals the right-component chain. -/
theorem Hurewicz.DegreeTwo.crossProductTriangle_zero_eq_zeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularHomology.crossProductTriangle X Y 0 =
      SingularHomology.crossProductZeroRight X Y 2 := by
  apply SingularHomology.chainBilinearMap_ext X Y 2 0
  intro σ τ
  rw [SingularHomology.crossProductTriangle_simplex,
    SingularHomology.formalTriangleCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex,
    SingularHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex,
    SingularHomology.crossProductZeroRight_simplex]
  apply congrArg (SingularChains.simplexChain (X × Y) 2)
  change
    (σ.prodMap τ).comp
        (SingularHomology.productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 2 i, SingularMayerVietoris.stdVertices 0 0))) =
      (SingularHomology.crossInsertRight
            (SingularHomology.zeroSimplexValue τ)).comp
        σ
  rw [SingularHomology.productAffineSimplex_point_right,
    SingularMayerVietoris.affineSimplex_stdVertices, ContinuousMap.comp_id]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The triangle cross product of a point chain on the left is the induced chain of
the left insertion. -/
theorem Hurewicz.DegreeTwo.crossProductTriangle_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularChains.Chains X 2) (y : Y) :
    SingularHomology.crossProductTriangle X Y 0 a (SingularChains.pointChain y) =
      SingularChains.inducedChain (SingularHomology.crossInsertRight y) 2 a := by
  rw [crossProductTriangle_zero_eq_zeroRight, SingularChains.pointChain,
    SingularHomology.crossProductZeroRight_simplex_right]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The edge cross product of a point chain on the left is the induced chain of the
left insertion. -/
theorem Hurewicz.DegreeTwo.crossProductEdge_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularChains.Chains X 1) (y : Y) :
    SingularHomology.crossProductEdge X Y 0 a (SingularChains.pointChain y) =
      SingularChains.inducedChain (SingularHomology.crossInsertRight y) 1 a := by
  rw [SingularChains.pointChain, SingularHomology.crossProductEdge_zero_simplex_right]
  rfl

/-- The remaining vertices index type (a subtype of `Fin` used for vertex iteration). -/
abbrev Hurewicz.DegreeTwo.Remaining :=
  { j : Fin 2 // j ≠ 0 }

/-- The based loop space of `X` at `x`: `GenLoop (Fin 1) X x`. -/
abbrev Hurewicz.DegreeTwo.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

/-! ### The square chain of a based square -/

/-- The evaluation map `C(BasedLoopSpace x × I, X)` sending `(p, t)` to `p` at the
constant cube `t`. -/
def Hurewicz.DegreeTwo.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (unitInterval), X)
    where
  toFun z := z.1 (fun _ => z.2)
  continuous_toFun := by fun_prop

/-- Evaluation at `t = 0` sends every loop to the basepoint `x`. -/
@[simp]
theorem Hurewicz.DegreeTwo.evaluation_zero {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 0) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inl rfl⟩

/-- Evaluation at `t = 1` sends every loop to the basepoint `x`. -/
@[simp]
theorem Hurewicz.DegreeTwo.evaluation_one {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 1) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inr rfl⟩

/-- `evaluation x` composed with the `0`-insertion on the right is the constant map
to `x`. -/
@[simp]
theorem Hurewicz.DegreeTwo.evaluation_comp_right_zero {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (SingularHomology.crossInsertRight (0 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_zero x p

/-- `evaluation x` composed with the `1`-insertion on the right is the constant map
to `x`. -/
@[simp]
theorem Hurewicz.DegreeTwo.evaluation_comp_right_one {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (SingularHomology.crossInsertRight (1 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_one x p

/-- The identification `I × I → Fin 2 → I` of the square with the `2`-cube. -/
def Hurewicz.DegreeTwo.squareCoordinates : C((unitInterval) × (unitInterval), Fin 2 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 2) (z.1, fun _ => z.2)
  continuous_toFun := by fun_prop

/-- On the `0`-boundary of the square, `squareCoordinates` lands on the cube
boundary. -/
@[simp]
theorem Hurewicz.DegreeTwo.squareCoordinates_zero (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 0 = z.1 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

/-- On the `1`-boundary of the square, `squareCoordinates` lands on the cube
boundary. -/
@[simp]
theorem Hurewicz.DegreeTwo.squareCoordinates_one (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 1 = z.2 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

/-- The map `I × I → X` of a based square `p`, precomposed with
`squareCoordinates`. -/
def Hurewicz.DegreeTwo.squareMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    C((unitInterval) × (unitInterval), X) :=
  p.val.comp squareCoordinates

/-- `evaluation x ∘ (toLoop p × id)` is the square map of `p`. -/
theorem Hurewicz.DegreeTwo.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
          (ContinuousMap.id (unitInterval))) =
      squareMap p := by
  ext z
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The fundamental `1`-chain of the interval: the identity simplex on `I`. -/
def Hurewicz.DegreeTwo.intervalChain : SingularChains.Chains (unitInterval) 1 :=
  SingularChains.pathChain Path.id

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `intervalChain` is `point 1 - point 0`. -/
theorem Hurewicz.DegreeTwo.intervalChain_boundary :
    SingularChains.boundaryOne (unitInterval) intervalChain =
      SingularChains.pointChain (1 : (unitInterval)) -
        SingularChains.pointChain (0 : (unitInterval)) :=
  SingularChains.boundaryOne_pathChain Path.id

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `evaluation x`-pushforward of a chain crossed with the `0`-point chain is
the constant-simplex chain. -/
theorem Hurewicz.DegreeTwo.evaluation_right_zero_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : SingularChains.Chains (BasedLoopSpace x) n) :
    SingularChains.inducedChain (evaluation x) n
        (SingularChains.inducedChain
          (SingularHomology.crossInsertRight (0 : (unitInterval))) n a) =
      SingularChains.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((SingularChains.inducedChain (evaluation x) n).comp
          (SingularChains.inducedChain
            (SingularHomology.crossInsertRight (0 : (unitInterval))) n))
        a =
      _
  rw [← SingularChains.inducedChain_comp, evaluation_comp_right_zero]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `evaluation x`-pushforward of a chain crossed with the `1`-point chain is
the constant-simplex chain. -/
theorem Hurewicz.DegreeTwo.evaluation_right_one_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : SingularChains.Chains (BasedLoopSpace x) n) :
    SingularChains.inducedChain (evaluation x) n
        (SingularChains.inducedChain
          (SingularHomology.crossInsertRight (1 : (unitInterval))) n a) =
      SingularChains.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((SingularChains.inducedChain (evaluation x) n).comp
          (SingularChains.inducedChain
            (SingularHomology.crossInsertRight (1 : (unitInterval))) n))
        a =
      _
  rw [← SingularChains.inducedChain_comp, evaluation_comp_right_one]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- In the evaluated edge chain, the endpoint contributions of a `1`-cycle cancel. -/
theorem Hurewicz.DegreeTwo.evaluated_edge_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 1) :
    SingularChains.inducedChain (evaluation x) 1
        (SingularHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
          (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductEdge_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- In the evaluated triangle chain, the endpoint contributions of a `2`-cycle
cancel. -/
theorem Hurewicz.DegreeTwo.evaluated_triangle_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 2) :
    SingularChains.inducedChain (evaluation x) 2
        (SingularHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
          (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductTriangle_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The first suspension operator: `Chains (BasedLoopSpace x) 1 →ₗ[ℤ] Chains X 2`,
`evaluation`-pushforward of the edge cross product with `intervalChain`. -/
def Hurewicz.DegreeTwo.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    SingularChains.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] SingularChains.Chains X 2 :=
  (SingularChains.inducedChain (evaluation x) 2).comp
    (SingularHomology.integerBilinearRightApply
      (SingularHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `suspensionOne x c` is the `evaluation x`-pushforward of `c × intervalChain`. -/
@[simp]
theorem Hurewicz.DegreeTwo.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      SingularChains.inducedChain (evaluation x) 2
        (SingularHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The second suspension operator: `Chains (BasedLoopSpace x) 2 →ₗ[ℤ] Chains X 3`,
`evaluation`-pushforward of the triangle cross product with `intervalChain`. -/
def Hurewicz.DegreeTwo.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    SingularChains.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] SingularChains.Chains X 3 :=
  (SingularChains.inducedChain (evaluation x) 3).comp
    (SingularHomology.integerBilinearRightApply
      (SingularHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `suspensionTwo x c` is the `evaluation x`-pushforward of `c × intervalChain`. -/
@[simp]
theorem Hurewicz.DegreeTwo.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      SingularChains.inducedChain (evaluation x) 3
        (SingularHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- For a `1`-cycle `c` of based loops, `∂ (suspensionOne x c) = 0`: the suspension
of a cycle is a cycle. -/
theorem Hurewicz.DegreeTwo.boundaryTwo_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 1)
    (ha : SingularChains.boundaryOne (BasedLoopSpace x) a = 0) :
    SingularChains.boundaryTwo X (suspensionOne x a) = 0 := by
  change ((SingularChains.singularComplex X).d 2 1).hom (suspensionOne x a) = 0
  rw [suspensionOne_apply, ← SingularChains.inducedChain_boundary,
    SingularHomology.crossProductEdge_boundary 0]
  change
    SingularChains.inducedChain (evaluation x) 1
        (SingularHomology.crossProductZeroLeft (BasedLoopSpace x) (unitInterval) 1
            (SingularChains.boundaryOne (BasedLoopSpace x) a) intervalChain -
          SingularHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
            (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_endpoint_cancel,
    neg_zero]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `suspensionTwo x c` relates to `suspensionOne x (∂ c)` with
endpoint terms cancelling. -/
theorem Hurewicz.DegreeTwo.boundaryThree_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 2) :
    ((SingularChains.singularComplex X).d 3 2).hom (suspensionTwo x a) =
      suspensionOne x (SingularChains.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← SingularChains.inducedChain_boundary,
    SingularHomology.crossProductTriangle_boundary 0]
  change
    SingularChains.inducedChain (evaluation x) 2
        (SingularHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1
            (SingularChains.boundaryTwo (BasedLoopSpace x) a) intervalChain +
          SingularHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
            (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      _
  rw [map_add, evaluated_triangle_endpoint_cancel, add_zero]
  rfl

/-- The `2`-cycle of `X` obtained by suspending the path chain of a path of based
loops. -/
def Hurewicz.DegreeTwo.pathSquareCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (suspensionOne x (SingularChains.pathChain p))
    (boundaryTwo_suspensionOne_of_cycle x (SingularChains.pathChain p)
      (SingularChains.boundaryOne_loop p))

/-- The underlying chain of `pathSquareCycle p` is `suspensionOne x (pathChain p)`. -/
@[simp]
theorem Hurewicz.DegreeTwo.pathSquareCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathSquareCycle x p).1 = suspensionOne x (SingularChains.pathChain p) :=
  rfl

/-- The homology class of `pathSquareCycle p`. -/
def Hurewicz.DegreeTwo.pathSquareClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
    (pathSquareCycle x p)

/-- The square chain of a homotopy of paths of loops has controlled boundary. -/
theorem Hurewicz.DegreeTwo.pathSquare_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((SingularChains.singularComplex X).d 3 2).hom
        (suspensionTwo x (SingularChains.homotopyChain H)) =
      (pathSquareCycle x p).1 - (pathSquareCycle x q).1 := by
  rw [boundaryThree_suspensionTwo, SingularChains.boundaryTwo_loopHomotopy, map_sub]
  rfl

/-- `pathSquareClass` is invariant under homotopy of the path of loops. -/
theorem Hurewicz.DegreeTwo.pathSquareClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathSquareClass x p = pathSquareClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 2 _
        _).mpr
    ⟨suspensionTwo x (SingularChains.homotopyChain H), pathSquare_homotopy_boundary x H⟩

/-- Homotopic paths of based loops give equal `pathSquareClass`. -/
theorem Hurewicz.DegreeTwo.pathSquareClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathSquareClass x p = pathSquareClass x q := by
  obtain ⟨H⟩ := h
  exact pathSquareClass_homotopy x H

/-- `pathSquareClass` of the constant path is `0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.pathSquareClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathSquareClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (SingularChains.singularComplex X)
        2 _).mpr
  refine
    ⟨suspensionTwo x (SingularChains.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryThree_suspensionTwo, SingularChains.boundaryTwo_constantTriangleChain]
  rfl

/-- The boundary computation for a concatenation of paths of loops. -/
theorem Hurewicz.DegreeTwo.pathSquare_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((SingularChains.singularComplex X).d 3 2).hom
        (-suspensionTwo x (SingularChains.concatChain p q)) =
      (pathSquareCycle x (p.trans q)).1 - ((pathSquareCycle x p).1 + (pathSquareCycle x q).1) := by
  rw [map_neg, boundaryThree_suspensionTwo, SingularChains.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathSquareCycle_val]
  abel

/-- `pathSquareClass` is additive under path concatenation. -/
theorem Hurewicz.DegreeTwo.pathSquareClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathSquareClass x (p.trans q) = pathSquareClass x p + pathSquareClass x q := by
  unfold pathSquareClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 2 _
        _).mpr
  exact ⟨-suspensionTwo x (SingularChains.concatChain p q), pathSquare_concat_boundary x p q⟩

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The product `2`-chain `intervalChain × intervalChain` on `I × I`. -/
def Hurewicz.DegreeTwo.productSquareChain :
    SingularChains.Chains ((unitInterval) × (unitInterval)) 2 :=
  SingularHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
    intervalChain

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `productSquareChain` is the signed sum of its four edge chains. -/
theorem Hurewicz.DegreeTwo.productSquareChain_boundary :
    SingularChains.boundaryTwo ((unitInterval) × (unitInterval)) productSquareChain =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft (1 : (unitInterval)))
            1 intervalChain -
          SingularChains.inducedChain
            (SingularHomology.crossInsertLeft (0 : (unitInterval))) 1 intervalChain -
        (SingularChains.inducedChain
            (SingularHomology.crossInsertRight (1 : (unitInterval))) 1 intervalChain -
          SingularChains.inducedChain
            (SingularHomology.crossInsertRight (0 : (unitInterval))) 1 intervalChain) := by
  change
    ((SingularChains.singularComplex ((unitInterval) × (unitInterval))).d 2 1).hom
        (SingularHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
          intervalChain) =
      _
  rw [SingularHomology.crossProductEdge_boundary 0]
  change
    SingularHomology.crossProductZeroLeft (unitInterval) (unitInterval) 1
          (SingularChains.boundaryOne (unitInterval) intervalChain) intervalChain -
        SingularHomology.crossProductEdge (unitInterval) (unitInterval) 0 intervalChain
          (SingularChains.boundaryOne (unitInterval) intervalChain) =
      _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply, crossProductEdge_point_right]
  simp only [SingularChains.pointChain,
    SingularHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The fundamental `2`-chain of the `2`-cube: the `squareCoordinates`-pushforward
of `productSquareChain`. -/
def Hurewicz.DegreeTwo.fundamentalSquareChain : SingularChains.Chains (Fin 2 → (unitInterval)) 2 :=
  SingularChains.inducedChain squareCoordinates 2 productSquareChain

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `1`-chain on `X` induced by a path `a → b` (the pushforward of
`intervalChain`). -/
theorem Hurewicz.DegreeTwo.induced_intervalChain {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) :
    SingularChains.inducedChain p.toContinuousMap 1 intervalChain = SingularChains.pathChain p := by
  rw [intervalChain, SingularChains.pathChain, SingularChains.inducedChain_simplex]
  apply congrArg (SingularChains.simplexChain X 1)
  ext s
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `suspensionOne` of the `toLoop` path chain relates the square chain of `p` to
endpoint terms. -/
theorem Hurewicz.DegreeTwo.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    suspensionOne x (SingularChains.pathChain (GenLoop.toLoop (0 : Fin 2) p)) =
      SingularChains.inducedChain (squareMap p) 2 productSquareChain := by
  have h :=
    SingularHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 2) p).toContinuousMap (ContinuousMap.id (unitInterval)) 1
      intervalChain intervalChain
  rw [induced_intervalChain, SingularChains.inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((SingularChains.inducedChain (evaluation x) 2).comp
          (SingularChains.inducedChain
            ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
              (ContinuousMap.id (unitInterval)))
            2))
        productSquareChain =
      _
  rw [← SingularChains.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The singular `2`-chain of a based square `p`: the `squareMap`-pushforward of
`productSquareChain`. -/
def Hurewicz.DegreeTwo.squareChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    SingularChains.Chains X 2 :=
  suspensionOne x (SingularChains.pathChain (GenLoop.toLoop (0 : Fin 2) p))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `squareChain p` is the signed sum of the four side loop chains. -/
theorem Hurewicz.DegreeTwo.squareChain_boundary {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : SingularChains.boundaryTwo X (squareChain p) = 0 :=
  boundaryTwo_suspensionOne_of_cycle x _ (SingularChains.boundaryOne_loop (GenLoop.toLoop 0 p))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `2`-cycle of `X` built from a based square `p`. -/
def Hurewicz.DegreeTwo.squareCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  pathSquareCycle x (GenLoop.toLoop (0 : Fin 2) p)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology class `⟦squareCycle p⟧` of a based square: the Hurewicz image of
`p`. -/
def Hurewicz.DegreeTwo.squareHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
    (squareCycle p)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The square class equals the path-square class of the corresponding path of
loops. -/
theorem Hurewicz.DegreeTwo.squareHomologyClass_eq_pathSquareClass {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    squareHomologyClass p = pathSquareClass x (GenLoop.toLoop (0 : Fin 2) p) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Homotopic based squares have equal square homology classes. -/
theorem Hurewicz.DegreeTwo.squareHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x} (h : GenLoop.Homotopic p q) :
    squareHomologyClass p = squareHomologyClass q :=
  pathSquareClass_homotopic x (GenLoop.homotopicTo (0 : Fin 2) h)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `toLoop` of the constant square is the constant loop of loops. -/
theorem Hurewicz.DegreeTwo.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.const : GenLoop (Fin 2) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The square class of the constant square is `0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.squareHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    squareHomologyClass (GenLoop.const : GenLoop (Fin 2) X x) = 0 := by
  rw [squareHomologyClass_eq_pathSquareClass, toLoop_const, pathSquareClass_refl]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `toLoop` of a `transAt` concatenation is the concatenation of the `toLoop`s. -/
theorem Hurewicz.DegreeTwo.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.transAt (0 : Fin 2) p q) =
      (GenLoop.toLoop (0 : Fin 2) p).trans (GenLoop.toLoop (0 : Fin 2) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 2))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 2)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The square class is additive under `transAt` concatenation. -/
theorem Hurewicz.DegreeTwo.squareHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    squareHomologyClass (GenLoop.transAt (0 : Fin 2) p q) =
      squareHomologyClass p + squareHomologyClass q := by
  simp only [squareHomologyClass_eq_pathSquareClass, toLoop_transAt, pathSquareClass_trans]

/-- Postcomposition of a generalized loop by a continuous map `f`. -/
def Hurewicz.DegreeTwo.mapGenLoop {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : C(GenLoop N X x, GenLoop N Y (f x))
    where
  toFun p := ⟨f.comp p.val, fun t ht => congrArg f (p.property t ht)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

/-- `(mapGenLoop f x p).val = f.comp p.val`. -/
@[simp]
theorem Hurewicz.DegreeTwo.mapGenLoop_val {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop N X x) : (mapGenLoop f x p).val = f.comp p.val :=
  rfl

/-- `mapGenLoop` sends the constant loop to the constant loop. -/
@[simp]
theorem Hurewicz.DegreeTwo.mapGenLoop_const {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapGenLoop (N := N) f x GenLoop.const = GenLoop.const :=
  rfl

/-- `mapGenLoop` preserves loop homotopy. -/
theorem Hurewicz.DegreeTwo.mapGenLoop_homotopic {N X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f x p) (mapGenLoop f x q) :=
  h.comp_continuousMap f

/-- `mapGenLoop` commutes with `transAt` concatenation. -/
@[simp]
theorem Hurewicz.DegreeTwo.mapGenLoop_transAt {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] (f : C(X, Y)) (x : X) (i : N) (p q : GenLoop N X x) :
    mapGenLoop f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f x p) (mapGenLoop f x q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) = if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

/-- The Hurewicz map `π_ 2 X x → H_2 X` as a function: the square homology class of
a representative. -/
def Hurewicz.DegreeTwo.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x → SingularMayerVietoris.SingularHomology X 2 :=
  Quotient.lift squareHomologyClass (fun _ _ h => squareHomologyClass_homotopic h)

/-- The Hurewicz map `π_ 2 X x → H_2 X` as a monoid homomorphism to the
multiplicative homology group. -/
def Hurewicz.DegreeTwo.hurewiczPi2 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (squareHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 2 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (squareHomologyClass (GenLoop.transAt (0 : Fin 2) q p)) =
        Multiplicative.ofAdd (squareHomologyClass p + squareHomologyClass q)
    rw [squareHomologyClass_transAt, add_comm]

/-- The degree-two Hurewicz map `Additive (π_ 2 X x) →ₗ[ℤ] H_2 X`. -/
def Hurewicz.DegreeTwo.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 2 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2
    where
  toFun := (hurewiczPi2 x).toAdditiveLeft
  map_add' := (hurewiczPi2 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi2 x).toAdditiveLeft ℤ ℤ n a

/-- `hurewiczMap x ⟦p⟧` is the square homology class of `p`. -/
theorem Hurewicz.DegreeTwo.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 2) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (squareCycle p) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-! ### The prism operator -/

/-- The time-`t` slice of a homotopy `H : C(I × A, X)`, as a map `C(A, X)`. -/
def Hurewicz.DegreeTwo.SimplyConnected.timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  H.comp (SingularHomology.crossInsertLeft t)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The zero-degree left cross product with a point chain is the `crossInsertLeft`
pushforward. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.crossPoint_left {A : Type} [TopologicalSpace A] (n : ℕ)
    (t : (unitInterval)) (c : SingularChains.Chains A n) :
    SingularHomology.crossProductZeroLeft (unitInterval) A n (SingularChains.pointChain t)
        c =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft t) n c := by
  rw [SingularChains.pointChain, SingularHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The `H`-pushforward of a `crossInsertLeft t` chain is the `timeSlice H t`
pushforward. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.inducedChain_timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) (n : ℕ)
    (c : SingularChains.Chains A n) :
    SingularChains.inducedChain H n
        (SingularChains.inducedChain (SingularHomology.crossInsertLeft t) n c) =
      SingularChains.inducedChain (timeSlice H t) n c := by
  change
    ((SingularChains.inducedChain H n).comp
          (SingularChains.inducedChain (SingularHomology.crossInsertLeft t) n))
        c =
      _
  rw [← SingularChains.inducedChain_comp]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism operator of a homotopy `H : C(I × A, X)`: `Chains A n →ₗ[ℤ]
Chains X (n+1)`, built from the degree-`n` cross product with `intervalChain`. -/
def Hurewicz.DegreeTwo.SimplyConnected.prismOperator {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) :
    SingularChains.Chains A n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  (SingularChains.inducedChain H (n + 1)).comp
    (SingularHomology.crossProductEdge (unitInterval) A n Hurewicz.DegreeTwo.intervalChain)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `prismOperator n H c` is the `H`-pushforward of `c × intervalChain`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.prismOperator_apply {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) (c : SingularChains.Chains A n) :
    prismOperator n H c =
      SingularChains.inducedChain H (n + 1)
        (SingularHomology.crossProductEdge (unitInterval) A n
          Hurewicz.DegreeTwo.intervalChain c) :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism boundary identity: `∂(prism c) = H₁# c - H₀# c - prism(∂c)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.prismOperator_boundary {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (c : SingularChains.Chains A (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom (prismOperator (n + 1) H c) =
      SingularChains.inducedChain (timeSlice H 1) (n + 1) c -
          SingularChains.inducedChain (timeSlice H 0) (n + 1) c -
        prismOperator n H (((SingularChains.singularComplex A).d (n + 1) n).hom c) := by
  rw [prismOperator_apply, ← SingularChains.inducedChain_boundary,
    SingularHomology.crossProductEdge_boundary n]
  change
    SingularChains.inducedChain H (n + 1)
        (SingularHomology.crossProductZeroLeft (unitInterval) A (n + 1)
            (SingularChains.boundaryOne (unitInterval) Hurewicz.DegreeTwo.intervalChain) c -
          SingularHomology.crossProductEdge (unitInterval) A n
            Hurewicz.DegreeTwo.intervalChain
            (((SingularChains.singularComplex A).d (n + 1) n).hom c)) =
      _
  simp only [Hurewicz.DegreeTwo.intervalChain_boundary, map_sub, LinearMap.sub_apply, crossPoint_left,
    inducedChain_timeSlice, prismOperator_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- Precomposing the homotopy with `id × f` equals pushing the chain forward by `f` first. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.prismOperator_domain {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] (n : ℕ) (f : C(A, B)) (H : C((unitInterval) × B, X))
    (c : SingularChains.Chains A n) :
    prismOperator n (H.comp ((ContinuousMap.id (unitInterval)).prodMap f)) c =
      prismOperator n H (SingularChains.inducedChain f n c) := by
  have h :=
    SingularHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f n
      Hurewicz.DegreeTwo.intervalChain c
  rw [SingularChains.inducedChain_id, LinearMap.id_apply] at h
  simp only [prismOperator_apply, SingularChains.inducedChain_comp, LinearMap.comp_apply]
  exact congrArg (SingularChains.inducedChain H (n + 1)) h

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The prism chain of a homotopy of the standard `n`-simplex:
`prismOperator n H` applied to the identity simplex chain. -/
def Hurewicz.DegreeTwo.SimplyConnected.simplexPrism {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : C((unitInterval) × SingularChains.Simplex n, X)) : SingularChains.Chains X (n + 1) :=
  prismOperator n H
    (SingularChains.simplexChain (SingularChains.Simplex n) n
      (ContinuousMap.id (SingularChains.Simplex n)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `prismOperator` on a simplex chain is the `H`-pushforward of the simplex prism. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.prismOperator_simplex {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (smp : SingularChains.SingularSimplex A n) :
    prismOperator n H (SingularChains.simplexChain A n smp) =
      simplexPrism n (H.comp ((ContinuousMap.id (unitInterval)).prodMap smp)) := by
  have h :=
    prismOperator_domain n smp H
      (SingularChains.simplexChain (SingularChains.Simplex n) n
        (ContinuousMap.id (SingularChains.Simplex n)))
  rw [SingularChains.inducedChain_simplex, ContinuousMap.comp_id] at h
  exact h.symm

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The boundary of `simplexPrism n H` is `H₁# id - H₀# id - ∑` face prisms. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexPrism_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (H : C((unitInterval) × SingularChains.Simplex (n + 1), X)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom (simplexPrism (n + 1) H) =
      SingularChains.simplexChain X (n + 1) (timeSlice H 1) -
          SingularChains.simplexChain X (n + 1) (timeSlice H 0) -
        ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ i.val •
            simplexPrism n
              (H.comp
                ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i))) := by
  rw [simplexPrism, prismOperator_boundary, SingularChains.inducedChain_simplex,
    SingularChains.inducedChain_simplex, ContinuousMap.comp_id, ContinuousMap.comp_id]
  rw [SingularChains.boundary_simplex, map_sum]
  simp only [map_zsmul, ContinuousMap.id_comp, prismOperator_simplex]

/-- The endpoint operator `Chains X n →ₗ[ℤ] Chains X n` sending each simplex to its
time-`t` slice under `H`. -/
def Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (t : (unitInterval)) : SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X n :=
  SingularChains.chainLift X n fun smp => SingularChains.simplexChain X n (timeSlice (H smp) t)

/-- `simplexEndpointOperator` sends a simplex to its time-`t` slice `timeSlice (H
smp) t`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (t : (unitInterval)) (smp : SingularChains.SingularSimplex X n) :
    simplexEndpointOperator n H t (SingularChains.simplexChain X n smp) =
      SingularChains.simplexChain X n (timeSlice (H smp) t) :=
  SingularChains.chainLift_simplex X n _ smp

/-- The simplexwise prism operator: `Chains X n →ₗ[ℤ] Chains X (n+1)` sending each
simplex `smp` to `simplexPrism n (H smp)`. -/
def Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X)) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  SingularChains.chainLift X n fun smp => simplexPrism n (H smp)

/-- `simplexPrismOperator` sends a simplex `smp` to `simplexPrism n (H smp)`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (smp : SingularChains.SingularSimplex X n) :
    simplexPrismOperator n H (SingularChains.simplexChain X n smp) = simplexPrism n (H smp) :=
  SingularChains.chainLift_simplex X n _ smp

/-- `H` and `H'` are face-compatible if `H'` restricted to each face equals `H` of
the face simplex. -/
def Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X)) :
    Prop :=
  ∀ smp i,
    (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
      H (smp.comp (SingularChains.simplexFace n i))

/-- For face-compatible families, the `i`-th face of a time slice of `H'` is the corresponding time slice of `H`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.timeSlice_face {X : Type} [TopologicalSpace X] {n : ℕ}
    {H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X)}
    {H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X)}
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (t : (unitInterval)) :
    (timeSlice (H' smp) t).comp (SingularChains.simplexFace n i) =
      timeSlice (H (smp.comp (SingularChains.simplexFace n i))) t :=
  congrArg (fun F => timeSlice F t) (h smp i)

/-- For a face-compatible family, `simplexEndpointOperator` commutes with the
boundary map. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (t : (unitInterval))
    (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 1) n).hom (simplexEndpointOperator (n + 1) H' t c) =
      simplexEndpointOperator n H t (((SingularChains.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((SingularChains.singularComplex X).d (n + 1) n).hom).comp
        (simplexEndpointOperator (n + 1) H' t) =
      (simplexEndpointOperator n H t).comp ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, simplexEndpointOperator_simplex,
      SingularChains.boundary_simplex, map_sum, map_zsmul, timeSlice_face h]
  exact LinearMap.congr_fun hc c

/-- For a face-compatible family, the simplexwise prism boundary identity holds:
`∂(prism c) = H₁# c - H₀# c - prism(∂c)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexPrismOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (c : SingularChains.Chains X (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom
        (simplexPrismOperator (n + 1) H' c) =
      simplexEndpointOperator (n + 1) H' 1 c - simplexEndpointOperator (n + 1) H' 0 c -
        simplexPrismOperator n H (((SingularChains.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom).comp
        (simplexPrismOperator (n + 1) H') =
      simplexEndpointOperator (n + 1) H' 1 - simplexEndpointOperator (n + 1) H' 0 -
        (simplexPrismOperator n H).comp ((SingularChains.singularComplex X).d (n + 1) n).hom := by
    apply SingularChains.chainMap_ext X (n + 1)
    intro smp
    have hface := h smp
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, simplexPrismOperator_simplex,
      simplexPrism_boundary, simplexEndpointOperator_simplex, SingularChains.boundary_simplex,
      map_sum, map_zsmul, hface]
  exact LinearMap.congr_fun hc c

/-- If every homotopy starts at its simplex, the time-`0` endpoint operator is the identity. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexEndpointOperator_zero {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (h₀ : ∀ smp, timeSlice (H smp) 0 = smp) : simplexEndpointOperator n H 0 = LinearMap.id := by
  apply SingularChains.chainMap_ext X n
  intro smp
  rw [simplexEndpointOperator_simplex, h₀]
  rfl

/-- The `2`-cycle obtained by applying the time-`1` endpoint operator of `H₂` to a
`2`-cycle `c`. -/
def Hurewicz.DegreeTwo.SimplyConnected.straightenedTwoCycle {X : Type} [TopologicalSpace X]
    (H₁ : SingularChains.SingularSimplex X 1 → C((unitInterval) × SingularChains.Simplex 1, X))
    (H₂ : SingularChains.SingularSimplex X 2 → C((unitInterval) × SingularChains.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (simplexEndpointOperator 2 H₂ 1 c.1)
    (by
      rw [simplexEndpointOperator_boundary 1 H₁ H₂ h,
        SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2
          c,
        map_zero])

/-- The straightened `2`-cycle is homologous to the original cycle (the prism is
its homology witness). -/
theorem Hurewicz.DegreeTwo.SimplyConnected.straightenedTwoCycle_class {X : Type} [TopologicalSpace X]
    (H₁ : SingularChains.SingularSimplex X 1 → C((unitInterval) × SingularChains.Simplex 1, X))
    (H₂ : SingularChains.SingularSimplex X 2 → C((unitInterval) × SingularChains.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂) (h₀ : ∀ smp, timeSlice (H₂ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (straightenedTwoCycle H₁ H₂ h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 2 _
        _).mpr
  refine ⟨simplexPrismOperator 2 H₂ c.1, ?_⟩
  rw [simplexPrismOperator_boundary 1 H₁ H₂ h, simplexEndpointOperator_zero 2 H₂ h₀,
    SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 c,
    map_zero, sub_zero]
  rfl

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

/-! ### The tetrahedron boundary and square rotation -/

/-- The one-skeleton of the tetrahedron: points with at least two vanishing
barycentric coordinates. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronOneSkeleton : Set (SingularChains.Simplex 3) :=
  {s | ∃ i j : Fin 4, i ≠ j ∧ s i = 0 ∧ s j = 0}

/-- A based tetrahedron at `x`: a `3`-simplex map sending the one-skeleton to `x`. -/
def Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(SingularChains.Simplex 3, X) // ∀ s ∈ tetrahedronOneSkeleton, τ s = x }

/-- Each face map of the triangle lands in `triangleBoundary`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_triangleBoundary (i : Fin 4)
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    SingularChains.simplexFace 2 i s ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, SingularChains.simplexFace_apply_self 2 i s,
      (SingularChains.simplexFace_apply_succAbove 2 i s j).trans hj⟩

/-- The `i`-th face of a based tetrahedron, as a based triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedronFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTetrahedron x) (i : Fin 4) : BasedTriangle x :=
  ⟨τ.val.comp (SingularChains.simplexFace 2 i), fun s hs =>
    τ.property _ (simplexFace_triangleBoundary i s hs)⟩

/-- The linear blend between two simplex values of a tetrahedron. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend {n : ℕ} (t : (unitInterval))
    (a b : SingularChains.Simplex n) : SingularChains.Simplex n :=
  ⟨(1 - (t : ℝ)) • (a : Fin (n + 1) → ℝ) + (t : ℝ) • (b : Fin (n + 1) → ℝ),
    convex_stdSimplex ℝ _ a.property b.property (sub_nonneg.mpr t.property.2) t.property.1
      (by ring)⟩

/-- At `t = 0` the tetrahedron blend is the first map. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_zero {n : ℕ}
    (a b : SingularChains.Simplex n) : tetrahedronSimplexBlend 0 a b = a := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) * a i + (0 : ℝ) * b i = a i
  simp

/-- At `t = 1` the tetrahedron blend is the second map. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_one {n : ℕ}
    (a b : SingularChains.Simplex n) : tetrahedronSimplexBlend 1 a b = b := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) * a i + (1 : ℝ) * b i = b i
  simp

/-- Blending a simplex point with itself is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_self {n : ℕ} (t : (unitInterval))
    (a : SingularChains.Simplex n) : tetrahedronSimplexBlend t a a = a := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * a i + (t : ℝ) * a i = a i
  ring

/-- The blend of two tetrahedron maps as a continuous map on the cylinder. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlendMap {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (f g : C(Y, SingularChains.Simplex n)) :
    C((unitInterval) × Y, SingularChains.Simplex n)
    where
  toFun p := tetrahedronSimplexBlend p.1 (f p.2) (g p.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change
      Continuous fun p : (unitInterval) × Y => (1 - (p.1 : ℝ)) * f p.2 i + (p.1 : ℝ) * g p.2 i
    have hf : Continuous fun p : (unitInterval) × Y => f p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
    have hg : Continuous fun p : (unitInterval) × Y => g p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (g.continuous.comp continuous_snd))
    exact
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hf).add
        ((continuous_subtype_val.comp continuous_fst).mul hg)

/-- A coordinate vanishing at both endpoints of a blend vanishes throughout. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate {n : ℕ}
    (t : (unitInterval)) (a b : SingularChains.Simplex n) (i : Fin (n + 1)) (ha : a i = 0)
    (hb : b i = 0) : tetrahedronSimplexBlend t a b i = 0 := by
  change (1 - (t : ℝ)) * a i + (t : ℝ) * b i = 0
  simp [ha, hb]

/-- Face `0` of a `2`-simplex is `![0, s 0, s 1, s 2]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_zero (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 0 s : Fin 4 → ℝ) = ![0, s 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_self 2 0 s
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 2

/-- Face `1` of a `2`-simplex is `![s 0, 0, s 1, s 2]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_one (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 1 s : Fin 4 → ℝ) = ![s 0, 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 0
  · exact SingularChains.simplexFace_apply_self 2 1 s
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 2

/-- Face `2` of a `2`-simplex is `![s 0, s 1, 0, s 2]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_two (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 2 s : Fin 4 → ℝ) = ![s 0, s 1, 0, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 1
  · exact SingularChains.simplexFace_apply_self 2 2 s
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 2

/-- Face `3` of a `2`-simplex is `![s 0, s 1, s 2, 0]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.simplexFace_two_three (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 3 s : Fin 4 → ℝ) = ![s 0, s 1, s 2, 0] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 2
  · exact SingularChains.simplexFace_apply_self 2 3 s

/-- A `3`-simplex map is a based tetrahedron if its one-skeleton restrictions are
constant at `x`. -/
def Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron.ofFaces {X : Type} [TopologicalSpace X]
    {x : X} (τ : C(SingularChains.Simplex 3, X))
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ Hurewicz.DegreeTwo.SimplyConnected.triangleBoundary,
          (τ.comp (SingularChains.simplexFace 2 i)) s = x) :
    Hurewicz.DegreeTwo.SimplyConnected.BasedTetrahedron x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := Hurewicz.DegreeTwo.SimplyConnected.simplexFaceInverse 2 i ⟨s, hi⟩
    have ht : t ∈ Hurewicz.DegreeTwo.SimplyConnected.triangleBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (SingularChains.simplexFace 2 i t) = x at he
    rw [show SingularChains.simplexFace 2 i t = s from
        Hurewicz.DegreeTwo.SimplyConnected.simplexFace_inverse 2 i ⟨s, hi⟩] at he
    exact he⟩

/-- The first quadrilateral filling the tetrahedron boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 3)
    where
  toFun
    u :=
    ⟨![1 - Max.max (u 0 : ℝ) (u 1 : ℝ), (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        Min.min (u 0 : ℝ) (u 1 : ℝ), (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (u 1).property.1
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
        · rw [min_eq_left h, max_eq_right h]
          ring
        · rw [min_eq_right h, max_eq_left h]
          ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

/-- `tetrahedronQuadrilateralA` sends the square boundary into the tetrahedron `1`-skeleton. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_boundary
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u ∈ tetrahedronOneSkeleton := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hi
      refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 0).property.1]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 1).property.2,
          max_eq_left (u 1).property.2]
    · change u 1 = 1 at hi
      refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 0).property.2,
          max_eq_right (u 0).property.2]

/-- The diagonal of `tetrahedronQuadrilateralA` lands in the `1`-skeleton. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_diagonal (t : (unitInterval)) :
    tetrahedronQuadrilateralA ![t, t] ∈ tetrahedronOneSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩ <;> simp [DFunLike.coe, tetrahedronQuadrilateralA]

/-- The cyclic shift of a `3`-simplex, `s ↦ ![s 3, s 0, s 1, s 2]`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift :
    C(SingularChains.Simplex 3, SingularChains.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 3, s 0, s 1, s 2], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val

/-- The cyclic index permutation `Fin 4 ≃ Fin 4` behind `tetrahedronQuarterShift`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterIndex : Fin 4 ≃ Fin 4
    where
  toFun i := ![1, 2, 3, 0] i
  invFun i := ![3, 0, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- `tetrahedronQuarterShift s` has `s i` at index `tetrahedronQuarterIndex i`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_index (s : SingularChains.Simplex 3)
    (i : Fin 4) : tetrahedronQuarterShift s (tetrahedronQuarterIndex i) = s i := by
  fin_cases i <;> rfl

/-- `tetrahedronQuarterShift` preserves the tetrahedron `1`-skeleton. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_oneSkeleton
    (s : SingularChains.Simplex 3) (hs : s ∈ tetrahedronOneSkeleton) :
    tetrahedronQuarterShift s ∈ tetrahedronOneSkeleton := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact
    ⟨tetrahedronQuarterIndex i, tetrahedronQuarterIndex j, fun h =>
      hij (tetrahedronQuarterIndex.injective h), by simpa, by simpa⟩

/-- The based square loop `τ ∘ tetrahedronQuadrilateralA`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp tetrahedronQuadrilateralA, fun u hu =>
    τ.property _ (tetrahedronQuadrilateralA_boundary u hu)⟩

/-- The quadrilateral loop sends diagonal points to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuadrilateralA_diagonal t)

/-- The based square loop `τ ∘ tetrahedronQuadrilateralB`. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedQuadrilateralLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA), fun u hu =>
    τ.property _
      (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_boundary u hu))⟩

/-- The shifted quadrilateral loop sends diagonal points to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronShiftedQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_diagonal t))

/-- The quarter-turn rotation of the square `I × I` about its center. -/
def Hurewicz.DegreeTwo.SimplyConnected.quarterTurn : C(Fin 2 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u 1, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

/-- `quarterTurn u = ![u 1, 1 - u 0]`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurn_apply (u : Fin 2 → (unitInterval)) :
    quarterTurn u = ![u 1, (unitInterval.symm) (u 0)] :=
  rfl

/-- `quarterTurn` preserves the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurn_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : quarterTurn u ∈ Cube.boundary (Fin 2) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨1, Or.inr (by simp [hi])⟩
    · exact ⟨0, Or.inl (by simpa using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨1, Or.inl (by simp [hi])⟩
    · exact ⟨0, Or.inr (by simpa using hi)⟩

/-- The based square loop `p ∘ quarterTurn`. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp quarterTurn, fun u hu => p.property _ (quarterTurn_boundary u hu)⟩

/-- The rotation vector field on the square used for the rotation homotopy. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationVector (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

/-- The norm of the rotation vector. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationVector_norm (v : ℝ × ℝ) :
    ‖rotationVector v‖ = ‖v‖ := by simp [rotationVector, Prod.norm_def, max_comm]

/-- The affine blend `((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)` interpolating `v` toward `rotationVector v`. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationBlend (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)

/-- At `t = 0` the rotation blend is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_zero (v : ℝ × ℝ) : rotationBlend 0 v = v := by
  ext <;> simp [rotationBlend]

/-- At `t = 1` the rotation blend reaches `rotationVector v`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_one (v : ℝ × ℝ) :
    rotationBlend 1 v = rotationVector v := by ext <;> simp [rotationBlend, rotationVector]

/-- For every `t`, `rotationBlend t 0 = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_zero_vector (t : ℝ) :
    rotationBlend t 0 = 0 := by ext <;> simp [rotationBlend]

/-- The rotation blend is nonzero off the center. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_ne_zero (t : ℝ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    rotationBlend t v ≠ 0 := by
  intro h
  have h₁ : (1 - t) * v.1 + t * v.2 = 0 := congrArg Prod.fst h
  have h₂ : (1 - t) * v.2 - t * v.1 = 0 := congrArg Prod.snd h
  have hd : (1 - t) ^ 2 + t ^ 2 ≠ 0 := by
    have hp : 0 < (1 - t) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    exact ne_of_gt hp
  have ha : ((1 - t) ^ 2 + t ^ 2) * v.1 = 0 := by linear_combination (1 - t) * h₁ - t * h₂
  have hb : ((1 - t) ^ 2 + t ^ 2) * v.2 = 0 := by linear_combination t * h₁ + (1 - t) * h₂
  apply hv
  exact Prod.ext (mul_eq_zero.mp ha |>.resolve_left hd) (mul_eq_zero.mp hb |>.resolve_left hd)

/-- The rotation blend is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationBlend_continuous :
    Continuous (fun z : ℝ × (ℝ × ℝ) => rotationBlend z.1 z.2) := by
  unfold rotationBlend
  fun_prop

/-- The centered square coordinates `(2 * u 0 - 1, 2 * u 1 - 1)`. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationCentered (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (2 * (u 0 : ℝ) - 1, 2 * (u 1 : ℝ) - 1)

/-- The centering map is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationCentered_continuous :
    Continuous rotationCentered := by
  unfold rotationCentered
  fun_prop

/-- The centered coordinates have norm at most `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationCentered_norm_le (u : Fin 2 → (unitInterval)) :
    ‖rotationCentered u‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  constructor <;> rw [Real.norm_eq_abs, abs_le]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 0).property.1, (u 0).property.2]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 1).property.1, (u 1).property.2]

/-- On the square boundary, the centered coordinates have norm `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationCentered_norm_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : ‖rotationCentered u‖ = 1 := by
  apply le_antisymm (rotationCentered_norm_le u)
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 0 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)
  · fin_cases i
    · change u 0 = 1 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 1 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)

/-- The normalizing denominator for radial projection to the boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationDenominator (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ :=
  1 - ‖rotationCentered u‖ + ‖rotationBlend t (rotationCentered u)‖

/-- The rotation denominator is positive. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationDenominator_pos (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : 0 < rotationDenominator t u := by
  by_cases hv : rotationCentered u = 0
  · simp [rotationDenominator, hv]
  · have hnorm : 0 < ‖rotationBlend t (rotationCentered u)‖ :=
      norm_pos_iff.mpr (rotationBlend_ne_zero t hv)
    have hle := rotationCentered_norm_le u
    unfold rotationDenominator
    linarith

/-- The rotation denominator is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationDenominator_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationDenominator z.1 z.2) := by
  unfold rotationDenominator
  apply Continuous.add
  · exact continuous_const.sub (rotationCentered_continuous.comp continuous_snd).norm
  · apply Continuous.norm
    exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

/-- The radial normalization of centered square coordinates to the boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (rotationDenominator t u)⁻¹ • rotationBlend t (rotationCentered u)

/-- The radial normalization is continuous. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationNormalized z.1 z.2) := by
  unfold rotationNormalized
  apply
    Continuous.smul (f := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      (rotationDenominator z.1 z.2)⁻¹) (g := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      rotationBlend z.1 (rotationCentered z.2))
  · exact
      rotationDenominator_continuous.inv₀ (fun z => ne_of_gt (rotationDenominator_pos z.1 z.2))
  · exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

/-- The normalized coordinates stay within the boundary norm. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_norm_le (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ‖rotationNormalized t u‖ ≤ 1 := by
  have hd := rotationDenominator_pos t u
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [inv_mul_le_iff₀ hd, mul_one]
  unfold rotationDenominator
  linarith [rotationCentered_norm_le u]

/-- On the boundary the normalization is the identity. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_norm_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ‖rotationNormalized t u‖ = 1 := by
  have hd := rotationDenominator_pos t u
  have he : rotationDenominator t u = ‖rotationBlend t (rotationCentered u)‖ := by
    simp [rotationDenominator, rotationCentered_norm_boundary u hu]
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [← he, inv_mul_cancel₀ (ne_of_gt hd)]

/-- At `t = 0` the normalization is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_zero (u : Fin 2 → (unitInterval)) :
    rotationNormalized 0 u = rotationCentered u := by
  simp [rotationNormalized, rotationDenominator]

/-- At `t = 1` the normalization reaches the quarter-turned boundary point. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationNormalized_one (u : Fin 2 → (unitInterval)) :
    rotationNormalized 1 u = rotationVector (rotationCentered u) := by
  simp [rotationNormalized, rotationDenominator]

/-- The uncentering map (adding the center back). -/
def Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    Fin 2 → (unitInterval) :=
  ![⟨(v.1 + 1) / 2,
      by
      have h := abs_le.mp (show |v.1| ≤ 1 from (norm_fst_le v).trans hv)
      constructor <;> linarith⟩,
    ⟨(v.2 + 1) / 2,
      by
      have h := abs_le.mp (show |v.2| ≤ 1 from (norm_snd_le v).trans hv)
      constructor <;> linarith⟩]

/-- `rotationUncenter` respects equality. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_congr {v w : ℝ × ℝ} {hv : ‖v‖ ≤ 1}
    {hw : ‖w‖ ≤ 1} (h : v = w) : rotationUncenter v hv = rotationUncenter w hw := by
  subst w
  rfl

/-- `rotationUncenter` of centered coordinates recovers the point. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_centered (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationCentered u) (rotationCentered_norm_le u) = u := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> dsimp [rotationUncenter, rotationCentered] <;> ring

/-- `rotationUncenter` applied to the rotated vector. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_vector (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationVector (rotationCentered u))
        (by simpa using rotationCentered_norm_le u) =
      quarterTurn u := by
  rw [quarterTurn_apply]
  funext i
  fin_cases i <;> apply Subtype.ext <;>
      dsimp [rotationUncenter, rotationVector, rotationCentered, unitInterval.symm] <;>
    ring

/-- `rotationUncenter` preserves the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotationUncenter_boundary (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1)
    (he : ‖v‖ = 1) : rotationUncenter v hv ∈ Cube.boundary (Fin 2) := by
  have hm : 1 ≤ Max.max |v.1| |v.2| := by simpa [Prod.norm_def, Real.norm_eq_abs] using he.ge
  rcases le_max_iff.mp hm with ha | hb
  · have hn : |v.1| = 1 := le_antisymm ((norm_fst_le v).trans hv) ha
    by_cases hp : 0 ≤ v.1
    · have h : v.1 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.1 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨0, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
  · have hn : |v.2| = 1 := le_antisymm ((norm_snd_le v).trans hv) hb
    by_cases hp : 0 ≤ v.2
    · have h : v.2 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.2 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨1, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith

/-- The homotopy map rotating the square by a quarter turn. -/
def Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap :
    C((unitInterval) × (Fin 2 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun z := rotationUncenter (rotationNormalized z.1 z.2) (rotationNormalized_norm_le z.1 z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).1 + 1) / 2)
      exact (rotationNormalized_continuous.fst.add continuous_const).div_const 2
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).2 + 1) / 2)
      exact (rotationNormalized_continuous.snd.add continuous_const).div_const 2

/-- At time `0` the quarter-turn homotopy is the identity. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_zero (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (0, u) = u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 0 u)
          (rotationNormalized_zero u)).trans
      (rotationUncenter_centered u)

/-- At time `1` the quarter-turn homotopy is the quarter turn. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_one (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (1, u) = quarterTurn u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 1 u)
          (rotationNormalized_one u)).trans
      (rotationUncenter_vector u)

/-- The quarter-turn homotopy preserves the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.quarterTurnHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurnHomotopyMap (t, u) ∈ Cube.boundary (Fin 2) :=
  rotationUncenter_boundary (rotationNormalized t u) (rotationNormalized_norm_le t u)
    (rotationNormalized_norm_boundary t u hu)

/-- The homotopy from a based square to its quarter-turned rotation. -/
def Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop_homotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (rotatedSquareLoop p).val (Cube.boundary (Fin 2))
    where
  toFun z := p (quarterTurnHomotopyMap z)
  continuous_toFun := p.val.continuous.comp quarterTurnHomotopyMap.continuous
  map_zero_left u := congrArg p (quarterTurnHomotopyMap_zero u)
  map_one_left u := congrArg p (quarterTurnHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (quarterTurnHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

/-- The rotated square loop has the same `π_2`-class: `⟦rotatedSquareLoop p⟧ = ⟦p⟧`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.rotatedSquareLoop_class {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) : (⟦rotatedSquareLoop p⟧ : π_ 2 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦rotatedSquareLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (rotatedSquareLoop p) from ⟨rotatedSquareLoop_homotopy p⟩)
  exact h.symm

/-- The second quadrilateral filling the tetrahedron boundary. -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralB :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 3) :=
  (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA).comp quarterTurn

/-- The perimeter relation between the two quadrilateral fillings. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateral_perimeter
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u = tetrahedronQuadrilateralB u := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuarterShift_zero (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 0 = s 3 := rfl
  have tetrahedronQuarterShift_one (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 1 = s 0 := rfl
  have tetrahedronQuarterShift_two (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 2 = s 1 := rfl
  have tetrahedronQuarterShift_three (s : SingularChains.Simplex 3) :
    tetrahedronQuarterShift s 3 = s 2 := rfl
  have tetrahedronQuadrilateralB_apply (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralB u =
      tetrahedronQuarterShift (tetrahedronQuadrilateralA ![u 1, (unitInterval.symm) (u 0)]) :=
    rfl
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA u j = tetrahedronQuadrilateralB u j
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 1).property.2, max_eq_right (u 1).property.2,
          min_eq_left (u 1).property.1, max_eq_right (u 1).property.1]
    · change u 1 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 0).property.1, max_eq_left (u 0).property.1, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 1).property.2, max_eq_left (u 1).property.2,
          min_eq_right (u 1).property.1, max_eq_left (u 1).property.1]
    · change u 1 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 0).property.2, max_eq_right (u 0).property.2, (u 0).property.1]

/-- The homotopy between the two quadrilateral fillings of a based tetrahedron
(using `Subsingleton (π_2)`). -/
def Hurewicz.DegreeTwo.SimplyConnected.tetrahedronFillingsHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (tetrahedronQuadrilateralLoop τ).val.HomotopyRel
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (tetrahedronQuadrilateralA p.2)
        (tetrahedronQuadrilateralB p.2))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap tetrahedronQuadrilateralA tetrahedronQuadrilateralB).continuous
  map_zero_left
    u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (tetrahedronQuadrilateralB u)
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu := by
    change τ.val (tetrahedronSimplexBlend t _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [← tetrahedronQuadrilateral_perimeter u hu, tetrahedronSimplexBlend_self]

/-- The two quadrilateral fillings are homotopic rel boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronFillings_homotopic {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    GenLoop.Homotopic (tetrahedronQuadrilateralLoop τ)
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)) :=
  ⟨tetrahedronFillingsHomotopy τ⟩

/-- The two quadrilateral fillings have equal `π_2`-classes. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronFillings_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (⟦tetrahedronQuadrilateralLoop τ⟧ : π_ 2 X x) = ⟦tetrahedronShiftedQuadrilateralLoop τ⟧ :=
  (Quotient.sound (tetrahedronFillings_homotopic τ)).trans
    (rotatedSquareLoop_class (tetrahedronShiftedQuadrilateralLoop τ))

/-! ### Cyclic permutation of the triangle -/

/-- The cyclic permutation of the triangle's vertices. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleCyclicPermutation :
    C(SingularChains.Simplex 2, SingularChains.Simplex 2)
    where
  toFun
    s :=
    ⟨![s 1, s 2, s 0], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + s 2) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

/-- The cyclic permutation preserves the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleCyclicPermutation_boundary
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleCyclicPermutation s ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩

/-- The cyclic permutation of a based triangle is again based. -/
def Hurewicz.DegreeTwo.SimplyConnected.cyclicBasedTriangle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : BasedTriangle x :=
  ⟨τ.val.comp triangleCyclicPermutation, fun s hs =>
    τ.property _ (triangleCyclicPermutation_boundary s hs)⟩

/-- The cyclically permuted triangle quotient agrees at the common zero face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.cyclicTriangleQuotient_commonZero
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3,
      triangleCyclicPermutation (triangleCubeQuotient u) i = 0 ∧
        triangleCubeQuotient (quarterTurn u) i = 0 := by
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have triangleCyclicPermutation_zero (s : SingularChains.Simplex 2) :
    triangleCyclicPermutation s 0 = s 1 := rfl
  have triangleCyclicPermutation_one (s : SingularChains.Simplex 2) :
    triangleCyclicPermutation s 1 = s 2 := rfl
  have triangleCyclicPermutation_two (s : SingularChains.Simplex 2) :
    triangleCyclicPermutation s 2 = s 0 := rfl
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_left (u 1).property.1, min_eq_left (u 1).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩
      · simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_right (u 0).property.1]
      · simp [triangleCubeQuotient_apply, hi, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_two, hi,
          min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_zero, hi,
          min_eq_left (u 0).property.2]

/-- The blend of the cyclically permuted cube quotient with the quarter-turned quotient stays in the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.cyclicTriangleQuotient_blend_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronSimplexBlend t (triangleCyclicPermutation (triangleCubeQuotient u))
        (triangleCubeQuotient (quarterTurn u)) ∈
      triangleBoundary := by
  obtain ⟨i, hi, hj⟩ := cyclicTriangleQuotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

/-- The `HomotopyRel` from the cyclically permuted based-triangle loop to its rotated square loop. -/
def Hurewicz.DegreeTwo.SimplyConnected.cyclicTriangleLoopHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop (cyclicBasedTriangle τ)).val.HomotopyRel
      (rotatedSquareLoop (basedTriangleLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (triangleCyclicPermutation (triangleCubeQuotient p.2))
        (triangleCubeQuotient (quarterTurn p.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap (triangleCyclicPermutation.comp triangleCubeQuotient)
          (triangleCubeQuotient.comp quarterTurn)).continuous
  map_zero_left
    u := by
    change
      τ.val (tetrahedronSimplexBlend 0 _ _) =
        τ.val (triangleCyclicPermutation (triangleCubeQuotient u))
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (triangleCubeQuotient (quarterTurn u))
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu :=
    (τ.property _ (cyclicTriangleQuotient_blend_boundary t u hu)).trans
      ((basedTriangleLoop (cyclicBasedTriangle τ)).property u hu).symm

/-- Cyclic permutation of a based triangle preserves its `π_2`-class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleClass_cyclic {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    basedTriangleClass (cyclicBasedTriangle τ) = basedTriangleClass τ := by
  have h :
    GenLoop.Homotopic (basedTriangleLoop (cyclicBasedTriangle τ))
      (rotatedSquareLoop (basedTriangleLoop τ)) :=
    ⟨cyclicTriangleLoopHomotopy τ⟩
  have he :
    (⟦basedTriangleLoop (cyclicBasedTriangle τ)⟧ : π_ 2 X x) =
      ⟦rotatedSquareLoop (basedTriangleLoop τ)⟧ :=
    Quotient.sound h
  exact congrArg Additive.ofMul (he.trans (rotatedSquareLoop_class (basedTriangleLoop τ)))

/-! ### Subdivision of the square -/

/-- The subdivision square `Fin 2 → unitInterval`. -/
abbrev Hurewicz.DegreeTwo.SimplyConnected.SubdivisionSquare :=
  Fin 2 → (unitInterval)

/-- A boundary point of the subdivision square has some coordinate equal to `0` or `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSquare_boundary_cases (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : u 0 = 0 ∨ u 0 = 1 ∨ u 1 = 0 ∨ u 1 = 1 := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

/-- Two square points share a `0`-coordinate, a `1`-coordinate, or lie on the diagonal. -/
inductive Hurewicz.DegreeTwo.SimplyConnected.SubdivisionSameSide (a b : SubdivisionSquare) : Prop
  | zero (i : Fin 2) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 2) (ha : a i = 1) (hb : b i = 1)
  | diagonal (ha : a 0 = a 1) (hb : b 0 = b 1)

/-- The blend between subdivision square points. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend (t : (unitInterval))
    (a b : SubdivisionSquare) : SubdivisionSquare := fun i => Set.Icc.convexComb (a i) (b i) t

/-- At `t = 0` the subdivision blend is the first point. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend_zero (a b : SubdivisionSquare) :
    subdivisionBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

/-- At `t = 1` the subdivision blend is the second point. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend_one (a b : SubdivisionSquare) :
    subdivisionBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

/-- The blend of two subdivision maps as a continuous map. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlendMap
    (f g : C(SubdivisionSquare, SubdivisionSquare)) :
    C((unitInterval) × SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := subdivisionBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

/-- A point on the subdivision diagonal. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionOnDiagonal {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (a : SubdivisionSquare) (ha : a 0 = a 1) : p a = x := by
  have h : a = ![a 0, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact ha.symm
  exact (congrArg p h).trans (hd _)

/-- For same-side maps, the blend stays based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionBlend_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    {a b : SubdivisionSquare} (h : SubdivisionSameSide a b) (t : (unitInterval)) :
    p (subdivisionBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
    apply p.property
    exact ⟨i, Or.inl (by simp [subdivisionBlend, ha, hb])⟩
  | one i ha hb =>
    apply p.property
    exact ⟨i, Or.inr (by simp [subdivisionBlend, ha, hb])⟩
  | diagonal ha hb =>
    apply subdivisionOnDiagonal p hd
    simp only [subdivisionBlend, ha, hb]

/-- The pullback of a based square along a subdivision map. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionPullbackLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp f, hf⟩

/-- The linear homotopy between subdivision pullbacks along same-side maps. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLinearHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (f g : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 2), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 2), SubdivisionSameSide (f u) (g u)) :
    (subdivisionPullbackLoop p f hf).val.HomotopyRel (subdivisionPullbackLoop p g hg).val
      (Cube.boundary (Fin 2))
    where
  toFun u := p (subdivisionBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (subdivisionBlendMap f g).continuous
  map_zero_left
    u := by
    change p (subdivisionBlend 0 (f u) (g u)) = p (f u)
    rw [subdivisionBlend_zero]
  map_one_left
    u := by
    change p (subdivisionBlend 1 (f u) (g u)) = p (g u)
    rw [subdivisionBlend_one]
  prop' t u hu := (subdivisionBlend_based p hd (hfg u hu) t).trans (hf u hu).symm

/-- `u - min (u, v)` as a point of the unit interval. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin (u v : (unitInterval)) : (unitInterval) :=
  ⟨(u : ℝ) - Min.min (u : ℝ) (v : ℝ), sub_nonneg.mpr (min_le_left _ _),
    (sub_le_self _ (le_min u.property.1 v.property.1)).trans u.property.2⟩

/-- `subdivisionSubMin 0 v = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_zero_left (v : (unitInterval)) :
    subdivisionSubMin 0 v = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.1]

/-- `subdivisionSubMin u 0 = u`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_zero_right (u : (unitInterval)) :
    subdivisionSubMin u 0 = u := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.1]

/-- `subdivisionSubMin 1 v = 1 - v`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_one_left (v : (unitInterval)) :
    subdivisionSubMin 1 v = (unitInterval.symm) v := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.2]

/-- `subdivisionSubMin u 1 = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionSubMin_one_right (u : (unitInterval)) :
    subdivisionSubMin u 1 = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.2]

/-- The product map onto the lower triangle of the subdivision. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, u 0 * u 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => u 0 * u 1
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp (continuous_apply 0)).mul
          (continuous_subtype_val.comp (continuous_apply 1))

/-- The product map onto the upper triangle of the subdivision. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

/-- The cone map onto the upper triangle of the subdivision. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0 * (unitInterval.symm) (u 1), Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => u 0 * (unitInterval.symm) (u 1)
      apply Continuous.subtype_mk
      change Continuous fun u : SubdivisionSquare => (u 0 : ℝ) * (1 - (u 1 : ℝ))
      fun_prop
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

/-- The map `u ↦ ![u 0, min (u 0) (u 1)]` onto the lower triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Min.min (u 0) (u 1)]
  continuous_toFun := by fun_prop

/-- The map from the subdivision square onto the upper triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![subdivisionSubMin (u 0) (u 1), u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => subdivisionSubMin (u 0) (u 1)
      unfold subdivisionSubMin
      fun_prop
    · exact continuous_apply 0

/-- `p (subdivisionLowerProductMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionLowerProductMap, h])

/-- `p (subdivisionUpperProductMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionUpperProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperProductMap, h])
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperProductMap, h])⟩

/-- `p (subdivisionUpperConeMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperConeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperConeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperConeMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩

/-- `p (subdivisionLowerTriangleMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

/-- `p (subdivisionUpperTriangleMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperTriangleMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩

/-- The pullback loop `p ∘ subdivisionLowerProductMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerProductMap (subdivisionLowerProductMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperProductMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperProductMap (subdivisionUpperProductMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperConeMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperConeMap (subdivisionUpperConeMap_based p hd)

/-- The pullback loop `p ∘ subdivisionLowerTriangleMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerTriangleMap (subdivisionLowerTriangleMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperTriangleMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperTriangleMap (subdivisionUpperTriangleMap_based p hd)

/-- The side restrictions of the lower product triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerProductTriangle_sides
    (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionLowerProductMap u) (subdivisionLowerTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .one 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .zero 1 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionLowerProductMap, h])
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

/-- The side restrictions of the upper product/cone maps. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperProductCone_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperProductMap u) (subdivisionUpperConeMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])

/-- The side restrictions of the upper cone and triangle maps. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeTriangle_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperConeMap u) (subdivisionUpperTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact .one 1 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])

/-- The `HomotopyRel` between the lower product and lower triangle loops. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionLowerProductLoop p hd).val.HomotopyRel (subdivisionLowerTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionLowerProductMap_based p hd)
    (subdivisionLowerTriangleMap_based p hd) subdivisionLowerProductTriangle_sides

/-- The `HomotopyRel` between the upper product and upper cone loops. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperConeHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperProductLoop p hd).val.HomotopyRel (subdivisionUpperConeLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperProductMap_based p hd)
    (subdivisionUpperConeMap_based p hd) subdivisionUpperProductCone_sides

/-- The `HomotopyRel` between the upper cone and upper triangle loops. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperConeLoop p hd).val.HomotopyRel (subdivisionUpperTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperConeMap_based p hd)
    (subdivisionUpperTriangleMap_based p hd) subdivisionUpperConeTriangle_sides

/-- `toLoop` of a `transAt` concatenation is the `trans` of the `toLoop`s. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_toLoop_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin 2) (a b : GenLoop (Fin 2) X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- `transAt` respects homotopy in both arguments. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_transAt_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin 2) {a b c d : GenLoop (Fin 2) X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [subdivision_toLoop_transAt, subdivision_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

/-- The warp coordinate interpolating between two subdivision maps. -/
noncomputable def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate :
    C((unitInterval) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) p.1
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

/-- `subdivisionWarpCoordinate (u, v)` is the `u`-blend between `2v - 1` and `2v` clamped to `I`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_apply (u v : (unitInterval)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1))
        (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ))) u :=
  rfl

/-- `subdivisionWarpCoordinate (u, 0) = 0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_zero (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 0) = 0 := by
  simp [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

/-- `subdivisionWarpCoordinate (u, 1) = 1`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_one (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 1) = 1 := by
  norm_num [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

/-- For `v ≤ 1/2`, `subdivisionWarpCoordinate (u, v) = u * (2v)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_of_le_half (u v : (unitInterval))
    (hv : (v : ℝ) ≤ 1 / 2) :
    subdivisionWarpCoordinate (u, v) = u * Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) := by
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hzero]
  apply Subtype.ext
  simp

/-- For `v ≥ 1/2`, `subdivisionWarpCoordinate` blends `u` toward `1` with parameter `2v - 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_of_half_le (u v : (unitInterval))
    (hv : 1 / 2 ≤ (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hone]
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  change (1 - (u : ℝ)) * _ + (u : ℝ) * 1 = (1 - _) * (u : ℝ) + _ * 1
  ring

/-- For `v > 1/2`, `subdivisionWarpCoordinate` blends `u` toward `1` with parameter `2v - 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (u v : (unitInterval))
    (hv : 1 / 2 < (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) :=
  subdivisionWarpCoordinate_of_half_le u v hv.le

/-- The warp map `u ↦ ![u 0, subdivisionWarpCoordinate (u 0, u 1)]`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpMap : C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, subdivisionWarpCoordinate (u 0, u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => subdivisionWarpCoordinate (u 0, u 1)
      exact
        subdivisionWarpCoordinate.continuous.comp
          (show Continuous (fun u : SubdivisionSquare => (u 0, u 1)) from
            (continuous_apply 0).prodMk (continuous_apply 1))

/-- Each boundary point is on the same side as its warp-map image. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpMap_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : SubdivisionSameSide u (subdivisionWarpMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 h (by simp [subdivisionWarpMap, h])
  · exact .one 0 h (by simp [subdivisionWarpMap, h])
  · exact .zero 1 h (by simp [subdivisionWarpMap, h])
  · exact .one 1 h (by simp [subdivisionWarpMap, h])

/-- `p (subdivisionWarpMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpMap_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    p (subdivisionWarpMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionWarpMap, h])⟩

/-- The pullback loop `p ∘ subdivisionWarpMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionWarpMap (subdivisionWarpMap_based p)

/-- The `HomotopyRel` from `p` to `subdivisionWarpLoop p`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    p.val.HomotopyRel (subdivisionWarpLoop p).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd (ContinuousMap.id _) subdivisionWarpMap p.property
    (subdivisionWarpMap_based p) subdivisionWarpMap_sides

/-- The warp loop is the `transAt 1` concatenation of the lower and upper product loops. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionWarpLoop_eq_transAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionWarpLoop p =
      GenLoop.transAt (1 : Fin 2) (subdivisionLowerProductLoop p hd)
        (subdivisionUpperProductLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![u 0, subdivisionWarpCoordinate (u 0, u 1)] =
      if (u 1 : ℝ) ≤ 1 / 2 then
        subdivisionLowerProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ))))
      else
        subdivisionUpperProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ) - 1)))
  split_ifs with h
  · simpa [subdivisionLowerProductLoop, subdivisionPullbackLoop, subdivisionLowerProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_le_half (u 0) (u 1) h)
  · simpa [subdivisionUpperProductLoop, subdivisionPullbackLoop, subdivisionUpperProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_half_lt (u 0) (u 1) (lt_of_not_ge h))

/-- `p` is homotopic to the `transAt 1` concatenation of its lower and upper triangle loops. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic p
      (GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
        (subdivisionUpperTriangleLoop p hd)) := by
  have hw : GenLoop.Homotopic p (subdivisionWarpLoop p) := ⟨subdivisionWarpHomotopy p hd⟩
  rw [subdivisionWarpLoop_eq_transAt p hd] at hw
  apply hw.trans
  apply subdivision_transAt_homotopic
  · exact ⟨subdivisionLowerTriangleHomotopy p hd⟩
  · exact ⟨(subdivisionUpperConeHomotopy p hd).trans (subdivisionUpperTriangleHomotopy p hd)⟩

/-- `⟦p⟧ = ⟦subdivisionLowerTriangleLoop⟧ * ⟦subdivisionUpperTriangleLoop⟧` in `π_2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦p⟧ : π_ 2 X x) =
      ((· * ·) : π_ 2 X x → π_ 2 X x → π_ 2 X x) ⟦subdivisionLowerTriangleLoop p hd⟧
        ⟦subdivisionUpperTriangleLoop p hd⟧ := by
  have h :
    (⟦p⟧ : π_ 2 X x) =
      (⟦GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
            (subdivisionUpperTriangleLoop p hd)⟧ :
        π_ 2 X x) :=
    Quotient.sound (subdivision_homotopic p hd)
  exact
    h.trans
      ((HomotopyGroup.mul_spec (i := (1 : Fin 2)) (p := subdivisionUpperTriangleLoop p hd) (q :=
            subdivisionLowerTriangleLoop p hd)).symm.trans
        (mul_comm _ _))

/-- The additive form of `subdivision_class`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· + ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivision_class p hd)

/-! ### Tetrahedron boundary relations -/

/-- On the lower triangle of the square, `tetrahedronQuadrilateralA` lands on face `3` of the tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_lower
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u) =
      SingularChains.simplexFace 2 3 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![u 0, Min.min (u 0) (u 1)] j =
      (SingularChains.simplexFace 2 3 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_three]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply]

/-- On the upper triangle of the square, `tetrahedronQuadrilateralA` lands on face `1` of the tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuadrilateralA_upper
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u) =
      SingularChains.simplexFace 2 1 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have subdivisionSubMin_coe (u v : (unitInterval)) :
    (subdivisionSubMin u v : ℝ) = (u : ℝ) - Min.min (u : ℝ) (v : ℝ) := rfl
  have hm : (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) ≤ (u 0 : ℝ) :=
    sub_le_self _ (le_min (u 0).property.1 (u 1).property.1)
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![subdivisionSubMin (u 0) (u 1), u 0] j =
      (SingularChains.simplexFace 2 1 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_one]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply,
      subdivisionSubMin_coe, min_eq_left hm, max_eq_right hm]

/-- The third face of the quarter-shifted tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_face_three
    (s : SingularChains.Simplex 2) :
    tetrahedronQuarterShift (SingularChains.simplexFace 2 3 s) = SingularChains.simplexFace 2 0 s :=
  by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (SingularChains.simplexFace 2 3 s) j =
      (SingularChains.simplexFace 2 0 s : Fin 4 → ℝ) j
  rw [simplexFace_two_zero]
  fin_cases j
  · exact SingularChains.simplexFace_apply_self 2 3 s
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 2

/-- The first face of the quarter-shifted tetrahedron. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronQuarterShift_face_one
    (s : SingularChains.Simplex 2) :
    tetrahedronQuarterShift (SingularChains.simplexFace 2 1 s) =
      SingularChains.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) := by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (SingularChains.simplexFace 2 1 s) j =
      (SingularChains.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) :
          Fin 4 → ℝ)
        j
  rw [simplexFace_two_two]
  fin_cases j
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 2
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 0
  · exact SingularChains.simplexFace_apply_self 2 1 s
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 1

/-- The lower subdivision loop of the quadrilateral loop equals the `basedTriangleLoop` of face `3`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 3) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u)) =
      τ.val (SingularChains.simplexFace 2 3 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower]

/-- The upper subdivision loop of the quadrilateral loop equals the `basedTriangleLoop` of face `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 1) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u)) =
      τ.val (SingularChains.simplexFace 2 1 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_upper]

/-- The lower subdivision loop of the shifted quadrilateral equals the `basedTriangleLoop` of face `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 0) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u))) =
      τ.val (SingularChains.simplexFace 2 0 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower, tetrahedronQuarterShift_face_three]

/-- The upper subdivision loop of the shifted quadrilateral equals the `basedTriangleLoop` of twice-cyclically-permuted face `2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.tetrahedronShiftedUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u))) =
      τ.val
        (SingularChains.simplexFace 2 2
          (triangleCyclicPermutation (triangleCyclicPermutation (triangleCubeQuotient u))))
  rw [tetrahedronQuadrilateralA_upper, tetrahedronQuarterShift_face_one]

/-- `basedTriangleClass (face 3) + basedTriangleClass (face 1) = basedTriangleClass (face 0) + basedTriangleClass (face 2)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_pair_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 3) +
        basedTriangleClass (basedTetrahedronFace τ 1) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass (basedTetrahedronFace τ 2) := by
  have hA :=
    subdivision_additiveClass (tetrahedronQuadrilateralLoop τ)
      (tetrahedronQuadrilateralLoop_diagonal τ)
  rw [tetrahedronLowerLoop_eq_face, tetrahedronUpperLoop_eq_face] at hA
  have hB :=
    subdivision_additiveClass (tetrahedronShiftedQuadrilateralLoop τ)
      (tetrahedronShiftedQuadrilateralLoop_diagonal τ)
  rw [tetrahedronShiftedLowerLoop_eq_face, tetrahedronShiftedUpperLoop_eq_face] at hB
  change
    Additive.ofMul (⟦tetrahedronShiftedQuadrilateralLoop τ⟧ : π_ 2 X x) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass
          (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) at hB
  simp only [basedTriangleClass_cyclic] at hB
  exact hA.symm.trans ((congrArg Additive.ofMul (tetrahedronFillings_class τ)).trans hB)

/-- The alternating sum `face 0 - face 1 + face 2 - face 3` of based-triangle classes is `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_boundary_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 0) -
            basedTriangleClass (basedTetrahedronFace τ 1) +
          basedTriangleClass (basedTetrahedronFace τ 2) -
        basedTriangleClass (basedTetrahedronFace τ 3) =
      0 := by
  calc
    _ =
        (basedTriangleClass (basedTetrahedronFace τ 0) +
            basedTriangleClass (basedTetrahedronFace τ 2)) -
          (basedTriangleClass (basedTetrahedronFace τ 3) +
            basedTriangleClass (basedTetrahedronFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedTetrahedron_pair_relation τ).symm

/-- The signed sum `∑ i, (-1)^i • basedTriangleClass (face i)` over the four faces is `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTetrahedron_signed_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • basedTriangleClass (basedTetrahedronFace τ i) = 0 := by
  have h := basedTetrahedron_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

/-- The normalized `3`-simplex packaged as a `BasedTetrahedron` via `normalizedTetrahedronMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) :
    BasedTetrahedron x :=
  BasedTetrahedron.ofFaces (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

/-- The faces of the normalized tetrahedron are normalized based triangles. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTetrahedron_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) (i : Fin 4) :
    basedTetrahedronFace (normalizedTetrahedron x smp) i =
      normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i)) := by
  apply Subtype.ext
  exact normalizedTetrahedronMap_face x smp i

/-- The signed sum of the normalized-triangle classes of the four faces is `0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangle_boundary_relation {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) :
    ∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          basedTriangleClass (normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i))) =
      0 := by
  simpa only [normalizedTetrahedron_face] using
    basedTetrahedron_signed_relation (normalizedTetrahedron x smp)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-! ### The two-triangle decomposition of the square -/

/-- The affine `2`-simplex into `I × I` with vertices `v : Fin 3 → Fin 2 × Fin 2`. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle (v : Fin 3 → Fin 2 × Fin 2) :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  ((SingularChains.pathSimplex Path.id).prodMap (SingularChains.pathSimplex Path.id)).comp
    (SingularHomology.productAffineSimplex
      (fun i =>
        (SingularMayerVietoris.stdVertices 1 (v i).1,
          SingularMayerVietoris.stdVertices 1 (v i).2)))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The first coordinate of `squareAffineTriangle v` is `∑ i, s i * stdVertices 1 (v i).1 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle_fst_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : SingularChains.Simplex 2) :
    ((squareAffineTriangle v s).1 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).1 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).1) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The second coordinate of `squareAffineTriangle v` is `∑ i, s i * stdVertices 1 (v i).2 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareAffineTriangle_snd_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : SingularChains.Simplex 2) :
    ((squareAffineTriangle v s).2 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).2 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).2) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The lower product triangle in `I × I`. -/
def Hurewicz.DegreeTwo.SimplyConnected.lowerProductTriangle :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (1, 0), (1, 1)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The upper product triangle in `I × I`. -/
def Hurewicz.DegreeTwo.SimplyConnected.upperProductTriangle :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 1), (1, 1)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degenerate left edge of the product square. -/
def Hurewicz.DegreeTwo.SimplyConnected.leftProductDegenerate :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (0, 1)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The degenerate bottom edge of the product square. -/
def Hurewicz.DegreeTwo.SimplyConnected.bottomProductDegenerate :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (1, 0)]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The first coordinate of `lowerProductTriangle` is `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerProductTriangle_fst (s : SingularChains.Simplex 2) :
    ((lowerProductTriangle s).1 : ℝ) = s 1 + s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The second coordinate of `lowerProductTriangle` is `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerProductTriangle_snd (s : SingularChains.Simplex 2) :
    ((lowerProductTriangle s).2 : ℝ) = s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The first coordinate of `upperProductTriangle` is `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperProductTriangle_fst (s : SingularChains.Simplex 2) :
    ((upperProductTriangle s).1 : ℝ) = s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The second coordinate of `upperProductTriangle` is `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperProductTriangle_snd (s : SingularChains.Simplex 2) :
    ((upperProductTriangle s).2 : ℝ) = s 1 + s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The first coordinate of `leftProductDegenerate` is `0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.leftProductDegenerate_fst (s : SingularChains.Simplex 2) :
    (leftProductDegenerate s).1 = 0 := by
  apply Subtype.ext
  simp [leftProductDegenerate, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- The second coordinate of `bottomProductDegenerate` is `0`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.bottomProductDegenerate_snd (s : SingularChains.Simplex 2) :
    (bottomProductDegenerate s).2 = 0 := by
  apply Subtype.ext
  simp [bottomProductDegenerate, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The lower triangle of the square's diagonal subdivision, as a singular
`2`-simplex. -/
def Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  Hurewicz.DegreeTwo.squareCoordinates.comp lowerProductTriangle

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The upper triangle of the square's diagonal subdivision, as a singular
`2`-simplex. -/
def Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  Hurewicz.DegreeTwo.squareCoordinates.comp upperProductTriangle

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `lowerSquareTriangle s` has coordinate `0` equal to `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_zero (s : SingularChains.Simplex 2) :
    (lowerSquareTriangle s 0 : ℝ) = s 1 + s 2 := by simp [lowerSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `lowerSquareTriangle s` has coordinate `1` equal to `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_one (s : SingularChains.Simplex 2) :
    (lowerSquareTriangle s 1 : ℝ) = s 2 := by simp [lowerSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `upperSquareTriangle s` has coordinate `0` equal to `s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_zero (s : SingularChains.Simplex 2) :
    (upperSquareTriangle s 0 : ℝ) = s 2 := by simp [upperSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in

/-- `upperSquareTriangle s` has coordinate `1` equal to `s 1 + s 2`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_one (s : SingularChains.Simplex 2) :
    (upperSquareTriangle s 1 : ℝ) = s 1 + s 2 := by simp [upperSquareTriangle]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `productSquareChain` decomposes as a sum of four signed triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.productSquareChain_four_triangles :
    Hurewicz.DegreeTwo.productSquareChain =
      SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
            SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle +
        SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 bottomProductDegenerate := by
  rw [Hurewicz.DegreeTwo.productSquareChain, Hurewicz.DegreeTwo.intervalChain, SingularChains.pathChain,
    SingularHomology.crossProductEdge_simplex,
    SingularHomology.formalEdgeCrossProduct_simplex_succ,
    SingularHomology.formalPointCrossProduct_edge_boundary,
    SingularHomology.formalBoundary_edge_simplex]
  simp only [map_sub, SingularHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    SingularHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex]
  change
    (SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate) -
        (SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2
            bottomProductDegenerate) =
      _
  abel

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `squareMap p ∘ leftProductDegenerate` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareMap_leftProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (Hurewicz.DegreeTwo.squareMap p).comp leftProductDegenerate =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨0, Or.inl ?_⟩
  rw [Hurewicz.DegreeTwo.squareCoordinates_zero, leftProductDegenerate_fst]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `squareMap p ∘ bottomProductDegenerate` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareMap_bottomProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (Hurewicz.DegreeTwo.squareMap p).comp bottomProductDegenerate =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨1, Or.inl ?_⟩
  rw [Hurewicz.DegreeTwo.squareCoordinates_one, bottomProductDegenerate_snd]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The square chain equals the signed sum of the two square triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareChain_two_triangles {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    Hurewicz.DegreeTwo.squareChain p =
      SingularChains.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
        SingularChains.simplexChain X 2 (p.val.comp upperSquareTriangle) := by
  rw [Hurewicz.DegreeTwo.squareChain, Hurewicz.DegreeTwo.suspensionOne_toLoop,
    productSquareChain_four_triangles]
  simp only [map_add, map_sub, SingularChains.inducedChain_simplex,
    squareMap_leftProductDegenerate, squareMap_bottomProductDegenerate]
  change
    (SingularChains.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
            SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x)) -
          SingularChains.simplexChain X 2 (p.val.comp upperSquareTriangle) +
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) =
      _
  abel

/-- `triangleQuotient ∘ lowerProductTriangle = id`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_lowerProductTriangle :
    triangleQuotient.comp lowerProductTriangle = ContinuousMap.id (SingularChains.Simplex 2) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + s 2) = 1 at hs
  have hle : s 2 ≤ s 1 + s 2 := le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  fin_cases i
  · change 1 - ((lowerProductTriangle s).1 : ℝ) = s 0
    rw [lowerProductTriangle_fst]
    linarith
  · change
      ((lowerProductTriangle s).1 : ℝ) -
          Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) =
        s 1
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]
    ring
  · change Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) = s 2
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]

/-- The triangle quotient of the upper product triangle lands on the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_upperProductTriangle_boundary
    (s : SingularChains.Simplex 2) :
    triangleQuotient (upperProductTriangle s) ∈ triangleBoundary := by
  refine ⟨1, ?_⟩
  rw [triangleQuotient_one, upperProductTriangle_fst, upperProductTriangle_snd,
    min_eq_left (le_add_of_nonneg_left (stdSimplex.zero_le s 1)), sub_self]

/-- The lower triangle of `basedTriangleLoop τ` under the quotient. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) : (basedTriangleLoop τ).val.comp lowerSquareTriangle = τ.val := by
  change (Hurewicz.DegreeTwo.squareMap (basedTriangleLoop τ)).comp lowerProductTriangle = _
  rw [squareMap_basedTriangleLoop, ContinuousMap.comp_assoc,
    triangleQuotient_lowerProductTriangle, ContinuousMap.comp_id]

/-- The upper triangle of `basedTriangleLoop τ` under the quotient. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp upperSquareTriangle =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  change (Hurewicz.DegreeTwo.squareMap (basedTriangleLoop τ)).comp upperProductTriangle = _
  rw [squareMap_basedTriangleLoop]
  ext s
  exact τ.property _ (triangleQuotient_upperProductTriangle_boundary s)

/-- The square chain of `basedTriangleLoop τ` expressed via the quotient. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareChain_basedTriangleLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTriangle x) :
    Hurewicz.DegreeTwo.squareChain (basedTriangleLoop τ) =
      SingularChains.simplexChain X 2 τ.val -
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) := by
  rw [squareChain_two_triangles, basedTriangleLoop_lower, basedTriangleLoop_upper]

/-! ### Descending to second homology -/

/-- The `2`-cycle of a based triangle (its square chain with boundary correction). -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTriangleCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (SingularChains.simplexChain X 2 τ.val -
      SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x))
    (by
      rw [← squareChain_basedTriangleLoop]
      exact Hurewicz.DegreeTwo.squareChain_boundary (basedTriangleLoop τ))

/-- The underlying chain of `basedTriangleCycle τ`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangleCycle_val {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleCycle τ).val =
      SingularChains.simplexChain X 2 τ.val -
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) :=
  rfl

/-- The Hurewicz map on the class of a based triangle equals its cycle class. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewicz_basedTriangleClass {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    Hurewicz.DegreeTwo.hurewiczMap x (basedTriangleClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (basedTriangleCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (Hurewicz.DegreeTwo.squareCycle (basedTriangleLoop τ)) =
      _
  congr 1
  apply Subtype.ext
  exact squareChain_basedTriangleLoop τ

/-- The descent of a normalized `2`-cycle to a `π_2`-class: the based triangle
classes summed over the cycle. -/
def Hurewicz.DegreeTwo.SimplyConnected.secondHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] M :=
  SingularHomology.homologyDesc (SingularChains.singularComplex X) 2
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2).subtype)
    (fun b => hF b)

/-- `hurewiczMap` of `secondHomologyDesc c` returns the class of `c`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.secondHomologyDesc_cycleClass {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    secondHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) =
      F c.1 :=
  SingularHomology.homologyDesc_cycleClass (SingularChains.singularComplex X) 2 _ _ c

/-- `hurewiczMap ∘ secondHomologyDesc` is the identity on homology classes. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.comp_secondHomologyDesc_eq_id {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) :
    g.comp (secondHomologyDesc F hF) = LinearMap.id := by
  apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex X) 2
  intro c
  simpa only [LinearMap.comp_apply, secondHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

/-! ### Chain augmentation and the inverse map -/

/-- The augmentation `Chains X n → ℤ` sending every simplex generator to `1`. -/
def Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] ℤ :=
  SingularChains.chainLift X n fun _ => 1

/-- `chainAugmentation` of a simplex generator is `1`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_simplex (X : Type) [TopologicalSpace X]
    (n : ℕ) (smp : SingularChains.SingularSimplex X n) :
    chainAugmentation X n (SingularChains.simplexChain X n smp) = 1 :=
  SingularChains.chainLift_simplex X n _ smp

/-- `chainAugmentation` of a degree-`2` boundary equals `chainAugmentation` of the `2`-chain. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_boundaryTwo (X : Type)
    [TopologicalSpace X] (c : SingularChains.Chains X 2) :
    chainAugmentation X 1 (SingularChains.boundaryTwo X c) = chainAugmentation X 2 c := by
  have h : (chainAugmentation X 1).comp (SingularChains.boundaryTwo X) = chainAugmentation X 2 := by
    apply SingularChains.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundaryTwo_simplex, map_add, map_sub,
      chainAugmentation_simplex, sub_self, zero_add]
  exact LinearMap.congr_fun h c

/-- `chainAugmentation` vanishes on `2`-cycles. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.chainAugmentation_twoCycle (X : Type) [TopologicalSpace X]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    chainAugmentation X 2 c.1 = 0 := by
  rw [← chainAugmentation_boundaryTwo]
  have hc :=
    SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 c
  change SingularChains.boundaryTwo X c.1 = 0 at hc
  rw [hc, map_zero]

/-- `chainLift` of `f - m` equals `chainLift` of `f` minus the augmentation times `m`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant (X : Type) [TopologicalSpace X]
    {M : Type} [AddCommGroup M] [Module ℤ M] (n : ℕ) (f : SingularChains.SingularSimplex X n → M)
    (m : M) (c : SingularChains.Chains X n) :
    SingularChains.chainLift X n (fun smp => f smp - m) c =
      SingularChains.chainLift X n f c - chainAugmentation X n c • m := by
  have h :
    SingularChains.chainLift X n (fun smp => f smp - m) =
      SingularChains.chainLift X n f -
        (LinearMap.toSpanSingleton ℤ M m).comp (chainAugmentation X n) := by
    apply SingularChains.chainMap_ext X n
    intro smp
    simp only [SingularChains.chainLift_simplex, LinearMap.sub_apply, LinearMap.comp_apply,
      chainAugmentation_simplex, LinearMap.toSpanSingleton_apply_one]
  exact
    (LinearMap.congr_fun h c).trans
      (congrArg (fun z : M => SingularChains.chainLift X n f c - z)
        (int_smul_eq_zsmul (inferInstance : Module ℤ M) (chainAugmentation X n c) m))

/-- On a `2`-cycle, `chainLift` of `f - m` equals `chainLift` of `f`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.chainLift_sub_constant_twoCycle (X : Type)
    [TopologicalSpace X] {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularChains.SingularSimplex X 2 → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularChains.chainLift X 2 (fun smp => f smp - m) c.1 = SingularChains.chainLift X 2 f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_twoCycle, zero_smul, sub_zero]

/-- The operator `Chains X 2 →ₗ[ℤ] Additive (π_2 X x)` summing the based triangle
classes. -/
def Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : SingularChains.Chains X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  SingularChains.chainLift X 2 fun smp => basedTriangleClass (normalizedTriangle x smp)

/-- `triangleClassOperator` applied to a simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) :
    triangleClassOperator x (SingularChains.simplexChain X 2 smp) =
      basedTriangleClass (normalizedTriangle x smp) :=
  SingularChains.chainLift_simplex X 2 _ smp

/-- `triangleClassOperator` vanishes on `3`-boundaries (the tetrahedron signed
relation). -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (b : SingularChains.Chains X 3) :
    triangleClassOperator x (((SingularChains.singularComplex X).d 3 2).hom b) = 0 := by
  have h : (triangleClassOperator x).comp ((SingularChains.singularComplex X).d 3 2).hom = 0 := by
    apply SingularChains.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundary_simplex, map_sum, map_zsmul,
      triangleClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedTriangle_boundary_relation x smp
  exact LinearMap.congr_fun h b

/-- The normalized cycle operator on `2`-chains. -/
def Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularChains.chainLift X 2 fun smp => basedTriangleCycle (normalizedTriangle x smp)

/-- `normalizedTriangleCycleOperator` applied to a simplex. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) :
    normalizedTriangleCycleOperator x (SingularChains.simplexChain X 2 smp) =
      basedTriangleCycle (normalizedTriangle x smp) :=
  SingularChains.chainLift_simplex X 2 _ smp

/-- The underlying chain of `normalizedTriangleCycleOperator c` is the `chainLift` of the normalized triangle minus the constant simplex. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator_val {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (c : SingularChains.Chains X 2) :
    (normalizedTriangleCycleOperator x c).val =
      SingularChains.chainLift X 2
        (fun smp =>
          SingularChains.simplexChain X 2 (normalizedTriangle x smp).val -
            SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2).subtype.comp
        (normalizedTriangleCycleOperator x) =
      SingularChains.chainLift X 2
        (fun smp =>
          SingularChains.simplexChain X 2 (normalizedTriangle x smp).val -
            SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x)) := by
    apply SingularChains.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, normalizedTriangleCycleOperator_simplex,
      Submodule.subtype_apply, basedTriangleCycle_val, SingularChains.chainLift_simplex]
  exact LinearMap.congr_fun h c

/-- On a `2`-cycle value, `normalizedTriangleCycleOperator` agrees with `normalizedTwoCycle`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.normalizedTriangleCycleOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    normalizedTriangleCycleOperator x c.val = normalizedTwoCycle x c := by
  apply Subtype.ext
  rw [normalizedTriangleCycleOperator_val, chainLift_sub_constant_twoCycle,
    normalizedTwoCycle_val]
  rfl

/-- Hurewicz after `triangleClassOperator` is `cycleClass` after `normalizedTriangleCycleOperator`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_comp_triangleClassOperator {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (Hurewicz.DegreeTwo.hurewiczMap x).comp (triangleClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2).comp
        (normalizedTriangleCycleOperator x) := by
  apply SingularChains.chainMap_ext X 2
  intro smp
  simp only [LinearMap.comp_apply, triangleClassOperator_simplex,
    normalizedTriangleCycleOperator_simplex]
  exact hurewicz_basedTriangleClass (normalizedTriangle x smp)

/-- `hurewiczMap` of the triangle-class operator on a `2`-cycle returns its class. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_triangleClassOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    Hurewicz.DegreeTwo.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_triangleClassOperator x) c.val
  change
    Hurewicz.DegreeTwo.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (normalizedTriangleCycleOperator x c.val) at h
  rw [normalizedTriangleCycleOperator_twoCycle] at h
  exact h.trans (normalizedTwoCycle_class x c)

/-- The inverse Hurewicz map `H_2 X →ₗ[ℤ] Additive (π_2 X x)` for simply
connected `X`. -/
def Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  secondHomologyDesc (triangleClassOperator x) (triangleClassOperator_boundary x)

/-- `hurewiczInverse` on a cycle class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) =
      triangleClassOperator x c.val :=
  secondHomologyDesc_cycleClass _ _ c

/-- `hurewiczMap ∘ hurewiczInverse` is the identity on `H_2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_comp_hurewiczInverse {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (Hurewicz.DegreeTwo.hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_secondHomologyDesc_eq_id (triangleClassOperator x) (triangleClassOperator_boundary x)
    (Hurewicz.DegreeTwo.hurewiczMap x) (hurewiczMap_triangleClassOperator_twoCycle x)

/-- `hurewiczMap` of `hurewiczInverse` of a class returns the class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (c : SingularMayerVietoris.SingularHomology X 2) :
    Hurewicz.DegreeTwo.hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

/-! ### Normalized squares -/

/-- The lower square triangle of `p` is vertex-based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp lowerSquareTriangle) := by
  intro i
  change p (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨1, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

/-- The upper square triangle of `p` is vertex-based. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp upperSquareTriangle) := by
  intro i
  change p (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

/-- The face-`1` restrictions of the lower and upper square triangles of `p` agree. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareTriangles_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).comp (SingularChains.simplexFace 1 1) =
      (p.val.comp upperSquareTriangle).comp (SingularChains.simplexFace 1 1) := by
  apply ContinuousMap.ext
  intro s
  change
    p.val (lowerSquareTriangle (SingularChains.simplexFace 1 1 s)) =
      p.val (upperSquareTriangle (SingularChains.simplexFace 1 1 s))
  apply congrArg p.val
  funext i
  apply Subtype.ext
  fin_cases i
  · change
      (lowerSquareTriangle (SingularChains.simplexFace 1 1 s) 0 : ℝ) =
        (upperSquareTriangle (SingularChains.simplexFace 1 1 s) 0 : ℝ)
    rw [lowerSquareTriangle_zero, upperSquareTriangle_zero, SingularChains.simplexFace_apply_self,
      zero_add]
  · change
      (lowerSquareTriangle (SingularChains.simplexFace 1 1 s) 1 : ℝ) =
        (upperSquareTriangle (SingularChains.simplexFace 1 1 s) 1 : ℝ)
    rw [lowerSquareTriangle_one, upperSquareTriangle_one, SingularChains.simplexFace_apply_self,
      zero_add]

/-- For `i ≠ 1`, face `i` of the lower square triangle of `p` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_outerFace {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp lowerSquareTriangle).comp (SingularChains.simplexFace 1 i) =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (SingularChains.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (SingularChains.simplexFace 1 0 s) 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    have h1 : SingularChains.simplexFace 1 0 s 1 = s 0 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 0
    have h2 : SingularChains.simplexFace 1 0 s 2 = s 1 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (SingularChains.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (SingularChains.simplexFace 1 2 s) 1 : ℝ) = 0
    rw [lowerSquareTriangle_one, SingularChains.simplexFace_apply_self]

/-- For `i ≠ 1`, face `i` of the upper square triangle of `p` is constant `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_outerFace {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp upperSquareTriangle).comp (SingularChains.simplexFace 1 i) =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (SingularChains.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (SingularChains.simplexFace 1 0 s) 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    have h1 : SingularChains.simplexFace 1 0 s 1 = s 0 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 0
    have h2 : SingularChains.simplexFace 1 0 s 2 = s 1 :=
      SingularChains.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (SingularChains.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (SingularChains.simplexFace 1 2 s) 0 : ℝ) = 0
    rw [upperSquareTriangle_zero, SingularChains.simplexFace_apply_self]

/-- For `t 1 ≤ t 0`, `lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.lowerSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 1 : ℝ) ≤ t 0) : lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 0 : ℝ) = (t 0 : ℝ)
    rw [lowerSquareTriangle_zero, triangleQuotient_one, triangleQuotient_two]
    ring
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 1 : ℝ) = (t 1 : ℝ)
    rw [lowerSquareTriangle_one, triangleQuotient_two, min_eq_right h]

/-- For `t 0 ≤ t 1`, `upperSquareTriangle (triangleQuotient (t 1, t 0)) = t`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.upperSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 0 : ℝ) ≤ t 1) : upperSquareTriangle (triangleQuotient (t 1, t 0)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 0 : ℝ) = (t 0 : ℝ)
    rw [upperSquareTriangle_zero, triangleQuotient_two, min_eq_right h]
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 1 : ℝ) = (t 1 : ℝ)
    rw [upperSquareTriangle_one, triangleQuotient_one, triangleQuotient_two]
    ring

/-- The perimeter of the triangle quotient on the lower half. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_perimeter_of_le
    (z : (unitInterval) × (unitInterval)) (hper : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1)
    (hle : (z.2 : ℝ) ≤ z.1) : triangleQuotient z 0 = 0 ∨ triangleQuotient z 2 = 0 := by
  rcases hper with h | h | h | h
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_left z.2.property.1
  · left
    rw [triangleQuotient_zero, h]
    norm_num
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_right z.1.property.1
  · have hu : z.1 = 1 := Subtype.ext (le_antisymm z.1.property.2 (by simpa only [h] using hle))
    left
    rw [triangleQuotient_zero, hu]
    norm_num

/-- A point of the `Fin 2` cube boundary has some coordinate equal to `0` or `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.cubeBoundary_productBoundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : t 0 = 0 ∨ t 0 = 1 ∨ t 1 = 0 ∨ t 1 = 1 := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hi))

/-- Glue `L` and `U` along the diagonal face `s 1 = 0`. -/
def Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopyMap {X : Type} [TopologicalSpace X]
    (L U : C((unitInterval) × SingularChains.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) :
    C((unitInterval) × (Fin 2 → (unitInterval)), X)
    where
  toFun
    z :=
    if (z.2 1 : ℝ) ≤ z.2 0 then L (z.1, triangleQuotient (z.2 0, z.2 1))
    else U (z.1, triangleQuotient (z.2 1, z.2 0))
  continuous_toFun := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro z h
    have he : z.2 1 = z.2 0 := Subtype.ext h
    have hq : triangleQuotient (z.2 0, z.2 1) 1 = 0 := by
      simp only [triangleQuotient_one, he, min_self, sub_self]
    simpa only [he] using hdiag z.1 (triangleQuotient (z.2 0, z.2 1)) hq

/-- The glued map is `x` on the square boundary, given the boundary hypotheses on `L` and `U`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopyMap_boundary {X : Type}
    [TopologicalSpace X] (L U : C((unitInterval) × SingularChains.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (x : X)
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x) (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x)
    (r : (unitInterval)) (t : Fin 2 → (unitInterval)) (ht : t ∈ Cube.boundary (Fin 2)) :
    gluedTriangleHomotopyMap L U hdiag (r, t) = x := by
  have hp := cubeBoundary_productBoundary t ht
  change (if (t 1 : ℝ) ≤ t 0 then _ else _) = x
  split_ifs with h
  · exact hL r _ (triangleQuotient_perimeter_of_le (t 0, t 1) hp h)
  · have hp' : t 1 = 0 ∨ t 1 = 1 ∨ t 0 = 0 ∨ t 0 = 1 := by
      rcases hp with hp | hp | hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inr (Or.inr hp))
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    exact hU r _ (triangleQuotient_perimeter_of_le (t 1, t 0) hp' (le_of_not_ge h))

/-- The `HomotopyRel` from `p` to `q` glued from lower- and upper-triangle homotopies. -/
def Hurewicz.DegreeTwo.SimplyConnected.gluedTriangleHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x}
    (L : (p.val.comp lowerSquareTriangle).Homotopy (q.val.comp lowerSquareTriangle))
    (U : (p.val.comp upperSquareTriangle).Homotopy (q.val.comp upperSquareTriangle))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel q.val (Cube.boundary (Fin 2))
    where
  toContinuousMap := gluedTriangleHomotopyMap L.toContinuousMap U.toContinuousMap hdiag
  map_zero_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = p.val t
    split_ifs with h
    · change L (0, triangleQuotient (t 0, t 1)) = p.val t
      rw [L.apply_zero]
      change p.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = p.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (0, triangleQuotient (t 1, t 0)) = p.val t
      rw [U.apply_zero]
      change p.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = p.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  map_one_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = q.val t
    split_ifs with h
    · change L (1, triangleQuotient (t 0, t 1)) = q.val t
      rw [L.apply_one]
      change q.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = q.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (1, triangleQuotient (t 1, t 0)) = q.val t
      rw [U.apply_one]
      change q.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = q.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  prop' r t
    ht :=
    (gluedTriangleHomotopyMap_boundary L.toContinuousMap U.toContinuousMap hdiag x hL hU r t
          ht).trans
      (GenLoop.boundary p t ht).symm

/-- Two based triangles agree on the diagonal edge (the `s 1 = 0` face where both are
constantly the basepoint). -/
private theorem Hurewicz.DegreeTwo.SimplyConnected.basedTriangles_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ υ : BasedTriangle x) (s : SingularChains.Simplex 2)
    (hs : s 1 = 0) : τ.val s = υ.val s :=
  (τ.property s ⟨1, hs⟩).trans (υ.property s ⟨1, hs⟩).symm

/-- The based square loop gluing `τ` on the lower triangle and `υ` on the upper triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ υ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨(gluedTriangleHomotopyMap (τ.val.comp ContinuousMap.snd) (υ.val.comp ContinuousMap.snd)
          (fun _ => basedTriangles_diagonal τ υ)).comp
      ⟨fun t => ((0 : (unitInterval)), t), by fun_prop⟩,
    by
    intro t ht
    exact
      gluedTriangleHomotopyMap_boundary _ _ (fun _ => basedTriangles_diagonal τ υ) x
        (fun _ s hs => τ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
        (fun _ s hs => υ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩))) 0 t ht⟩

/-- `basedTrianglesLoop τ υ` is `τ` below the diagonal and `υ` above it. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_apply {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (t : Fin 2 → (unitInterval)) :
    basedTrianglesLoop τ υ t =
      if (t 1 : ℝ) ≤ t 0 then τ.val (triangleQuotient (t 0, t 1))
      else υ.val (triangleQuotient (t 1, t 0)) :=
  rfl

/-- `basedTrianglesLoop` sends diagonal points to `x`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (u : (unitInterval)) :
    basedTrianglesLoop τ υ (fun _ => u) = x := by
  rw [basedTrianglesLoop_apply, if_pos le_rfl]
  apply τ.property
  exact ⟨1, by simp only [triangleQuotient_one, min_self, sub_self]⟩

/-- The lower triangle restriction of `basedTrianglesLoop τ υ` is `τ`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp lowerSquareTriangle = τ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (lowerSquareTriangle s) = τ.val s
  rw [basedTrianglesLoop_apply]
  have hle : (lowerSquareTriangle s 1 : ℝ) ≤ lowerSquareTriangle s 0 := by
    rw [lowerSquareTriangle_zero, lowerSquareTriangle_one]
    exact le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  rw [if_pos hle]
  change
    τ.val (triangleQuotient ((lowerProductTriangle s).1, (lowerProductTriangle s).2)) = τ.val s
  exact congrArg τ.val (ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s)

/-- The triangle quotient of the swapped upper-square-triangle pair returns the original
simplex: the upper triangle of the square covers the standard triangle. -/
private theorem Hurewicz.DegreeTwo.SimplyConnected.triangleQuotient_swapped_upper
    (s : SingularChains.Simplex 2) :
    triangleQuotient (upperSquareTriangle s 1, upperSquareTriangle s 0) = s := by
  have hpair : (upperSquareTriangle s 1, upperSquareTriangle s 0) = lowerProductTriangle s := by
    apply Prod.ext <;> apply Subtype.ext
    · rw [upperSquareTriangle_one, lowerProductTriangle_fst]
    · rw [upperSquareTriangle_zero, lowerProductTriangle_snd]
  rw [hpair]
  exact ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s

/-- The upper triangle restriction of `basedTrianglesLoop τ υ` is `υ`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp upperSquareTriangle = υ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (upperSquareTriangle s) = υ.val s
  rw [basedTrianglesLoop_apply]
  split_ifs with h
  · have hs : s 1 = 0 := by
      rw [upperSquareTriangle_zero, upperSquareTriangle_one] at h
      exact le_antisymm (by linarith) (stdSimplex.zero_le s 1)
    have he : upperSquareTriangle s 0 = upperSquareTriangle s 1 := by
      apply Subtype.ext
      rw [upperSquareTriangle_zero, upperSquareTriangle_one, hs, zero_add]
    have hq : triangleQuotient (upperSquareTriangle s 0, upperSquareTriangle s 1) = s := by
      simpa only [he] using triangleQuotient_swapped_upper s
    rw [hq]
    exact basedTriangles_diagonal τ υ s hs
  · rw [triangleQuotient_swapped_upper]

/-- The `HomotopyRel` from `p` to `basedTrianglesLoop τ υ` assembled from triangle homotopies `L`, `U`. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  gluedTriangleHomotopy (L.cast rfl (basedTrianglesLoop_lower τ υ).symm)
    (U.cast rfl (basedTrianglesLoop_upper τ υ).symm) hdiag hL hU

/-- If `P` holds on all points of face `i`, it holds at every `s` with `s i = 0`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleProperty_of_face
    {P : SingularChains.Simplex 2 → Prop} (i : Fin 3)
    (h : ∀ u, P (SingularChains.simplexFace 1 i u)) (s : SingularChains.Simplex 2) (hs : s i = 0) :
    P s := by simpa only [simplexFace_inverse] using h (simplexFaceInverse 1 i ⟨s, hs⟩)

/-- The `HomotopyRel` from `p` to `basedTrianglesLoop τ υ` given homotopies to `τ` and `υ` on the two triangles. -/
def Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesHomotopy_of_faces {X : Type} [TopologicalSpace X]
    {x : X} {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag :
      ∀ r s, L (r, SingularChains.simplexFace 1 1 s) = U (r, SingularChains.simplexFace 1 1 s))
    (hL : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, L (r, SingularChains.simplexFace 1 i s) = x)
    (hU : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, U (r, SingularChains.simplexFace 1 i s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy τ υ L U
    (fun r s hs => triangleProperty_of_face (P := fun s => L (r, s) = U (r, s)) 1 (hdiag r) s hs)
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => L (r, s) = x) 0 (hL r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => L (r, s) = x) 2 (hL r 2 (by decide)) s))
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => U (r, s) = x) 0 (hU r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => U (r, s) = x) 2 (hU r 2 (by decide)) s))

/-- The edge-straightened `BasedTriangle` of the lower square triangle of `p`. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizedLowerTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp lowerSquareTriangle)
    (lowerSquareTriangle_verticesBased p)

/-- The edge-straightened `BasedTriangle` of the upper square triangle of `p`. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizedUpperTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp upperSquareTriangle)
    (upperSquareTriangle_verticesBased p)

/-- The homotopy from a vertex-based `2`-simplex to its edge-straightened triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizationTriangleHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(SingularChains.Simplex 2, X))
    (h : VerticesBased x 2 smp) : smp.Homotopy (edgeStraightenedTriangle x smp h).val
    where
  toContinuousMap := triangleEdgeStraighteningHomotopy x smp
  map_zero_left := triangleEdgeStraighteningHomotopy_zero x smp
  map_one_left _ := rfl

/-- The homotopy from `p ∘ lowerSquareTriangle` to its normalized triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareLowerNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).Homotopy (squareNormalizedLowerTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (lowerSquareTriangle_verticesBased p)

/-- The homotopy from `p ∘ upperSquareTriangle` to its normalized triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareUpperNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp upperSquareTriangle).Homotopy (squareNormalizedUpperTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (upperSquareTriangle_verticesBased p)

/-- On face `i`, the triangle edge-straightening homotopy is `edgeStraighteningHomotopy` of that face. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_edge_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(SingularChains.Simplex 2, X))
    (i : Fin 3) (r : (unitInterval)) (s : SingularChains.Simplex 1) :
    triangleEdgeStraighteningHomotopy x smp (r, SingularChains.simplexFace 1 i s) =
      edgeStraighteningHomotopy x (smp.comp (SingularChains.simplexFace 1 i)) (r, s) :=
  DFunLike.congr_fun (triangleEdgeStraighteningHomotopy_face x smp i) (r, s)

/-- The lower and upper normalization homotopies agree on face `1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_diagonal {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (s : SingularChains.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, SingularChains.simplexFace 1 1 s) =
      squareUpperNormalizationHomotopy p (r, SingularChains.simplexFace 1 1 s) := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, SingularChains.simplexFace 1 1 s) =
      triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, SingularChains.simplexFace 1 1 s)
  rw [squareNormalization_edge_face, squareNormalization_edge_face, squareTriangles_diagonal]

/-- The lower normalization homotopy is `x` on outer faces `i ≠ 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareLowerNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : SingularChains.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, SingularChains.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, SingularChains.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, lowerSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

/-- The upper normalization homotopy is `x` on outer faces `i ≠ 1`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareUpperNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : SingularChains.Simplex 1) :
    squareUpperNormalizationHomotopy p (r, SingularChains.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, SingularChains.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, upperSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

/-- The `HomotopyRel` from `p` to the loop of its normalized lower/upper triangles. -/
def Hurewicz.DegreeTwo.SimplyConnected.squareNormalizationHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)).val
      (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy_of_faces (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p) (squareLowerNormalizationHomotopy p)
    (squareUpperNormalizationHomotopy p) (squareNormalization_diagonal p)
    (squareLowerNormalization_outerFace p) (squareUpperNormalization_outerFace p)

/-- `p` is homotopic to `basedTrianglesLoop` of its normalized triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_homotopic {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    GenLoop.Homotopic p
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)) :=
  ⟨squareNormalizationHomotopy p⟩

/-! ### Subdivision triangle classes -/

/-- The square map of the positively oriented upper subdivision triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  Hurewicz.DegreeTwo.squareCoordinates.comp (squareAffineTriangle ![(0, 0), (1, 1), (0, 1)])

/-- The `0`-face of the upper positive subdivision triangle. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_zero
    (s : SingularChains.Simplex 2) : (subdivisionUpperPositiveSquareTriangle s 0 : ℝ) = s 1 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_fst_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

/-- The `1`-face of the upper positive subdivision triangle. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_one
    (s : SingularChains.Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_snd_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

/-- The coordinate sum of a subdivision triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionTriangle_coordinate_sum
    (s : SingularChains.Simplex 2) : s 0 + s 1 + s 2 = 1 := by
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  linarith

/-- `p (lowerSquareTriangle s) = x` for `s` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (lowerSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle s 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

/-- `p (upperSquareTriangle s) = x` for `s` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (upperSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle s 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

/-- `p (subdivisionUpperPositiveSquareTriangle s) = x` for `s` on the triangle boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (subdivisionUpperPositiveSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = 1
    rw [subdivisionUpperPositiveSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi
  · change s 2 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]

/-- The lower subdivision triangle as a based triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerBasedTriangle {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    BasedTriangle x :=
  ⟨p.val.comp lowerSquareTriangle, subdivisionLowerSquareTriangle_based p hd⟩

/-- The upper subdivision triangle read against the orientation, as a `BasedTriangle`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp upperSquareTriangle, subdivisionUpperNegativeSquareTriangle_based p hd⟩

/-- The upper subdivision triangle read with the orientation, as a `BasedTriangle`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp subdivisionUpperPositiveSquareTriangle,
    subdivisionUpperPositiveSquareTriangle_based p hd⟩

/-- The lower triangle loop equals the loop of the lower based triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionLowerTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionLowerTriangleLoop p hd = basedTriangleLoop (subdivisionLowerBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, Min.min (u 0) (u 1)] = p (lowerSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

/-- The upper triangle loops equal the loops of the upper based triangles. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperTriangleLoop p hd =
      basedTriangleLoop (subdivisionUpperPositiveBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![subdivisionSubMin (u 0) (u 1), u 0] =
      p (subdivisionUpperPositiveSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp [subdivisionSubMin]

/-- The loop of the upper negative based triangle at `u` is `p ![min (u 0) (u 1), u 0]`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeBasedTriangle_loop_apply {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : Fin 2 → (unitInterval)) :
    basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) u =
      p ![Min.min (u 0) (u 1), u 0] := by
  change p (upperSquareTriangle (triangleQuotient (u 0, u 1))) = p ![Min.min (u 0) (u 1), u 0]
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

/-- `⟦p⟧` splits as the sum of the lower and upper positive based-triangle classes. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_basedTriangleClass_sum {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) +
        basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) := by
  simpa only [subdivisionLowerTriangleLoop_eq_basedTriangleLoop,
    subdivisionUpperTriangleLoop_eq_basedTriangleLoop, basedTriangleClass] using
    subdivision_additiveClass p hd

/-- The subdivision-square map underlying the negatively oriented upper triangle. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) (u 1), u 0]
  continuous_toFun := by fun_prop

/-- The `subdivisionUpperNegativeMap` with the second coordinate reversed. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0]
  continuous_toFun := by fun_prop

/-- `p (subdivisionUpperNegativeMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

/-- `p (subdivisionUpperNegativeReversedMap u) = x` for `u` on the square boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeReversedMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩

/-- The pullback loop `p ∘ subdivisionUpperNegativeMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeMap (subdivisionUpperNegativeMap_based p hd)

/-- The pullback loop `p ∘ subdivisionUpperNegativeReversedMap`. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedLoop {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeReversedMap
    (subdivisionUpperNegativeReversedMap_based p hd)

/-- The upper triangle map and the reversed upper negative map land on the same side of the boundary. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperTriangleMap u) (subdivisionUpperNegativeReversedMap u) :=
  by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .one 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperTriangleMap, h])
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact
      .zero 0 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])

/-- The homotopy relating the upper negative loop to its reversal. -/
def Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientationHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperTriangleLoop p hd).val.HomotopyRel
      (subdivisionUpperNegativeReversedLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperTriangleMap_based p hd)
    (subdivisionUpperNegativeReversedMap_based p hd) subdivisionUpperOrientation_sides

/-- The reversed upper negative loop is `symmAt 1` of the upper negative loop. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeReversedLoop_eq_symmAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeReversedLoop p hd =
      GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0] =
      subdivisionUpperNegativeLoop p hd
        (fun j => if j = 1 then (unitInterval.symm) (u 1) else u j)
  simp [subdivisionUpperNegativeLoop, subdivisionPullbackLoop, subdivisionUpperNegativeMap]

/-- The upper triangle loop is homotopic to the `symmAt 1`-reversed upper negative loop. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic (subdivisionUpperTriangleLoop p hd)
      (GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)) := by
  rw [← subdivisionUpperNegativeReversedLoop_eq_symmAt]
  exact ⟨subdivisionUpperOrientationHomotopy p hd⟩

/-- `⟦subdivisionUpperTriangleLoop⟧ = ⟦subdivisionUpperNegativeLoop⟧⁻¹` in `π_2`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_class {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((·⁻¹) : π_ 2 X x → π_ 2 X x) ⟦subdivisionUpperNegativeLoop p hd⟧ := by
  have h :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      (⟦GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)⟧ : π_ 2 X x) :=
    Quotient.sound (subdivisionUpperOrientation_homotopic p hd)
  exact
    h.trans
      (HomotopyGroup.inv_spec (i := (1 : Fin 2)) (p := subdivisionUpperNegativeLoop p hd)).symm

/-- The additive form of `subdivisionUpperOrientation_class`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperOrientation_additiveClass {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((-·) : Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivisionUpperOrientation_class p hd)

/-- From `a = b + c` and `c = -d`, conclude `a = b - d`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_eq_sub_of_eq_add {A : Type*} [AddGroup A]
    {a b c d : A} (h : a = b + c) (hc : c = -d) : a = b - d :=
  h.trans ((congrArg (fun z => b + z) hc).trans (sub_eq_add_neg b d).symm)

/-- The upper negative loop equals the loop of its based triangle. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperNegativeLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeLoop p hd =
      basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  exact (subdivisionUpperNegativeBasedTriangle_loop_apply p hd u).symm

/-- The class of the upper positive based triangle is the negated upper negative
class. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivisionUpperPositiveBasedTriangle_class_eq_neg
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) =
      -basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) := by
  unfold basedTriangleClass
  rw [← subdivisionUpperTriangleLoop_eq_basedTriangleLoop, ←
    subdivisionUpperNegativeLoop_eq_basedTriangleLoop]
  exact subdivisionUpperOrientation_additiveClass p hd

/-- `⟦p⟧` splits as the lower based-triangle class minus the upper negative one. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.subdivision_basedTriangleClass_sub {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) -
        basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_basedTriangleClass_sum p hd)
    (subdivisionUpperPositiveBasedTriangle_class_eq_neg p hd)

/-- `⟦basedTrianglesLoop τ υ⟧` is `basedTriangleClass τ - basedTriangleClass υ`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.basedTrianglesLoop_class {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x) =
      basedTriangleClass τ - basedTriangleClass υ := by
  have hd : ∀ t : (unitInterval), basedTrianglesLoop τ υ ![t, t] = x := by
    intro t
    have he : (![t, t] : Fin 2 → (unitInterval)) = fun _ => t := by
      funext i
      fin_cases i <;> rfl
    rw [he, basedTrianglesLoop_diagonal]
  have hl : subdivisionLowerBasedTriangle (basedTrianglesLoop τ υ) hd = τ :=
    Subtype.ext (basedTrianglesLoop_lower τ υ)
  have hu : subdivisionUpperNegativeBasedTriangle (basedTrianglesLoop τ υ) hd = υ :=
    Subtype.ext (basedTrianglesLoop_upper τ υ)
  simpa only [hl, hu] using subdivision_basedTriangleClass_sub (basedTrianglesLoop τ υ) hd

/-- `⟦p⟧ = ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_quotient {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (⟦p⟧ : π_ 2 X x) =
      ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧ :=
  Quotient.sound (squareNormalization_homotopic p)

/-- `basedTriangleClass (lower) - basedTriangleClass (upper) = ⟦p⟧` additively. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.squareNormalization_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    basedTriangleClass (squareNormalizedLowerTriangle p) -
        basedTriangleClass (squareNormalizedUpperTriangle p) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  have h := congrArg Additive.ofMul (squareNormalization_quotient p)
  exact
    (basedTrianglesLoop_class (squareNormalizedLowerTriangle p)
          (squareNormalizedUpperTriangle p)).symm.trans
      h.symm

/-- `triangleClassOperator` of the square chain of `p` is `⟦p⟧` additively. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.triangleClassOperator_squareChain {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    triangleClassOperator x (Hurewicz.DegreeTwo.squareChain p) = Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [squareChain_two_triangles, map_sub, triangleClassOperator_simplex,
    triangleClassOperator_simplex,
    normalizedTriangle_of_verticesBased x _ (lowerSquareTriangle_verticesBased p),
    normalizedTriangle_of_verticesBased x _ (upperSquareTriangle_verticesBased p)]
  exact squareNormalization_class p

/-- `hurewiczInverse ∘ hurewiczMap` on a `⟦p⟧` representative returns `⟦p⟧`. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_hurewiczMap_mk {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczInverse x (Hurewicz.DegreeTwo.hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [Hurewicz.DegreeTwo.hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact triangleClassOperator_squareChain x p

/-- `hurewiczInverse` of `hurewiczMap` of a class returns the class. -/
@[simp]
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczInverse x (Hurewicz.DegreeTwo.hurewiczMap x a) = a := by
  change
    hurewiczInverse x (Hurewicz.DegreeTwo.hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

/-- `hurewiczInverse ∘ hurewiczMap` is the identity on `Additive (π_2)`. -/
theorem Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_comp_hurewiczMap {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (hurewiczInverse x).comp (Hurewicz.DegreeTwo.hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

/-! ### The degree-two Hurewicz equivalence -/

/-- **The degree-two Hurewicz equivalence**: for `SimplyConnectedSpace X`,
`hurewiczMap` and `hurewiczInverse` are inverse `ℤ`-linear maps, giving
`Additive (π_ 2 X x) ≃ₗ[ℤ] H_2 X`. -/
def Hurewicz.degreeTwoLinearEquiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    Additive (π_ 2 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2 :=
  LinearEquiv.ofLinearMap (Hurewicz.DegreeTwo.hurewiczMap x)
    (Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse x)
    (Hurewicz.DegreeTwo.SimplyConnected.hurewiczMap_comp_hurewiczInverse x)
    (Hurewicz.DegreeTwo.SimplyConnected.hurewiczInverse_comp_hurewiczMap x)

/-- The monoid equivalence `π_ 2 X x ≃* Multiplicative (H_2 X)` for simply
connected `X`. -/
def Hurewicz.DegreeTwo.SimplyConnected.hurewiczPi2Equiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    π_ 2 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  __ := Hurewicz.DegreeTwo.hurewiczPi2 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))


/-! ### Composing homotopy families -/

/-- A continuous cylinder map `I × A → X` viewed as a `Homotopy` between its
time-`0` and time-`1` slices. -/
def Hurewicz.cylinderHomotopy {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (H : C((unitInterval) × A, X)) :
    ContinuousMap.Homotopy (Hurewicz.DegreeTwo.SimplyConnected.timeSlice H 0)
      (Hurewicz.DegreeTwo.SimplyConnected.timeSlice H 1)
    where
  toContinuousMap := H
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Transitivity of homotopies commutes with precomposition by a continuous map. -/
theorem Hurewicz.homotopyTrans_compContinuousMap {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (f : C(B, A)) :
    (F.trans G).toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap f) =
      ((F.compContinuousMap f).trans (G.compContinuousMap f)).toContinuousMap := by
  ext z
  change (F.trans G) (z.1, f z.2) = ((F.compContinuousMap f).trans (G.compContinuousMap f)) z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

/-- The concatenation of two constant homotopies is the constant homotopy. -/
theorem Hurewicz.homotopyTrans_const {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (x : X)
    (hF : F.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x)
    (hG : G.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x) :
    (F.trans G).toContinuousMap = ContinuousMap.const ((unitInterval) × A) x := by
  ext z
  change (F.trans G) z = x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

/-- `HomotopyRel` transitivity respects equality of the homotopies. -/
theorem Hurewicz.homotopyTrans_congr {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (F' : g₀.Homotopy g₁)
    (G' : g₁.Homotopy g₂) (hF : F.toContinuousMap = F'.toContinuousMap)
    (hG : G.toContinuousMap = G'.toContinuousMap) :
    (F.trans G).toContinuousMap = (F'.trans G').toContinuousMap := by
  ext z
  change (F.trans G) z = (F'.trans G') z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

/-- A simplex-indexed family `H` starting at `smp` viewed as a `Homotopy` from
`smp` to its time-`1` endpoint. -/
def Hurewicz.simplexFamilyHomotopy {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : SingularChains.SingularSimplex X n) :
    smp.Homotopy (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1) :=
  (cylinderHomotopy (H smp)).cast (by ext s; exact h₀ smp s) rfl

/-- The composition of two coherent simplex homotopy families (first `H₀` then
`H₁`), staying face-compatible. -/
def Hurewicz.composeSimplexHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) : C((unitInterval) × SingularChains.Simplex n, X) :=
  ((simplexFamilyHomotopy H hH₀ smp).trans
      (simplexFamilyHomotopy G hG₀
        (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1))).toContinuousMap

/-- At time `0`, `composeSimplexHomotopies H₀ H₁` is `H₀` at time `0`. -/
@[simp]
theorem Hurewicz.composeSimplexHomotopies_zero {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) (s : SingularChains.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (0, s) = smp s :=
  ContinuousMap.Homotopy.apply_zero _ s

/-- At time `1`, `composeSimplexHomotopies H G` evaluates `G` at the time-`1`
endpoint of `H smp`. -/
@[simp]
theorem Hurewicz.composeSimplexHomotopies_one {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) (s : SingularChains.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (1, s) =
      G (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1) (1, s) :=
  ContinuousMap.Homotopy.apply_one _ s

/-- The time-`1` slice of the composed homotopy is the time-`1` slice of `G`
applied to the time-`1` endpoint of `H smp`. -/
@[simp]
theorem Hurewicz.timeSlice_composeSimplexHomotopies_one {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 1 =
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice
        (G (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H smp) 1)) 1 := by
  ext s
  exact composeSimplexHomotopies_one H G hH₀ hG₀ smp s

/-- The face restriction of the composed homotopy is the composition of the face
homotopies. -/
theorem Hurewicz.composeSimplexHomotopies_face {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' G' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH'₀ : ∀ smp s, H' smp (0, s) = smp s) (hG'₀ : ∀ smp s, G' smp (0, s) = smp s)
    (hH : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hG : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n G G') :
    Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n
      (composeSimplexHomotopies H G hH₀ hG₀) (composeSimplexHomotopies H' G' hH'₀ hG'₀) := by
  intro smp i
  unfold composeSimplexHomotopies
  rw [homotopyTrans_compContinuousMap]
  apply homotopyTrans_congr
  · change
      (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
        H (smp.comp (SingularChains.simplexFace n i))
    exact hH smp i
  · change
      (G' (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1)).comp
          ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
        G
          (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H (smp.comp (SingularChains.simplexFace n i)))
            1)
    rw [hG (Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H' smp) 1) i,
      Hurewicz.DegreeTwo.SimplyConnected.timeSlice_face hH smp i 1]

/-- If `H` and `G` are both stationary on the constant simplex at `x`, so is
their composition on the constant simplex. -/
theorem Hurewicz.composeSimplexHomotopies_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s) (x : X)
    (hH :
      H (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x)
    (hG :
      G (ContinuousMap.const (SingularChains.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x) :
    composeSimplexHomotopies H G hH₀ hG₀ (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  have h₁ :
    Hurewicz.DegreeTwo.SimplyConnected.timeSlice (H (ContinuousMap.const (SingularChains.Simplex n) x))
        1 =
      ContinuousMap.const (SingularChains.Simplex n) x := by
    rw [hH]
    rfl
  unfold composeSimplexHomotopies
  apply homotopyTrans_const
  · exact hH
  · change
      G
          (Hurewicz.DegreeTwo.SimplyConnected.timeSlice
            (H (ContinuousMap.const (SingularChains.Simplex n) x)) 1) =
        _
    rw [h₁]
    exact hG


/-- The glued boundary map of a constant family is the constant map. -/
theorem Hurewicz.gluedBoundaryMap_constant_value {X : Type} [TopologicalSpace X] {n : ℕ}
    (f : C(SingularChains.Simplex n, X))
    (g : C((unitInterval) × Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary n, X))
    (h₀ : ∀ s, g (0, s) = f s.val) (x : X) (hf : ∀ s, f s = x) (hg : ∀ u, g u = x)
    (u : ↥(Hurewicz.DegreeTwo.SimplyConnected.bottomOrSide n)) :
    Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap f g h₀ u = x := by
  rcases u.property with hb | hs
  · have hu : u = Hurewicz.DegreeTwo.SimplyConnected.bottomInclusion n u.val.2 := by
      apply Subtype.ext
      exact Prod.ext hb rfl
    exact
      (congrArg (Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap_bottomInclusion f g h₀ _).trans (hf _))
  · have hu : u = Hurewicz.DegreeTwo.SimplyConnected.sideInclusion n (u.val.1, ⟨u.val.2, hs⟩) := by
      apply Subtype.ext
      rfl
    exact
      (congrArg (Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap_sideInclusion f g h₀ _).trans (hg _))

/-- The coherent boundary homotopy of the constant family is stationary. -/
theorem Hurewicz.coherentFaceBoundaryHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hc :
      H' (ContinuousMap.const (SingularChains.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex (n + 1)) x) :
    Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
        (ContinuousMap.const (SingularChains.Simplex (n + 2)) x) =
      ContinuousMap.const
        ((unitInterval) × Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (n + 2)) x := by
  unfold Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy
  apply
    (Hurewicz.DegreeTwo.SimplyConnected.glueFaceHomotopies_unique _ _ (ContinuousMap.const _ x)
        ?_).symm
  intro i r s
  change x = H' (ContinuousMap.const (SingularChains.Simplex (n + 1)) x) (r, s)
  rw [hc]
  rfl

/-- The coherent extension of the constant family is stationary. -/
theorem Hurewicz.extendCoherentSimplexHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : Hurewicz.DegreeTwo.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s) (x : X)
    (hc :
      H' (ContinuousMap.const (SingularChains.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × SingularChains.Simplex (n + 1)) x) :
    Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy H H' h h₀
        (ContinuousMap.const (SingularChains.Simplex (n + 2)) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex (n + 2)) x := by
  unfold Hurewicz.DegreeTwo.SimplyConnected.extendCoherentSimplexHomotopy
  ext u
  change
    Hurewicz.DegreeTwo.SimplyConnected.gluedBoundaryMap
        (ContinuousMap.const (SingularChains.Simplex (n + 2)) x)
        (Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
          (ContinuousMap.const (SingularChains.Simplex (n + 2)) x))
        (Hurewicz.DegreeTwo.SimplyConnected.coherentFaceBoundaryHomotopy_zero H H' h h₀
          (ContinuousMap.const (SingularChains.Simplex (n + 2)) x))
        (Hurewicz.DegreeTwo.SimplyConnected.cylinderRetraction (n + 2) u) =
      x
  apply gluedBoundaryMap_constant_value _ _ _ x (fun _ => rfl)
  intro v
  exact
    congrArg
      (fun F : C((unitInterval) × Hurewicz.DegreeTwo.SimplyConnected.SimplexBoundary (n + 2), X) =>
        F v)
      (coherentFaceBoundaryHomotopy_const H H' h x hc)

