/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.CrossProductPoint
/-!
# The square chain and the degree-two Hurewicz map

A based square `p : GenLoop (Fin 2) X x` is a path of based loops `I → Ω X`; evaluating it along
the fundamental chain of the interval gives a singular `2`-chain `squareChain p`, a cycle whose
class `squareHomologyClass p ∈ H_2 X` depends only on the homotopy class of `p` and is additive
for concatenation.  This is the degree-two Hurewicz homomorphism
`Hurewicz.DegreeTwo.hurewiczMap x : Additive (π_ 2 X x) →ₗ[ℤ] H_2 X` (Hatcher, §4.2, the
homomorphism `h : π_n(X, x₀) → H_n(X)` at `n = 2`).

## Main definitions

* `Hurewicz.DegreeTwo.evaluation`, `intervalChain`, `suspensionOne`, `suspensionTwo`: the
  suspension operators `Chains (Ω X) n →ₗ[ℤ] Chains X (n + 1)`, with
  `boundaryThree_suspensionTwo` (`∂ ∘ S₂ = S₁ ∘ ∂`) and `boundaryTwo_suspensionOne_of_cycle`.
* `Hurewicz.DegreeTwo.pathSquareClass`: the class of a path of loops, invariant under homotopy
  (`pathSquareClass_homotopic`) and additive (`pathSquareClass_trans`).
* `Hurewicz.DegreeTwo.squareChain`, `squareCycle`, `squareHomologyClass`: the singular `2`-cycle
  of a based square and its class.
* `Hurewicz.DegreeTwo.hurewiczMap`: the Hurewicz map `π_ 2 X x → H_2 X`.
-/

open Set Function Topology

noncomputable section

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
