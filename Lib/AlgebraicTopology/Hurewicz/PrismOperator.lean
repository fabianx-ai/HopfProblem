/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.CrossInsert

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

noncomputable section

namespace Mathoverflow1973

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.crossProductTriangle_zero_eq_zeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    PeriodTorusHigherHomology.crossProductTriangle X Y 0 =
      PeriodTorusHigherHomology.crossProductZeroRight X Y 2 := by
  apply PeriodTorusHigherHomology.chainBilinearMap_ext X Y 2 0
  intro σ τ
  rw [PeriodTorusHigherHomology.crossProductTriangle_simplex,
    PeriodTorusHigherHomology.formalTriangleCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex,
    PeriodTorusHigherHomology.crossProductZeroRight_simplex]
  apply congrArg (SingularChains.simplexChain (X × Y) 2)
  change
    (σ.prodMap τ).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 2 i, SingularMayerVietoris.stdVertices 0 0))) =
      (PeriodTorusHigherHomology.crossInsertRight
            (PeriodTorusHigherHomology.zeroSimplexValue τ)).comp
        σ
  rw [PeriodTorusHigherHomology.productAffineSimplex_point_right,
    SingularMayerVietoris.affineSimplex_stdVertices, ContinuousMap.comp_id]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.crossProductTriangle_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularChains.Chains X 2) (y : Y) :
    PeriodTorusHigherHomology.crossProductTriangle X Y 0 a (SingularChains.pointChain y) =
      SingularChains.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 2 a := by
  rw [crossProductTriangle_zero_eq_zeroRight, SingularChains.pointChain,
    PeriodTorusHigherHomology.crossProductZeroRight_simplex_right]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.crossProductEdge_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularChains.Chains X 1) (y : Y) :
    PeriodTorusHigherHomology.crossProductEdge X Y 0 a (SingularChains.pointChain y) =
      SingularChains.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 1 a := by
  rw [SingularChains.pointChain, PeriodTorusHigherHomology.crossProductEdge_zero_simplex_right]
  rfl

abbrev SecondHurewicz.Remaining :=
  { j : Fin 2 // j ≠ 0 }

abbrev SecondHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

def SecondHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (unitInterval), X)
    where
  toFun z := z.1 (fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem SecondHurewicz.evaluation_zero {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 0) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inl rfl⟩

@[simp]
theorem SecondHurewicz.evaluation_one {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 1) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inr rfl⟩

@[simp]
theorem SecondHurewicz.evaluation_comp_right_zero {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_zero x p

@[simp]
theorem SecondHurewicz.evaluation_comp_right_one {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_one x p

def SecondHurewicz.squareCoordinates : C((unitInterval) × (unitInterval), Fin 2 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 2) (z.1, fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem SecondHurewicz.squareCoordinates_zero (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 0 = z.1 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem SecondHurewicz.squareCoordinates_one (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 1 = z.2 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

def SecondHurewicz.squareMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    C((unitInterval) × (unitInterval), X) :=
  p.val.comp squareCoordinates

theorem SecondHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
          (ContinuousMap.id (unitInterval))) =
      squareMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.intervalChain : SingularChains.Chains (unitInterval) 1 :=
  SingularChains.pathChain Path.id

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.intervalChain_boundary :
    SingularChains.boundaryOne (unitInterval) intervalChain =
      SingularChains.pointChain (1 : (unitInterval)) -
        SingularChains.pointChain (0 : (unitInterval)) :=
  SingularChains.boundaryOne_pathChain Path.id

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluation_right_zero_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : SingularChains.Chains (BasedLoopSpace x) n) :
    SingularChains.inducedChain (evaluation x) n
        (SingularChains.inducedChain
          (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) n a) =
      SingularChains.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((SingularChains.inducedChain (evaluation x) n).comp
          (SingularChains.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) n))
        a =
      _
  rw [← SingularChains.inducedChain_comp, evaluation_comp_right_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluation_right_one_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : SingularChains.Chains (BasedLoopSpace x) n) :
    SingularChains.inducedChain (evaluation x) n
        (SingularChains.inducedChain
          (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) n a) =
      SingularChains.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((SingularChains.inducedChain (evaluation x) n).comp
          (SingularChains.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) n))
        a =
      _
  rw [← SingularChains.inducedChain_comp, evaluation_comp_right_one]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluated_edge_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 1) :
    SingularChains.inducedChain (evaluation x) 1
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
          (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductEdge_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluated_triangle_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 2) :
    SingularChains.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
          (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductTriangle_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    SingularChains.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] SingularChains.Chains X 2 :=
  (SingularChains.inducedChain (evaluation x) 2).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      SingularChains.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    SingularChains.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] SingularChains.Chains X 3 :=
  (SingularChains.inducedChain (evaluation x) 3).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      SingularChains.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.boundaryTwo_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 1)
    (ha : SingularChains.boundaryOne (BasedLoopSpace x) a = 0) :
    SingularChains.boundaryTwo X (suspensionOne x a) = 0 := by
  change ((SingularChains.singularComplex X).d 2 1).hom (suspensionOne x a) = 0
  rw [suspensionOne_apply, ← SingularChains.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 0]
  change
    SingularChains.inducedChain (evaluation x) 1
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x) (unitInterval) 1
            (SingularChains.boundaryOne (BasedLoopSpace x) a) intervalChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
            (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_endpoint_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.boundaryThree_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : SingularChains.Chains (BasedLoopSpace x) 2) :
    ((SingularChains.singularComplex X).d 3 2).hom (suspensionTwo x a) =
      suspensionOne x (SingularChains.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← SingularChains.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 0]
  change
    SingularChains.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1
            (SingularChains.boundaryTwo (BasedLoopSpace x) a) intervalChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
            (SingularChains.boundaryOne (unitInterval) intervalChain)) =
      _
  rw [map_add, evaluated_triangle_endpoint_cancel, add_zero]
  rfl

def SecondHurewicz.pathSquareCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (suspensionOne x (SingularChains.pathChain p))
    (boundaryTwo_suspensionOne_of_cycle x (SingularChains.pathChain p)
      (SingularChains.boundaryOne_loop p))

@[simp]
theorem SecondHurewicz.pathSquareCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathSquareCycle x p).1 = suspensionOne x (SingularChains.pathChain p) :=
  rfl

def SecondHurewicz.pathSquareClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
    (pathSquareCycle x p)

theorem SecondHurewicz.pathSquare_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((SingularChains.singularComplex X).d 3 2).hom
        (suspensionTwo x (SingularChains.homotopyChain H)) =
      (pathSquareCycle x p).1 - (pathSquareCycle x q).1 := by
  rw [boundaryThree_suspensionTwo, SingularChains.boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem SecondHurewicz.pathSquareClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathSquareClass x p = pathSquareClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 2 _
        _).mpr
    ⟨suspensionTwo x (SingularChains.homotopyChain H), pathSquare_homotopy_boundary x H⟩

theorem SecondHurewicz.pathSquareClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathSquareClass x p = pathSquareClass x q := by
  obtain ⟨H⟩ := h
  exact pathSquareClass_homotopy x H

@[simp]
theorem SecondHurewicz.pathSquareClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathSquareClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (SingularChains.singularComplex X)
        2 _).mpr
  refine
    ⟨suspensionTwo x (SingularChains.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryThree_suspensionTwo, SingularChains.boundaryTwo_constantTriangleChain]
  rfl

theorem SecondHurewicz.pathSquare_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((SingularChains.singularComplex X).d 3 2).hom
        (-suspensionTwo x (SingularChains.concatChain p q)) =
      (pathSquareCycle x (p.trans q)).1 - ((pathSquareCycle x p).1 + (pathSquareCycle x q).1) := by
  rw [map_neg, boundaryThree_suspensionTwo, SingularChains.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathSquareCycle_val]
  abel

theorem SecondHurewicz.pathSquareClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathSquareClass x (p.trans q) = pathSquareClass x p + pathSquareClass x q := by
  unfold pathSquareClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (SingularChains.singularComplex X) 2 _
        _).mpr
  exact ⟨-suspensionTwo x (SingularChains.concatChain p q), pathSquare_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.productSquareChain :
    SingularChains.Chains ((unitInterval) × (unitInterval)) 2 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
    intervalChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.productSquareChain_boundary :
    SingularChains.boundaryTwo ((unitInterval) × (unitInterval)) productSquareChain =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft (1 : (unitInterval)))
            1 intervalChain -
          SingularChains.inducedChain
            (SingularHomology.crossInsertLeft (0 : (unitInterval))) 1 intervalChain -
        (SingularChains.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) 1 intervalChain -
          SingularChains.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) 1 intervalChain) := by
  change
    ((SingularChains.singularComplex ((unitInterval) × (unitInterval))).d 2 1).hom
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
          intervalChain) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 0]
  change
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (unitInterval) 1
          (SingularChains.boundaryOne (unitInterval) intervalChain) intervalChain -
        PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 0 intervalChain
          (SingularChains.boundaryOne (unitInterval) intervalChain) =
      _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply, crossProductEdge_point_right]
  simp only [SingularChains.pointChain,
    PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.fundamentalSquareChain : SingularChains.Chains (Fin 2 → (unitInterval)) 2 :=
  SingularChains.inducedChain squareCoordinates 2 productSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.induced_intervalChain {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) :
    SingularChains.inducedChain p.toContinuousMap 1 intervalChain = SingularChains.pathChain p := by
  rw [intervalChain, SingularChains.pathChain, SingularChains.inducedChain_simplex]
  apply congrArg (SingularChains.simplexChain X 1)
  ext s
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    suspensionOne x (SingularChains.pathChain (GenLoop.toLoop (0 : Fin 2) p)) =
      SingularChains.inducedChain (squareMap p) 2 productSquareChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.squareChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    SingularChains.Chains X 2 :=
  suspensionOne x (SingularChains.pathChain (GenLoop.toLoop (0 : Fin 2) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareChain_boundary {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : SingularChains.boundaryTwo X (squareChain p) = 0 :=
  boundaryTwo_suspensionOne_of_cycle x _ (SingularChains.boundaryOne_loop (GenLoop.toLoop 0 p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.squareCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  pathSquareCycle x (GenLoop.toLoop (0 : Fin 2) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.squareHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
    (squareCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareHomologyClass_eq_pathSquareClass {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    squareHomologyClass p = pathSquareClass x (GenLoop.toLoop (0 : Fin 2) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x} (h : GenLoop.Homotopic p q) :
    squareHomologyClass p = squareHomologyClass q :=
  pathSquareClass_homotopic x (GenLoop.homotopicTo (0 : Fin 2) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.const : GenLoop (Fin 2) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.squareHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    squareHomologyClass (GenLoop.const : GenLoop (Fin 2) X x) = 0 := by
  rw [squareHomologyClass_eq_pathSquareClass, toLoop_const, pathSquareClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.transAt (0 : Fin 2) p q) =
      (GenLoop.toLoop (0 : Fin 2) p).trans (GenLoop.toLoop (0 : Fin 2) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 2))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 2)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    squareHomologyClass (GenLoop.transAt (0 : Fin 2) p q) =
      squareHomologyClass p + squareHomologyClass q := by
  simp only [squareHomologyClass_eq_pathSquareClass, toLoop_transAt, pathSquareClass_trans]

def SecondHurewicz.mapGenLoop {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : C(GenLoop N X x, GenLoop N Y (f x))
    where
  toFun p := ⟨f.comp p.val, fun t ht => congrArg f (p.property t ht)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem SecondHurewicz.mapGenLoop_val {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop N X x) : (mapGenLoop f x p).val = f.comp p.val :=
  rfl

@[simp]
theorem SecondHurewicz.mapGenLoop_const {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapGenLoop (N := N) f x GenLoop.const = GenLoop.const :=
  rfl

theorem SecondHurewicz.mapGenLoop_homotopic {N X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f x p) (mapGenLoop f x q) :=
  h.comp_continuousMap f

@[simp]
theorem SecondHurewicz.mapGenLoop_transAt {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] (f : C(X, Y)) (x : X) (i : N) (p q : GenLoop N X x) :
    mapGenLoop f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f x p) (mapGenLoop f x q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) = if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

def SecondHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x → SingularMayerVietoris.SingularHomology X 2 :=
  Quotient.lift squareHomologyClass (fun _ _ h => squareHomologyClass_homotopic h)

def SecondHurewicz.hurewiczPi2 {X : Type} [TopologicalSpace X] (x : X) :
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

def SecondHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 2 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2
    where
  toFun := (hurewiczPi2 x).toAdditiveLeft
  map_add' := (hurewiczPi2 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi2 x).toAdditiveLeft ℤ ℤ n a

theorem SecondHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 2) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (squareCycle p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  H.comp (SingularHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.crossPoint_left {A : Type} [TopologicalSpace A] (n : ℕ)
    (t : (unitInterval)) (c : SingularChains.Chains A n) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) A n (SingularChains.pointChain t)
        c =
      SingularChains.inducedChain (SingularHomology.crossInsertLeft t) n c := by
  rw [SingularChains.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.inducedChain_timeSlice {A X : Type} [TopologicalSpace A]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.prismOperator {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) :
    SingularChains.Chains A n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  (SingularChains.inducedChain H (n + 1)).comp
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n SecondHurewicz.intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.prismOperator_apply {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) (c : SingularChains.Chains A n) :
    prismOperator n H c =
      SingularChains.inducedChain H (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n
          SecondHurewicz.intervalChain c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.prismOperator_boundary {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (c : SingularChains.Chains A (n + 1)) :
    ((SingularChains.singularComplex X).d (n + 2) (n + 1)).hom (prismOperator (n + 1) H c) =
      SingularChains.inducedChain (timeSlice H 1) (n + 1) c -
          SingularChains.inducedChain (timeSlice H 0) (n + 1) c -
        prismOperator n H (((SingularChains.singularComplex A).d (n + 1) n).hom c) := by
  rw [prismOperator_apply, ← SingularChains.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary n]
  change
    SingularChains.inducedChain H (n + 1)
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) A (n + 1)
            (SingularChains.boundaryOne (unitInterval) SecondHurewicz.intervalChain) c -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n
            SecondHurewicz.intervalChain
            (((SingularChains.singularComplex A).d (n + 1) n).hom c)) =
      _
  simp only [SecondHurewicz.intervalChain_boundary, map_sub, LinearMap.sub_apply, crossPoint_left,
    inducedChain_timeSlice, prismOperator_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.prismOperator_domain {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] (n : ℕ) (f : C(A, B)) (H : C((unitInterval) × B, X))
    (c : SingularChains.Chains A n) :
    prismOperator n (H.comp ((ContinuousMap.id (unitInterval)).prodMap f)) c =
      prismOperator n H (SingularChains.inducedChain f n c) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f n
      SecondHurewicz.intervalChain c
  rw [SingularChains.inducedChain_id, LinearMap.id_apply] at h
  simp only [prismOperator_apply, SingularChains.inducedChain_comp, LinearMap.comp_apply]
  exact congrArg (SingularChains.inducedChain H (n + 1)) h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.simplexPrism {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : C((unitInterval) × SingularChains.Simplex n, X)) : SingularChains.Chains X (n + 1) :=
  prismOperator n H
    (SingularChains.simplexChain (SingularChains.Simplex n) n
      (ContinuousMap.id (SingularChains.Simplex n)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.prismOperator_simplex {A X : Type} [TopologicalSpace A]
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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.simplexPrism_boundary {X : Type} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.simplexEndpointOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (t : (unitInterval)) : SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X n :=
  SingularChains.chainLift X n fun smp => SingularChains.simplexChain X n (timeSlice (H smp) t)

@[simp]
theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (t : (unitInterval)) (smp : SingularChains.SingularSimplex X n) :
    simplexEndpointOperator n H t (SingularChains.simplexChain X n smp) =
      SingularChains.simplexChain X n (timeSlice (H smp) t) :=
  SingularChains.chainLift_simplex X n _ smp

def SecondHurewicz.SimplyConnected.simplexPrismOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X)) :
    SingularChains.Chains X n →ₗ[ℤ] SingularChains.Chains X (n + 1) :=
  SingularChains.chainLift X n fun smp => simplexPrism n (H smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.simplexPrismOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (smp : SingularChains.SingularSimplex X n) :
    simplexPrismOperator n H (SingularChains.simplexChain X n smp) = simplexPrism n (H smp) :=
  SingularChains.chainLift_simplex X n _ smp

def SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X)) :
    Prop :=
  ∀ smp i,
    (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
      H (smp.comp (SingularChains.simplexFace n i))

theorem SecondHurewicz.SimplyConnected.timeSlice_face {X : Type} [TopologicalSpace X] {n : ℕ}
    {H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X)}
    {H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X)}
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (t : (unitInterval)) :
    (timeSlice (H' smp) t).comp (SingularChains.simplexFace n i) =
      timeSlice (H (smp.comp (SingularChains.simplexFace n i))) t :=
  congrArg (fun F => timeSlice F t) (h smp i)

theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary {X : Type}
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

theorem SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary {X : Type}
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

theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (h₀ : ∀ smp, timeSlice (H smp) 0 = smp) : simplexEndpointOperator n H 0 = LinearMap.id := by
  apply SingularChains.chainMap_ext X n
  intro smp
  rw [simplexEndpointOperator_simplex, h₀]
  rfl

def SecondHurewicz.SimplyConnected.straightenedTwoCycle {X : Type} [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.straightenedTwoCycle_class {X : Type} [TopologicalSpace X]
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

structure SecondHurewicz.SimplyConnected.VertexHomotopyData {X : Type} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X)) :
    C((unitInterval) × SimplexBoundary (n + 1), X) :=
  glueFaceHomotopies (fun i => D.homotopy (smp.comp (SingularChains.simplexFace n i)))
    (D.face_compatible smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X))
    (i : Fin (n + 2)) (r : (unitInterval)) (s : SingularChains.Simplex n) :
    vertexBoundaryHomotopy D smp (r, simplexFaceBoundary n i s) =
      D.homotopy (smp.comp (SingularChains.simplexFace n i)) (r, s) :=
  glueFaceHomotopies_face _ _ i r s

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X))
    (s : SimplexBoundary (n + 1)) : vertexBoundaryHomotopy D smp (0, s) = smp s.val :=
  glueFaceHomotopies_zero _ _ smp (fun i t => D.zero (smp.comp (SingularChains.simplexFace n i)) t)
    s

def SecondHurewicz.SimplyConnected.vertexStepHomotopy {X : Type} [TopologicalSpace X] {x : X}
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

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) (h : VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × SingularChains.Simplex (n + 1), SingularChains.Simplex (n + 1))) := by
  classical simp only [vertexStepHomotopy, if_pos h]

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_not_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) (h : ¬VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp) := by classical simp only [vertexStepHomotopy, if_neg h]

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(SingularChains.Simplex (n + 1), X))
    (s : SingularChains.Simplex (n + 1)) : vertexStepHomotopy D smp (0, s) = smp s := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h]
    exact extendBoundaryHomotopy_bottom _ _ _ s

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_face_apply {X : Type}
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

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) :
    FaceCompatibleHomotopies n D.homotopy (vertexStepHomotopy D) := by
  intro smp i
  ext u
  exact vertexStepHomotopy_face_apply D smp i u.1 u.2

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 1), X)) :
    VerticesBased x (n + 1) (timeSlice (vertexStepHomotopy D smp) 1) := by
  intro k
  obtain ⟨i, j, hij⟩ := simplexVertex_exists_face n k
  change vertexStepHomotopy D smp (1, stdSimplex.vertex k) = x
  rw [← hij, vertexStepHomotopy_face_apply]
  exact D.one_verticesBased (smp.comp (SingularChains.simplexFace n i)) j

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_faceCompatible {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(SingularChains.Simplex (n + 2), X)) :
    FaceCompatible
      (fun i => vertexStepHomotopy D (smp.comp (SingularChains.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij r u
  rw [vertexStepHomotopy_face_apply, vertexStepHomotopy_face_apply,
    PeriodTorusLineBundle.ChernCocycle.singularSimplex_face_face smp hij]

def SecondHurewicz.SimplyConnected.VertexHomotopyData.next {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : SecondHurewicz.SimplyConnected.VertexHomotopyData x n) :
    SecondHurewicz.SimplyConnected.VertexHomotopyData x (n + 1)
    where
  homotopy := SecondHurewicz.SimplyConnected.vertexStepHomotopy D
  zero := SecondHurewicz.SimplyConnected.vertexStepHomotopy_zero D
  one_verticesBased := SecondHurewicz.SimplyConnected.vertexStepHomotopy_one_verticesBased D
  of_verticesBased := SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_verticesBased D
  face_compatible := SecondHurewicz.SimplyConnected.vertexStepHomotopy_faceCompatible D

def SecondHurewicz.SimplyConnected.basedEdgePath {X : Type} [TopologicalSpace X] (x : X)
    (smp : C(SingularChains.Simplex 1, X)) (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) : Path x x :=
  (SingularChains.simplexPath smp).cast h₀.symm h₁.symm

@[simp]
theorem SecondHurewicz.SimplyConnected.basedEdgePath_const {X : Type} [TopologicalSpace X]
    (x : X) :
    basedEdgePath x (ContinuousMap.const (SingularChains.Simplex 1) x) rfl rfl = Path.refl x := by
  apply Path.ext
  funext t
  rfl

def SecondHurewicz.SimplyConnected.chosenBasePath {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x y : X) : Path y x := by
  classical exact if h : y = x then (Path.refl x).cast h rfl else PathConnectedSpace.somePath y x

@[simp]
theorem SecondHurewicz.SimplyConnected.chosenBasePath_self {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : chosenBasePath x x = Path.refl x := by
  simp [chosenBasePath]

def SecondHurewicz.SimplyConnected.chosenNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (p : Path x x) : p.Homotopy (Path.refl x) := by
  classical
    exact
    if h : p = Path.refl x then (Path.Homotopy.refl (Path.refl x)).cast h.symm rfl
    else Classical.choice (SimplyConnectedSpace.paths_homotopic p (Path.refl x))

@[simp]
theorem SecondHurewicz.SimplyConnected.chosenNullHomotopy_refl {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    chosenNullHomotopy x (Path.refl x) = Path.Homotopy.refl (Path.refl x) := by
  simp [chosenNullHomotopy]
  rfl

def SecondHurewicz.SimplyConnected.vertexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 0, X)) :
    C((unitInterval) × SingularChains.Simplex 0, X) :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).toContinuousMap.comp
    (ContinuousMap.fst : C((unitInterval) × SingularChains.Simplex 0, (unitInterval)))

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 0, X))
    (s : SingularChains.Simplex 0) : vertexHomotopy x smp (0, s) = smp s := by
  change chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) 0 = smp s
  rw [Path.source, SingularChains.simplexZero_eq_vertex s]

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 0, X))
    (s : SingularChains.Simplex 0) : vertexHomotopy x smp (1, s) = x :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).target

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    vertexHomotopy x (ContinuousMap.const (SingularChains.Simplex 0) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex 0) x := by
  ext t
  change chosenBasePath x x t.1 = x
  rw [chosenBasePath_self]
  rfl

def SecondHurewicz.SimplyConnected.edgeNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) :
    C((unitInterval) × SingularChains.Simplex 1, X) :=
  (chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)).toContinuousMap.comp
    ((ContinuousMap.id (unitInterval)).prodMap
      ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩)

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) (h₀ h₁)
    (s : SingularChains.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (0, s) = smp s := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (0, stdSimplexHomeomorphUnitInterval s) =
      smp s
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change smp (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = smp s
  rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) (h₀ h₁)
    (s : SingularChains.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (1, s) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (1, stdSimplexHomeomorphUnitInterval s) = x
  rw [ContinuousMap.HomotopyWith.apply_one]
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_vertex_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (h₀ h₁) (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero]
  exact Path.Homotopy.source _ t

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_vertex_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) (h₀ h₁)
    (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_one]
  exact Path.Homotopy.target _ t

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_const {X : Type} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.vertexInitialData {X : Type} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.vertexStraighteningData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : (n : ℕ) → VertexHomotopyData x n
  | 0 => vertexInitialData x
  | n + 1 => (vertexStraighteningData x n).next

def SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : C(SingularChains.Simplex n, X)) :
    C((unitInterval) × SingularChains.Simplex n, X) :=
  (vertexStraighteningData x n).homotopy smp

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) (s : SingularChains.Simplex n) :
    vertexStraighteningHomotopy x n smp (0, s) = smp s :=
  (vertexStraighteningData x n).zero smp s

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) :
    timeSlice (vertexStraighteningHomotopy x n smp) 0 = smp := by
  ext s
  exact vertexStraighteningHomotopy_zero x n smp s

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    FaceCompatibleHomotopies n (vertexStraighteningHomotopy x n)
      (vertexStraighteningHomotopy x (n + 1)) :=
  vertexStepHomotopy_face (vertexStraighteningData x n)

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval)) :
    (timeSlice (vertexStraighteningHomotopy x (n + 1) smp) r).comp
        (SingularChains.simplexFace n i) =
      timeSlice (vertexStraighteningHomotopy x n (smp.comp (SingularChains.simplexFace n i))) r :=
  timeSlice_face (vertexStraighteningHomotopy_face x n) smp i r

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) :
    VerticesBased x n (timeSlice (vertexStraighteningHomotopy x n smp) 1) :=
  (vertexStraighteningData x n).one_verticesBased smp

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) (h : VerticesBased x n smp) :
    vertexStraighteningHomotopy x n smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × SingularChains.Simplex n, SingularChains.Simplex n)) :=
  (vertexStraighteningData x n).of_verticesBased smp h

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_of_verticesBased
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(SingularChains.Simplex n, X)) (h : VerticesBased x n smp) (r : (unitInterval)) :
    timeSlice (vertexStraighteningHomotopy x n smp) r = smp := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n smp h]
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    vertexStraighteningHomotopy x n (ContinuousMap.const (SingularChains.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex n) x := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n _ (verticesBased_const x n)]
  rfl

def SecondHurewicz.SimplyConnected.stationarySimplexHomotopy {X : Type} [TopologicalSpace X]
    (n : ℕ) (smp : C(SingularChains.Simplex n, X)) :
    C((unitInterval) × SingularChains.Simplex n, X) :=
  smp.comp
    (ContinuousMap.snd : C((unitInterval) × SingularChains.Simplex n, SingularChains.Simplex n))

def SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X)) :
    C((unitInterval) × SingularChains.Simplex 1, X) := by
  classical
    exact
    if h :
        smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
          smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x then
      edgeNullHomotopy x smp h.1 h.2
    else stationarySimplexHomotopy 1 smp

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(SingularChains.Simplex 1, X))
    (s : SingularChains.Simplex 1) : edgeStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · exact edgeNullHomotopy_zero x smp _ _ s
  · rfl

theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_one {X : Type}
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

theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_vertex {X : Type}
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

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    edgeStraighteningHomotopy x (ContinuousMap.const (SingularChains.Simplex 1) x) =
      ContinuousMap.const ((unitInterval) × SingularChains.Simplex 1) x := by
  classical
  simp only [edgeStraighteningHomotopy, ContinuousMap.const_apply]
  exact edgeNullHomotopy_const x

theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.nextFaceHomotopies_compatible {X : Type}
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
  rw [PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij]

def SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : SingularChains.SingularSimplex X (n + 2)) :
    C((unitInterval) × SimplexBoundary (n + 2), X) :=
  glueFaceHomotopies (fun i => H' (smp.comp (SingularChains.simplexFace (n + 1) i)))
    (nextFaceHomotopies_compatible H H' h smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_zero {X : Type}
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

def SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy {X : Type} [TopologicalSpace X]
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

@[simp]
theorem SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X (n + 2)) (s : SingularChains.Simplex (n + 2)) :
    extendCoherentSimplexHomotopy H H' h h₀ smp (0, s) = smp s :=
  extendBoundaryHomotopy_bottom _ _ _ s

theorem SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face {X : Type}
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

def SecondHurewicz.SimplyConnected.triangleBoundary : Set (SingularChains.Simplex 2) :=
  {s | ∃ i, s i = 0}

def SecondHurewicz.SimplyConnected.BasedTriangle {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(SingularChains.Simplex 2, X) // ∀ s ∈ triangleBoundary, τ s = x }

def SecondHurewicz.SimplyConnected.triangleQuotient :
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

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleQuotient_zero
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 0 = 1 - (z.1 : ℝ) :=
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleQuotient_one
    (z : (unitInterval) × (unitInterval)) :
    triangleQuotient z 1 = (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleQuotient_two
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 2 = Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

def SecondHurewicz.SimplyConnected.triangleCubeQuotient :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 2) :=
  triangleQuotient.comp ⟨fun t => (t 0, t 1), by fun_prop⟩

theorem SecondHurewicz.SimplyConnected.triangleCubeQuotient_boundary (t : Fin 2 → (unitInterval))
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

def SecondHurewicz.SimplyConnected.basedTriangleLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp triangleCubeQuotient, fun t ht => τ.property _ (triangleCubeQuotient_boundary t ht)⟩

theorem SecondHurewicz.SimplyConnected.squareMap_basedTriangleLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.squareMap (basedTriangleLoop τ) = τ.val.comp triangleQuotient := by
  ext z
  change
    τ.val
        (triangleQuotient
          (SecondHurewicz.squareCoordinates z 0, SecondHurewicz.squareCoordinates z 1)) =
      _
  rw [SecondHurewicz.squareCoordinates_zero, SecondHurewicz.squareCoordinates_one]
  rfl

def SecondHurewicz.SimplyConnected.basedTriangleClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : Additive (π_ 2 X x) :=
  Additive.ofMul (⟦basedTriangleLoop τ⟧ : π_ 2 X x)

def SecondHurewicz.SimplyConnected.constantBasedTriangle {X : Type} [TopologicalSpace X] (x : X) :
    BasedTriangle x :=
  ⟨ContinuousMap.const (SingularChains.Simplex 2) x, fun _ _ => rfl⟩

def SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) : C((unitInterval) × SingularChains.Simplex 2, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x) smp

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (s : SingularChains.Simplex 2) :
    triangleEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 1 (edgeStraighteningHomotopy x)
      (triangleEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x)

def SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) : C((unitInterval) × SingularChains.Simplex 3, X) :=
  extendCoherentSimplexHomotopy (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x) smp

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) (s : SingularChains.Simplex 3) :
    tetrahedronEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 2 (triangleEdgeStraighteningHomotopy x)
      (tetrahedronEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x)

theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_one_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (h : VerticesBased x 2 smp) (i : Fin 3) :
    (timeSlice (triangleEdgeStraighteningHomotopy x smp) 1).comp (SingularChains.simplexFace 1 i) =
      ContinuousMap.const (SingularChains.Simplex 1) x := by
  rw [timeSlice_face (triangleEdgeStraighteningHomotopy_face x)]
  ext s
  exact
    edgeStraighteningHomotopy_one x (smp.comp (SingularChains.simplexFace 1 i)) (h.face i 0)
      (h.face i 1) s

theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_one_boundary {X : Type}
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

def SecondHurewicz.SimplyConnected.edgeStraightenedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2)
    (h : VerticesBased x 2 smp) : BasedTriangle x :=
  ⟨timeSlice (triangleEdgeStraighteningHomotopy x smp) 1,
    triangleEdgeStraighteningHomotopy_one_boundary x smp h⟩

def SecondHurewicz.SimplyConnected.vertexNormalizedSimplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : SingularChains.SingularSimplex X n) :
    SingularChains.SingularSimplex X n :=
  timeSlice (vertexStraighteningHomotopy x n smp) 1

theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : SingularChains.SingularSimplex X n) :
    VerticesBased x n (vertexNormalizedSimplex x n smp) :=
  vertexStraighteningHomotopy_one_verticesBased x n smp

theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : SingularChains.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (vertexNormalizedSimplex x (n + 1) smp).comp (SingularChains.simplexFace n i) =
      vertexNormalizedSimplex x n (smp.comp (SingularChains.simplexFace n i)) :=
  vertexStraighteningHomotopy_timeSlice_face x n smp i 1

theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : SingularChains.SingularSimplex X n) (h : VerticesBased x n smp) :
    vertexNormalizedSimplex x n smp = smp :=
  vertexStraighteningHomotopy_timeSlice_of_verticesBased x n smp h 1

def SecondHurewicz.SimplyConnected.normalizedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2) :
    BasedTriangle x :=
  edgeStraightenedTriangle x (vertexNormalizedSimplex x 2 smp)
    (vertexNormalizedSimplex_verticesBased x 2 smp)

theorem SecondHurewicz.SimplyConnected.normalizedTriangle_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) (h : VerticesBased x 2 smp) :
    normalizedTriangle x smp = edgeStraightenedTriangle x smp h := by
  apply Subtype.ext
  change
    timeSlice (triangleEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 2 smp)) 1 =
      timeSlice (triangleEdgeStraighteningHomotopy x smp) 1
  rw [vertexNormalizedSimplex_of_verticesBased x 2 smp h]

def SecondHurewicz.SimplyConnected.normalizedTetrahedronMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) :
    SingularChains.SingularSimplex X 3 :=
  timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1

theorem SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) (i : Fin 4) (s : SingularChains.Simplex 2)
    (hs : s ∈ triangleBoundary) :
    normalizedTetrahedronMap x smp (SingularChains.simplexFace 2 i s) = x := by
  have hf :=
    congrArg (fun f : C(SingularChains.Simplex 2, X) => f s)
      (normalizedTetrahedronMap_face x smp i)
  exact hf.trans ((normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i))).property s hs)

def SecondHurewicz.SimplyConnected.normalizedTwoChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : SingularChains.Chains X 2 →ₗ[ℤ] SingularChains.Chains X 2 :=
  SingularChains.chainLift X 2 fun smp =>
    SingularChains.simplexChain X 2 (normalizedTriangle x smp).val

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTwoChain_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 2) :
    normalizedTwoChain x (SingularChains.simplexChain X 2 smp) =
      SingularChains.simplexChain X 2 (normalizedTriangle x smp).val :=
  SingularChains.chainLift_simplex X 2 _ smp

theorem SecondHurewicz.SimplyConnected.normalizedTwoChain_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    normalizedTwoChain x =
      (simplexEndpointOperator 2 (triangleEdgeStraighteningHomotopy x) 1).comp
        (simplexEndpointOperator 2 (vertexStraighteningHomotopy x 2) 1) := by
  apply SingularChains.chainMap_ext X 2
  intro smp
  simp only [normalizedTwoChain_simplex, LinearMap.comp_apply, simplexEndpointOperator_simplex]
  rfl

def SecondHurewicz.SimplyConnected.vertexNormalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  straightenedTwoCycle (vertexStraighteningHomotopy x 1) (vertexStraighteningHomotopy x 2)
    (vertexStraighteningHomotopy_face x 1) c

theorem SecondHurewicz.SimplyConnected.vertexNormalizedTwoCycle_class {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (vertexNormalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c :=
  straightenedTwoCycle_class _ _ (vertexStraighteningHomotopy_face x 1)
    (vertexStraighteningHomotopy_timeSlice_zero x 2) c

def SecondHurewicz.SimplyConnected.normalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  straightenedTwoCycle (edgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy_face x) (vertexNormalizedTwoCycle x c)

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTwoCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    (normalizedTwoCycle x c).val = normalizedTwoChain x c.val := by
  rw [normalizedTwoChain_eq]
  rfl

theorem SecondHurewicz.SimplyConnected.normalizedTwoCycle_class {X : Type} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.tetrahedronOneSkeleton : Set (SingularChains.Simplex 3) :=
  {s | ∃ i j : Fin 4, i ≠ j ∧ s i = 0 ∧ s j = 0}

def SecondHurewicz.SimplyConnected.BasedTetrahedron {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(SingularChains.Simplex 3, X) // ∀ s ∈ tetrahedronOneSkeleton, τ s = x }

theorem SecondHurewicz.SimplyConnected.simplexFace_triangleBoundary (i : Fin 4)
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    SingularChains.simplexFace 2 i s ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, SingularChains.simplexFace_apply_self 2 i s,
      (SingularChains.simplexFace_apply_succAbove 2 i s j).trans hj⟩

def SecondHurewicz.SimplyConnected.basedTetrahedronFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTetrahedron x) (i : Fin 4) : BasedTriangle x :=
  ⟨τ.val.comp (SingularChains.simplexFace 2 i), fun s hs =>
    τ.property _ (simplexFace_triangleBoundary i s hs)⟩

def SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend {n : ℕ} (t : (unitInterval))
    (a b : SingularChains.Simplex n) : SingularChains.Simplex n :=
  ⟨(1 - (t : ℝ)) • (a : Fin (n + 1) → ℝ) + (t : ℝ) • (b : Fin (n + 1) → ℝ),
    convex_stdSimplex ℝ _ a.property b.property (sub_nonneg.mpr t.property.2) t.property.1
      (by ring)⟩

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero {n : ℕ}
    (a b : SingularChains.Simplex n) : tetrahedronSimplexBlend 0 a b = a := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) * a i + (0 : ℝ) * b i = a i
  simp

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one {n : ℕ}
    (a b : SingularChains.Simplex n) : tetrahedronSimplexBlend 1 a b = b := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) * a i + (1 : ℝ) * b i = b i
  simp

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_self {n : ℕ} (t : (unitInterval))
    (a : SingularChains.Simplex n) : tetrahedronSimplexBlend t a a = a := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * a i + (t : ℝ) * a i = a i
  ring

def SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap {n : ℕ} {Y : Type}
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

theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate {n : ℕ}
    (t : (unitInterval)) (a b : SingularChains.Simplex n) (i : Fin (n + 1)) (ha : a i = 0)
    (hb : b i = 0) : tetrahedronSimplexBlend t a b i = 0 := by
  change (1 - (t : ℝ)) * a i + (t : ℝ) * b i = 0
  simp [ha, hb]

theorem SecondHurewicz.SimplyConnected.simplexFace_two_zero (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 0 s : Fin 4 → ℝ) = ![0, s 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_self 2 0 s
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 0 s 2

theorem SecondHurewicz.SimplyConnected.simplexFace_two_one (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 1 s : Fin 4 → ℝ) = ![s 0, 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 0
  · exact SingularChains.simplexFace_apply_self 2 1 s
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 1 s 2

theorem SecondHurewicz.SimplyConnected.simplexFace_two_two (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 2 s : Fin 4 → ℝ) = ![s 0, s 1, 0, s 2] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 1
  · exact SingularChains.simplexFace_apply_self 2 2 s
  · exact SingularChains.simplexFace_apply_succAbove 2 2 s 2

theorem SecondHurewicz.SimplyConnected.simplexFace_two_three (s : SingularChains.Simplex 2) :
    (SingularChains.simplexFace 2 3 s : Fin 4 → ℝ) = ![s 0, s 1, s 2, 0] := by
  funext i
  fin_cases i
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 0
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 1
  · exact SingularChains.simplexFace_apply_succAbove 2 3 s 2
  · exact SingularChains.simplexFace_apply_self 2 3 s

def SecondHurewicz.SimplyConnected.BasedTetrahedron.ofFaces {X : Type} [TopologicalSpace X]
    {x : X} (τ : C(SingularChains.Simplex 3, X))
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (τ.comp (SingularChains.simplexFace 2 i)) s = x) :
    SecondHurewicz.SimplyConnected.BasedTetrahedron x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 i ⟨s, hi⟩
    have ht : t ∈ SecondHurewicz.SimplyConnected.triangleBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (SingularChains.simplexFace 2 i t) = x at he
    rw [show SingularChains.simplexFace 2 i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse 2 i ⟨s, hi⟩] at he
    exact he⟩

def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA :
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

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_boundary
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

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_diagonal (t : (unitInterval)) :
    tetrahedronQuadrilateralA ![t, t] ∈ tetrahedronOneSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩ <;> simp [DFunLike.coe, tetrahedronQuadrilateralA]

def SecondHurewicz.SimplyConnected.tetrahedronQuarterShift :
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

def SecondHurewicz.SimplyConnected.tetrahedronQuarterIndex : Fin 4 ≃ Fin 4
    where
  toFun i := ![1, 2, 3, 0] i
  invFun i := ![3, 0, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_index (s : SingularChains.Simplex 3)
    (i : Fin 4) : tetrahedronQuarterShift s (tetrahedronQuarterIndex i) = s i := by
  fin_cases i <;> rfl

theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_oneSkeleton
    (s : SingularChains.Simplex 3) (hs : s ∈ tetrahedronOneSkeleton) :
    tetrahedronQuarterShift s ∈ tetrahedronOneSkeleton := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact
    ⟨tetrahedronQuarterIndex i, tetrahedronQuarterIndex j, fun h =>
      hij (tetrahedronQuarterIndex.injective h), by simpa, by simpa⟩

def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp tetrahedronQuadrilateralA, fun u hu =>
    τ.property _ (tetrahedronQuadrilateralA_boundary u hu)⟩

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuadrilateralA_diagonal t)

def SecondHurewicz.SimplyConnected.tetrahedronShiftedQuadrilateralLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA), fun u hu =>
    τ.property _
      (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_boundary u hu))⟩

theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronShiftedQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_diagonal t))

def SecondHurewicz.SimplyConnected.quarterTurn : C(Fin 2 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u 1, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem SecondHurewicz.SimplyConnected.quarterTurn_apply (u : Fin 2 → (unitInterval)) :
    quarterTurn u = ![u 1, (unitInterval.symm) (u 0)] :=
  rfl

theorem SecondHurewicz.SimplyConnected.quarterTurn_boundary (u : Fin 2 → (unitInterval))
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

def SecondHurewicz.SimplyConnected.rotatedSquareLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp quarterTurn, fun u hu => p.property _ (quarterTurn_boundary u hu)⟩

def SecondHurewicz.SimplyConnected.rotationVector (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationVector_norm (v : ℝ × ℝ) :
    ‖rotationVector v‖ = ‖v‖ := by simp [rotationVector, Prod.norm_def, max_comm]

def SecondHurewicz.SimplyConnected.rotationBlend (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationBlend_zero (v : ℝ × ℝ) : rotationBlend 0 v = v := by
  ext <;> simp [rotationBlend]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationBlend_one (v : ℝ × ℝ) :
    rotationBlend 1 v = rotationVector v := by ext <;> simp [rotationBlend, rotationVector]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationBlend_zero_vector (t : ℝ) :
    rotationBlend t 0 = 0 := by ext <;> simp [rotationBlend]

theorem SecondHurewicz.SimplyConnected.rotationBlend_ne_zero (t : ℝ) {v : ℝ × ℝ} (hv : v ≠ 0) :
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

theorem SecondHurewicz.SimplyConnected.rotationBlend_continuous :
    Continuous (fun z : ℝ × (ℝ × ℝ) => rotationBlend z.1 z.2) := by
  unfold rotationBlend
  fun_prop

def SecondHurewicz.SimplyConnected.rotationCentered (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (2 * (u 0 : ℝ) - 1, 2 * (u 1 : ℝ) - 1)

theorem SecondHurewicz.SimplyConnected.rotationCentered_continuous :
    Continuous rotationCentered := by
  unfold rotationCentered
  fun_prop

theorem SecondHurewicz.SimplyConnected.rotationCentered_norm_le (u : Fin 2 → (unitInterval)) :
    ‖rotationCentered u‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  constructor <;> rw [Real.norm_eq_abs, abs_le]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 0).property.1, (u 0).property.2]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 1).property.1, (u 1).property.2]

theorem SecondHurewicz.SimplyConnected.rotationCentered_norm_boundary (u : Fin 2 → (unitInterval))
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

def SecondHurewicz.SimplyConnected.rotationDenominator (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ :=
  1 - ‖rotationCentered u‖ + ‖rotationBlend t (rotationCentered u)‖

theorem SecondHurewicz.SimplyConnected.rotationDenominator_pos (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : 0 < rotationDenominator t u := by
  by_cases hv : rotationCentered u = 0
  · simp [rotationDenominator, hv]
  · have hnorm : 0 < ‖rotationBlend t (rotationCentered u)‖ :=
      norm_pos_iff.mpr (rotationBlend_ne_zero t hv)
    have hle := rotationCentered_norm_le u
    unfold rotationDenominator
    linarith

theorem SecondHurewicz.SimplyConnected.rotationDenominator_continuous :
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

def SecondHurewicz.SimplyConnected.rotationNormalized (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (rotationDenominator t u)⁻¹ • rotationBlend t (rotationCentered u)

theorem SecondHurewicz.SimplyConnected.rotationNormalized_continuous :
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

theorem SecondHurewicz.SimplyConnected.rotationNormalized_norm_le (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ‖rotationNormalized t u‖ ≤ 1 := by
  have hd := rotationDenominator_pos t u
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [inv_mul_le_iff₀ hd, mul_one]
  unfold rotationDenominator
  linarith [rotationCentered_norm_le u]

theorem SecondHurewicz.SimplyConnected.rotationNormalized_norm_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ‖rotationNormalized t u‖ = 1 := by
  have hd := rotationDenominator_pos t u
  have he : rotationDenominator t u = ‖rotationBlend t (rotationCentered u)‖ := by
    simp [rotationDenominator, rotationCentered_norm_boundary u hu]
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [← he, inv_mul_cancel₀ (ne_of_gt hd)]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationNormalized_zero (u : Fin 2 → (unitInterval)) :
    rotationNormalized 0 u = rotationCentered u := by
  simp [rotationNormalized, rotationDenominator]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationNormalized_one (u : Fin 2 → (unitInterval)) :
    rotationNormalized 1 u = rotationVector (rotationCentered u) := by
  simp [rotationNormalized, rotationDenominator]

def SecondHurewicz.SimplyConnected.rotationUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    Fin 2 → (unitInterval) :=
  ![⟨(v.1 + 1) / 2,
      by
      have h := abs_le.mp (show |v.1| ≤ 1 from (norm_fst_le v).trans hv)
      constructor <;> linarith⟩,
    ⟨(v.2 + 1) / 2,
      by
      have h := abs_le.mp (show |v.2| ≤ 1 from (norm_snd_le v).trans hv)
      constructor <;> linarith⟩]

theorem SecondHurewicz.SimplyConnected.rotationUncenter_congr {v w : ℝ × ℝ} {hv : ‖v‖ ≤ 1}
    {hw : ‖w‖ ≤ 1} (h : v = w) : rotationUncenter v hv = rotationUncenter w hw := by
  subst w
  rfl

theorem SecondHurewicz.SimplyConnected.rotationUncenter_centered (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationCentered u) (rotationCentered_norm_le u) = u := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> dsimp [rotationUncenter, rotationCentered] <;> ring

theorem SecondHurewicz.SimplyConnected.rotationUncenter_vector (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationVector (rotationCentered u))
        (by simpa using rotationCentered_norm_le u) =
      quarterTurn u := by
  rw [quarterTurn_apply]
  funext i
  fin_cases i <;> apply Subtype.ext <;>
      dsimp [rotationUncenter, rotationVector, rotationCentered, unitInterval.symm] <;>
    ring

theorem SecondHurewicz.SimplyConnected.rotationUncenter_boundary (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1)
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

def SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap :
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

@[simp]
theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (0, u) = u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 0 u)
          (rotationNormalized_zero u)).trans
      (rotationUncenter_centered u)

@[simp]
theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_one (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (1, u) = quarterTurn u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 1 u)
          (rotationNormalized_one u)).trans
      (rotationUncenter_vector u)

theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurnHomotopyMap (t, u) ∈ Cube.boundary (Fin 2) :=
  rotationUncenter_boundary (rotationNormalized t u) (rotationNormalized_norm_le t u)
    (rotationNormalized_norm_boundary t u hu)

def SecondHurewicz.SimplyConnected.rotatedSquareLoop_homotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (rotatedSquareLoop p).val (Cube.boundary (Fin 2))
    where
  toFun z := p (quarterTurnHomotopyMap z)
  continuous_toFun := p.val.continuous.comp quarterTurnHomotopyMap.continuous
  map_zero_left u := congrArg p (quarterTurnHomotopyMap_zero u)
  map_one_left u := congrArg p (quarterTurnHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (quarterTurnHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

theorem SecondHurewicz.SimplyConnected.rotatedSquareLoop_class {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) : (⟦rotatedSquareLoop p⟧ : π_ 2 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦rotatedSquareLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (rotatedSquareLoop p) from ⟨rotatedSquareLoop_homotopy p⟩)
  exact h.symm

def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralB :
    C(Fin 2 → (unitInterval), SingularChains.Simplex 3) :=
  (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA).comp quarterTurn

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateral_perimeter
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

def SecondHurewicz.SimplyConnected.tetrahedronFillingsHomotopy {X : Type} [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.tetrahedronFillings_homotopic {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    GenLoop.Homotopic (tetrahedronQuadrilateralLoop τ)
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)) :=
  ⟨tetrahedronFillingsHomotopy τ⟩

theorem SecondHurewicz.SimplyConnected.tetrahedronFillings_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (⟦tetrahedronQuadrilateralLoop τ⟧ : π_ 2 X x) = ⟦tetrahedronShiftedQuadrilateralLoop τ⟧ :=
  (Quotient.sound (tetrahedronFillings_homotopic τ)).trans
    (rotatedSquareLoop_class (tetrahedronShiftedQuadrilateralLoop τ))

def SecondHurewicz.SimplyConnected.triangleCyclicPermutation :
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

theorem SecondHurewicz.SimplyConnected.triangleCyclicPermutation_boundary
    (s : SingularChains.Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleCyclicPermutation s ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩

def SecondHurewicz.SimplyConnected.cyclicBasedTriangle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : BasedTriangle x :=
  ⟨τ.val.comp triangleCyclicPermutation, fun s hs =>
    τ.property _ (triangleCyclicPermutation_boundary s hs)⟩

theorem SecondHurewicz.SimplyConnected.cyclicTriangleQuotient_commonZero
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

theorem SecondHurewicz.SimplyConnected.cyclicTriangleQuotient_blend_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronSimplexBlend t (triangleCyclicPermutation (triangleCubeQuotient u))
        (triangleCubeQuotient (quarterTurn u)) ∈
      triangleBoundary := by
  obtain ⟨i, hi, hj⟩ := cyclicTriangleQuotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

def SecondHurewicz.SimplyConnected.cyclicTriangleLoopHomotopy {X : Type} [TopologicalSpace X]
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

@[simp]
theorem SecondHurewicz.SimplyConnected.basedTriangleClass_cyclic {X : Type} [TopologicalSpace X]
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

abbrev SecondHurewicz.SimplyConnected.SubdivisionSquare :=
  Fin 2 → (unitInterval)

theorem SecondHurewicz.SimplyConnected.subdivisionSquare_boundary_cases (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : u 0 = 0 ∨ u 0 = 1 ∨ u 1 = 0 ∨ u 1 = 1 := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

inductive SecondHurewicz.SimplyConnected.SubdivisionSameSide (a b : SubdivisionSquare) : Prop
  | zero (i : Fin 2) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 2) (ha : a i = 1) (hb : b i = 1)
  | diagonal (ha : a 0 = a 1) (hb : b 0 = b 1)

def SecondHurewicz.SimplyConnected.subdivisionBlend (t : (unitInterval))
    (a b : SubdivisionSquare) : SubdivisionSquare := fun i => Set.Icc.convexComb (a i) (b i) t

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionBlend_zero (a b : SubdivisionSquare) :
    subdivisionBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionBlend_one (a b : SubdivisionSquare) :
    subdivisionBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def SecondHurewicz.SimplyConnected.subdivisionBlendMap
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

theorem SecondHurewicz.SimplyConnected.subdivisionOnDiagonal {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (a : SubdivisionSquare) (ha : a 0 = a 1) : p a = x := by
  have h : a = ![a 0, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact ha.symm
  exact (congrArg p h).trans (hd _)

theorem SecondHurewicz.SimplyConnected.subdivisionBlend_based {X : Type*} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.subdivisionPullbackLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp f, hf⟩

def SecondHurewicz.SimplyConnected.subdivisionLinearHomotopy {X : Type*} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.subdivisionSubMin (u v : (unitInterval)) : (unitInterval) :=
  ⟨(u : ℝ) - Min.min (u : ℝ) (v : ℝ), sub_nonneg.mpr (min_le_left _ _),
    (sub_le_self _ (le_min u.property.1 v.property.1)).trans u.property.2⟩

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_zero_left (v : (unitInterval)) :
    subdivisionSubMin 0 v = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.1]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_zero_right (u : (unitInterval)) :
    subdivisionSubMin u 0 = u := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.1]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_one_left (v : (unitInterval)) :
    subdivisionSubMin 1 v = (unitInterval.symm) v := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.2]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_one_right (u : (unitInterval)) :
    subdivisionSubMin u 1 = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.2]

def SecondHurewicz.SimplyConnected.subdivisionLowerProductMap :
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

def SecondHurewicz.SimplyConnected.subdivisionUpperProductMap :
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

def SecondHurewicz.SimplyConnected.subdivisionUpperConeMap :
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

def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Min.min (u 0) (u 1)]
  continuous_toFun := by fun_prop

def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleMap :
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

theorem SecondHurewicz.SimplyConnected.subdivisionLowerProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionLowerProductMap, h])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionUpperProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperProductMap, h])
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperProductMap, h])⟩

theorem SecondHurewicz.SimplyConnected.subdivisionUpperConeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperConeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperConeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperConeMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩

theorem SecondHurewicz.SimplyConnected.subdivisionLowerTriangleMap_based {X : Type*}
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperTriangleMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩

def SecondHurewicz.SimplyConnected.subdivisionLowerProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerProductMap (subdivisionLowerProductMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperProductMap (subdivisionUpperProductMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperConeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperConeMap (subdivisionUpperConeMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerTriangleMap (subdivisionLowerTriangleMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperTriangleMap (subdivisionUpperTriangleMap_based p hd)

theorem SecondHurewicz.SimplyConnected.subdivisionLowerProductTriangle_sides
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperProductCone_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperProductMap u) (subdivisionUpperConeMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperConeTriangle_sides (u : SubdivisionSquare)
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

def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionLowerProductLoop p hd).val.HomotopyRel (subdivisionLowerTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionLowerProductMap_based p hd)
    (subdivisionLowerTriangleMap_based p hd) subdivisionLowerProductTriangle_sides

def SecondHurewicz.SimplyConnected.subdivisionUpperConeHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperProductLoop p hd).val.HomotopyRel (subdivisionUpperConeLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperProductMap_based p hd)
    (subdivisionUpperConeMap_based p hd) subdivisionUpperProductCone_sides

def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperConeLoop p hd).val.HomotopyRel (subdivisionUpperTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperConeMap_based p hd)
    (subdivisionUpperTriangleMap_based p hd) subdivisionUpperConeTriangle_sides

theorem SecondHurewicz.SimplyConnected.subdivision_toLoop_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin 2) (a b : GenLoop (Fin 2) X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

theorem SecondHurewicz.SimplyConnected.subdivision_transAt_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin 2) {a b c d : GenLoop (Fin 2) X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [subdivision_toLoop_transAt, subdivision_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

noncomputable def SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate :
    C((unitInterval) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) p.1
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_apply (u v : (unitInterval)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1))
        (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ))) u :=
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_zero (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 0) = 0 := by
  simp [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_one (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 1) = 1 := by
  norm_num [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_le_half (u v : (unitInterval))
    (hv : (v : ℝ) ≤ 1 / 2) :
    subdivisionWarpCoordinate (u, v) = u * Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) := by
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hzero]
  apply Subtype.ext
  simp

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_le (u v : (unitInterval))
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

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (u v : (unitInterval))
    (hv : 1 / 2 < (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) :=
  subdivisionWarpCoordinate_of_half_le u v hv.le

def SecondHurewicz.SimplyConnected.subdivisionWarpMap : C(SubdivisionSquare, SubdivisionSquare)
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

theorem SecondHurewicz.SimplyConnected.subdivisionWarpMap_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : SubdivisionSameSide u (subdivisionWarpMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 h (by simp [subdivisionWarpMap, h])
  · exact .one 0 h (by simp [subdivisionWarpMap, h])
  · exact .zero 1 h (by simp [subdivisionWarpMap, h])
  · exact .one 1 h (by simp [subdivisionWarpMap, h])

theorem SecondHurewicz.SimplyConnected.subdivisionWarpMap_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    p (subdivisionWarpMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionWarpMap, h])⟩

def SecondHurewicz.SimplyConnected.subdivisionWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionWarpMap (subdivisionWarpMap_based p)

def SecondHurewicz.SimplyConnected.subdivisionWarpHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    p.val.HomotopyRel (subdivisionWarpLoop p).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd (ContinuousMap.id _) subdivisionWarpMap p.property
    (subdivisionWarpMap_based p) subdivisionWarpMap_sides

theorem SecondHurewicz.SimplyConnected.subdivisionWarpLoop_eq_transAt {X : Type*}
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

theorem SecondHurewicz.SimplyConnected.subdivision_homotopic {X : Type*} [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.subdivision_class {X : Type*} [TopologicalSpace X] {x : X}
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

theorem SecondHurewicz.SimplyConnected.subdivision_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· + ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivision_class p hd)

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_lower
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

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_upper
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

theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_face_three
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

theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_face_one
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

theorem SecondHurewicz.SimplyConnected.tetrahedronLowerLoop_eq_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.tetrahedronUpperLoop_eq_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedLowerLoop_eq_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedUpperLoop_eq_face {X : Type}
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

theorem SecondHurewicz.SimplyConnected.basedTetrahedron_pair_relation {X : Type}
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

theorem SecondHurewicz.SimplyConnected.basedTetrahedron_boundary_relation {X : Type}
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

theorem SecondHurewicz.SimplyConnected.basedTetrahedron_signed_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • basedTriangleClass (basedTetrahedronFace τ i) = 0 := by
  have h := basedTetrahedron_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

def SecondHurewicz.SimplyConnected.normalizedTetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) :
    BasedTetrahedron x :=
  BasedTetrahedron.ofFaces (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTetrahedron_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : SingularChains.SingularSimplex X 3) (i : Fin 4) :
    basedTetrahedronFace (normalizedTetrahedron x smp) i =
      normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i)) := by
  apply Subtype.ext
  exact normalizedTetrahedronMap_face x smp i

theorem SecondHurewicz.SimplyConnected.normalizedTriangle_boundary_relation {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 3) :
    ∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          basedTriangleClass (normalizedTriangle x (smp.comp (SingularChains.simplexFace 2 i))) =
      0 := by
  simpa only [normalizedTetrahedron_face] using
    basedTetrahedron_signed_relation (normalizedTetrahedron x smp)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.squareAffineTriangle (v : Fin 3 → Fin 2 × Fin 2) :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  ((SingularChains.pathSimplex Path.id).prodMap (SingularChains.pathSimplex Path.id)).comp
    (PeriodTorusHigherHomology.productAffineSimplex
      (fun i =>
        (SingularMayerVietoris.stdVertices 1 (v i).1,
          SingularMayerVietoris.stdVertices 1 (v i).2)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareAffineTriangle_fst_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : SingularChains.Simplex 2) :
    ((squareAffineTriangle v s).1 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).1 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).1) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareAffineTriangle_snd_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : SingularChains.Simplex 2) :
    ((squareAffineTriangle v s).2 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).2 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).2) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.lowerProductTriangle :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (1, 0), (1, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.upperProductTriangle :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 1), (1, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.leftProductDegenerate :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (0, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.bottomProductDegenerate :
    C(SingularChains.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (1, 0)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.lowerProductTriangle_fst (s : SingularChains.Simplex 2) :
    ((lowerProductTriangle s).1 : ℝ) = s 1 + s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.lowerProductTriangle_snd (s : SingularChains.Simplex 2) :
    ((lowerProductTriangle s).2 : ℝ) = s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.upperProductTriangle_fst (s : SingularChains.Simplex 2) :
    ((upperProductTriangle s).1 : ℝ) = s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.upperProductTriangle_snd (s : SingularChains.Simplex 2) :
    ((upperProductTriangle s).2 : ℝ) = s 1 + s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.leftProductDegenerate_fst (s : SingularChains.Simplex 2) :
    (leftProductDegenerate s).1 = 0 := by
  apply Subtype.ext
  simp [leftProductDegenerate, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.bottomProductDegenerate_snd (s : SingularChains.Simplex 2) :
    (bottomProductDegenerate s).2 = 0 := by
  apply Subtype.ext
  simp [bottomProductDegenerate, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.lowerSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp lowerProductTriangle

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.upperSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp upperProductTriangle

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_zero (s : SingularChains.Simplex 2) :
    (lowerSquareTriangle s 0 : ℝ) = s 1 + s 2 := by simp [lowerSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_one (s : SingularChains.Simplex 2) :
    (lowerSquareTriangle s 1 : ℝ) = s 2 := by simp [lowerSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_zero (s : SingularChains.Simplex 2) :
    (upperSquareTriangle s 0 : ℝ) = s 2 := by simp [upperSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in

@[simp]
theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_one (s : SingularChains.Simplex 2) :
    (upperSquareTriangle s 1 : ℝ) = s 1 + s 2 := by simp [upperSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.productSquareChain_four_triangles :
    SecondHurewicz.productSquareChain =
      SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
            SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle +
        SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 bottomProductDegenerate := by
  rw [SecondHurewicz.productSquareChain, SecondHurewicz.intervalChain, SingularChains.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    PeriodTorusHigherHomology.formalBoundary_edge_simplex]
  simp only [map_sub, PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, SingularChains.inducedChain_simplex]
  change
    (SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate) -
        (SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle -
          SingularChains.simplexChain ((unitInterval) × (unitInterval)) 2
            bottomProductDegenerate) =
      _
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareMap_leftProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (SecondHurewicz.squareMap p).comp leftProductDegenerate =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨0, Or.inl ?_⟩
  rw [SecondHurewicz.squareCoordinates_zero, leftProductDegenerate_fst]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareMap_bottomProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (SecondHurewicz.squareMap p).comp bottomProductDegenerate =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨1, Or.inl ?_⟩
  rw [SecondHurewicz.squareCoordinates_one, bottomProductDegenerate_snd]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareChain_two_triangles {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    SecondHurewicz.squareChain p =
      SingularChains.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
        SingularChains.simplexChain X 2 (p.val.comp upperSquareTriangle) := by
  rw [SecondHurewicz.squareChain, SecondHurewicz.suspensionOne_toLoop,
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

theorem SecondHurewicz.SimplyConnected.triangleQuotient_lowerProductTriangle :
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

theorem SecondHurewicz.SimplyConnected.triangleQuotient_upperProductTriangle_boundary
    (s : SingularChains.Simplex 2) :
    triangleQuotient (upperProductTriangle s) ∈ triangleBoundary := by
  refine ⟨1, ?_⟩
  rw [triangleQuotient_one, upperProductTriangle_fst, upperProductTriangle_snd,
    min_eq_left (le_add_of_nonneg_left (stdSimplex.zero_le s 1)), sub_self]

theorem SecondHurewicz.SimplyConnected.basedTriangleLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) : (basedTriangleLoop τ).val.comp lowerSquareTriangle = τ.val := by
  change (SecondHurewicz.squareMap (basedTriangleLoop τ)).comp lowerProductTriangle = _
  rw [squareMap_basedTriangleLoop, ContinuousMap.comp_assoc,
    triangleQuotient_lowerProductTriangle, ContinuousMap.comp_id]

theorem SecondHurewicz.SimplyConnected.basedTriangleLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp upperSquareTriangle =
      ContinuousMap.const (SingularChains.Simplex 2) x := by
  change (SecondHurewicz.squareMap (basedTriangleLoop τ)).comp upperProductTriangle = _
  rw [squareMap_basedTriangleLoop]
  ext s
  exact τ.property _ (triangleQuotient_upperProductTriangle_boundary s)

theorem SecondHurewicz.SimplyConnected.squareChain_basedTriangleLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.squareChain (basedTriangleLoop τ) =
      SingularChains.simplexChain X 2 τ.val -
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) := by
  rw [squareChain_two_triangles, basedTriangleLoop_lower, basedTriangleLoop_upper]

def SecondHurewicz.SimplyConnected.basedTriangleCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex X) 2
    (SingularChains.simplexChain X 2 τ.val -
      SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x))
    (by
      rw [← squareChain_basedTriangleLoop]
      exact SecondHurewicz.squareChain_boundary (basedTriangleLoop τ))

@[simp]
theorem SecondHurewicz.SimplyConnected.basedTriangleCycle_val {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleCycle τ).val =
      SingularChains.simplexChain X 2 τ.val -
        SingularChains.simplexChain X 2 (ContinuousMap.const (SingularChains.Simplex 2) x) :=
  rfl

theorem SecondHurewicz.SimplyConnected.hurewicz_basedTriangleClass {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.hurewiczMap x (basedTriangleClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (basedTriangleCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (SecondHurewicz.squareCycle (basedTriangleLoop τ)) =
      _
  congr 1
  apply Subtype.ext
  exact squareChain_basedTriangleLoop τ

def SecondHurewicz.SimplyConnected.secondHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF :
      ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (SingularChains.singularComplex X) 2
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2).subtype)
    (fun b => hF b)

@[simp]
theorem SecondHurewicz.SimplyConnected.secondHomologyDesc_cycleClass {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    secondHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (SingularChains.singularComplex X) 2 _ _ c

theorem SecondHurewicz.SimplyConnected.comp_secondHomologyDesc_eq_id {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : SingularChains.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : SingularChains.Chains X 3, F (((SingularChains.singularComplex X).d 3 2).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) :
    g.comp (secondHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (SingularChains.singularComplex X) 2
  intro c
  simpa only [LinearMap.comp_apply, secondHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

def SecondHurewicz.SimplyConnected.chainAugmentation (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularChains.Chains X n →ₗ[ℤ] ℤ :=
  SingularChains.chainLift X n fun _ => 1

@[simp]
theorem SecondHurewicz.SimplyConnected.chainAugmentation_simplex (X : Type) [TopologicalSpace X]
    (n : ℕ) (smp : SingularChains.SingularSimplex X n) :
    chainAugmentation X n (SingularChains.simplexChain X n smp) = 1 :=
  SingularChains.chainLift_simplex X n _ smp

theorem SecondHurewicz.SimplyConnected.chainAugmentation_boundaryTwo (X : Type)
    [TopologicalSpace X] (c : SingularChains.Chains X 2) :
    chainAugmentation X 1 (SingularChains.boundaryTwo X c) = chainAugmentation X 2 c := by
  have h : (chainAugmentation X 1).comp (SingularChains.boundaryTwo X) = chainAugmentation X 2 := by
    apply SingularChains.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundaryTwo_simplex, map_add, map_sub,
      chainAugmentation_simplex, sub_self, zero_add]
  exact LinearMap.congr_fun h c

@[simp]
theorem SecondHurewicz.SimplyConnected.chainAugmentation_twoCycle (X : Type) [TopologicalSpace X]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    chainAugmentation X 2 c.1 = 0 := by
  rw [← chainAugmentation_boundaryTwo]
  have hc :=
    SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 2 c
  change SingularChains.boundaryTwo X c.1 = 0 at hc
  rw [hc, map_zero]

theorem SecondHurewicz.SimplyConnected.chainLift_sub_constant (X : Type) [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.chainLift_sub_constant_twoCycle (X : Type)
    [TopologicalSpace X] {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularChains.SingularSimplex X 2 → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SingularChains.chainLift X 2 (fun smp => f smp - m) c.1 = SingularChains.chainLift X 2 f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_twoCycle, zero_smul, sub_zero]

def SecondHurewicz.SimplyConnected.triangleClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : SingularChains.Chains X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  SingularChains.chainLift X 2 fun smp => basedTriangleClass (normalizedTriangle x smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleClassOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) :
    triangleClassOperator x (SingularChains.simplexChain X 2 smp) =
      basedTriangleClass (normalizedTriangle x smp) :=
  SingularChains.chainLift_simplex X 2 _ smp

theorem SecondHurewicz.SimplyConnected.triangleClassOperator_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (b : SingularChains.Chains X 3) :
    triangleClassOperator x (((SingularChains.singularComplex X).d 3 2).hom b) = 0 := by
  have h : (triangleClassOperator x).comp ((SingularChains.singularComplex X).d 3 2).hom = 0 := by
    apply SingularChains.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, SingularChains.boundary_simplex, map_sum, map_zsmul,
      triangleClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedTriangle_boundary_relation x smp
  exact LinearMap.congr_fun h b

def SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularChains.Chains X 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2 :=
  SingularChains.chainLift X 2 fun smp => basedTriangleCycle (normalizedTriangle x smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : SingularChains.SingularSimplex X 2) :
    normalizedTriangleCycleOperator x (SingularChains.simplexChain X 2 smp) =
      basedTriangleCycle (normalizedTriangle x smp) :=
  SingularChains.chainLift_simplex X 2 _ smp

theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_val {X : Type}
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

theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    normalizedTriangleCycleOperator x c.val = normalizedTwoCycle x c := by
  apply Subtype.ext
  rw [normalizedTriangleCycleOperator_val, chainLift_sub_constant_twoCycle,
    normalizedTwoCycle_val]
  rfl

theorem SecondHurewicz.SimplyConnected.hurewiczMap_comp_triangleClassOperator {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (SecondHurewicz.hurewiczMap x).comp (triangleClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2).comp
        (normalizedTriangleCycleOperator x) := by
  apply SingularChains.chainMap_ext X 2
  intro smp
  simp only [LinearMap.comp_apply, triangleClassOperator_simplex,
    normalizedTriangleCycleOperator_simplex]
  exact hurewicz_basedTriangleClass (normalizedTriangle x smp)

theorem SecondHurewicz.SimplyConnected.hurewiczMap_triangleClassOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    SecondHurewicz.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_triangleClassOperator x) c.val
  change
    SecondHurewicz.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2
        (normalizedTriangleCycleOperator x c.val) at h
  rw [normalizedTriangleCycleOperator_twoCycle] at h
  exact h.trans (normalizedTwoCycle_class x c)

def SecondHurewicz.SimplyConnected.hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  secondHomologyDesc (triangleClassOperator x) (triangleClassOperator_boundary x)

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 2) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 2 c) =
      triangleClassOperator x c.val :=
  secondHomologyDesc_cycleClass _ _ c

theorem SecondHurewicz.SimplyConnected.hurewiczMap_comp_hurewiczInverse {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (SecondHurewicz.hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_secondHomologyDesc_eq_id (triangleClassOperator x) (triangleClassOperator_boundary x)
    (SecondHurewicz.hurewiczMap x) (hurewiczMap_triangleClassOperator_twoCycle x)

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (c : SingularMayerVietoris.SingularHomology X 2) :
    SecondHurewicz.hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_verticesBased {X : Type}
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

theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_verticesBased {X : Type}
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

theorem SecondHurewicz.SimplyConnected.squareTriangles_diagonal {X : Type} [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_outerFace {X : Type}
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

theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_outerFace {X : Type}
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

theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 1 : ℝ) ≤ t 0) : lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 0 : ℝ) = (t 0 : ℝ)
    rw [lowerSquareTriangle_zero, triangleQuotient_one, triangleQuotient_two]
    ring
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 1 : ℝ) = (t 1 : ℝ)
    rw [lowerSquareTriangle_one, triangleQuotient_two, min_eq_right h]

theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 0 : ℝ) ≤ t 1) : upperSquareTriangle (triangleQuotient (t 1, t 0)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 0 : ℝ) = (t 0 : ℝ)
    rw [upperSquareTriangle_zero, triangleQuotient_two, min_eq_right h]
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 1 : ℝ) = (t 1 : ℝ)
    rw [upperSquareTriangle_one, triangleQuotient_one, triangleQuotient_two]
    ring

theorem SecondHurewicz.SimplyConnected.triangleQuotient_perimeter_of_le
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

theorem SecondHurewicz.SimplyConnected.cubeBoundary_productBoundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : t 0 = 0 ∨ t 0 = 1 ∨ t 1 = 0 ∨ t 1 = 1 := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hi))

def SecondHurewicz.SimplyConnected.gluedTriangleHomotopyMap {X : Type} [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.gluedTriangleHomotopyMap_boundary {X : Type}
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

def SecondHurewicz.SimplyConnected.gluedTriangleHomotopy {X : Type} [TopologicalSpace X] {x : X}
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

private theorem SecondHurewicz.SimplyConnected.basedTriangles_diagonal_mo1973_6743 {X : Type}
    [TopologicalSpace X] {x : X} (τ υ : BasedTriangle x) (s : SingularChains.Simplex 2)
    (hs : s 1 = 0) : τ.val s = υ.val s :=
  (τ.property s ⟨1, hs⟩).trans (υ.property s ⟨1, hs⟩).symm

def SecondHurewicz.SimplyConnected.basedTrianglesLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ υ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨(gluedTriangleHomotopyMap (τ.val.comp ContinuousMap.snd) (υ.val.comp ContinuousMap.snd)
          (fun _ => basedTriangles_diagonal_mo1973_6743 τ υ)).comp
      ⟨fun t => ((0 : (unitInterval)), t), by fun_prop⟩,
    by
    intro t ht
    exact
      gluedTriangleHomotopyMap_boundary _ _ (fun _ => basedTriangles_diagonal_mo1973_6743 τ υ) x
        (fun _ s hs => τ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
        (fun _ s hs => υ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩))) 0 t ht⟩

@[simp]
theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_apply {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (t : Fin 2 → (unitInterval)) :
    basedTrianglesLoop τ υ t =
      if (t 1 : ℝ) ≤ t 0 then τ.val (triangleQuotient (t 0, t 1))
      else υ.val (triangleQuotient (t 1, t 0)) :=
  rfl

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (u : (unitInterval)) :
    basedTrianglesLoop τ υ (fun _ => u) = x := by
  rw [basedTrianglesLoop_apply, if_pos le_rfl]
  apply τ.property
  exact ⟨1, by simp only [triangleQuotient_one, min_self, sub_self]⟩

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_lower {X : Type} [TopologicalSpace X]
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

private theorem SecondHurewicz.SimplyConnected.triangleQuotient_swapped_upper_mo1973_6748
    (s : SingularChains.Simplex 2) :
    triangleQuotient (upperSquareTriangle s 1, upperSquareTriangle s 0) = s := by
  have hpair : (upperSquareTriangle s 1, upperSquareTriangle s 0) = lowerProductTriangle s := by
    apply Prod.ext <;> apply Subtype.ext
    · rw [upperSquareTriangle_one, lowerProductTriangle_fst]
    · rw [upperSquareTriangle_zero, lowerProductTriangle_snd]
  rw [hpair]
  exact ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_upper {X : Type} [TopologicalSpace X]
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
      simpa only [he] using triangleQuotient_swapped_upper_mo1973_6748 s
    rw [hq]
    exact basedTriangles_diagonal_mo1973_6743 τ υ s hs
  · rw [triangleQuotient_swapped_upper_mo1973_6748]

def SecondHurewicz.SimplyConnected.basedTrianglesHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  gluedTriangleHomotopy (L.cast rfl (basedTrianglesLoop_lower τ υ).symm)
    (U.cast rfl (basedTrianglesLoop_upper τ υ).symm) hdiag hL hU

theorem SecondHurewicz.SimplyConnected.triangleProperty_of_face
    {P : SingularChains.Simplex 2 → Prop} (i : Fin 3)
    (h : ∀ u, P (SingularChains.simplexFace 1 i u)) (s : SingularChains.Simplex 2) (hs : s i = 0) :
    P s := by simpa only [simplexFace_inverse] using h (simplexFaceInverse 1 i ⟨s, hs⟩)

def SecondHurewicz.SimplyConnected.basedTrianglesHomotopy_of_faces {X : Type} [TopologicalSpace X]
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

def SecondHurewicz.SimplyConnected.squareNormalizedLowerTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp lowerSquareTriangle)
    (lowerSquareTriangle_verticesBased p)

def SecondHurewicz.SimplyConnected.squareNormalizedUpperTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp upperSquareTriangle)
    (upperSquareTriangle_verticesBased p)

def SecondHurewicz.SimplyConnected.squareNormalizationTriangleHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(SingularChains.Simplex 2, X))
    (h : VerticesBased x 2 smp) : smp.Homotopy (edgeStraightenedTriangle x smp h).val
    where
  toContinuousMap := triangleEdgeStraighteningHomotopy x smp
  map_zero_left := triangleEdgeStraighteningHomotopy_zero x smp
  map_one_left _ := rfl

def SecondHurewicz.SimplyConnected.squareLowerNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).Homotopy (squareNormalizedLowerTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (lowerSquareTriangle_verticesBased p)

def SecondHurewicz.SimplyConnected.squareUpperNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp upperSquareTriangle).Homotopy (squareNormalizedUpperTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (upperSquareTriangle_verticesBased p)

theorem SecondHurewicz.SimplyConnected.squareNormalization_edge_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(SingularChains.Simplex 2, X))
    (i : Fin 3) (r : (unitInterval)) (s : SingularChains.Simplex 1) :
    triangleEdgeStraighteningHomotopy x smp (r, SingularChains.simplexFace 1 i s) =
      edgeStraighteningHomotopy x (smp.comp (SingularChains.simplexFace 1 i)) (r, s) :=
  DFunLike.congr_fun (triangleEdgeStraighteningHomotopy_face x smp i) (r, s)

theorem SecondHurewicz.SimplyConnected.squareNormalization_diagonal {X : Type}
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

theorem SecondHurewicz.SimplyConnected.squareLowerNormalization_outerFace {X : Type}
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

theorem SecondHurewicz.SimplyConnected.squareUpperNormalization_outerFace {X : Type}
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

def SecondHurewicz.SimplyConnected.squareNormalizationHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)).val
      (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy_of_faces (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p) (squareLowerNormalizationHomotopy p)
    (squareUpperNormalizationHomotopy p) (squareNormalization_diagonal p)
    (squareLowerNormalization_outerFace p) (squareUpperNormalization_outerFace p)

theorem SecondHurewicz.SimplyConnected.squareNormalization_homotopic {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    GenLoop.Homotopic p
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)) :=
  ⟨squareNormalizationHomotopy p⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle :
    C(SingularChains.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (squareAffineTriangle ![(0, 0), (1, 1), (0, 1)])

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_zero
    (s : SingularChains.Simplex 2) : (subdivisionUpperPositiveSquareTriangle s 0 : ℝ) = s 1 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_fst_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_one
    (s : SingularChains.Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_snd_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

theorem SecondHurewicz.SimplyConnected.subdivisionTriangle_coordinate_sum
    (s : SingularChains.Simplex 2) : s 0 + s 1 + s 2 = 1 := by
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  linarith

theorem SecondHurewicz.SimplyConnected.subdivisionLowerSquareTriangle_based {X : Type}
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based {X : Type}
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based {X : Type}
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

def SecondHurewicz.SimplyConnected.subdivisionLowerBasedTriangle {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    BasedTriangle x :=
  ⟨p.val.comp lowerSquareTriangle, subdivisionLowerSquareTriangle_based p hd⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp upperSquareTriangle, subdivisionUpperNegativeSquareTriangle_based p hd⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperPositiveBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp subdivisionUpperPositiveSquareTriangle,
    subdivisionUpperPositiveSquareTriangle_based p hd⟩

theorem SecondHurewicz.SimplyConnected.subdivisionLowerTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionLowerTriangleLoop p hd = basedTriangleLoop (subdivisionLowerBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, Min.min (u 0) (u 1)] = p (lowerSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

theorem SecondHurewicz.SimplyConnected.subdivisionUpperTriangleLoop_eq_basedTriangleLoop
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeBasedTriangle_loop_apply {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : Fin 2 → (unitInterval)) :
    basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) u =
      p ![Min.min (u 0) (u 1), u 0] := by
  change p (upperSquareTriangle (triangleQuotient (u 0, u 1))) = p ![Min.min (u 0) (u 1), u 0]
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

theorem SecondHurewicz.SimplyConnected.subdivision_basedTriangleClass_sum {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) +
        basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) := by
  simpa only [subdivisionLowerTriangleLoop_eq_basedTriangleLoop,
    subdivisionUpperTriangleLoop_eq_basedTriangleLoop, basedTriangleClass] using
    subdivision_additiveClass p hd

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) (u 1), u 0]
  continuous_toFun := by fun_prop

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0]
  continuous_toFun := by fun_prop

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeMap_based {X : Type*}
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedMap_based {X : Type*}
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

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeMap (subdivisionUpperNegativeMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedLoop {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeReversedMap
    (subdivisionUpperNegativeReversedMap_based p hd)

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_sides (u : SubdivisionSquare)
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

def SecondHurewicz.SimplyConnected.subdivisionUpperOrientationHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperTriangleLoop p hd).val.HomotopyRel
      (subdivisionUpperNegativeReversedLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperTriangleMap_based p hd)
    (subdivisionUpperNegativeReversedMap_based p hd) subdivisionUpperOrientation_sides

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedLoop_eq_symmAt {X : Type*}
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic (subdivisionUpperTriangleLoop p hd)
      (GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)) := by
  rw [← subdivisionUpperNegativeReversedLoop_eq_symmAt]
  exact ⟨subdivisionUpperOrientationHomotopy p hd⟩

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_class {X : Type*}
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

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_additiveClass {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((-·) : Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivisionUpperOrientation_class p hd)

theorem SecondHurewicz.SimplyConnected.subdivision_eq_sub_of_eq_add {A : Type*} [AddGroup A]
    {a b c d : A} (h : a = b + c) (hc : c = -d) : a = b - d :=
  h.trans ((congrArg (fun z => b + z) hc).trans (sub_eq_add_neg b d).symm)

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeLoop p hd =
      basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  exact (subdivisionUpperNegativeBasedTriangle_loop_apply p hd u).symm

theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveBasedTriangle_class_eq_neg
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) =
      -basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) := by
  unfold basedTriangleClass
  rw [← subdivisionUpperTriangleLoop_eq_basedTriangleLoop, ←
    subdivisionUpperNegativeLoop_eq_basedTriangleLoop]
  exact subdivisionUpperOrientation_additiveClass p hd

theorem SecondHurewicz.SimplyConnected.subdivision_basedTriangleClass_sub {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) -
        basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_basedTriangleClass_sum p hd)
    (subdivisionUpperPositiveBasedTriangle_class_eq_neg p hd)

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_class {X : Type} [TopologicalSpace X]
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

theorem SecondHurewicz.SimplyConnected.squareNormalization_quotient {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (⟦p⟧ : π_ 2 X x) =
      ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧ :=
  Quotient.sound (squareNormalization_homotopic p)

theorem SecondHurewicz.SimplyConnected.squareNormalization_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    basedTriangleClass (squareNormalizedLowerTriangle p) -
        basedTriangleClass (squareNormalizedUpperTriangle p) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  have h := congrArg Additive.ofMul (squareNormalization_quotient p)
  exact
    (basedTrianglesLoop_class (squareNormalizedLowerTriangle p)
          (squareNormalizedUpperTriangle p)).symm.trans
      h.symm

theorem SecondHurewicz.SimplyConnected.triangleClassOperator_squareChain {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    triangleClassOperator x (SecondHurewicz.squareChain p) = Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [squareChain_two_triangles, map_sub, triangleClassOperator_simplex,
    triangleClassOperator_simplex,
    normalizedTriangle_of_verticesBased x _ (lowerSquareTriangle_verticesBased p),
    normalizedTriangle_of_verticesBased x _ (upperSquareTriangle_verticesBased p)]
  exact squareNormalization_class p

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczInverse_hurewiczMap_mk {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczInverse x (SecondHurewicz.hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [SecondHurewicz.hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact triangleClassOperator_squareChain x p

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczInverse x (SecondHurewicz.hurewiczMap x a) = a := by
  change
    hurewiczInverse x (SecondHurewicz.hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem SecondHurewicz.SimplyConnected.hurewiczInverse_comp_hurewiczMap {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (hurewiczInverse x).comp (SecondHurewicz.hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

def SecondHurewicz.SimplyConnected.hurewiczLinearEquiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    Additive (π_ 2 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2 :=
  LinearEquiv.ofLinearMap (SecondHurewicz.hurewiczMap x) (hurewiczInverse x)
    (hurewiczMap_comp_hurewiczInverse x) (hurewiczInverse_comp_hurewiczMap x)

def SecondHurewicz.SimplyConnected.hurewiczPi2Equiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    π_ 2 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  __ := SecondHurewicz.hurewiczPi2 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))


def ThirdHurewicz.cylinderHomotopy {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (H : C((unitInterval) × A, X)) :
    ContinuousMap.Homotopy (SecondHurewicz.SimplyConnected.timeSlice H 0)
      (SecondHurewicz.SimplyConnected.timeSlice H 1)
    where
  toContinuousMap := H
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem ThirdHurewicz.homotopyTrans_compContinuousMap {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (f : C(B, A)) :
    (F.trans G).toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap f) =
      ((F.compContinuousMap f).trans (G.compContinuousMap f)).toContinuousMap := by
  ext z
  change (F.trans G) (z.1, f z.2) = ((F.compContinuousMap f).trans (G.compContinuousMap f)) z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

theorem ThirdHurewicz.homotopyTrans_const {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
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

theorem ThirdHurewicz.homotopyTrans_congr {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
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

def ThirdHurewicz.simplexFamilyHomotopy {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : SingularChains.SingularSimplex X n) :
    smp.Homotopy (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1) :=
  (cylinderHomotopy (H smp)).cast (by ext s; exact h₀ smp s) rfl

def ThirdHurewicz.composeSimplexHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) : C((unitInterval) × SingularChains.Simplex n, X) :=
  ((simplexFamilyHomotopy H hH₀ smp).trans
      (simplexFamilyHomotopy G hG₀
        (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1))).toContinuousMap

@[simp]
theorem ThirdHurewicz.composeSimplexHomotopies_zero {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) (s : SingularChains.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (0, s) = smp s :=
  ContinuousMap.Homotopy.apply_zero _ s

@[simp]
theorem ThirdHurewicz.composeSimplexHomotopies_one {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) (s : SingularChains.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (1, s) =
      G (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1) (1, s) :=
  ContinuousMap.Homotopy.apply_one _ s

@[simp]
theorem ThirdHurewicz.timeSlice_composeSimplexHomotopies_one {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : SingularChains.SingularSimplex X n) :
    SecondHurewicz.SimplyConnected.timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 1 =
      SecondHurewicz.SimplyConnected.timeSlice
        (G (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1)) 1 := by
  ext s
  exact composeSimplexHomotopies_one H G hH₀ hG₀ smp s

theorem ThirdHurewicz.composeSimplexHomotopies_face {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : SingularChains.SingularSimplex X n → C((unitInterval) × SingularChains.Simplex n, X))
    (H' G' :
      SingularChains.SingularSimplex X (n + 1) →
        C((unitInterval) × SingularChains.Simplex (n + 1), X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH'₀ : ∀ smp s, H' smp (0, s) = smp s) (hG'₀ : ∀ smp s, G' smp (0, s) = smp s)
    (hH : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hG : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n G G') :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n
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
      (G' (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)).comp
          ((ContinuousMap.id (unitInterval)).prodMap (SingularChains.simplexFace n i)) =
        G
          (SecondHurewicz.SimplyConnected.timeSlice (H (smp.comp (SingularChains.simplexFace n i)))
            1)
    rw [hG (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1) i,
      SecondHurewicz.SimplyConnected.timeSlice_face hH smp i 1]

theorem ThirdHurewicz.composeSimplexHomotopies_const {X : Type} [TopologicalSpace X] {n : ℕ}
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
    SecondHurewicz.SimplyConnected.timeSlice (H (ContinuousMap.const (SingularChains.Simplex n) x))
        1 =
      ContinuousMap.const (SingularChains.Simplex n) x := by
    rw [hH]
    rfl
  unfold composeSimplexHomotopies
  apply homotopyTrans_const
  · exact hH
  · change
      G
          (SecondHurewicz.SimplyConnected.timeSlice
            (H (ContinuousMap.const (SingularChains.Simplex n) x)) 1) =
        _
    rw [h₁]
    exact hG

end Mathoverflow1973
