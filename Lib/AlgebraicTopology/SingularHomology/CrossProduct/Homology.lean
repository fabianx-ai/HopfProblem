/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.SingularHomology.Chains
public import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
public import Lib.AlgebraicTopology.SingularHomology.CrossInsert
public import Lib.AlgebraicTopology.SingularHomology.CircleProduct
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.Chain
public import Lib.AlgebraicTopology.SingularHomology.CrossProduct.HomologyDescent

open Set Function Filter Manifold Topology

open scoped BigOperators TensorProduct

/-!
# The cross product on homology, `H₁(X) ⊗ Hₙ(Y) → H_{n+1}(X × Y)`

Descent of the chain-level cross product `SingularHomology.crossProductEdge` to homology.  A
`1`-cycle times an `n`-cycle is an `(n+1)`-cycle (`SingularHomology.crossProductCycles`); a cycle
times a boundary is a boundary (`SingularHomology.crossProductCycleClasses_boundary_right`, by the
Leibniz rule) and a boundary times a cycle is a boundary
(`SingularHomology.crossProductCycleClasses_boundary_left`,
`.crossProductHomologyCycles_boundary_left`, by the Leibniz rule for the degree-`2` product), so
the product descends in the right argument (`SingularHomology.crossProductHomologyFixed`,
`.crossProductHomologyCycles`) and then in the left one to

* `SingularHomology.crossProductHomology X Y n :
  (singularComplex X).homology 1 →ₗ[ℤ] (singularComplex Y).homology n →ₗ[ℤ]
  (singularComplex (X × Y)).homology (n + 1)`,

computed on cycle classes by `SingularHomology.crossProductHomology_cycleClass`.  At `n = 0` the
product is point insertion: `SingularHomology.crossProductEdge_zero_eq_zeroRight` and
`SingularHomology.crossProductHomology_pointClass_right`.

This is the cross product `H_p(X) ⊗ H_q(Y) → H_{p+q}(X × Y)` of Hatcher, *Algebraic Topology*,
§3.B, at `p = 1`.
-/


@[expose] public noncomputable section


/-! ### The cross product on cycles -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a `1`-cycle in `X` and a cycle in `Y`, landing in cycles of
`X × Y` via `crossProductEdge` (linear in the right argument). -/
def SingularHomology.crossProductCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
        SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex (X × Y)) (n + 1)
    where
  toFun
    a :=
    { toFun
        b :=
        SingularMayerVietoris.ModuleHomology.mkCycle (SingularChains.singularComplex (X × Y))
          (n + 1) (SingularHomology.crossProductEdge X Y n a.1 b.1)
          (by
            rw [Nat.add_sub_cancel]
            exact
              SingularHomology.crossProductEdge_cycle n a.1 b.1
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex X) 1 a)
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (SingularChains.singularComplex Y) n b))
      map_add' b
        c := by
        apply Subtype.ext
        exact (SingularHomology.crossProductEdge X Y n a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (SingularHomology.crossProductEdge X Y n a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) => f c.1)
        ((SingularHomology.crossProductEdge X Y n).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : SingularChains.Chains Y n →ₗ[ℤ] SingularChains.Chains (X × Y) (n + 1) => f c.1)
        ((SingularHomology.crossProductEdge X Y n).map_smul r a.1)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The underlying chain of `crossProductCycles a b` is `crossProductEdge a.1 b.1`. -/
@[simp]
theorem SingularHomology.crossProductCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    (SingularHomology.crossProductCycles X Y n a b).1 = SingularHomology.crossProductEdge X Y n a.1 b.1 :=
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a `1`-cycle and a cycle as a map to homology classes of
`X × Y`, linear in the right argument. -/
def SingularHomology.crossProductCycleClasses (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  SingularHomology.integerBilinearPostcompose (SingularHomology.crossProductCycles X Y n)
    (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
      (n + 1))

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class-valued edge cross product vanishes when the right chain is a boundary. -/
theorem SingularHomology.crossProductCycleClasses_boundary_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularChains.Chains Y (n + 1)) :
    SingularHomology.crossProductCycleClasses X Y n a
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex Y) n
          b) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨-SingularHomology.crossProductEdge X Y (n + 1) a.1 b, ?_⟩
  change
    ((SingularChains.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (-SingularHomology.crossProductEdge X Y (n + 1) a.1 b) =
      SingularHomology.crossProductEdge X Y n a.1 (((SingularChains.singularComplex Y).d (n + 1) n).hom b)
  rw [map_neg,
    SingularHomology.crossProductEdge_boundary_of_left_cycle n a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex X) 1
        a),
    neg_neg]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a fixed left `1`-cycle `a` with `Y`-homology classes,
descended in the right argument. -/
def SingularHomology.crossProductHomologyFixed {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1) :
    (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
      (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  SingularHomology.homologyDesc (SingularChains.singularComplex Y) n (SingularHomology.crossProductCycleClasses X Y n a)
    (SingularHomology.crossProductCycleClasses_boundary_right n a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductHomologyFixed a` sends the class of a cycle `b` to the class of
`crossProductCycles` on representatives. -/
@[simp]
theorem SingularHomology.crossProductHomologyFixed_cycleClass {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularHomology.crossProductHomologyFixed n a
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (SingularHomology.crossProductCycles X Y n a b) :=
  SingularHomology.homologyDesc_cycleClass _ _ _ _ b

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The cross product of a `1`-cycle in `X` with a cycle in `Y` as a map into
`n + 1`-homology of `X × Y` (descended in the right argument). -/
def SingularHomology.crossProductHomologyCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1 →ₗ[ℤ]
      ((SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1))
    where
  toFun a := SingularHomology.crossProductHomologyFixed n a
  map_add' a
    b := by
    apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex Y) n
    intro c
    change
      SingularHomology.crossProductHomologyFixed n (a + b)
          (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
            c) =
        SingularHomology.crossProductHomologyFixed n a
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
              c) +
          SingularHomology.crossProductHomologyFixed n b
            (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n
              c)
    simp only [SingularHomology.crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
              (SingularChains.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((SingularHomology.crossProductCycleClasses X Y n).map_add a b)
  map_smul' r
    a := by
    apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex Y) n
    intro c
    simp only [LinearMap.smul_apply, RingHom.id_apply, SingularHomology.crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n →ₗ[ℤ]
              (SingularChains.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((SingularHomology.crossProductCycleClasses X Y n).map_smul r a)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The class-valued edge cross product vanishes when the left chain is a boundary. -/
theorem SingularHomology.crossProductCycleClasses_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularHomology.crossProductCycleClasses X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1 a)
        b =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (SingularChains.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨SingularHomology.crossProductTriangle X Y n a b.1, ?_⟩
  exact
    SingularHomology.crossProductTriangle_boundary_of_right_cycle n a b.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (SingularChains.singularComplex Y) n b)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology-valued edge cross product vanishes when the left `1`-chain is a
boundary. -/
theorem SingularHomology.crossProductHomologyCycles_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : SingularChains.Chains X 2) :
    SingularHomology.crossProductHomologyCycles X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1
          a) =
      0 := by
  apply SingularHomology.homologyLinearMap_ext (SingularChains.singularComplex Y) n
  intro b
  change
    SingularHomology.crossProductHomologyFixed n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (SingularChains.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      0
  rw [SingularHomology.crossProductHomologyFixed_cycleClass]
  exact SingularHomology.crossProductCycleClasses_boundary_left n a b


/-! ### The cross product on homology -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- The homology cross product `H_1(X) →ₗ[ℤ] H_n(Y) →ₗ[ℤ] H_{n+1}(X × Y)`. -/
def SingularHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    (SingularChains.singularComplex X).homology 1 →ₗ[ℤ]
      (SingularChains.singularComplex Y).homology n →ₗ[ℤ]
        (SingularChains.singularComplex (X × Y)).homology (n + 1) :=
  SingularHomology.homologyDesc (SingularChains.singularComplex X) 1 (SingularHomology.crossProductHomologyCycles X Y n)
    (SingularHomology.crossProductHomologyCycles_boundary_left n)

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- `crossProductHomology` on cycle classes `⟦a⟧`, `⟦b⟧` is the class of the edge
cross product `a × b`. -/
@[simp]
theorem SingularHomology.crossProductHomology_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex Y) n) :
    SingularHomology.crossProductHomology X Y n
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex (X × Y))
        (n + 1) (SingularHomology.crossProductCycles X Y n a b) := by
  rw [SingularHomology.crossProductHomology, SingularHomology.homologyDesc_cycleClass]
  exact SingularHomology.crossProductHomologyFixed_cycleClass n a b


/-! ### Degenerations at degree zero -/

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- In right degree `0`, `crossProductEdge` coincides with `crossProductZeroRight`
(up to the degree identification). -/
theorem SingularHomology.crossProductEdge_zero_eq_zeroRight (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    SingularHomology.crossProductEdge X Y 0 = SingularHomology.crossProductZeroRight X Y 1 := by
  apply SingularHomology.chainBilinearMap_ext X Y 1 0
  intro σ τ
  rw [SingularHomology.crossProductEdge_simplex, SingularHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularHomology.productAffineChainMap_simplex,
    SingularChains.inducedChain_simplex, SingularHomology.crossProductZeroRight_simplex]
  apply congrArg (SingularChains.simplexChain (X × Y) 1)
  change
    (σ.prodMap τ).comp
        (SingularHomology.productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 1 i, SingularMayerVietoris.stdVertices 0 0))) =
      (SingularHomology.crossInsertRight (zeroSimplexValue τ)).comp σ
  rw [productAffineSimplex_point_right, SingularMayerVietoris.affineSimplex_stdVertices,
    ContinuousMap.comp_id]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a `0`-simplex right generator, `crossProductEdge` at degree `0` sends
`(σ, τ)` to `σ` composed with the point insertion. -/
theorem SingularHomology.crossProductEdge_zero_simplex_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1)
    (τ : SingularChains.SingularSimplex Y 0) :
    crossProductEdge X Y 0 a (SingularChains.simplexChain Y 0 τ) =
      SingularChains.inducedChain (SingularHomology.crossInsertRight (zeroSimplexValue τ)) 1 a := by
  rw [crossProductEdge_zero_eq_zeroRight, crossProductZeroRight_simplex_right]

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a point `0`-cycle `y`, `crossProductEdge a` agrees with the point-insertion
pushforward of `a`. -/
@[simp]
theorem SingularHomology.crossProductEdge_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularChains.Chains X 1) (y : Y) :
    crossProductEdge X Y 0 a (SingularHomology.pointCycle y).1 =
      SingularChains.inducedChain (SingularHomology.crossInsertRight y) 1 a := by
  rw [SingularHomology.pointCycle_val, crossProductEdge_zero_simplex_right]
  rfl

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On a point `0`-cycle, `crossProductCycles a` is the pushforward of `a` along the
point insertion. -/
@[simp]
theorem SingularHomology.crossProductCycles_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 1) (y : Y) :
    SingularHomology.crossProductCycles X Y 0 a (SingularHomology.pointCycle y) =
      SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularChains.singularChainMap (SingularHomology.crossInsertRight y)) 1 a := by
  apply Subtype.ext
  rw [SingularHomology.crossProductCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact SingularHomology.crossProductEdge_pointCycle_right X Y a.1 y

attribute [local instance] SingularHomology.integerLinearMapModule
    SingularHomology.integerTensorModule in
/-- On the homology class of a point `0`-cycle, `crossProductHomology a` is the
point-insertion pushforward on homology. -/
@[simp]
theorem SingularHomology.crossProductHomology_pointClass_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (y : Y) :
    crossProductHomology X Y 0 a (SingularHomology.pointClass y) =
      SingularMayerVietoris.singularHomologyMap (SingularHomology.crossInsertRight y) 1 a := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (SingularChains.singularComplex X) 1
      a
  change
    SingularHomology.crossProductHomology X Y 0
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 1 c)
        (SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex Y) 0
          (SingularHomology.pointCycle y)) =
      _
  rw [SingularHomology.crossProductHomology_cycleClass, SingularHomology.crossProductCycles_pointCycle_right]
  exact
    (SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass
        (SingularChains.singularChainMap (SingularHomology.crossInsertRight y)) 1 c).symm
