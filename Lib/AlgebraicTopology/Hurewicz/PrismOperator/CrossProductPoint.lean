/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
/-!
# Cross products with a point chain

The degree-zero cross products with the point chain of a point `y` (on the right) or `t`
(on the left) are the pushforwards along the insertions `x ↦ (x, y)` and `y ↦ (t, y)`:
`SingularHomology.crossProductTriangle X Y 0 a (pointChain y)` and
`crossProductEdge X Y 0 a (pointChain y)` are `inducedChain (crossInsertRight y)` of `a`, and
`crossProductZeroLeft I A n (pointChain t) c` is `inducedChain (crossInsertLeft t)` of `c`.
These are the boundary terms `H₀# c`, `H₁# c` of the prism operator (Hatcher, Thm 2.10).

## Main results

* `Hurewicz.DegreeTwo.crossProductTriangle_point_right`, `crossProductEdge_point_right`
* `Hurewicz.DegreeTwo.SimplyConnected.crossPoint_left`
-/

open Set Function Topology

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

/-! ### The left cross product with a point chain -/

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
