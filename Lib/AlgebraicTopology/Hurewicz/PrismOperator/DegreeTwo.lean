/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczInverse
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.HurewiczMap
import Lib.AlgebraicTopology.Hurewicz.PrismOperator.SubdivisionTriangleClass
/-!
# The degree-two Hurewicz theorem

For a simply connected space `X` the Hurewicz map is a `ℤ`-linear isomorphism
`Hurewicz.degreeTwoLinearEquiv x : Additive (π_ 2 X x) ≃ₗ[ℤ] H_2 X`, with inverse
`hurewiczInverse x`; multiplicatively, `hurewiczPi2Equiv x : π_ 2 X x ≃* Multiplicative (H_2 X)`.
This is Hatcher, Thm 4.32, at `n = 2`.

## Main definitions

* `Hurewicz.degreeTwoLinearEquiv`
* `Hurewicz.DegreeTwo.SimplyConnected.hurewiczPi2Equiv`
-/

open Set Function Topology

noncomputable section

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
