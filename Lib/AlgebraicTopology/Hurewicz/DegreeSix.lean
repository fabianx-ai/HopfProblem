/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.Hurewicz.PrismOperator
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition
import Lib.AlgebraicTopology.Hurewicz.Straightening
import Lib.AlgebraicTopology.Hurewicz.CubeSphere
import Lib.AlgebraicTopology.Hurewicz.Naturality

/-!
# The Hurewicz map in degree six

The degree-six instance of the higher Hurewicz theory (`Hurewicz.hurewiczMap`,
`Hurewicz.hurewiczLinearEquiv`, `Hurewicz.cubeChain_natural`, ...): for a space `X` with base
point `x`, the cube chain and cube cycle of a six-loop, the Hurewicz homomorphism
`SixthHurewicz.hurewiczPi6 : π_ 6 X x →* Multiplicative (H_6 X)`, its `ℤ`-linear form
`SixthHurewicz.hurewiczMap`, the inverse and the linear equivalence
`SixthHurewicz.hurewiczLinearEquiv` when `X` is simply connected with `π_ k X x` trivial for
`2 ≤ k ≤ 5`, the group isomorphism `SixthHurewicz.hurewiczPi6Equiv`, and the naturality of all of
these under continuous maps.

Every declaration is the `n = 6` (`m = 4`, resp. `m = 3`) case of the corresponding
`Hurewicz.*` declaration; the file exists so that a consumer can state the sixth Hurewicz
isomorphism without the offset bookkeeping.

Moved verbatim from `Hopf/Recognition.lean` (statements unchanged; qualifier retargets
`HigherHurewicz.* -> Hurewicz.*`, `FirstHurewicz.* -> SingularChains.*`,
`SecondHurewicz.mapGenLoop -> Hurewicz.DegreeTwo.mapGenLoop`, which name the same constants).
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

def SixthHurewicz.fundamentalCubeChain : SingularChains.Chains (Fin 6 → (unitInterval)) 6 :=
  Hurewicz.fundamentalCubeChain 6

def SixthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SingularChains.Chains X 6 :=
  Hurewicz.cubeChain p

theorem SixthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    cubeChain p = SingularChains.inducedChain p.val 6 fundamentalCubeChain :=
  rfl

def SixthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularChains.singularComplex X) 6 :=
  Hurewicz.cubeCycle p

@[simp]
theorem SixthHurewicz.cubeCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : (cubeCycle p).1 = cubeChain p :=
  rfl

def SixthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : SingularMayerVietoris.SingularHomology X 6 :=
  Hurewicz.cubeHomologyClass p

theorem SixthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  Hurewicz.cubeHomologyClass_homotopic h

def SixthHurewicz.homotopyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (x : X) : π_ 6 X x →* π_ 6 Y (f x) :=
  Hurewicz.homotopyMap f x

def SixthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 6 X x → SingularMayerVietoris.SingularHomology X 6 :=
  Hurewicz.hurewiczFunction (m := 4) x

def SixthHurewicz.hurewiczPi6 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 6 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 6) :=
  Hurewicz.hurewiczPi (m := 4) x

def SixthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 6 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6 :=
  Hurewicz.hurewiczMap (m := 4) x

theorem SixthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 6) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (SingularChains.singularComplex X) 6
        (cubeCycle p) :=
  rfl

def SixthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    SingularMayerVietoris.SingularHomology X 6 →ₗ[ℤ] Additive (π_ 6 X x) :=
  Hurewicz.hurewiczInverse (m := 3) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def SixthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    Additive (π_ 6 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6 :=
  Hurewicz.hurewiczLinearEquiv (m := 3) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def SixthHurewicz.hurewiczPi6Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    π_ 6 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 6)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

theorem SixthHurewicz.cubeChain_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularChains.inducedChain f 6 (cubeChain p) = cubeChain (Hurewicz.DegreeTwo.mapGenLoop f x p) :=
  Hurewicz.cubeChain_natural f x p

theorem SixthHurewicz.cubeCycle_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles (SingularChains.singularChainMap f) 6
        (cubeCycle p) =
      cubeCycle (Hurewicz.DegreeTwo.mapGenLoop f x p) :=
  Hurewicz.cubeCycle_natural f x p

theorem SixthHurewicz.cubeHomologyClass_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.singularHomologyMap f 6 (cubeHomologyClass p) =
      cubeHomologyClass (Hurewicz.DegreeTwo.mapGenLoop f x p) :=
  Hurewicz.cubeHomologyClass_natural f x p

theorem SixthHurewicz.hurewiczFunction_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : π_ 6 X x) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczFunction x a) =
      hurewiczFunction (f x) (homotopyMap f x a) :=
  Hurewicz.hurewiczFunction_natural f x a

theorem SixthHurewicz.hurewiczMap_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : Additive (π_ 6 X x)) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczMap x a) =
      hurewiczMap (f x) ((homotopyMap f x).toAdditive a) :=
  Hurewicz.hurewiczMap_natural f x a

theorem SixthHurewicz.hurewiczLinearEquiv_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]
    [Subsingleton (π_ 4 Y (f x))] [Subsingleton (π_ 5 Y (f x))] (a : Additive (π_ 6 X x)) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczLinearEquiv x a) =
      hurewiczLinearEquiv (f x) ((homotopyMap f x).toAdditive a) :=
  Hurewicz.hurewiczLinearEquiv_natural f x
    (by intro j hj hjn; interval_cases j <;> infer_instance)
    (by intro j hj hjn; interval_cases j <;> infer_instance) a

end
