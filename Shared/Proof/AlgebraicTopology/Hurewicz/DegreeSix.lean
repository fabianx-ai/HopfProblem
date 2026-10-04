/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.Hurewicz.PrismOperator
import Lib.AlgebraicTopology.Hurewicz.Straightening
import Lib.AlgebraicTopology.Hurewicz.CubeSphere
import Lib.AlgebraicTopology.Hurewicz.Naturality

/-!
# The Hurewicz map in degree six

Proof-specific: every declaration below is the `n = 6` (`m = 4`, resp. `m = 3`) case of the
corresponding general `Hurewicz.*` declaration of `Lib/AlgebraicTopology/Hurewicz/`, with the
degree `6` fixed because the project's target is `S⁶`.  No textbook states a degree-six Hurewicz
theorem; the theorems are `Hurewicz.hurewiczLinearEquiv`, `Hurewicz.cubeChain_natural` and their
companions, instantiated so that a consumer can state the sixth Hurewicz isomorphism without the
offset bookkeeping.

The general statements this file instantiates live in
`Lib/AlgebraicTopology/Hurewicz/{Degree, HopfDegree, Naturality}.lean`.  Moved out of
`Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean` by the round-8 D-file pass
(`Lib/reports/round-7/judgement/d-files.md`).

Moved verbatim from `Hopf/Proof/AlgebraicTopology/Hurewicz/DegreeSix.lean`: the declarations of that
file that both the old proof and the center construction use
(`Lib/reports/center-proof/RECEIPT.md`).
-/

open Set Function Filter Manifold Topology

noncomputable section

def SixthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : SingularMayerVietoris.SingularHomology X 6 :=
  Hurewicz.cubeHomologyClass p

def SixthHurewicz.homotopyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (x : X) : π_ 6 X x →* π_ 6 Y (f x) :=
  Hurewicz.homotopyMap f x

def SixthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    Additive (π_ 6 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6 :=
  Hurewicz.hurewiczLinearEquiv (m := 3) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

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
