/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

This file is a formalization of the claim that the six-sphere admits a complex
manifold structure compatible with its standard topology.

The mathematical content is drawn from "A compact complex threefold fibred by
tori over the projective line, and the six-sphere" (https://alpo.ge/s6.pdf),
originally shared by Levent Alpöge on X:
https://x.com/__alpoge__/status/2091639597193368014

The majority of the Lean code in this formalization is written by Codex.

The statement of the final result is adapted from the Formal Conjectures
formalization of MathOverflow question 1973:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Mathoverflow/1973.lean

Parts of the complex-analysis development, including the Riemann mapping
theorem, Hurwitz's theorem, analytic factorization, normal-family arguments,
and unit-disc automorphisms, were adapted from Yury Kudryashov's Mathlib work:
https://github.com/leanprover-community/mathlib4/pull/33505
Source commit: d43061d911b1aeae0788591da437a3b115098962
Upstream files:
  Mathlib/Analysis/Complex/RiemannMapping.lean
  Mathlib/Analysis/Complex/UnitDisc/Shift.lean

Additional preliminary Riemann-mapping lemmas were adapted from
Mathlib/Analysis/Complex/RiemannMapping.lean in Mathlib v4.33.0:
https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/RiemannMapping.lean

Parts of the topology development, including simple connectedness of spheres,
the path-factorization portion of the van Kampen development, and associated
compatibility lemmas, were adapted from Sebastian Kumar's Mathlib work:
https://github.com/leanprover-community/mathlib4/pull/28246
Source commit: 037ad801e1e5a5b7aa1750957c07f7769812effc
Upstream files:
  Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnectedSphere.lean
  Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen.lean
  Mathlib/Topology/Path.lean
  Mathlib/Logic/Equiv/PartialEquiv.lean

The reused upstream materials were released under the Apache License,
Version 2.0. They were modified, reorganized, and adapted for this
formalization; some results were also strengthened. Their copyright
and author notices are retained below.

Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Authors: Yury Kudryashov

Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Authors: Sebastian Kumar

Copyright 2025 The Formal Conjectures Authors.
-/

/-
Move-only extraction from HopfProblem Solution.lean at 9ac8a456b526527837d7082ff775213ca8bc9809.
Original source lines 81183--104759; see PROVENANCE.md.
-/

import Hopf.LibShims
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
import Lib.AlgebraicTopology.SingularHomology.CrossProduct
import Lib.AlgebraicTopology.Hurewicz.SimplexCube
import Lib.AlgebraicTopology.Hurewicz.HomotopyExtension
import Lib.AlgebraicTopology.Hurewicz.CubeTriangulation
import Lib.AlgebraicTopology.Hurewicz.PrismOperator
import Lib.AlgebraicTopology.Hurewicz.Subdivision
import Lib.AlgebraicTopology.Hurewicz.CubeGluing
import Lib.AlgebraicTopology.Hurewicz.Degree
import Lib.AlgebraicTopology.Hurewicz.CubeChainDecomposition
import Lib.AlgebraicTopology.Hurewicz.HopfDegree
import Lib.AlgebraicTopology.FundamentalGroup.SimplyConnectedCover
import Lib.AlgebraicTopology.FundamentalGroup.TwoSimplyConnectedCover
import Lib.AlgebraicTopology.FundamentalGroup.VanKampen
import Lib.Topology.Homeomorph.DiskCube
import Hopf.SphereTopology

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


theorem fundamentalGroup_eq_one_of_path {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (hx : ∀ g : FundamentalGroup X x, g = 1) (g : FundamentalGroup X y) : g = 1 := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  obtain ⟨h, rfl⟩ := e.surjective g
  rw [hx h, map_one]

theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) : SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 :=
  by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    exact fun _ => Subsingleton.elim _ _
  · intro hx
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, ?_⟩
    intro y γ
    exact
      Path.Homotopic.Quotient.eq.mp
        (fundamentalGroup_eq_one_of_path (PathConnectedSpace.somePath x y) hx
          (Path.Homotopic.Quotient.mk γ))

theorem simplyConnectedSpace_of_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hx : ∀ g : FundamentalGroup X x, g = 1) :
    SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_fundamentalGroup_eq_one x).mpr hx

theorem SphereHomology.twoOpenCover_pathConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩

theorem SphereHomology.twoOpenCover_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] (g : FundamentalGroup X D.base) : g = 1 := by
  have h :
    MonoidHom.id (FundamentalGroup X D.base) =
      (1 : FundamentalGroup X D.base →* FundamentalGroup X D.base) := by
    apply D.hom_ext
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomU a = 1
      rw [ha, map_one]
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomV a = 1
      rw [ha, map_one]
  exact DFunLike.congr_fun h g

theorem SphereHomology.twoOpenCover_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroup.VanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] : SimplyConnectedSpace X := by
  let := twoOpenCover_pathConnectedSpace D
  exact
    simplyConnectedSpace_of_fundamentalGroup_eq_one D.base
      (twoOpenCover_fundamentalGroup_eq_one D)

def SphereHomology.suspensionConeCover (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) : FundamentalGroup.VanKampen.TwoOpenCover (Suspension.topSus X)
    where
  U := ⟨Suspension.topSus.northOpen, Suspension.topSus.northOpen_isOpen⟩
  V := ⟨Suspension.topSus.southOpen, Suspension.topSus.southOpen_isOpen⟩
  cover := Suspension.topSus.open_cover
  pathConnectedU := by
    change
      IsPathConnected
        (Suspension.topSus.northOpen : Set (Suspension.topSus X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedV := by
    change
      IsPathConnected
        (Suspension.topSus.southOpen : Set (Suspension.topSus X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedIntersection := by
    change IsPathConnected (Suspension.topSus.middleBand X)
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  base := Suspension.topSus.mk ⟨1 / 2, by norm_num⟩ x
  baseU := by
    change (1 / 2 : ℝ) < 3 / 4
    norm_num
  baseV := by
    change (1 / 4 : ℝ) < 1 / 2
    norm_num

instance SphereHomology.suspension_simplyConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : SimplyConnectedSpace (Suspension.topSus X) := by
  let D := suspensionConeCover X (Classical.choice (inferInstance : Nonempty X))
  let : SimplyConnectedSpace D.U := by
    change
      SimplyConnectedSpace
        (Suspension.topSus.northOpen : Set (Suspension.topSus X))
    infer_instance
  let : SimplyConnectedSpace D.V := by
    change
      SimplyConnectedSpace
        (Suspension.topSus.southOpen : Set (Suspension.topSus X))
    infer_instance
  exact twoOpenCover_simplyConnectedSpace D

instance SphereHomology.unitSphere_simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace (UnitSphere (n + 2)) :=
  (suspensionSphereHomeomorph (n + 1)).symm.toHomotopyEquiv.simplyConnectedSpace
theorem SphereHomology.unitSphere_piTwo_subsingleton (n : ℕ) (x : UnitSphere (n + 3)) :
    Subsingleton (π_ 2 (UnitSphere (n + 3)) x) := by
  let := unitSphere_homology_subsingleton (n + 2) 2 (by decide) (by omega)
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton


def ThirdHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    Additive (π_ 3 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3 :=
  HigherHurewicz.hurewiczLinearEquiv (m := 0) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def ThirdHurewicz.hurewiczPi3Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    π_ 3 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 3)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

def FourthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    Additive (π_ 4 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 4 :=
  HigherHurewicz.hurewiczLinearEquiv (m := 1) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def FourthHurewicz.hurewiczPi4Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    π_ 4 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 4)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

def FifthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    Additive (π_ 5 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 5 :=
  HigherHurewicz.hurewiczLinearEquiv (m := 2) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def FifthHurewicz.hurewiczPi5Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    π_ 5 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 5)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

abbrev SixSphereCube.StandardSphere :=
  SphereHomology.UnitSphere 6

def SixSphereCube.euclideanOnePointSphereHomeomorph :
    OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 6)) (ι := Fin 7) (by simp)

def SixSphereCube.sphereBasePoint : StandardSphere :=
  euclideanOnePointSphereHomeomorph (OnePoint.infty)

theorem Sphere.piTwo_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 2 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 2 (by decide) (by decide) x

theorem Sphere.piThree_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 3 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 3 (by decide) (by decide) x

theorem Sphere.piFour_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 4 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 4 (by decide) (by decide) x

theorem Sphere.piFive_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 5 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 5 (by decide) (by decide) x

end Mathoverflow1973

end
