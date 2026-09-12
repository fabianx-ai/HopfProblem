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
Original source lines 237525--248758; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.LCP.IntegralHomology
import Lib.AlgebraicTopology.Hurewicz.CubeSphere
import Lib.Topology.Homotopy.CellFilling
import Lib.Geometry.Manifold.ChartedSpace.Transport
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Geometry.Manifold.Morse.CellStructure

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

theorem SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 3 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  have := ThreefoldHomology.ThirdDegree.homologyThree_subsingleton
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

theorem SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 4 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  have := SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  have := ThreefoldHomology.FourthDegree.homologyFour_subsingleton
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

theorem SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ 5 SpecialPeriods.Threefold.Space x) :=
  by
  have := SpecialPeriods.Threefold.space_simplyConnected
  have := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  have := SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  have := SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton x
  have := ThreefoldHomology.FifthDegree.homologyFive_subsingleton
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

def SixthHurewicz.lowerSevenSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 7) :
    C((unitInterval) × FirstHurewicz.Simplex 7, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) smp

@[simp]
theorem SixthHurewicz.lowerSevenSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (s : FirstHurewicz.Simplex 7) : lowerSevenSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SixthHurewicz.lowerSevenSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 6
      (FifthHurewicz.normalizationSixSimplexHomotopy x) (lowerSevenSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (FifthHurewicz.normalizationSixHomotopy_face x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x)

def SixthHurewicz.fiveSixSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6) :
    C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) smp

@[simp]
theorem SixthHurewicz.fiveSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : fiveSixSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SixthHurewicz.fiveSixSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5
      (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 4)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)

def SixthHurewicz.fiveSevenSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7) :
    C((unitInterval) × FirstHurewicz.Simplex 7, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy_face x) (fiveSixSimplexHomotopy_zero x) smp

@[simp]
theorem SixthHurewicz.fiveSevenSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (s : FirstHurewicz.Simplex 7) : fiveSevenSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SixthHurewicz.fiveSevenSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 6 (fiveSixSimplexHomotopy x)
      (fiveSevenSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (HigherHurewicz.simplexStraighteningHomotopy 5 x) (fiveSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy_face x) (fiveSixSimplexHomotopy_zero x)

def SixthHurewicz.normalizationFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.SingularSimplex X 5 → C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)

def SixthHurewicz.normalizationSixSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.SingularSimplex X 6 → C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy x) (FifthHurewicz.normalizationSixSimplexHomotopy_zero x)
    (fiveSixSimplexHomotopy_zero x)

def SixthHurewicz.normalizationSevenSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.SingularSimplex X 7 → C((unitInterval) × FirstHurewicz.Simplex 7, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerSevenSimplexHomotopy x)
    (fiveSevenSimplexHomotopy x) (lowerSevenSimplexHomotopy_zero x)
    (fiveSevenSimplexHomotopy_zero x)

@[simp]
theorem SixthHurewicz.normalizationSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

theorem SixthHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5 (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationSixSimplexHomotopy x) (fiveSixSimplexHomotopy x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x)
    (FifthHurewicz.normalizationSixHomotopy_face x) (fiveSixSimplexHomotopy_face x)

theorem SixthHurewicz.normalizationSevenHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 6 (normalizationSixSimplexHomotopy x)
      (normalizationSevenSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FifthHurewicz.normalizationSixSimplexHomotopy x)
    (fiveSixSimplexHomotopy x) (lowerSevenSimplexHomotopy x) (fiveSevenSimplexHomotopy x)
    (FifthHurewicz.normalizationSixSimplexHomotopy_zero x) (fiveSixSimplexHomotopy_zero x)
    (lowerSevenSimplexHomotopy_zero x) (fiveSevenSimplexHomotopy_zero x)
    (lowerSevenSimplexHomotopy_face x) (fiveSevenSimplexHomotopy_face x)

@[simp]
theorem SixthHurewicz.normalizationFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (FifthHurewicz.normalizationFiveSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 5 x)
    (FifthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 5 x) x
    (FifthHurewicz.normalizationFiveSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 5 x)

@[simp]
theorem SixthHurewicz.normalizationFiveSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1 =
      ContinuousMap.const (FirstHurewicz.Simplex 5) x := by
  rw [normalizationFiveSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    FifthHurewicz.normalizationFiveSimplexHomotopy_endpoint]
  ext s
  exact
    HigherHurewicz.simplexStraighteningHomotopy_one 5 x
      (FifthHurewicz.normalizedFiveSimplex x smp).val
      (FifthHurewicz.normalizedFiveSimplex x smp).property s

abbrev SixthHurewicz.sixSimplexBoundary : Set (FirstHurewicz.Simplex 6) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 6

abbrev SixthHurewicz.BasedSixSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 6 x

abbrev SixthHurewicz.basedSixSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : GenLoop (Fin 6) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

abbrev SixthHurewicz.basedSixSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : Additive (π_ 6 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

theorem SixthHurewicz.basedSixSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) (i : Fin 7) :
    τ.val.comp (FirstHurewicz.simplexFace 5 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 5) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

def SixthHurewicz.normalizedSixSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 6) : BasedSixSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (normalizationSixSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationFiveSimplexHomotopy_endpoint x) smp⟩

def SixthHurewicz.normalizedSevenSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 7) : FirstHurewicz.SingularSimplex X 7 :=
  SecondHurewicz.SimplyConnected.timeSlice (normalizationSevenSimplexHomotopy x smp) 1

theorem SixthHurewicz.normalizedSevenSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (i : Fin 8) :
    (normalizedSevenSimplexMap x smp).comp (FirstHurewicz.simplexFace 6 i) =
      (normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i))).val :=
  SecondHurewicz.SimplyConnected.timeSlice_face (normalizationSevenHomotopy_face x) smp i 1

theorem SixthHurewicz.normalizedSevenSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (i : Fin 8) (s : FirstHurewicz.Simplex 6) (hs : s ∈ sixSimplexBoundary) :
    normalizedSevenSimplexMap x smp (FirstHurewicz.simplexFace 6 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 6, X) => f s)
      (normalizedSevenSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i))).property s hs)

def SixthHurewicz.sixSimplexClassOperator {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] : FirstHurewicz.Chains X 6 →ₗ[ℤ] Additive (π_ 6 X x) :=
  FirstHurewicz.chainLift X 6 fun smp => basedSixSimplexClass (normalizedSixSimplex x smp)

@[simp]
theorem SixthHurewicz.sixSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) :
    sixSimplexClassOperator x (FirstHurewicz.simplexChain X 6 smp) =
      basedSixSimplexClass (normalizedSixSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 6 _ smp

abbrev SixthHurewicz.BasedSevenSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary 7 x

abbrev SixthHurewicz.basedSevenSimplexFace {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSevenSimplex x) (i : Fin 8) : BasedSixSimplex x :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace τ i

def SixthHurewicz.BasedSevenSimplex.ofFaces {X : Type*} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 7, X))
    (h :
      ∀ i : Fin 8,
        ∀ s ∈ SixthHurewicz.sixSimplexBoundary, (τ.comp (FirstHurewicz.simplexFace 6 i)) s = x) :
    SixthHurewicz.BasedSevenSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces τ h

theorem SixthHurewicz.basedSevenSimplex_signed_relation {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSevenSimplex x) :
    (∑ i : Fin 8, (-1 : ℤ) ^ i.val • basedSixSimplexClass (basedSevenSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 4) τ

def SixthHurewicz.normalizedSevenSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7) : BasedSevenSimplex x :=
  BasedSevenSimplex.ofFaces (normalizedSevenSimplexMap x smp)
    (normalizedSevenSimplexMap_face_boundary x smp)

@[simp]
theorem SixthHurewicz.normalizedSevenSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (smp : FirstHurewicz.SingularSimplex X 7)
    (i : Fin 8) :
    basedSevenSimplexFace (normalizedSevenSimplex x smp) i =
      normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i)) := by
  apply Subtype.ext
  exact normalizedSevenSimplexMap_face x smp i

theorem SixthHurewicz.normalizedSixSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 7) :
    ∑ i : Fin 8,
        (-1 : ℤ) ^ i.val •
          basedSixSimplexClass
            (normalizedSixSimplex x (smp.comp (FirstHurewicz.simplexFace 6 i))) =
      0 := by
  simpa only [normalizedSevenSimplex_face] using
    basedSevenSimplex_signed_relation (normalizedSevenSimplex x smp)

theorem SixthHurewicz.sixSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (b : FirstHurewicz.Chains X 7) :
    sixSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 7 6).hom b) = 0 := by
  have h : (sixSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 7 6).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 7
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      sixSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedSixSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

def SixthHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) : GenLoop (Fin 6) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) p

theorem SixthHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 6)) :
    (normalizedCube x p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      (normalizedSixSimplex x
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) p e

def SixthHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 6)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) (normalizationSixSimplexHomotopy_zero x) p

theorem SixthHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x)
    (u : Fin 6 → (unitInterval)) (i j : Fin 6) (hij : i ≠ j) (hu : u i = u j) :
    normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased (normalizationFiveSimplexHomotopy x)
    (normalizationSixSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFiveSimplexHomotopy_const x) (normalizationFiveSimplexHomotopy_endpoint x) p u i
    j hij hu

theorem SixthHurewicz.normalizedCube_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x)
    (e : Equiv.Perm (Fin 6)) :
    HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x p)
        (normalizedCube_internalBased x p) e =
      normalizedSixSimplex x (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

abbrev SixthHurewicz.Remaining :=
  { j : Fin 6 // j ≠ 0 }

def SixthHurewicz.remainingCoordinates : C(Fin 5 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
theorem SixthHurewicz.remainingCoordinates_succ (u : Fin 5 → (unitInterval)) (i : Fin 5) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

theorem SixthHurewicz.remainingCoordinates_boundary {u : Fin 5 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 5)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

abbrev SixthHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

def SixthHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 5 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

theorem SixthHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 5 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 5)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

theorem SixthHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (x : X) (f : C(A, Fin 5 → (unitInterval)))
    (hf : ∀ a, f a ∈ Cube.boundary (Fin 5)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

def SixthHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 5 → (unitInterval)), Fin 6 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 6) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem SixthHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 5 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem SixthHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 5 → (unitInterval)))
    (i : Fin 5) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

def SixthHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    C((unitInterval) × (Fin 5 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

theorem SixthHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 6) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 5 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.remainingCubeSideFirst (t : (unitInterval)) :
    C(Fin 4 → (unitInterval), Fin 5 → (unitInterval)) :=
  FifthHurewicz.cubeCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.remainingCubeSide {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 4 → (unitInterval))) : C((unitInterval) × A, Fin 5 → (unitInterval)) :=
  FifthHurewicz.cubeCoordinates.comp ((ContinuousMap.id (unitInterval)).prodMap f)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.remainingCubeSideFirst_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (u : Fin 4 → (unitInterval)) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 5) := by
  refine ⟨0, ?_⟩
  change FifthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨ FifthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [FifthHurewicz.cubeCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 4 → (unitInterval))) (hf : ∀ a, f a ∈ Cube.boundary (Fin 4))
    (z : (unitInterval) × A) : remainingCubeSide f z ∈ Cube.boundary (Fin 5) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change
    FifthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
      FifthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [FifthHurewicz.cubeCoordinates_succ] using hi

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.remainingCubeSide_chain {A : Type} [TopologicalSpace A] (k : ℕ)
    (f : C(A, Fin 4 → (unitInterval))) (b : FirstHurewicz.Chains A k) :
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) k
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (remainingCubeSide f) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A k
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f k
      SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (unitInterval)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.productTwoIntervalSquareChain :
    FirstHurewicz.Chains ((unitInterval) × ((unitInterval) × (Fin 2 → (unitInterval)))) 4 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval)
    ((unitInterval) × (Fin 2 → (unitInterval))) 3 SecondHurewicz.intervalChain
    ThirdHurewicz.productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.productFourIntervalChain :
    FirstHurewicz.Chains ((unitInterval) × ((unitInterval) × ((unitInterval) × (unitInterval))))
      4 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval)
    ((unitInterval) × ((unitInterval) × (unitInterval))) 3 SecondHurewicz.intervalChain
    FifthHurewicz.productThreeIntervalChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.remainingCubeChain_boundary :
    ((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
        FifthHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (remainingCubeSideFirst 1) 4
            FourthHurewicz.fundamentalCubeChain -
          FirstHurewicz.inducedChain (remainingCubeSideFirst 0) 4
            FourthHurewicz.fundamentalCubeChain -
        (FirstHurewicz.inducedChain (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst 1)) 4
              FourthHurewicz.productCubeChain -
            FirstHurewicz.inducedChain
              (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst 0)) 4
              FourthHurewicz.productCubeChain -
          (FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 1)))
                4 productTwoIntervalSquareChain -
              FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 0)))
                4 productTwoIntervalSquareChain -
            (FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 1))))
                  4 productFourIntervalChain -
                FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 0))))
                  4 productFourIntervalChain -
              (FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 1))))
                  4 productFourIntervalChain -
                FirstHurewicz.inducedChain
                  (remainingCubeSide
                    (FifthHurewicz.remainingCubeSide
                      (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 0))))
                  4 productFourIntervalChain)))) := by
  have hpoint (t : (unitInterval)) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 4 → (unitInterval)) 4
        (FirstHurewicz.pointChain t) FourthHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 4
        FourthHurewicz.fundamentalCubeChain := by
    rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : (unitInterval)) :
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 4
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 4
          FourthHurewicz.fundamentalCubeChain) =
      FirstHurewicz.inducedChain (remainingCubeSideFirst t) 4
        FourthHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, FirstHurewicz.inducedChain_comp]
    rfl
  rw [FifthHurewicz.fundamentalCubeChain, ← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 4
        (((FirstHurewicz.singularComplex ((unitInterval) × (Fin 4 → (unitInterval)))).d 5 4).hom
          (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 4
            SecondHurewicz.intervalChain FourthHurewicz.fundamentalCubeChain)) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 3]
  change
    FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 4
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 4 → (unitInterval)) 4
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain)
            FourthHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 3
            SecondHurewicz.intervalChain
            (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
              FourthHurewicz.fundamentalCubeChain)) =
      _
  rw [SecondHurewicz.intervalChain_boundary, FifthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.evaluated_edge_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 5 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 5)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) k
          a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f k a
      b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.evaluated_triangle_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 5 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 5)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 5 → (unitInterval)) k a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      k a b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 2)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.evaluated_edge_cubeBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 4
          a
          (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
            FifthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 FourthHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 FourthHurewicz.productCubeChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hT (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productTwoIntervalSquareChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSideFirst_boundary t ht)))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideLeft_boundary t ht))))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideRight_boundary t ht))))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hT 1 (Or.inr rfl), hT 0 (Or.inl rfl), hL 1 (Or.inr rfl),
    hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.evaluated_triangle_cubeBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 5 → (unitInterval)) 4 a
          (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
            FifthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 FourthHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 FourthHurewicz.productCubeChain
      (remainingCubeSide (FifthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FifthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hT (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productTwoIntervalSquareChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t)))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSideFirst_boundary t ht)))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideLeft_boundary t ht))))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 4 productFourIntervalChain
      (remainingCubeSide
        (FifthHurewicz.remainingCubeSide
          (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t))))
      (remainingCubeSide_boundary _
        (FifthHurewicz.remainingCubeSide_boundary _
          (FourthHurewicz.remainingCubeSide_boundary _
            (ThirdHurewicz.squareSideRight_boundary t ht))))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hT 1 (Or.inr rfl), hT 0 (Or.inl rfl), hL 1 (Or.inr rfl),
    hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 6 :=
  (FirstHurewicz.inducedChain (evaluation x) 6).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 5)
      FifthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SixthHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 5
          a FifthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 7 :=
  (FirstHurewicz.inducedChain (evaluation x) 7).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 5 → (unitInterval))
        5)
      FifthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SixthHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 7
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 5 → (unitInterval)) 5 a FifthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.boundarySix_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 4]
  change
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 5 → (unitInterval)) 5 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            FifthHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 4
            a
            (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
              FifthHurewicz.fundamentalCubeChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_cubeBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.boundarySeven_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 7 6).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 4]
  change
    FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 5 → (unitInterval)) 5
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) FifthHurewicz.fundamentalCubeChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 5 → (unitInterval)) 4 a
            (((FirstHurewicz.singularComplex (Fin 5 → (unitInterval))).d 5 4).hom
              FifthHurewicz.fundamentalCubeChain)) =
      _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

def SixthHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 6
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundarySix_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
theorem SixthHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

def SixthHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 6 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
    (pathCubeCycle x p)

theorem SixthHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 7 6).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundarySeven_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem SixthHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 6 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem SixthHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
theorem SixthHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        6 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundarySeven_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

theorem SixthHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 7 6).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundarySeven_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem SixthHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 6 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 5 → (unitInterval))) 6 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 5 → (unitInterval)) 5
    SecondHurewicz.intervalChain FifthHurewicz.fundamentalCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 6 → (unitInterval)) 6 :=
  FirstHurewicz.inducedChain cubeCoordinates 6 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 6) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 6 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 6) p).toContinuousMap (ContinuousMap.id (Fin 5 → (unitInterval))) 5
      SecondHurewicz.intervalChain FifthHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 6).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 6) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 5 → (unitInterval))))
            6))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    FirstHurewicz.Chains X 6 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 6) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 6 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 6 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 6).comp (FirstHurewicz.inducedChain cubeCoordinates 6))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 6) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SixthHurewicz.cubeCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : (cubeCycle p).1 = cubeChain p :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : SingularMayerVietoris.SingularHomology X 6 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 6) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 6) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 6) (GenLoop.const : GenLoop (Fin 6) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SixthHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 6) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 6) X x) :
    GenLoop.toLoop (0 : Fin 6) (GenLoop.transAt (0 : Fin 6) p q) =
      (GenLoop.toLoop (0 : Fin 6) p).trans (GenLoop.toLoop (0 : Fin 6) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 6))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 6)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 6) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 6) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

theorem SixthHurewicz.CubeSubdivision.cubeCoordinates_boundary_right (s : (unitInterval))
    {u : Fin 5 → (unitInterval)} (hu : u ∈ Cube.boundary (Fin 5)) :
    SixthHurewicz.cubeCoordinates (s, u) ∈ Cube.boundary (Fin 6) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [SixthHurewicz.cubeCoordinates_succ] using hi⟩

def SixthHurewicz.CubeSubdivision.curryLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    GenLoop (Fin 5) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((SixthHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry,
    by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

theorem SixthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 6) X x) :
    (FourthHurewicz.CubeSubdivision.evalLeft X).comp
        ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      SixthHurewicz.cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.CubeSubdivision.evalLeft_crossProductEdge_curryLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) (n : ℕ)
    (b : FirstHurewicz.Chains (Fin 5 → (unitInterval)) n) :
    FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain (curryLoop p).val n b)) =
      FirstHurewicz.inducedChain (SixthHurewicz.cubeMap p) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 5 → (unitInterval)) n
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval))
      (curryLoop p).val n SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)).comp
          (FirstHurewicz.inducedChain
            ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) (n + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evalLeft_comp_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.CubeSubdivision.cubeChain_eq_curriedCrossProduct {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 6
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 5
          SecondHurewicz.intervalChain (FifthHurewicz.cubeChain (curryLoop p))) := by
  rw [FifthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    SixthHurewicz.cubeChain_eq_induced, SixthHurewicz.fundamentalCubeChain]
  change
    (FirstHurewicz.inducedChain p.val 6)
        ((FirstHurewicz.inducedChain SixthHurewicz.cubeCoordinates 6)
          SixthHurewicz.productCubeChain) =
      (FirstHurewicz.inducedChain (p.val.comp SixthHurewicz.cubeCoordinates) 6)
        SixthHurewicz.productCubeChain
  rw [FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SixthHurewicz.CubeSubdivision.intervalFiveSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) : FirstHurewicz.Chains X 6 :=
  FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 6
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 5
      SecondHurewicz.intervalChain
      (FirstHurewicz.simplexChain C((unitInterval), X) 5
        ((curryLoop p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.CubeSubdivision.intervalFiveSimplexChain_eq_original {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) :
    intervalFiveSimplexChain p e =
      FirstHurewicz.inducedChain (SixthHurewicz.cubeMap p) 6
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 5 → (unitInterval)) 5
          SecondHurewicz.intervalChain
          (FirstHurewicz.simplexChain (Fin 5 → (unitInterval)) 5
            (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [intervalFiveSimplexChain, ← FirstHurewicz.inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.CubeSubdivision.cubeChain_eq_sum_prisms {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • intervalFiveSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct, FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalFiveSimplexChain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.CubeSubdivision.prismCubeMap_five (e : Equiv.Perm (Fin 5)) :
    SixthHurewicz.cubeCoordinates.comp
        ((FirstHurewicz.pathSimplex Path.id).prodMap
          (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      FourthHurewicz.CubeSubdivision.prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact SixthHurewicz.cubeCoordinates_zero _
  · change
      SixthHurewicz.cubeCoordinates
          (FirstHurewicz.pathSimplex Path.id z.1,
            HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
          j.succ =
        _
    rw [SixthHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SixthHurewicz.CubeSubdivision.intervalFiveSimplexChain_eq_prismCubeRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) (e : Equiv.Perm (Fin 5)) :
    intervalFiveSimplexChain p e =
      FourthHurewicz.CubeSubdivision.prismCubeRealization p.val e 6
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 5
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 6 => j))) := by
  rw [intervalFiveSimplexChain_eq_original, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct]
  change
    ((FirstHurewicz.inducedChain (SixthHurewicz.cubeMap p) 6).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))
            6))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  change
    FirstHurewicz.inducedChain
        (p.val.comp
          (SixthHurewicz.cubeCoordinates.comp
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))))
        6 _ =
      _
  rw [prismCubeMap_five]

theorem SixthHurewicz.CubeSubdivision.cubeChain_eq_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      FourthHurewicz.CubeSubdivision.orientedPrismRealization p.val 6
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 5
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 6 => j))) := by
  rw [cubeChain_eq_sum_prisms, FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum]
  simp only [intervalFiveSimplexChain_eq_prismCubeRealization]

theorem SixthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 6) X x) :
    SixthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 6),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 6
            (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard (n := 3) p,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism]

theorem SixthHurewicz.sixSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    sixSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 6),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          basedSixSimplexClass
            (normalizedSixSimplex x
              (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, sixSimplexClassOperator_simplex]

theorem SixthHurewicz.sixSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    sixSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 6 X x) := by
  rw [sixSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 6 X x) := by
      simpa only [normalizedCube_simplex, basedSixSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
            (normalizedCube_internalBased x p)).symm
    _ = _ :=
      congrArg Additive.ofMul
        (Quotient.sound
          (show GenLoop.Homotopic (normalizedCube x p) p from
            ⟨(normalizationCubeHomotopy x p).symm⟩))

def SixthHurewicz.basedSixSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : FirstHurewicz.Chains X 6 :=
  HigherHurewicz.correctedSimplexChain 6 x τ.val

def SixthHurewicz.basedSixSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  HigherHurewicz.correctedSimplexCycle 5 x τ.val (basedSixSimplex_face τ)

theorem SixthHurewicz.basedSixSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    (∑ e : Equiv.Perm (Fin 6),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 6
            ((basedSixSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedSixSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 4) τ

def SixthHurewicz.normalizedSixSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    FirstHurewicz.Chains X 6 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6 :=
  HigherHurewicz.normalizedCycleAssignment 5 x (normalizedSixSimplex x)

@[simp]
theorem SixthHurewicz.normalizedSixSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) :
    normalizedSixSimplexCycleOperator x (FirstHurewicz.simplexChain X 6 smp) =
      basedSixSimplexCycle (normalizedSixSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 5 x (normalizedSixSimplex x) smp

theorem SixthHurewicz.normalizedSixSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (normalizedSixSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 c := by
  apply
    HigherHurewicz.normalizedCycleAssignment_class 5 x (normalizedSixSimplex x)
      (normalizationFiveSimplexHomotopy x) (normalizationSixSimplexHomotopy x)
      (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationSixSimplexHomotopy_zero x smp s

def SixthHurewicz.homotopyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (x : X) : π_ 6 X x →* π_ 6 Y (f x)
    where
  toFun :=
    Quotient.map (SecondHurewicz.mapGenLoop f x)
      (fun _ _ h => SecondHurewicz.mapGenLoop_homotopic f x h)
  map_one' := by
    change (⟦SecondHurewicz.mapGenLoop f x GenLoop.const⟧ : π_ 6 Y (f x)) = ⟦GenLoop.const⟧
    rw [SecondHurewicz.mapGenLoop_const]
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    exact
      (congrArg
            (Quotient.map (SecondHurewicz.mapGenLoop f x)
              (fun _ _ h => SecondHurewicz.mapGenLoop_homotopic f x h))
            (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := p) (q := q))).trans
        ((congrArg (fun r : GenLoop (Fin 6) Y (f x) => (⟦r⟧ : π_ 6 Y (f x)))
              (SecondHurewicz.mapGenLoop_transAt f x (0 : Fin 6) q p)).trans
          (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := SecondHurewicz.mapGenLoop f x p) (q :=
              SecondHurewicz.mapGenLoop f x q)).symm)

def SixthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 6 X x → SingularMayerVietoris.SingularHomology X 6 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

def SixthHurewicz.hurewiczPi6 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 6 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 6)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 6 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 6)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 6) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

def SixthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 6 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6
    where
  toFun := (hurewiczPi6 x).toAdditiveLeft
  map_add' := (hurewiczPi6 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi6 x).toAdditiveLeft ℤ ℤ n a

theorem SixthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 6) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (cubeCycle p) :=
  rfl

theorem SixthHurewicz.cubeChain_basedSixSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : cubeChain (basedSixSimplexLoop τ) = basedSixSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedSixSimplex_simplexChain_sum]

theorem SixthHurewicz.cubeCycle_basedSixSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) : cubeCycle (basedSixSimplexLoop τ) = basedSixSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedSixSimplexLoop τ

theorem SixthHurewicz.hurewicz_basedSixSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    hurewiczMap x (basedSixSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (basedSixSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (cubeCycle (basedSixSimplexLoop τ)) =
      _
  rw [cubeCycle_basedSixSimplexLoop]

theorem SixthHurewicz.hurewiczMap_comp_sixSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    (hurewiczMap x).comp (sixSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6).comp
        (normalizedSixSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 6
  intro smp
  simp only [LinearMap.comp_apply, sixSimplexClassOperator_simplex,
    normalizedSixSimplexCycleOperator_simplex]
  exact hurewicz_basedSixSimplexClass (normalizedSixSimplex x smp)

theorem SixthHurewicz.hurewiczMap_sixSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6) :
    hurewiczMap x (sixSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_sixSimplexClassOperator x) c.val
  change
    hurewiczMap x (sixSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
        (normalizedSixSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedSixSimplexCycleOperator_class x c)

def SixthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    SingularMayerVietoris.SingularHomology X 6 →ₗ[ℤ] Additive (π_ 6 X x) :=
  HigherHurewicz.singularHomologyDesc 6 (sixSimplexClassOperator x)
    (sixSimplexClassOperator_boundary x)

@[simp]
theorem SixthHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 6) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6 c) =
      sixSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 6 _ _ c

theorem SixthHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 6 (sixSimplexClassOperator x)
    (sixSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_sixSimplexClassOperator_cycle x)

@[simp]
theorem SixthHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
    (c : SingularMayerVietoris.SingularHomology X 6) : hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp]
theorem SixthHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (p : GenLoop (Fin 6) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 6 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact sixSimplexClassOperator_cubeChain x p

@[simp]
theorem SixthHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (a : Additive (π_ 6 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem SixthHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

def SixthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    Additive (π_ 6 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 6 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x) (hurewiczMap_comp_hurewiczInverse x)
    (hurewiczInverse_comp_hurewiczMap x)

def SixthHurewicz.hurewiczPi6Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] :
    π_ 6 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 6)
    where
  __ := hurewiczPi6 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

theorem SixthHurewicz.cubeChain_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    FirstHurewicz.inducedChain f 6 (cubeChain p) = cubeChain (SecondHurewicz.mapGenLoop f x p) := by
  rw [cubeChain_eq_induced, cubeChain_eq_induced, SecondHurewicz.mapGenLoop_val,
    FirstHurewicz.inducedChain_comp, LinearMap.comp_apply]

theorem SixthHurewicz.cubeCycle_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap f) 6
        (cubeCycle p) =
      cubeCycle (SecondHurewicz.mapGenLoop f x p) := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, cubeCycle_val, cubeCycle_val]
  exact cubeChain_natural f x p

theorem SixthHurewicz.cubeHomologyClass_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.singularHomologyMap f 6 (cubeHomologyClass p) =
      cubeHomologyClass (SecondHurewicz.mapGenLoop f x p) := by
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap f) 6).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 6
          (cubeCycle p)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, cubeCycle_natural]
  rfl

theorem SixthHurewicz.hurewiczFunction_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (a : π_ 6 X x) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczFunction x a) =
      hurewiczFunction (f x) (homotopyMap f x a) := by
  refine Quotient.inductionOn a fun p => ?_
  exact cubeHomologyClass_natural f x p

theorem SixthHurewicz.hurewiczMap_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : Additive (π_ 6 X x)) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczMap x a) =
      hurewiczMap (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczFunction_natural f x a.toMul

theorem SixthHurewicz.hurewiczLinearEquiv_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]
    [Subsingleton (π_ 4 Y (f x))] [Subsingleton (π_ 5 Y (f x))] (a : Additive (π_ 6 X x)) :
    SingularMayerVietoris.singularHomologyMap f 6 (hurewiczLinearEquiv x a) =
      hurewiczLinearEquiv (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczMap_natural f x a

def SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv (x : SpecialPeriods.Threefold.Space) :
    Additive (π_ 6 SpecialPeriods.Threefold.Space x) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 := by
  letI := SpecialPeriods.Threefold.space_simplyConnected
  letI := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  letI := SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  letI := SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton x
  letI := SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton x
  exact SixthHurewicz.hurewiczLinearEquiv x

@[simp]
theorem SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv_mk (x : SpecialPeriods.Threefold.Space)
    (p : GenLoop (Fin 6) SpecialPeriods.Threefold.Space x) :
    hurewiczEquiv x (Additive.ofMul (⟦p⟧ : π_ 6 SpecialPeriods.Threefold.Space x)) =
      SixthHurewicz.cubeHomologyClass p :=
  rfl

def SpecialPeriods.Threefold.HomotopySix.piSixEquiv (x : SpecialPeriods.Threefold.Space) :
    Additive (π_ 6 SpecialPeriods.Threefold.Space x) ≃ₗ[ℤ] ℤ :=
  (hurewiczEquiv x).trans ThreefoldHomology.TopDegree.homologySixEquiv

def SpecialPeriods.Threefold.HomotopySix.generator (x : SpecialPeriods.Threefold.Space) :
    Additive (π_ 6 SpecialPeriods.Threefold.Space x) :=
  (hurewiczEquiv x).symm ThreefoldHomology.TopDegree.topClass

@[simp]
theorem SpecialPeriods.Threefold.HomotopySix.hurewiczEquiv_generator
    (x : SpecialPeriods.Threefold.Space) :
    hurewiczEquiv x (generator x) = ThreefoldHomology.TopDegree.topClass :=
  (hurewiczEquiv x).apply_symm_apply _

theorem SpecialPeriods.Threefold.HomotopySix.exists_cube_topClass
    (x : SpecialPeriods.Threefold.Space) :
    ∃ p : GenLoop (Fin 6) SpecialPeriods.Threefold.Space x,
      SixthHurewicz.cubeHomologyClass p = ThreefoldHomology.TopDegree.topClass := by
  obtain ⟨p, hp⟩ := Quotient.exists_rep (Additive.toMul (generator x))
  have hclass : Additive.ofMul (⟦p⟧ : π_ 6 SpecialPeriods.Threefold.Space x) = generator x :=
    congrArg Additive.ofMul hp
  exact
    ⟨p,
      (hurewiczEquiv_mk x p).symm.trans
        ((congrArg (hurewiczEquiv x) hclass).trans (hurewiczEquiv_generator x))⟩

def SpecialPeriods.Threefold.HomotopySix.generatingCube (x : SpecialPeriods.Threefold.Space) :
    GenLoop (Fin 6) SpecialPeriods.Threefold.Space x :=
  Classical.choose (exists_cube_topClass x)

@[simp]
theorem SpecialPeriods.Threefold.HomotopySix.generatingCube_homologyClass
    (x : SpecialPeriods.Threefold.Space) :
    SixthHurewicz.cubeHomologyClass (generatingCube x) = ThreefoldHomology.TopDegree.topClass :=
  Classical.choose_spec (exists_cube_topClass x)

abbrev SixSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

def SixSphereHomology.homologyZeroEquiv :
    SingularMayerVietoris.SingularHomology SixSphere 0 ≃ₗ[ℤ] ℤ :=
  SphereHomology.unitSphereHomologyZeroEquiv 5

def SixSphereHomology.homologySixEquiv :
    SingularMayerVietoris.SingularHomology SixSphere 6 ≃ₗ[ℤ] ℤ :=
  SphereHomology.unitSphereHomologyTopEquiv 5

theorem SixSphereHomology.homology_subsingleton (k : ℕ) (hk : k ≠ 0) (hk6 : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology SixSphere k) :=
  SphereHomology.unitSphere_homology_subsingleton 5 k hk hk6

theorem SpecialPeriods.Threefold.HomologySphere.homology_subsingleton (n : ℕ) (hn0 : n ≠ 0)
    (hn6 : n ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n) := by
  by_cases hn : 6 < n
  · exact ThreefoldHomology.Finiteness.homology_subsingleton_of_lt hn
  have hn' : n ≤ 6 := Nat.le_of_not_gt hn
  interval_cases n
  · exact (hn0 rfl).elim
  · exact SpecialPeriods.Threefold.LowDegrees.singularH1_subsingleton
  · exact ThreefoldHomology.SecondDegree.homologyTwo_subsingleton
  · exact ThreefoldHomology.ThirdDegree.homologyThree_subsingleton
  · exact ThreefoldHomology.FourthDegree.homologyFour_subsingleton
  · exact ThreefoldHomology.FifthDegree.homologyFive_subsingleton
  · exact (hn6 rfl).elim

def SpecialPeriods.Threefold.HomologySphere.homologyZeroEquivSixSphere :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 0 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SixSphere 0 :=
  SpecialPeriods.Threefold.LowDegrees.singularH0Equiv.trans
    SixSphereHomology.homologyZeroEquiv.symm

def SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SixSphere 6 :=
  ThreefoldHomology.TopDegree.homologySixEquiv.trans SixSphereHomology.homologySixEquiv.symm

theorem SpecialPeriods.Threefold.SphereHomologyMap.six_surjective_of_topClass_preimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha :
      SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f 6) := by
  intro b
  refine ⟨ThreefoldHomology.TopDegree.homologySixEquiv b • a, ?_⟩
  rw [map_zsmul, ha]
  exact (ThreefoldHomology.TopDegree.eq_smul_topClass b).symm

theorem SpecialPeriods.Threefold.SphereHomologyMap.six_bijective_of_topClass_preimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha :
      SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap f 6) := by
  let :
    IsNoetherian ℤ (SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6) :=
    isNoetherian_of_injective ThreefoldHomology.TopDegree.homologySixEquiv.toLinearMap
      ThreefoldHomology.TopDegree.homologySixEquiv.injective
  have hsurj := six_surjective_of_topClass_preimage f a ha
  refine ⟨?_, hsurj⟩
  exact
    IsNoetherian.injective_of_surjective_of_injective
      SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere.symm.toLinearMap
      (SingularMayerVietoris.singularHomologyMap f 6)
      SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere.symm.injective hsurj

theorem SpecialPeriods.Threefold.SphereHomologyMap.homologyMap_bijective_of_topClass_preimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha : SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass)
    (n : ℕ) : Function.Bijective (SingularMayerVietoris.singularHomologyMap f n) := by
  by_cases hn0 : n = 0
  · subst n
    let := SpecialPeriods.Threefold.space_pathConnected
    exact SphereHomology.singularHomologyMap_zero_bijective f
  by_cases hn6 : n = 6
  · subst n
    exact six_bijective_of_topClass_preimage f a ha
  let := SpecialPeriods.Threefold.HomologySphere.homology_subsingleton n hn0 hn6
  let := SixSphereHomology.homology_subsingleton n hn0 hn6
  exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

def SpecialPeriods.Threefold.SphereHomologyMap.homologyEquivOfTopClassPreimage
    (f : C(SixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology SixSphere 6)
    (ha : SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology SixSphere n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n :=
  LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap f n)
    (homologyMap_bijective_of_topClass_preimage f a ha n)

abbrev SixSphereCube.CubeInterior :=
  CubeInteriorN 6

theorem SixSphereCube.isClosed_cubeBoundary : IsClosed (Cube.boundary (Fin 6)) :=
  isClosed_cubeBoundaryN 6

abbrev SixSphereCube.cubeInteriorHomeomorph : CubeInterior ≃ₜ EuclideanSpace ℝ (Fin 6) :=
  cubeInteriorEuclideanHomeomorph 6

@[simp]
theorem SixSphereCube.zero_mem_cubeBoundary :
    (0 : Fin 6 → (unitInterval)) ∈ Cube.boundary (Fin 6) :=
  ⟨0, Or.inl rfl⟩

theorem SixSphereCube.cubeBoundary_nonempty : (Cube.boundary (Fin 6)).Nonempty :=
  ⟨0, zero_mem_cubeBoundary⟩

def SixSphereCube.cubeInteriorSphereHomeomorph : OnePoint CubeInterior ≃ₜ StandardSphere :=
  Degree.SphereCube.compactification 6

@[simp]
theorem SixSphereCube.cubeInteriorSphereHomeomorph_infty :
    cubeInteriorSphereHomeomorph (OnePoint.infty) = sphereBasePoint :=
  rfl

def SixSphereCube.cubeSphereMap : C(Fin 6 → (unitInterval), StandardSphere) :=
  Degree.SphereCube.quotient 6

@[simp]
theorem SixSphereCube.cubeSphereMap_apply (u : Fin 6 → (unitInterval)) :
    cubeSphereMap u = cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) :=
  rfl

theorem SixSphereCube.cubeSphereMap_boundary (u : Fin 6 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 6)) : cubeSphereMap u = sphereBasePoint :=
  Degree.SphereCube.quotient_boundary 6 u hu

theorem SixSphereCube.cubeSphereMap_eq_iff (u v : Fin 6 → (unitInterval)) :
    cubeSphereMap u = cubeSphereMap v ↔
      u = v ∨ u ∈ Cube.boundary (Fin 6) ∧ v ∈ Cube.boundary (Fin 6) :=
  Degree.SphereCube.quotient_eq_iff 6 u v

theorem SixSphereCube.cubeSphereMap_surjective : Function.Surjective cubeSphereMap :=
  Degree.SphereCube.quotient_surjective (by decide)

def SixSphereCube.cubeSphereLoop : GenLoop (Fin 6) StandardSphere sphereBasePoint :=
  Degree.SphereCube.quotientLoop 6

@[simp]
theorem SixSphereCube.cubeSphereLoop_val : cubeSphereLoop.val = cubeSphereMap :=
  rfl

def SixSphereCube.factorMap {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    C(StandardSphere, X) :=
  Degree.SphereCube.factorMap (by decide) p

@[simp]
theorem SixSphereCube.factorMap_cubeSphereMap {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (u : Fin 6 → (unitInterval)) :
    factorMap p (cubeSphereMap u) = p u :=
  Degree.SphereCube.factorMap_quotient (by decide) p u

@[simp]
theorem SixSphereCube.factorMap_comp_cubeSphereMap {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : (factorMap p).comp cubeSphereMap = p.val :=
  Degree.SphereCube.factorMap_comp_quotient (by decide) p

theorem SixSphereCube.factorMap_unique {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (f : C(StandardSphere, X)) (hf : f.comp cubeSphereMap = p.val) :
    f = factorMap p :=
  Degree.SphereCube.factorMap_unique (by decide) p f hf


theorem SixSphereCube.factor_cubeChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    FirstHurewicz.inducedChain (factorMap p) 6 (SixthHurewicz.cubeChain cubeSphereLoop) =
      SixthHurewicz.cubeChain p := by
  calc
    _ =
        FirstHurewicz.inducedChain ((factorMap p).comp cubeSphereMap) 6
          SixthHurewicz.fundamentalCubeChain := by
      rw [SixthHurewicz.cubeChain_eq_induced, cubeSphereLoop_val, FirstHurewicz.inducedChain_comp,
        LinearMap.comp_apply]
    _ = _ := by rw [factorMap_comp_cubeSphereMap, SixthHurewicz.cubeChain_eq_induced]

theorem SixSphereCube.factor_cubeCycle {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap (factorMap p))
        6 (SixthHurewicz.cubeCycle cubeSphereLoop) =
      SixthHurewicz.cubeCycle p := by
  apply Subtype.ext
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, SixthHurewicz.cubeCycle_val,
    SixthHurewicz.cubeCycle_val]
  exact factor_cubeChain p

theorem SixSphereCube.factor_cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) :
    SingularMayerVietoris.singularHomologyMap (factorMap p) 6
        (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass p := by
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap (factorMap p)) 6).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex StandardSphere) 6
          (SixthHurewicz.cubeCycle cubeSphereLoop)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, factor_cubeCycle]
  rfl

def SpecialPeriods.Threefold.SphereHomologyEquivalence.sourceCubeClass :
    SingularMayerVietoris.SingularHomology SixSphere 6 :=
  SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop

def SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap
    (x : SpecialPeriods.Threefold.Space) : C(SixSphere, SpecialPeriods.Threefold.Space) :=
  SixSphereCube.factorMap (SpecialPeriods.Threefold.HomotopySix.generatingCube x)

@[simp]
theorem SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap_sourceCubeClass
    (x : SpecialPeriods.Threefold.Space) :
    SingularMayerVietoris.singularHomologyMap (sphereMap x) 6 sourceCubeClass =
      ThreefoldHomology.TopDegree.topClass :=
  (SixSphereCube.factor_cubeHomologyClass
        (SpecialPeriods.Threefold.HomotopySix.generatingCube x)).trans
    (SpecialPeriods.Threefold.HomotopySix.generatingCube_homologyClass x)

theorem SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyMap_bijective
    (x : SpecialPeriods.Threefold.Space) (n : ℕ) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (sphereMap x) n) :=
  SpecialPeriods.Threefold.SphereHomologyMap.homologyMap_bijective_of_topClass_preimage
    (sphereMap x) sourceCubeClass (sphereMap_sourceCubeClass x) n

def SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyEquiv
    (x : SpecialPeriods.Threefold.Space) (n : ℕ) :
    SingularMayerVietoris.SingularHomology SixSphere n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n :=
  SpecialPeriods.Threefold.SphereHomologyMap.homologyEquivOfTopClassPreimage (sphereMap x)
    sourceCubeClass (sphereMap_sourceCubeClass x) n

theorem Degree.sphereMap_piSix_bijective (x : SpecialPeriods.Threefold.Space) :
    Function.Bijective
      (SixthHurewicz.homotopyMap (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
        SixSphereCube.sphereBasePoint) := by
  let f := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  let := Sphere.piTwo_subsingleton SixSphereCube.sphereBasePoint
  let := Sphere.piThree_subsingleton SixSphereCube.sphereBasePoint
  let := Sphere.piFour_subsingleton SixSphereCube.sphereBasePoint
  let := Sphere.piFive_subsingleton SixSphereCube.sphereBasePoint
  let := SpecialPeriods.Threefold.space_simplyConnected
  let := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton (f SixSphereCube.sphereBasePoint)
  let :=
    SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton (f SixSphereCube.sphereBasePoint)
  let :=
    SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton (f SixSphereCube.sphereBasePoint)
  let :=
    SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton (f SixSphereCube.sphereBasePoint)
  let source := SixthHurewicz.hurewiczLinearEquiv SixSphereCube.sphereBasePoint
  let target := SixthHurewicz.hurewiczLinearEquiv (f SixSphereCube.sphereBasePoint)
  let middle := SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyEquiv x 6
  have natural (a : π_ 6 SixSphereCube.StandardSphere SixSphereCube.sphereBasePoint) :
    middle (source (Additive.ofMul a)) =
      target (Additive.ofMul (SixthHurewicz.homotopyMap f SixSphereCube.sphereBasePoint a)) :=
    SixthHurewicz.hurewiczLinearEquiv_natural f SixSphereCube.sphereBasePoint (Additive.ofMul a)
  constructor
  · intro a b hab
    have hm : middle (source (Additive.ofMul a)) = middle (source (Additive.ofMul b)) :=
      (natural a).trans
        ((congrArg (fun c => target (Additive.ofMul c)) hab).trans (natural b).symm)
    exact congrArg Additive.toMul (source.injective (middle.injective hm))
  · intro b
    let a := source.symm (middle.symm (target (Additive.ofMul b)))
    refine ⟨Additive.toMul a, ?_⟩
    have ht :
      target
          (Additive.ofMul
            (SixthHurewicz.homotopyMap f SixSphereCube.sphereBasePoint (Additive.toMul a))) =
        target (Additive.ofMul b) := by
      calc
        _ = middle (source a) := (natural (Additive.toMul a)).symm
        _ = target (Additive.ofMul b) := by
          dsimp [a]
          rw [source.apply_symm_apply, middle.apply_symm_apply]
    exact congrArg Additive.toMul (target.injective ht)

theorem Degree.BasedDiskLifting.exists_based_disk_lift {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (x : SpecialPeriods.Threefold.Space)
    (L : V ≃L[ℝ] (Fin 6 → ℝ))
    (u : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space))
    (hu :
      ∀ z : Degree.DiskCylinder.Disk (E := V),
        ‖(z : V)‖ = 1 →
          u z =
            SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
              SixSphereCube.sphereBasePoint) :
    ∃ v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere),
      (∀ z : Degree.DiskCylinder.Disk (E := V),
          ‖(z : V)‖ = 1 → v z = SixSphereCube.sphereBasePoint) ∧
        ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp v).HomotopicRel u
          {z : Degree.DiskCylinder.Disk (E := V) | ‖(z : V)‖ = 1} := by
  let F := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  let e := Degree.DiskCube.homeomorph L
  let q : GenLoop (Fin 6) SpecialPeriods.Threefold.Space (F SixSphereCube.sphereBasePoint) :=
    ⟨u.comp (e.symm : C(_, _)), fun z hz =>
      hu (e.symm z) ((Degree.DiskCube.symm_boundary_iff L z).mpr hz)⟩
  obtain ⟨a, ha⟩ := (Degree.sphereMap_piSix_bijective x).2 ⟦q⟧
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  have he : SixthHurewicz.homotopyMap F SixSphereCube.sphereBasePoint ⟦p⟧ = ⟦q⟧ :=
    (congrArg (SixthHurewicz.homotopyMap F SixSphereCube.sphereBasePoint) hp).trans ha
  have hh : GenLoop.Homotopic (SecondHurewicz.mapGenLoop F SixSphereCube.sphereBasePoint p) q :=
    Quotient.exact he
  obtain ⟨H⟩ := hh
  let v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere) :=
    p.val.comp (e : C(_, _))
  refine
    ⟨v, ?_,
      ⟨{  toFun := fun z => H (z.1, e z.2)
          continuous_toFun :=
            H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩⟩
  · intro z hz
    exact p.property (e z) ((Degree.DiskCube.boundary_iff L z).mpr hz)
  · intro z
    exact H.apply_zero (e z)
  · intro z
    exact (H.apply_one (e z)).trans (congrArg u (e.symm_apply_apply z))
  · intro t z hz
    exact H.eq_fst t ((Degree.DiskCube.boundary_iff L z).mpr hz)

theorem Degree.Sphere.pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6)
    (x : SixSphereCube.StandardSphere) : Subsingleton (π_ n SixSphereCube.StandardSphere x) := by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact piTwo_subsingleton x
  · exact piThree_subsingleton x
  · exact piFour_subsingleton x
  · exact piFive_subsingleton x

theorem Degree.Sphere.boundary_homotopic_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V ≤ 6)
    (u : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (x : SixSphereCube.StandardSphere) : u.Homotopic (ContinuousMap.const _ x) :=
  boundary_homotopic_const_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

theorem Degree.Sphere.exists_boundary_extension {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V ≤ 6)
    (u : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (x : SixSphereCube.StandardSphere) :
    ∃ v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere),
      (∀ s, v (Degree.DiskCylinder.boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x :=
  exists_boundary_extension_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

theorem Degree.LowCellLifting.relativeDiskLifting_five {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (F : C(SixSphereCube.StandardSphere, Y))
    (hpi : ∀ n, 0 < n → n < 6 → ∀ y : Y, Subsingleton (π_ n Y y)) :
    Degree.FiniteCells.RelativeDiskLifting F 5 := by
  intro V _ _ _ hd a u H h0 h1
  obtain ⟨v, hv, _⟩ :=
    Degree.Sphere.exists_boundary_extension (hd.trans (by decide)) a SixSphereCube.sphereBasePoint
  have h0' : ∀ s, H (0, s) = (F.comp v) (Degree.DiskCylinder.boundaryToDisk s) := by
    intro s
    exact (h0 s).trans (congrArg F (hv s).symm)
  obtain ⟨G, hG0, hG1, hGside⟩ :=
    Degree.CylinderFilling.exists_filling hpi (by omega : Module.finrank ℝ V + 1 ≤ 6) (F.comp v) u
      H h0' h1 (F SixSphereCube.sphereBasePoint)
  exact ⟨v, G, hv, hG0, hG1, hGside⟩

attribute [local instance] SpecialPeriods.Threefold.space_simplyConnected in
theorem Degree.LowCellLifting.threefold_pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6)
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ n SpecialPeriods.Threefold.Space x) :=
  by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  · exact SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  · exact SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton x
  · exact SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton x

attribute [local instance] SpecialPeriods.Threefold.space_simplyConnected in
theorem Degree.LowCellLifting.sphereMap_relativeDiskLifting_five
    (x : SpecialPeriods.Threefold.Space) :
    Degree.FiniteCells.RelativeDiskLifting
      (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) 5 :=
  relativeDiskLifting_five _ (fun _ hn hn6 => threefold_pi_subsingleton hn hn6)

theorem Degree.TopCellLifting.exists_top_disk_lift {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (x : SpecialPeriods.Threefold.Space)
    (L : V ≃L[ℝ] (Fin 6 → ℝ)) (hd : Module.finrank ℝ V ≤ 6)
    (a : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (u : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), SpecialPeriods.Threefold.Space))
    (h0 : ∀ s, H (0, s) = SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x (a s))
    (h1 : ∀ s, H (1, s) = u (Degree.DiskCylinder.boundaryToDisk s)) :
    ∃ (v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere)) (G :
      C((unitInterval) × Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space)),
      (∀ s, v (Degree.DiskCylinder.boundaryToDisk s) = a s) ∧
        (∀ z, G (0, z) = SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x (v z)) ∧
          (∀ z, G (1, z) = u z) ∧ ∀ t s, G (t, Degree.DiskCylinder.boundaryToDisk s) = H (t, s) :=
  by
  let F := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  let c : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere) :=
    ContinuousMap.const _ SixSphereCube.sphereBasePoint
  obtain ⟨Ac⟩ := (Degree.Sphere.boundary_homotopic_const hd a SixSphereCube.sphereBasePoint).symm
  let A : Path c a := Degree.MappingPaths.ofHomotopy Ac
  let FA : Path (F.comp c) (F.comp a) := A.map (ContinuousMap.continuous_postcomp F)
  let HP : Path (F.comp a) (u.comp Degree.DiskCylinder.boundaryToDisk) :=
    { toContinuousMap := H.curry
      source' := ContinuousMap.ext h0
      target' := ContinuousMap.ext h1 }
  let K := HP.symm.trans FA.symm
  obtain ⟨u₀, E, hE, hu₀⟩ := Degree.BoundaryPathTransport.exists_transport u K rfl
  have hu₀' :
    ∀ z : Degree.DiskCylinder.Disk (E := V),
      ‖(z : V)‖ = 1 → u₀ z = F SixSphereCube.sphereBasePoint := by
    intro z hz
    exact ContinuousMap.congr_fun hu₀ ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨p, hp, ⟨B⟩⟩ := Degree.BasedDiskLifting.exists_based_disk_lift x L u₀ hu₀'
  have hp' : p.comp Degree.DiskCylinder.boundaryToDisk = c := by
    apply ContinuousMap.ext
    intro s
    exact hp (Degree.DiskCylinder.boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)
  obtain ⟨v, P, hP, hv⟩ := Degree.BoundaryPathTransport.exists_transport p A hp'
  let FP : Path (F.comp p) (F.comp v) := P.map (ContinuousMap.continuous_postcomp F)
  let BP := Degree.MappingPaths.ofHomotopy B.toHomotopy
  have hFP :
    Degree.MappingPaths.Over
      (fun w : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space) =>
        w.comp Degree.DiskCylinder.boundaryToDisk)
      FP FA := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact congrArg F (ContinuousMap.congr_fun (hP t) s)
  have hBP :
    Degree.MappingPaths.Over
      (fun w : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space) =>
        w.comp Degree.DiskCylinder.boundaryToDisk)
      BP (Path.refl (F.comp c)) := by
    intro t
    apply ContinuousMap.ext
    intro s
    have hs : ‖(Degree.DiskCylinder.boundaryToDisk s : V)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp s.property
    exact (B.eq_fst t hs).trans (congrArg F (hp (Degree.DiskCylinder.boundaryToDisk s) hs))
  let R := FP.symm.trans (BP.trans E.symm)
  let Q := FA.symm.trans ((Path.refl (F.comp c)).trans K.symm)
  have hR :
    Degree.MappingPaths.Over
      (fun w : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space) =>
        w.comp Degree.DiskCylinder.boundaryToDisk)
      R Q :=
    hFP.symm.trans (hBP.trans hE.symm)
  have hQ : Q.Homotopic HP := Degree.MappingPaths.normalization_cancellation FA HP
  obtain ⟨G, hG0, hG1, hGside⟩ := Degree.SideRectification.exists_rectification R Q HP hR hQ
  exact ⟨v, G, fun s => ContinuousMap.congr_fun hv s, hG0, hG1, hGside⟩

theorem Degree.TopCellLifting.sphereMap_relativeDiskLifting_six
    (x : SpecialPeriods.Threefold.Space) :
    Degree.FiniteCells.RelativeDiskLifting
      (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) 6 := by
  intro V _ _ _ hd a u H h0 h1
  by_cases hlow : Module.finrank ℝ V ≤ 5
  · exact Degree.LowCellLifting.sphereMap_relativeDiskLifting_five x V hlow a u H h0 h1
  · have heq : Module.finrank ℝ V = 6 := by omega
    obtain ⟨L⟩ :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
        (show Module.finrank ℝ V = Module.finrank ℝ (Fin 6 → ℝ) by simpa using heq)
    exact exists_top_disk_lift x L hd a u H h0 h1

theorem Degree.MorseCells.built_upper_sublevels {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (c : (p : Smale.ManifoldMorse.criticalPoints E f) → Cell (E := E) f p.val)
    (hdis : ∀ p q, p ≠ q → Disjoint (c p).band (c q).band)
    (p : Smale.ManifoldMorse.criticalPoints E f) :
    Degree.FiniteCells.Built (Module.finrank ℝ E) { x : M // f x ≤ f p + (c p).radius ^ 2 } := by
  classical
  let K := Smale.ManifoldMorse.criticalPoints E f
  let : Fintype K := (Smale.ManifoldMorse.finite_criticalPoints hf hm).fintype
  let : LinearOrder K :=
    LinearOrder.lift' (fun p : K => f p.val)
      (fun p q h => Subtype.ext (hinj p.property q.property h))
  have hstep (p : K) :
    Degree.FiniteCells.Built (Module.finrank ℝ E) { x : M // f x ≤ f p + (c p).radius ^ 2 } := by
    induction p using WellFoundedLT.induction with
    | ind p
      ih =>
      have hlower :
        Degree.FiniteCells.Built (Module.finrank ℝ E) { x : M // f x ≤ f p - (c p).radius ^ 2 } :=
        by
        by_cases hex : ∃ q : K, q < p
        · let s : Finset K := Finset.univ.filter (fun q => q < p)
          have hs : s.Nonempty := by
            obtain ⟨q, hq⟩ := hex
            exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
          let q := s.max' hs
          have hqp : q < p := (Finset.mem_filter.mp (s.max'_mem hs)).2
          have hgap : f q + (c q).radius ^ 2 < f p - (c p).radius ^ 2 :=
            upper_lt_lower_of_disjoint (c q) (c p) (hdis q p (ne_of_lt hqp)) hqp
          obtain ⟨e, _⟩ :=
            Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv hf hgap.le
              (by
                intro x hx hcrit
                let r : K := ⟨x, hcrit⟩
                have hrp : r < p := by
                  change f x < f p
                  nlinarith [sq_pos_of_pos (c p).radius_pos, hx.2]
                have hrq : r ≤ q := s.le_max' r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrp⟩)
                change f x ≤ f q at hrq
                nlinarith [sq_pos_of_pos (c q).radius_pos, hx.1])
          exact Degree.FiniteCells.Built.equiv e (ih q hqp)
        · let : IsEmpty { x : M // f x ≤ f p - (c p).radius ^ 2 } :=
            isEmpty_sublevel_of_no_critical hf
              (by
                intro x hx hle
                apply hex
                refine ⟨⟨x, hx⟩, ?_⟩
                change f x < f p
                nlinarith [sq_pos_of_pos (c p).radius_pos])
          exact Degree.FiniteCells.Built.empty _
      apply Degree.FiniteCells.Built.equiv (c p).comparison
      exact
        Degree.FiniteCells.Built.attach _
          (coreCellMap (c p).chart (c p).radius (c p).radius_pos (c p).block)
          (fun u hu =>
            (coreCellMap_lower_iff (c p).chart (c p).radius (c p).radius_pos (c p).block u).mpr
              hu)
          (c p).dimension_le hlower
  exact hstep p

theorem Degree.MorseCells.built_of_compact_smooth_manifold {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    Degree.FiniteCells.Built (Module.finrank ℝ E) M := by
  classical
    cases isEmpty_or_nonempty M with
  | inl h => exact Degree.FiniteCells.Built.empty _
  | inr
    h =>
    obtain ⟨f, hf, hm, _, hinj⟩ :=
      Smale.ManifoldMorse.exists_morse_function_with_distinct_critical_values E M
    obtain ⟨c, hdis⟩ := exists_disjoint_cells hf hm hinj
    obtain ⟨p, _, hmax⟩ :=
      isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hf.continuous.continuousOn
    have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
      Smale.ManifoldMorse.mem_criticalPoints_of_localMax hf
        (Filter.Eventually.of_forall (fun y => hmax (Set.mem_univ y)))
    let q : Smale.ManifoldMorse.criticalPoints E f := ⟨p, hp⟩
    have hb := built_upper_sublevels hf hm hinj c hdis q
    have hfull : {x : M | f x ≤ f q + (c q).radius ^ 2} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      change f x ≤ f p + (c q).radius ^ 2
      exact (hmax (Set.mem_univ x)).trans (le_add_of_nonneg_right (sq_nonneg (c q).radius))
    exact
      Degree.FiniteCells.Built.equiv
        ((Homeomorph.setCongr hfull).trans (Homeomorph.Set.univ M)).toHomotopyEquiv hb

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_isSmoothRealManifold in
theorem Degree.Threefold.finite_homotopy_cells :
    Degree.FiniteCells.Built 6 SpecialPeriods.Threefold.Space := by
  simpa only [SpecialPeriods.Threefold.real_dimension] using
    (Degree.MorseCells.built_of_compact_smooth_manifold (E := ℂ × ComplexPlane₂) (M :=
      SpecialPeriods.Threefold.Space))

theorem Degree.exists_right_homotopy_inverse (x : SpecialPeriods.Threefold.Space) :
    ∃ g : C(SpecialPeriods.Threefold.Space, SixSphereCube.StandardSphere),
      ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
        (ContinuousMap.id SpecialPeriods.Threefold.Space) :=
  FiniteCells.mapsLift_of_built (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    (TopCellLifting.sphereMap_relativeDiskLifting_six x) Threefold.finite_homotopy_cells
    (ContinuousMap.id SpecialPeriods.Threefold.Space)

def Degree.cylinderQuotient :
    C((unitInterval) × (Fin 6 → (unitInterval)), (unitInterval) × SixSphereCube.StandardSphere) :=
  (ContinuousMap.id (unitInterval)).prodMap SixSphereCube.cubeSphereMap

theorem Degree.cylinderQuotient_surjective : Function.Surjective cylinderQuotient := by
  rintro ⟨t, z⟩
  obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
  exact ⟨(t, u), rfl⟩

theorem Degree.cylinderQuotient_isQuotientMap : Topology.IsQuotientMap cylinderQuotient :=
  .of_surjective_continuous cylinderQuotient_surjective cylinderQuotient.continuous

theorem Degree.cubeHomotopy_constant_on_cylinderFibres {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6)))
    (a b : (unitInterval) × (Fin 6 → (unitInterval)))
    (h : cylinderQuotient a = cylinderQuotient b) : H a = H b := by
  rcases a with ⟨t, u⟩
  rcases b with ⟨s, v⟩
  have ht : t = s := congrArg Prod.fst h
  subst s
  have huv : SixSphereCube.cubeSphereMap u = SixSphereCube.cubeSphereMap v := congrArg Prod.snd h
  rcases (SixSphereCube.cubeSphereMap_eq_iff u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · exact
      ((H.eq_fst t hu).trans (p.property u hu)).trans
        ((H.eq_fst t hv).trans (p.property v hv)).symm

def Degree.cubeHomotopyLift {X : Type*} [TopologicalSpace X] {x : X} {p q : GenLoop (Fin 6) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6))) :
    C((unitInterval) × SixSphereCube.StandardSphere, X) :=
  cylinderQuotient_isQuotientMap.lift H.toHomotopy.toContinuousMap
    (cubeHomotopy_constant_on_cylinderFibres H)

@[simp]
theorem Degree.cubeHomotopyLift_apply {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6)))
    (t : (unitInterval)) (u : Fin 6 → (unitInterval)) :
    cubeHomotopyLift H (t, SixSphereCube.cubeSphereMap u) = H (t, u) :=
  ContinuousMap.congr_fun
    (cylinderQuotient_isQuotientMap.lift_comp H.toHomotopy.toContinuousMap
      (cubeHomotopy_constant_on_cylinderFibres H))
    (t, u)

def Degree.factorHomotopy {X : Type*} [TopologicalSpace X] {x : X} {p q : GenLoop (Fin 6) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6))) :
    (SixSphereCube.factorMap p).HomotopyRel (SixSphereCube.factorMap q)
      { SixSphereCube.sphereBasePoint }
    where
  toContinuousMap := cubeHomotopyLift H
  map_zero_left
    z := by
    obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
    change
      cubeHomotopyLift H (0, SixSphereCube.cubeSphereMap u) =
        SixSphereCube.factorMap p (SixSphereCube.cubeSphereMap u)
    rw [cubeHomotopyLift_apply, H.apply_zero, SixSphereCube.factorMap_cubeSphereMap]
    rfl
  map_one_left
    z := by
    obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
    change
      cubeHomotopyLift H (1, SixSphereCube.cubeSphereMap u) =
        SixSphereCube.factorMap q (SixSphereCube.cubeSphereMap u)
    rw [cubeHomotopyLift_apply, H.apply_one, SixSphereCube.factorMap_cubeSphereMap]
    rfl
  prop' t z
    hz := by
    have hz' : z = SixSphereCube.sphereBasePoint := hz
    subst z
    change
      cubeHomotopyLift H (t, SixSphereCube.sphereBasePoint) =
        SixSphereCube.factorMap p SixSphereCube.sphereBasePoint
    rw [← SixSphereCube.cubeSphereMap_boundary 0 SixSphereCube.zero_mem_cubeBoundary,
      cubeHomotopyLift_apply]
    rw [H.eq_fst t SixSphereCube.zero_mem_cubeBoundary, SixSphereCube.factorMap_cubeSphereMap]
    rfl

theorem Degree.factorMap_homotopicRel {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (h : GenLoop.Homotopic p q) :
    (SixSphereCube.factorMap p).HomotopicRel (SixSphereCube.factorMap q)
      { SixSphereCube.sphereBasePoint } := by
  obtain ⟨H⟩ := h
  exact ⟨factorHomotopy H⟩

theorem Degree.SphereBasepoint.exists_adjustment {Y : Type*} [TopologicalSpace Y] {y : Y}
    (u : C(SixSphereCube.StandardSphere, Y)) (P : Path (u SixSphereCube.sphereBasePoint) y) :
    ∃ v : C(SixSphereCube.StandardSphere, Y),
      v SixSphereCube.sphereBasePoint = y ∧ u.Homotopic v := by
  let V := Fin 6 → ℝ
  let L : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  let e := Degree.DiskCube.homeomorph L
  let f : C(Degree.DiskCylinder.Disk (E := V), Y) :=
    u.comp (SixSphereCube.cubeSphereMap.comp (e : C(_, _)))
  let side : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), Y) :=
    P.toContinuousMap.comp ContinuousMap.fst
  have h0 : ∀ s, side (0, s) = f (Degree.DiskCylinder.boundaryToDisk s) := by
    intro s
    have hs :=
      (Degree.DiskCube.boundary_iff L (Degree.DiskCylinder.boundaryToDisk s)).mpr
        (mem_sphere_zero_iff_norm.mp s.property)
    exact P.source.trans (congrArg u (SixSphereCube.cubeSphereMap_boundary _ hs)).symm
  let W := Degree.DiskCylinder.extend f side h0
  let C : C((unitInterval) × (Fin 6 → (unitInterval)), Y) :=
    W.comp ((ContinuousMap.id (unitInterval)).prodMap (e.symm : C(_, _)))
  have hCboundary (t : (unitInterval)) (z : Fin 6 → (unitInterval))
    (hz : z ∈ Cube.boundary (Fin 6)) : C (t, z) = P t := by
    let s : Degree.DiskCylinder.Sphere (E := V) :=
      ⟨(e.symm z).val,
        mem_sphere_zero_iff_norm.mpr ((Degree.DiskCube.symm_boundary_iff L z).mpr hz)⟩
    exact Degree.DiskCylinder.extend_side f side h0 t s
  have hfib : ∀ a b, Degree.cylinderQuotient a = Degree.cylinderQuotient b → C a = C b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : SixSphereCube.cubeSphereMap z = SixSphereCube.cubeSphereMap w :=
      congrArg Prod.snd h
    rcases (SixSphereCube.cubeSphereMap_eq_iff z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hCboundary t z hz).trans (hCboundary t w hw).symm
  let G := Degree.cylinderQuotient_isQuotientMap.lift C hfib
  have hG (t : (unitInterval)) (z : Fin 6 → (unitInterval)) :
    G (t, SixSphereCube.cubeSphereMap z) = C (t, z) :=
    ContinuousMap.congr_fun (Degree.cylinderQuotient_isQuotientMap.lift_comp C hfib) (t, z)
  let v : C(SixSphereCube.StandardSphere, Y) :=
    G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  refine
    ⟨v, ?_,
      ⟨{  toContinuousMap := G
          map_zero_left := ?_
          map_one_left := fun _ => rfl }⟩⟩
  · change G (1, SixSphereCube.sphereBasePoint) = y
    rw [← SixSphereCube.cubeSphereMap_boundary 0 SixSphereCube.zero_mem_cubeBoundary, hG]
    exact (hCboundary 1 0 SixSphereCube.zero_mem_cubeBoundary).trans P.target
  · intro z
    obtain ⟨w, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
    exact
      (hG 0 w).trans
        ((Degree.DiskCylinder.extend_bottom f side h0 (e.symm w)).trans
          (congrArg (fun q => u (SixSphereCube.cubeSphereMap q)) (e.apply_symm_apply w)))

def Degree.basedSphereCube {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    GenLoop (Fin 6) X x :=
  ⟨f.comp SixSphereCube.cubeSphereMap, by
    intro u hu
    change f (SixSphereCube.cubeSphereMap u) = x
    rw [SixSphereCube.cubeSphereMap_boundary u hu]
    exact hf⟩

@[simp]
theorem Degree.factorMap_basedSphereCube {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    SixSphereCube.factorMap (basedSphereCube f hf) = f := by
  symm
  apply SixSphereCube.factorMap_unique
  rfl

theorem Degree.basedSphereCube_homologyClass {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    SixthHurewicz.cubeHomologyClass (basedSphereCube f hf) =
      SingularMayerVietoris.singularHomologyMap f 6
        (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) := by
  rw [← SixSphereCube.factor_cubeHomologyClass, factorMap_basedSphereCube]

theorem Degree.sphere_homotopicRel_of_topClass_eq {X : Type} [TopologicalSpace X] {x : X}
    [SimplyConnectedSpace X] [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (f g : C(SixSphereCube.StandardSphere, X))
    (hf : f SixSphereCube.sphereBasePoint = x) (hg : g SixSphereCube.sphereBasePoint = x)
    (h :
      SingularMayerVietoris.singularHomologyMap f 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop)) :
    f.HomotopicRel g { SixSphereCube.sphereBasePoint } := by
  have he : (⟦basedSphereCube f hf⟧ : π_ 6 X x) = ⟦basedSphereCube g hg⟧ := by
    apply (SixthHurewicz.hurewiczPi6Equiv x).injective
    change
      Multiplicative.ofAdd (SixthHurewicz.cubeHomologyClass (basedSphereCube f hf)) =
        Multiplicative.ofAdd (SixthHurewicz.cubeHomologyClass (basedSphereCube g hg))
    rw [basedSphereCube_homologyClass, basedSphereCube_homologyClass, h]
  have hh := factorMap_homotopicRel (Quotient.exact he)
  simpa only [factorMap_basedSphereCube] using hh

theorem Degree.Sphere.based_homotopicRel_id_of_topClass
    (g : C(SixSphereCube.StandardSphere, SixSphereCube.StandardSphere))
    (hg : g SixSphereCube.sphereBasePoint = SixSphereCube.sphereBasePoint)
    (hd :
      SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) :
    g.HomotopicRel (ContinuousMap.id SixSphereCube.StandardSphere)
      { SixSphereCube.sphereBasePoint } := by
  let := piTwo_subsingleton SixSphereCube.sphereBasePoint
  let := piThree_subsingleton SixSphereCube.sphereBasePoint
  let := piFour_subsingleton SixSphereCube.sphereBasePoint
  let := piFive_subsingleton SixSphereCube.sphereBasePoint
  apply
    Degree.sphere_homotopicRel_of_topClass_eq g (ContinuousMap.id SixSphereCube.StandardSphere) hg
      rfl
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] using hd

theorem Degree.Sphere.homotopic_id_of_topClass
    (g : C(SixSphereCube.StandardSphere, SixSphereCube.StandardSphere))
    (hd :
      SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) :
    g.Homotopic (ContinuousMap.id SixSphereCube.StandardSphere) := by
  obtain ⟨v, hv, hgv⟩ :=
    Degree.SphereBasepoint.exists_adjustment g
      (PathConnectedSpace.somePath (g SixSphereCube.sphereBasePoint)
        SixSphereCube.sphereBasePoint)
  have hmap := PeriodTorusHigherHomology.homotopic_homologyMap hgv 6
  have hvd :
    SingularMayerVietoris.singularHomologyMap v 6
        (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop :=
    (LinearMap.congr_fun hmap _).symm.trans hd
  obtain ⟨H⟩ := based_homotopicRel_id_of_topClass v hv hvd
  exact hgv.trans ⟨H.toHomotopy⟩

theorem Degree.right_inverse_is_left_inverse (x : SpecialPeriods.Threefold.Space)
    (g : C(SpecialPeriods.Threefold.Space, SixSphereCube.StandardSphere))
    (hfg :
      ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
        (ContinuousMap.id SpecialPeriods.Threefold.Space)) :
    (g.comp (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)).Homotopic
      (ContinuousMap.id SixSphereCube.StandardSphere) := by
  let F := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  have hh : (F.comp (g.comp F)).Homotopic F := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      hfg.comp (ContinuousMap.Homotopic.refl F)
  apply Sphere.homotopic_id_of_topClass
  apply (SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyMap_bijective x 6).1
  have he :=
    LinearMap.congr_fun (PeriodTorusHigherHomology.homotopic_homologyMap hh 6)
      (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply] at he
  exact he

def Degree.sphereHomotopyEquiv (x : SpecialPeriods.Threefold.Space) :
    SixSphereCube.StandardSphere ≃ₕ SpecialPeriods.Threefold.Space := by
  let g := Classical.choose (exists_right_homotopy_inverse x)
  have hfg := Classical.choose_spec (exists_right_homotopy_inverse x)
  exact
    { toFun := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
      invFun := g
      left_inv := right_inverse_is_left_inverse x g hfg
      right_inv := hfg }

def Degree.threefoldHomotopyEquiv :
    SpecialPeriods.Threefold.Space ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1 :=
  (sphereHomotopyEquiv (Classical.choice SpecialPeriods.Threefold.space_nonempty)).symm

theorem MorseCancel.nativeMorseCount_eq_interval_length {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (k a b : ℕ) (hab : a ≤ b) (hb : b ≤ S.count)
    (hindex : ∀ i : Fin S.count, nativeMorseIndex E f (S.point i) = k ↔ a ≤ i.val ∧ i.val < b) :
    nativeMorseCount E f k = b - a := by
  let K : Set M := {x | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k}
  let u : Fin (b - a) → K := fun j =>
    ⟨(S.point ⟨a + j.val, by omega⟩).val, (S.point ⟨a + j.val, by omega⟩).property,
      (hindex ⟨a + j.val, by omega⟩).mpr
        (show a ≤ a + j.val ∧ a + j.val < b from ⟨by omega, by omega⟩)⟩
  have hu : Function.Bijective u := by
    constructor
    · intro i j hij
      have hv : (u i).val = (u j).val := congrArg Subtype.val hij
      have hp : S.point ⟨a + i.val, by omega⟩ = S.point ⟨a + j.val, by omega⟩ := Subtype.ext hv
      have he := congrArg Fin.val (S.point.injective hp)
      exact Fin.ext (by simpa only [Nat.add_left_cancel_iff] using he)
    · intro x
      let i := S.point.symm ⟨x.val, x.property.1⟩
      have hi : S.point i = ⟨x.val, x.property.1⟩ := S.point.apply_symm_apply _
      have hxi : nativeMorseIndex E f (S.point i) = k := by
        rw [hi]
        exact x.property.2
      have hib := (hindex i).mp hxi
      refine ⟨⟨i.val - a, by omega⟩, ?_⟩
      apply Subtype.ext
      change (S.point ⟨a + (i.val - a), _⟩).val = x.val
      have he : (⟨a + (i.val - a), by omega⟩ : Fin S.count) = i :=
        Fin.ext (show a + (i.val - a) = i.val by omega)
      rw [he, hi]
  have hc := (Nat.card_congr (Equiv.ofBijective u hu)).symm
  change K.ncard = b - a
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_fin] using hc

theorem MorseCancel.native_middle_block_counts {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    nativeMorseCount E f 2 = r ∧ nativeMorseCount E f 3 = c := by
  have hn := S.count_pos hf
  have hi0 (i : Fin S.count) (hi : i.val = 0) : nativeMorseIndex E f (S.point i) = 0 := by
    have he : i = ⟨0, hn⟩ := Fin.ext hi
    rw [he]
    exact (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hi2 (i : Fin S.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
    nativeMorseIndex E f (S.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin S.count) (hri : r < i.val) (hic : i.val ≤ r + c) :
    nativeMorseIndex E f (S.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (hthree i hri hic)
  have hi4 (i : Fin S.count) (hic : r + c < i.val) : 4 ≤ nativeMorseIndex E f (S.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    exact hafter i hic
  have hcases (i : Fin S.count) :
    (i.val = 0 ∧ nativeMorseIndex E f (S.point i) = 0) ∨
      (0 < i.val ∧ i.val ≤ r ∧ nativeMorseIndex E f (S.point i) = 2) ∨
        (r < i.val ∧ i.val ≤ r + c ∧ nativeMorseIndex E f (S.point i) = 3) ∨
          (r + c < i.val ∧ 4 ≤ nativeMorseIndex E f (S.point i)) := by
    by_cases hz : i.val = 0
    · exact Or.inl ⟨hz, hi0 i hz⟩
    by_cases hr : i.val ≤ r
    · exact Or.inr (Or.inl ⟨by omega, hr, hi2 i (by omega) hr⟩)
    by_cases hrc : i.val ≤ r + c
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, hrc, hi3 i (by omega) hrc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hi4 i (by omega)⟩))
  constructor
  · have hh :=
      nativeMorseCount_eq_interval_length S 2 1 (r + 1) (by omega) (by omega)
        (fun i => by have h := hcases i; omega)
    simpa only [Nat.add_sub_cancel_right] using hh
  · have hh :=
      nativeMorseCount_eq_interval_length S 3 (r + 1) (r + c + 1) (by omega) (by omega)
        (fun i => by have h := hcases i; omega)
    have he : r + c + 1 - (r + 1) = c := by omega
    simpa only [he] using hh

theorem AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section {E M X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [TopologicalSpace X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)]
    [PreconnectedSpace (Smale.Hemisphere.Sphere n)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (α : C(X, { y : M // f y = a })) (x₀ : X)
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val)) :
    ∀ u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((S.data p).surgery.attachingSphere u).val ∈
        Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  have hback (x : X) := (hfull (α x)).mp (Set.mem_range_self x)
  have hreach (x : X) :=
    S.backward_basin_reaches_attaching_level hf p (ha (α x).val (α x).property) (hback x)
  obtain ⟨t₀, ht₀⟩ := hreach x₀
  obtain ⟨D, hsource, htarget, horbit⟩ :=
    S.exists_native_level_basin_transport hf ha (S.data p).lower_regular (α x₀)
      ⟨S.flow t₀ (α x₀).val, ht₀⟩
  have hsrc (x : X) : α x ∈ D.source := hsource.symm ▸ hreach x
  let β : X → (S.data p).LowerLevel := D ∘ α
  have hβ : Continuous β := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact
      (D.contMDiffOn_toFun.continuousOn.continuousAt (D.open_source.mem_nhds (hsrc x))).comp
        α.continuous.continuousAt
  have hβback (x : X) : Filter.Tendsto (fun t => S.flow t (β x).val) Filter.atBot (𝓝 p.val) := by
    obtain ⟨t, ht⟩ := horbit (α x) (hsrc x)
    change Filter.Tendsto (fun t => S.flow t (D (α x)).val) Filter.atBot (𝓝 p.val)
    rw [← ht]
    exact (MorseCancel.flow_time_atBot_limit_iff S.flow t (α x).val p.val).mpr (hback x)
  let e :=
    (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
        n).toHomeomorph
  let A : C(Smale.Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    (S.data p).surgery.attachingSphere.comp (e : C(_, _))
  let U : Set (Smale.Hemisphere.Sphere n) := A ⁻¹' D.target
  have hUeq : U = A ⁻¹' Set.range β := by
    ext u
    constructor
    · intro hu
      have hxu : D.symm (A u) ∈ D.source := D.map_target' hu
      have hright : D (D.symm (A u)) = A u := D.right_inv' hu
      obtain ⟨t, ht⟩ := horbit (D.symm (A u)) hxu
      rw [hright] at ht
      have hAback : Filter.Tendsto (fun t => S.flow t (A u).val) Filter.atBot (𝓝 p.val) :=
        (S.attaching_basin_iff hf p (A u)).mpr ⟨e u, rfl⟩
      have hxb : Filter.Tendsto (fun t => S.flow t (D.symm (A u)).val) Filter.atBot (𝓝 p.val) := by
        rw [← ht] at hAback
        exact (MorseCancel.flow_time_atBot_limit_iff S.flow t (D.symm (A u)).val p.val).mp hAback
      obtain ⟨x, hx⟩ := (hfull (D.symm (A u))).mpr hxb
      exact ⟨x, (congrArg D hx).trans hright⟩
    · rintro ⟨x, hx⟩
      change A u ∈ D.target
      rw [← hx]
      exact D.map_source' (hsrc x)
  have hUopen : IsOpen U := D.open_target.preimage A.continuous
  have hUclosed : IsClosed U := by
    rw [hUeq]
    exact (isCompact_range hβ).isClosed.preimage A.continuous
  have hUne : U.Nonempty := by
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p (β x₀)).mp (hβback x₀)
    obtain ⟨v, hv⟩ := e.surjective u
    refine ⟨v, ?_⟩
    change A v ∈ D.target
    have heq : A v = β x₀ := by change (S.data p).surgery.attachingSphere (e v) = _; rw [hv, hu]
    rw [heq]
    exact D.map_source' (hsrc x₀)
  have hUall : U = Set.univ := IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne
  intro u
  obtain ⟨v, rfl⟩ := e.surjective u
  have hv : A v ∈ D.target := show v ∈ U from hUall.symm ▸ Set.mem_univ v
  rw [htarget] at hv
  exact hv

theorem MorseCancel.nativeIndexThreeAttachingSphere_regular {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (nativeIndexThreeAttachingSphere S p hp) ∧
      Topology.IsClosedEmbedding (nativeIndexThreeAttachingSphere S p hp) ∧
        ∀ x,
          Function.Injective
            (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E)
              (nativeIndexThreeAttachingSphere S p hp) x) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let e := Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2
  have hs :
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (nativeIndexThreeAttachingSphere S p hp) :=
    ((S.data p).attaching_smooth hf 2).comp e.contMDiff
  have hi : Function.Injective (nativeIndexThreeAttachingSphere S p hp) :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  refine ⟨hs, hs.continuous.isClosedEmbedding hi, ?_⟩
  intro x
  change
    Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e) x)
  rw [mfderiv_comp x (((S.data p).attaching_smooth hf 2).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
  exact
    ((S.data p).attaching_derivative_injective hf 2 (e x)).comp
      (e.mfderivToContinuousLinearEquiv (by simp) x).injective

theorem AdaptedWindows.exists_canonical_basin_sphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {X : Type} [TopologicalSpace X] [CompactSpace X]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (α : C(X, { y : M // f y = a })) (x₀ : X)
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val)) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
      ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ ∧
        Topology.IsClosedEmbedding γ ∧
          (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)) ∧
            Set.range γ = Set.range α ∧
              (∀ x,
                  ∃ t : ℝ,
                    S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S p hp x).val =
                      (γ x).val) ∧
                ∀ y,
                  y ∈ Set.range γ ↔
                    Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach := S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α x₀ hfull
  obtain ⟨hs, he, hi⟩ := MorseCancel.nativeIndexThreeAttachingSphere_regular S hf p hp
  let z₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨D, -, -, γ, hγ, hγi, hγd, -, -, horbit⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha
      (MorseCancel.nativeIndexThreeAttachingSphere S p hp) z₀ hs he.injective hi
      (fun z => hreach _)
  have hγfull (y : { x : M // f x = a }) :
    y ∈ Set.range γ ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) :=
    S.transported_attaching_range_iff hf p ha
      (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2)
      (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
          2).surjective
      γ horbit y
  exact
    ⟨γ, hγ, hγ.continuous.isClosedEmbedding hγi, hγd,
      Set.ext (fun y => (hγfull y).trans (hfull y).symm), horbit, hγfull⟩

theorem AdaptedWindows.exists_canonical_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a })
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ γ : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a },
      MorseCancel.IsNativeMiddleBasinFamily S hf ha p γ ∧
        (∀ j, Set.range (γ j) = Set.range (α j)) ∧
          ∀ j x,
            ∃ t : ℝ,
              S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
                (γ j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  obtain ⟨hαs, -, -, hαpair, hαfull⟩ := hα
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  have hex (j : Fin n) :=
    S.exists_canonical_basin_sphere hf (p j) (hp j) ha ⟨α j, (hαs j).continuous⟩ x₀ (hαfull j)
  choose γ hγs hγe hγi hγrange hγflow hγfull using hex
  refine ⟨fun j => γ j, ⟨hγs, hγe, hγi, ?_, hγfull⟩, hγrange, hγflow⟩
  intro i j hij
  rw [hγrange i, hγrange j]
  exact hαpair hij

def MorseCancel.levelSublevelMap {M : Type} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) : C({ y : M // f y = a }, { y : M // f y ≤ b }) :=
  ⟨fun y => ⟨y.val, y.property.le.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

theorem AdaptedWindows.level_transport_homotopic_in_sublevel {E M X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [TopologicalSpace X]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (g : C(X, { y : M // f y = b })) (γ : C(X, { y : M // f y = a }))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (g x).val = (γ x).val) :
    ContinuousMap.Homotopic ((MorseCancel.levelSublevelMap f le_rfl).comp g)
      ((MorseCancel.levelSublevelMap f hab.le).comp γ) := by
  have hboundary (y : M) (hy : f y = a) : mvfderiv 𝓘(ℝ, E) f y (S.field y) < 0 :=
    S.descent y (ha y hy)
  have hreach (x : X) : (g x).val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, by rw [ht]; exact (γ x).property⟩
  let θ : X → ℝ := fun x => Degree.FlowCancellation.signedLevelTime S.flow f a (g x).val
  obtain ⟨hB, htime, -⟩ :=
    Degree.FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral hboundary
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact
      ContinuousAt.comp (f := fun y : X => (g y).val)
        (htime.continuousOn.continuousAt (hB.mem_nhds (hreach x)))
        (continuous_subtype_val.comp g.continuous).continuousAt
  have hhit (x : X) : f (S.flow (θ x) (g x).val) = a :=
    Degree.FlowCancellation.signedLevelTime_hits S.flow f a (hreach x)
  have hθpos (x : X) : 0 < θ x := by
    by_contra h
    have hh :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent (g x).val
        (le_of_not_gt h)
    change f (S.flow 0 (g x).val) ≤ f (S.flow (θ x) (g x).val) at hh
    rw [S.flow.map_zero_apply, (g x).property, hhit x] at hh
    exact not_le_of_gt hab hh
  have hend (x : X) : S.flow (θ x) (g x).val = (γ x).val := by
    obtain ⟨t, ht⟩ := horbit x
    have hθt : θ x = t :=
      Degree.FlowCancellation.signedLevelTime_eq_of_level S.flow hf.continuous
        (MorseCancel.contMDiff_directionalDerivative hf S.smooth).continuous
        (fun y s => Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (S.integral y) s)
        hboundary (by rw [ht]; exact (γ x).property)
    rw [hθt]
    exact ht
  have hstay (u : unitInterval) (x : X) : f (S.flow ((u : ℝ) * θ x) (g x).val) ≤ b := by
    have hh :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent (g x).val
        (mul_nonneg u.property.1 (hθpos x).le)
    simpa only [S.flow.map_zero_apply, (g x).property] using hh
  refine
    ⟨{  toFun := fun z => ⟨S.flow ((z.1 : ℝ) * θ z.2) (g z.2).val, hstay z.1 z.2⟩
        continuous_toFun :=
          (S.flow.continuous
                ((continuous_subtype_val.comp continuous_fst).mul (hθ.comp continuous_snd))
                (continuous_subtype_val.comp (g.continuous.comp continuous_snd))).subtype_mk
            _
        map_zero_left := ?_
        map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change S.flow ((0 : ℝ) * θ x) (g x).val = (g x).val
    simp
  · intro x
    apply Subtype.ext
    change S.flow ((1 : ℝ) * θ x) (g x).val = (γ x).val
    simpa only [one_mul] using hend x

theorem Smale.ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass_parametrized {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    d.indexThreeAttachingClass hindex.out =
      SingularMayerVietoris.singularHomologyMap
        (d.coreBoundaryMap.comp
          (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
              2).toHomeomorph.toHomotopyEquiv.toFun)
        2 (SphereHomology.unitSphereTopClass 1) := by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

def MorseCancel.sublevelMap {M : Type} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    C({ y : M // f y ≤ a }, { y : M // f y ≤ b }) :=
  ⟨fun y => ⟨y.val, y.property.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

def MorseCancel.middleSectionClass {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 :=
  SingularMayerVietoris.singularHomologyMap ((levelSublevelMap f le_rfl).comp γ) 2
    (SphereHomology.unitSphereTopClass 1)

theorem AdaptedWindows.native_attaching_class_of_flow_section {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hab : a < S.toSurgeryWindows.lower p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val) :
    SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab.le) 2
        (MorseCancel.middleSectionClass γ) =
      (S.data p).indexThreeAttachingClass
        ((MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hh :=
    S.level_transport_homotopic_in_sublevel hf hab ha
      (MorseCancel.nativeIndexThreeAttachingSphere S p hp) γ horbit
  have hm := PeriodTorusHigherHomology.homotopic_homologyMap hh 2
  have hparam :
    SingularMayerVietoris.singularHomologyMap
        ((MorseCancel.levelSublevelMap f (le_refl (S.toSurgeryWindows.lower p))).comp
          (MorseCancel.nativeIndexThreeAttachingSphere S p hp))
        2 (SphereHomology.unitSphereTopClass 1) =
      (S.data p).indexThreeAttachingClass
        ((MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) :=
    (S.data p).indexThreeAttachingClass_parametrized.symm
  rw [← hparam, hm]
  rw [MorseCancel.middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

theorem AdaptedWindows.exists_native_core_inclusion_equiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ e :
      ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range (S.data p).coreMap) ≃ₕ
        { y : M // f y ≤ S.toSurgeryWindows.upper p },
      ∀ x, (e x).val = x.val := by
  let d := S.data p
  have hagreement :
    ∀ x ∈ Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block),
      ∀ᶠ y in 𝓝 x, S.field y = d.chart.descentField y := by
    rintro x ⟨z, rfl⟩
    exact S.model_germ p _ (Smale.MorseHandle.modelMap_mem_product d.radius_pos z)
  obtain ⟨B, hB⟩ :=
    d.chart.exists_attachingUnionHomotopyEquiv hf S.smooth S.zero S.descent S.flow S.integral
      d.radius d.radius_pos d.block hagreement (S.isolated p)
  let C :=
    Smale.ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ S.toSurgeryWindows.lower p}
      d.handleMap (isClosed_le hf.continuous continuous_const)
      (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
      (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)
  exact ⟨C.trans B, fun x => hB (C x)⟩

theorem AdaptedWindows.exists_core_inclusion_homology_comparison {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (k : ℕ) :
    ∃ A :
      SingularMayerVietoris.SingularHomology
          (↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range (S.data p).coreMap)) k ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ S.toSurgeryWindows.upper p } k,
      ∀ a,
        A
            (((S.data p).coreCellPresentation hf.continuous).oldHomologyMap k
              ((S.data p).cellOldHomologyEquiv hf.continuous k a)) =
          SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f
              ((S.toSurgeryWindows.lower_lt_value p).trans
                  (S.toSurgeryWindows.value_lt_upper p)).le)
            k a := by
  obtain ⟨B, hB⟩ := S.exists_native_core_inclusion_equiv hf p
  let d := S.data p
  let A := PeriodTorusHigherHomology.homotopyEquivHomologyEquiv B k
  let old :=
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C((d.coreCellPresentation hf.continuous).old,
        ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range d.coreMap)))
  have hmaps :
    (B.toFun.comp old).comp (d.cellOldHomeomorph hf.continuous).toHomotopyEquiv.toFun =
      MorseCancel.sublevelMap f
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hB _)
  refine ⟨A, ?_⟩
  intro a
  change
    SingularMayerVietoris.singularHomologyMap B.toFun k
        (SingularMayerVietoris.singularHomologyMap old k
          (SingularMayerVietoris.singularHomologyMap
            (d.cellOldHomeomorph hf.continuous).toHomotopyEquiv.toFun k a)) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, hmaps]
  rfl

theorem AdaptedWindows.native_sublevel_inclusion_exact {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range ((S.data p).coreBoundaryHomologyMap k) =
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (MorseCancel.sublevelMap f
            ((S.toSurgeryWindows.lower_lt_value p).trans
                (S.toSurgeryWindows.value_lt_upper p)).le)
          k) := by
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p k
  let d := S.data p
  refine
    Smale.HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
      (d.cellOldHomologyEquiv hf.continuous k).symm A
      ((d.coreCellPresentation hf.continuous).attachingHomologyMap k)
      ((d.coreCellPresentation hf.continuous).oldHomologyMap k) (d.coreBoundaryHomologyMap k) _ ?_
      ?_ ((d.coreCellPresentation hf.continuous).cell_exact_at_old k hk)
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf.continuous k).symm
          ((d.coreCellPresentation hf.continuous).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous k).symm a)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm

theorem AdaptedWindows.native_index_three_inclusion_relation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) :
    let I :=
      SingularMayerVietoris.singularHomologyMap
        (MorseCancel.sublevelMap f
          ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le)
        2
    Function.Surjective I ∧
      LinearMap.ker I =
        Submodule.span ℤ
          {(S.data p).indexThreeAttachingClass
              ((MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp)} := by
  let d := S.data p
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3 :=
    (MorseCancel.nativeMorseIndex_eq_chart d.chart).symm.trans hp
  let _ :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  have hsurj : Function.Surjective ((d.coreCellPresentation hf.continuous).oldHomologyMap 2) := by
    intro a
    have ha : a ∈ LinearMap.ker ((d.coreCellPresentation hf.continuous).cellConnectingMap 1) :=
      Subsingleton.elim _ _
    rw [← (d.coreCellPresentation hf.continuous).cell_exact_at_ambient 1] at ha
    exact ha
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p 2
  constructor
  · intro a
    obtain ⟨x, hx⟩ := hsurj (A.symm a)
    refine ⟨(d.cellOldHomologyEquiv hf.continuous 2).symm x, ?_⟩
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous 2).symm x)
    rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  · rw [← S.native_sublevel_inclusion_exact hf p 2 (by decide), d.coreBoundary_two_range hindex]

theorem MorseCancel.sublevelMap_trans {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (sublevelMap f hbc).comp (sublevelMap f hab) = sublevelMap f (hab.trans hbc) :=
  rfl

theorem MorseCancel.sublevelHomologyMap_comp {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (k : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (sublevelMap f hbc) k).comp
        (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) k) =
      SingularMayerVietoris.singularHomologyMap (sublevelMap f (hab.trans hbc)) k := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, sublevelMap_trans]

theorem MorseCancel.regular_sublevel_inclusion_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (k : ℕ) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) k) := by
  obtain ⟨e, he⟩ := Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv hf hab hband
  have hmap : e.toFun = sublevelMap f hab := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (he x)
  have hh := (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e k).bijective
  change Function.Bijective (SingularMayerVietoris.singularHomologyMap e.toFun k) at hh
  rwa [hmap] at hh

theorem AdaptedWindows.middle_inclusion_step {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hbp : b < S.toSurgeryWindows.lower p)
    (hband :
      ∀ y,
        f y ∈ Set.Icc b (S.toSurgeryWindows.lower p) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ, S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val)
    (hsurj :
      Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab) 2)) :
    let hau :=
      (hab.trans hbp.le).trans
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le
    Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hau) 2) ∧
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hau) 2) =
        LinearMap.ker
            (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab) 2) ⊔
          Submodule.span ℤ {MorseCancel.middleSectionClass γ} := by
  let hl := (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  let P := SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab) 2
  let J := SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hbp.le) 2
  let Q := SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hl.le) 2
  have hJ : Function.Bijective J :=
    MorseCancel.regular_sublevel_inclusion_bijective hf hbp.le hband 2
  obtain ⟨hQ, hkerQ⟩ := S.native_index_three_inclusion_relation hf p hp
  have hclass := S.native_attaching_class_of_flow_section hf p hp ha (hab.trans_lt hbp) γ horbit
  have hcomp :
    J.comp P =
      SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f (hab.trans hbp.le))
        2 :=
    MorseCancel.sublevelHomologyMap_comp f hab hbp.le 2
  have htotal :
    Q.comp (J.comp P) =
      SingularMayerVietoris.singularHomologyMap
        (MorseCancel.sublevelMap f ((hab.trans hbp.le).trans hl.le)) 2 := by
    rw [hcomp]
    exact MorseCancel.sublevelHomologyMap_comp f (hab.trans hbp.le) hl.le 2
  have hkerJ : LinearMap.ker (J.comp P) = LinearMap.ker P := by
    ext v
    change J (P v) = 0 ↔ P v = 0
    exact ⟨fun h => hJ.injective (h.trans (map_zero J).symm), fun h => by rw [h, map_zero]⟩
  have hker :
    LinearMap.ker Q = Submodule.span ℤ {(J.comp P) (MorseCancel.middleSectionClass γ)} := by
    rw [hcomp, hclass]
    exact hkerQ
  constructor
  · rw [← htotal]
    exact hQ.comp (hJ.surjective.comp hsurj)
  · rw [← htotal,
      Smale.HomologyTransport.ker_comp_span_singleton (J.comp P) Q
        (MorseCancel.middleSectionClass γ) hker,
      hkerJ]

theorem MorseCancel.span_prefix_succ {A : Type} [AddCommGroup A] [Module ℤ A] {n k : ℕ}
    (v : Fin n → A) (hk : k < n) :
    Submodule.span ℤ (Set.range (fun j : Fin k => v ⟨j.val, j.isLt.trans hk⟩)) ⊔
        Submodule.span ℤ {v ⟨k, hk⟩} =
      Submodule.span ℤ (Set.range (fun j : Fin (k + 1) => v ⟨j.val, by omega⟩)) := by
  have heq :
    (fun j : Fin (k + 1) => v ⟨j.val, by omega⟩) =
      Fin.snoc (fun j : Fin k => v ⟨j.val, j.isLt.trans hk⟩) (v ⟨k, hk⟩) := by
    funext j
    cases j using Fin.lastCases <;> simp
  rw [heq, Fin.range_snoc, Submodule.span_insert, sup_comm]

theorem AdaptedWindows.finite_middle_inclusion_relations {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3) (cut : Fin (n + 1) → ℝ)
    (ha : ∀ y, f y = cut 0 → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hbase : ∀ i, cut 0 ≤ cut i) (hnext : ∀ j, cut j.succ = S.toSurgeryWindows.upper (p j))
    (hlower : ∀ j, cut j.castSucc < S.toSurgeryWindows.lower (p j))
    (hband :
      ∀ j y,
        f y ∈ Set.Icc (cut j.castSucc) (S.toSurgeryWindows.lower (p j)) →
          y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = cut 0 }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
            (γ j x).val) :
    Function.Surjective
        (SingularMayerVietoris.singularHomologyMap
          (MorseCancel.sublevelMap f (hbase (Fin.last n))) 2) ∧
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f (hbase (Fin.last n))) 2) =
        Submodule.span ℤ (Set.range (fun j => MorseCancel.middleSectionClass (γ j))) := by
  have hprefix (k : ℕ) :
    ∀ hk : k ≤ n,
      Function.Surjective
          (SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f (hbase ⟨k, by omega⟩)) 2) ∧
        LinearMap.ker
            (SingularMayerVietoris.singularHomologyMap
              (MorseCancel.sublevelMap f (hbase ⟨k, by omega⟩)) 2) =
          Submodule.span ℤ
            (Set.range
              (fun j : Fin k =>
                MorseCancel.middleSectionClass (γ ⟨j.val, j.isLt.trans_le hk⟩))) := by
    induction k with
    | zero =>
      intro hk
      have hid :
        SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f (hbase ⟨0, by omega⟩)) 2 =
          LinearMap.id := by
        change
          SingularMayerVietoris.singularHomologyMap (ContinuousMap.id { y : M // f y ≤ cut 0 })
              2 =
            _
        exact PeriodTorusHigherHomology.singularHomologyMap_id _ _
      constructor
      · rw [hid]
        exact Function.surjective_id
      · rw [hid]
        simp only [Set.range_eq_empty, Submodule.span_empty]
        ext v
        rfl
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      let j : Fin n := ⟨k, hkn⟩
      obtain ⟨hprev, hkernel⟩ := ih (by omega)
      have hstep :=
        S.middle_inclusion_step hf (p j) (hp j) (hbase j.castSucc) ha (hlower j) (hband j) (γ j)
          (horbit j) hprev
      have hstep' :
        Function.Surjective
            (SingularMayerVietoris.singularHomologyMap
              (MorseCancel.sublevelMap f (hbase ⟨k + 1, by omega⟩)) 2) ∧
          LinearMap.ker
              (SingularMayerVietoris.singularHomologyMap
                (MorseCancel.sublevelMap f (hbase ⟨k + 1, by omega⟩)) 2) =
            LinearMap.ker
                (SingularMayerVietoris.singularHomologyMap
                  (MorseCancel.sublevelMap f (hbase j.castSucc)) 2) ⊔
              Submodule.span ℤ {MorseCancel.middleSectionClass (γ j)} := by
        have heq : cut ⟨k + 1, by omega⟩ = S.toSurgeryWindows.upper (p j) := hnext j
        have aux (b : ℝ) (hb : cut 0 ≤ b) (he : b = S.toSurgeryWindows.upper (p j)) :
          Function.Surjective
              (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hb) 2) ∧
            LinearMap.ker
                (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hb) 2) =
              LinearMap.ker
                  (SingularMayerVietoris.singularHomologyMap
                    (MorseCancel.sublevelMap f (hbase j.castSucc)) 2) ⊔
                Submodule.span ℤ {MorseCancel.middleSectionClass (γ j)} := by
          subst b
          exact hstep
        exact aux _ _ heq
      refine ⟨hstep'.1, ?_⟩
      rw [hstep'.2, hkernel]
      exact MorseCancel.span_prefix_succ (fun i => MorseCancel.middleSectionClass (γ i)) hkn
  simpa only using hprefix n le_rfl

def MorseCancel.nativeMiddleBaseCut {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) : ℝ :=
  S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r, by omega⟩)

def MorseCancel.nativeMiddleCutSequence {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) :
    Fin (n + 1) → ℝ :=
  Fin.cases (nativeMiddleBaseCut S r n hn)
    (fun j => T.toSurgeryWindows.upper (nativeMiddleBlockPoint S r n hn j))

theorem MorseCancel.nativeMiddleCutSequence_bands {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hn <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j)) :
    let p := nativeMiddleBlockPoint S r n hn
    let cut := nativeMiddleCutSequence S T r n hn
    (∀ i, cut 0 ≤ cut i) ∧
      (∀ j, cut j.succ = T.toSurgeryWindows.upper (p j)) ∧
        (∀ j, cut j.castSucc < T.toSurgeryWindows.lower (p j)) ∧
          ∀ j y,
            f y ∈ Set.Icc (cut j.castSucc) (T.toSurgeryWindows.lower (p j)) →
              y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  let p := nativeMiddleBlockPoint S r n hn
  let cut := nativeMiddleCutSequence S T r n hn
  have hbase (i : Fin (n + 1)) : cut 0 ≤ cut i := by
    cases i using Fin.cases with
    | zero => exact le_rfl
    | succ j =>
      exact
        ((hbefore j).trans
            ((T.toSurgeryWindows.lower_lt_value (p j)).trans
              (T.toSurgeryWindows.value_lt_upper (p j)))).le
  have hstep (j : Fin n) : cut j.castSucc < T.toSurgeryWindows.lower (p j) := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact hbefore 0
      | succ
        j =>
        change T.toSurgeryWindows.upper (p j.castSucc) < T.toSurgeryWindows.lower (p j.succ)
        apply T.separated
        apply S.toSurgeryWindows.point_strictMono
        change r + j.val + 1 < r + (j.val + 1) + 1
        omega
  have hpred (j : Fin n) : f (S.toSurgeryWindows.point ⟨r + j.val, by omega⟩) < cut j.castSucc := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact S.toSurgeryWindows.value_lt_upper _
      | succ j => exact T.toSurgeryWindows.value_lt_upper (p j.castSucc)
  refine ⟨hbase, fun _ => rfl, hstep, ?_⟩
  intro j y hy hcrit
  have hconsecutive :=
    S.toSurgeryWindows.point_consecutive ⟨r + j.val, by omega⟩ ⟨r + j.val + 1, by omega⟩ rfl
  exact
    hconsecutive ⟨y, hcrit⟩
      ⟨(hpred j).trans_le hy.1, hy.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p j))⟩

theorem MorseCancel.ordered_middle_inclusion_relations {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hn <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hn }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hn j) (hp j)
                  x).val =
            (γ j x).val) :
    ∃ h : nativeMiddleBaseCut S r n hn ≤ nativeMiddleCutSequence S T r n hn (Fin.last n),
      Function.Surjective (SingularMayerVietoris.singularHomologyMap (sublevelMap f h) 2) ∧
        LinearMap.ker (SingularMayerVietoris.singularHomologyMap (sublevelMap f h) 2) =
          Submodule.span ℤ (Set.range (fun j => middleSectionClass (γ j))) := by
  obtain ⟨hbase, hnext, hlower, hband⟩ := nativeMiddleCutSequence_bands S T r n hn hbefore
  refine ⟨hbase (Fin.last n), ?_⟩
  exact
    T.finite_middle_inclusion_relations hf n (nativeMiddleBlockPoint S r n hn) hp
      (nativeMiddleCutSequence S T r n hn)
      (S.data (S.toSurgeryWindows.point ⟨r, by omega⟩)).upper_regular hbase hnext hlower hband γ
      horbit

theorem MorseCancel.native_middle_terminal_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n) :
    ∃ hrc : r + n < S.toSurgeryWindows.count,
      Subsingleton
        (SingularMayerVietoris.SingularHomology
          { y : M // f y ≤ S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r + n, hrc⟩) }
          2) := by
  obtain ⟨r', n', htwo, hrc, hthree, hj, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr, hnn] at hrc hj hafter
  refine ⟨hrc, ?_⟩
  exact
    S.toSurgeryWindows.upper_homology_subsingleton_of_later_indices hf hdim e ⟨r + n, hrc⟩ hj 2
      (by norm_num) (by norm_num)
      (fun i hi _ => by have hh := hafter i hi; exact ⟨by omega, by omega⟩)

theorem MorseCancel.nativeMiddleCutSequence_terminal_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { y : M // f y ≤ nativeMiddleCutSequence S T r n hrc (Fin.last n) } 2) := by
  cases n with
  |
    zero =>
    obtain ⟨h, hH⟩ :=
      native_middle_terminal_homology_subsingleton S hf hdim e horder hzero hone r 0 hr hn
    exact hH
  | succ
    n =>
    obtain ⟨h, hH⟩ :=
      native_middle_terminal_homology_subsingleton T hf hdim e horder hzero hone r (n + 1) hr hn
    exact hH

theorem MorseCancel.middle_section_classes_span {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hrc <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j)
                  x).val =
            (γ j x).val) :
    Submodule.span ℤ (Set.range (fun j => middleSectionClass (γ j))) = ⊤ := by
  obtain ⟨h, -, hker⟩ := ordered_middle_inclusion_relations S T hf r n hrc hp hbefore γ horbit
  let _ :=
    nativeMiddleCutSequence_terminal_homology_subsingleton S T hf hdim e horder hzero hone r n hr
      hn hrc
  apply top_unique
  intro v hv
  rw [← hker]
  exact Subsingleton.elim _ _

def MorseCancel.classCoordinateMatrix {A : Type} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) : Matrix (Fin r) (Fin n) ℤ := fun i j =>
  B.symm (v j) i

theorem MorseCancel.classCoordinateMatrix_mulVec {A : Type} [AddCommGroup A] [Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) (z : Fin n → ℤ) :
    B ((classCoordinateMatrix B v).mulVec z) = ∑ j, z j • v j := by
  have hvec : (classCoordinateMatrix B v).mulVec z = ∑ j, z j • B.symm (v j) := by
    funext i
    simp [classCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_zsmul, LinearEquiv.apply_symm_apply]

theorem MorseCancel.classCoordinateMatrix_surjective {A : Type} [AddCommGroup A] [hA : Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A)
    (hspan : Submodule.span ℤ (Set.range v) = ⊤) :
    Function.Surjective (classCoordinateMatrix B v).mulVec := by
  intro w
  have hw : B w ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
  refine ⟨z, B.injective ?_⟩
  rw [classCoordinateMatrix_mulVec]
  have hsum : (∑ j, z j • v j) = ∑ j, hA.smul (z j) (v j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (int_smul_eq_zsmul hA (z j) (v j)).symm
  exact hsum.trans hz

def MorseCancel.canonicalMiddleMatrix {M : Type} [TopologicalSpace M] {f : M → ℝ} {r n : ℕ}
    {a : ℝ} (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    Matrix (Fin r) (Fin n) ℤ :=
  classCoordinateMatrix B (fun j => middleSectionClass (γ j))

theorem MorseCancel.canonical_middle_matrix_surjective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hrc <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ nativeMiddleBaseCut S r n hrc } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j)
                  x).val =
            (γ j x).val) :
    Function.Surjective (canonicalMiddleMatrix B γ).mulVec :=
  classCoordinateMatrix_surjective B _
    (middle_section_classes_span S T hf hdim e horder hzero hone r n hr hn hrc hp hbefore γ
      horbit)

theorem AdaptedWindows.no_connection_above_canonical_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hq : MorseCancel.nativeMorseIndex E f q = 3) {a : ℝ} (hap : a < f p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  let e := Smale.SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2
  intro x hx
  have hplower : f p < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq)
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hx.1
      hx.2 (S.toSurgeryWindows.lower_lt_value q) hplower
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 q.val) :=
    (MorseCancel.flow_time_atBot_limit_iff S.flow t x q.val).mpr hx.1
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  obtain ⟨z, hz⟩ := e.surjective u
  have hpoint : MorseCancel.nativeIndexThreeAttachingSphere S q hq z = y := by
    change (S.data q).surgery.attachingSphere (e z) = y
    exact (congrArg (S.data q).surgery.attachingSphere (show e z = u from hz)).trans hu
  obtain ⟨s, hs⟩ := horbit z
  rw [hpoint] at hs
  have hyforward : Filter.Tendsto (fun v => S.flow v y.val) Filter.atTop (𝓝 p.val) :=
    (MorseCancel.flow_time_atTop_limit_iff S.flow t x p.val).mpr hx.2
  have hγforward := (MorseCancel.flow_time_atTop_limit_iff S.flow s y.val p.val).mpr hyforward
  rw [hs] at hγforward
  have hheight : Filter.Tendsto (fun v => f (S.flow v (γ z).val)) Filter.atTop (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hγforward
  have hh :=
    (Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
          (γ z).val).le_of_tendsto
      hheight 0
  have hpa : f p ≤ a := by simpa only [S.flow.map_zero_apply, (γ z).property] using hh
  exact not_le_of_gt hap hpa

theorem MorseCancel.lower_cuts_preserved_of_critical_bound {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l a : ℝ} (ha : a < l) (hexterior : ∀ y, f y ≤ l → g =ᶠ[𝓝 y] f)
    (hcritical : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    (∀ y, g y ≤ a ↔ f y ≤ a) ∧ (∀ y, g y = a ↔ f y = a) ∧ ∀ y, f y ≤ a → g =ᶠ[𝓝 y] f := by
  have hbound :=
    superlevel_bound_of_critical_bound hf hg
      (fun y hy => (hexterior y hy.le).self_of_nhds.trans hy) hcritical
  have hbelow (y : M) (hy : g y ≤ a) : f y ≤ l := by
    by_contra h
    exact (ha.trans_le (hbound y (le_of_not_ge h))).not_ge hy
  refine ⟨?_, ?_, fun y hy => hexterior y (hy.trans ha.le)⟩
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy)).self_of_nhds) ▸ hy
    · intro hy
      rw [(hexterior y (hy.trans ha.le)).self_of_nhds]
      exact hy
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy.le)).self_of_nhds).symm.trans hy
    · intro hy
      exact (hexterior y (hy ▸ ha.le)).self_of_nhds.trans hy

theorem AdaptedWindows.exists_common_cut_value_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hq : MorseCancel.nativeMorseIndex E f q = 3) (hal : a < S.toSurgeryWindows.lower p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ z,
                      f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                        g =ᶠ[𝓝 z] f) ∧
                    (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                        z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          MorseCancel.nativeMorseIndex E g z =
                            MorseCancel.nativeMorseIndex E f z) ∧
                        (∀ k,
                            MorseCancel.nativeMorseCount E g k =
                              MorseCancel.nativeMorseCount E f k) ∧
                          (∀ y, g y ≤ a ↔ f y ≤ a) ∧
                            (∀ y, g y = a ↔ f y = a) ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                (∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g) ∧
                                  ∃ T : AdaptedWindows E g,
                                    T.field = S.field ∧
                                      T.flow = S.flow ∧
                                        (∀ r : Smale.ManifoldMorse.criticalPoints E g,
                                            g r < a → T.toSurgeryWindows.upper r < a) ∧
                                          ∀ r : Smale.ManifoldMorse.criticalPoints E g,
                                            a < g r → a < T.toSurgeryWindows.lower r := by
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  have hnoconnection :=
    S.no_connection_above_canonical_cut hf p q hpq hq
      (hal.trans (S.toSurgeryWindows.lower_lt_value p)) γ horbit
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdesc, hexterior, hpgerm, hqgerm, hothers, hindices⟩ :=
    Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm S.smooth S.flow
      S.integral S.zero S.descent S.distinct (S.data p).chart (S.data q).chart
      (S.critical_model_germ p) (S.critical_model_germ q) hpband hqband hpq hqband hpband
      (MorseCancel.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hnoconnection
  have hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      MorseCancel.injOn_of_exchanged_values S.distinct p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels (r : Smale.ManifoldMorse.criticalPoints E g) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g r.val,
      ∀ᶠ y in 𝓝 r.val, S.field y = c.descentField y := by
    have hr : r.val ∈ Smale.ManifoldMorse.criticalPoints E f := hcrit ▸ r.property
    by_cases hrp : r.val = p.val
    · obtain ⟨c, hc⟩ :=
        MorseCancel.exists_signed_morse_chart_of_shift_germ_preserving_field (S.data p).chart
          hpgerm
      rw [hrp]
      exact ⟨c, hc ▸ S.critical_model_germ p⟩
    by_cases hrq : r.val = q.val
    · obtain ⟨c, hc⟩ :=
        MorseCancel.exists_signed_morse_chart_of_shift_germ_preserving_field (S.data q).chart
          hqgerm
      rw [hrq]
      exact ⟨c, hc ▸ S.critical_model_germ q⟩
    obtain ⟨c, hc⟩ :=
      MorseCancel.exists_signed_morse_chart_of_germ_preserving_field (S.data ⟨r.val, hr⟩).chart
        (hothers r hr hrp hrq)
    exact ⟨c, hc ▸ S.critical_model_germ ⟨r.val, hr⟩⟩
  have hout (y : M) (hy : f y ≤ S.toSurgeryWindows.lower p) : g =ᶠ[𝓝 y] f :=
    hexterior y (fun h => h.1.not_ge hy)
  have hbound (y : M) (hy : y ∈ Smale.ManifoldMorse.criticalPoints E g)
    (hfy : S.toSurgeryWindows.lower p ≤ f y) : S.toSurgeryWindows.lower p ≤ g y := by
    by_cases hyp : y = p.val
    · rw [hyp, hgp]
      exact hqband.1.le
    by_cases hyq : y = q.val
    · rw [hyq, hgq]
      exact hpband.1.le
    rw [(hothers y (hcrit ▸ hy) hyp hyq).self_of_nhds]
    exact hfy
  obtain ⟨hsub, hlevel, hgerm⟩ :=
    MorseCancel.lower_cuts_preserved_of_critical_bound hf.continuous hg hal hout hbound
  have hga (y : M) (hy : g y = a) : y ∉ Smale.ManifoldMorse.criticalPoints E g := by
    rw [hcrit]
    exact ha y ((hlevel y).mp hy)
  choose c hc using hnewmodels
  obtain ⟨T₀, hfield₀, hflow₀, -⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow hg hmg hinjg S.smooth S.flow
      S.integral (fun x hx => S.zero x (hcrit ▸ hx)) (fun x hx => hdesc x (hcrit ▸ hx)) c hc
  obtain ⟨T, hfield, hflow, -, hbelow, habove⟩ :=
    T₀.exists_same_flow_windows_avoiding_level hg hmg hga
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hexterior, hothers, hindices,
      MorseCancel.nativeMorseCount_eq_of_preserved_indices hcrit hindices, hsub, hlevel, hgerm,
      hga, T, hfield.trans hfield₀, hflow.trans hflow₀, hbelow, habove⟩

def MorseCancel.equalCutSection {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }) :=
  ⟨fun x => ⟨(γ x).val, (hlevel _).mpr (γ x).property⟩,
    (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩

def MorseCancel.equalCutSublevelHomeomorph {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) : { y : M // f y ≤ a } ≃ₜ { y : M // g y ≤ a }
    where
  toFun y := ⟨y.val, (hsub y).mpr y.property⟩
  invFun y := ⟨y.val, (hsub y).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def MorseCancel.equalCutHomologyEquiv {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // g y ≤ a } 2 :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
    (equalCutSublevelHomeomorph hsub).toHomotopyEquiv 2

theorem MorseCancel.equalCutSection_class {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f g : M → ℝ} {a : ℝ} (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    equalCutHomologyEquiv hsub (middleSectionClass γ) =
      middleSectionClass (equalCutSection hlevel γ) := by
  have hmaps :
    (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun.comp
        ((levelSublevelMap f le_rfl).comp γ) =
      (levelSublevelMap g le_rfl).comp (equalCutSection hlevel γ) := by
    apply ContinuousMap.ext
    intro x
    rfl
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun 2 (middleSectionClass γ) =
      _
  rw [middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, hmaps]
  rfl

theorem MorseCancel.canonicalMiddleMatrix_equalCut {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f g : M → ℝ} {a : ℝ} [Nonempty M] (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    canonicalMiddleMatrix (B.trans (equalCutHomologyEquiv hsub))
        (fun j => equalCutSection hlevel (γ j)) =
      canonicalMiddleMatrix B γ := by
  funext i j
  change
    B.symm ((equalCutHomologyEquiv hsub).symm (middleSectionClass (equalCutSection hlevel (γ j))))
        i =
      B.symm (middleSectionClass (γ j)) i
  rw [← equalCutSection_class hsub hlevel, LinearEquiv.symm_apply_apply]

theorem MorseCancel.nativeMiddleBasinFamily_equalCut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} {a : ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hlevel : ∀ y, g y = a ↔ f y = a) (hflow : T.flow = S.flow) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) :
    IsNativeMiddleBasinFamily T hg hga (fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩)
      (fun j => equalCutSection hlevel (γ j)) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hg hga
  let e := equalLevelDiffeomorph hf hg ha hga hlevel
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hγ
  have hβs (j : Fin n) :
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (equalCutSection hlevel (γ j)) := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (e ∘ γ j)
    exact e.contMDiff.comp (hs j)
  refine ⟨hβs, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (hβs j).continuous.isClosedEmbedding
    change Function.Injective (e ∘ γ j)
    exact e.injective.comp (he j).injective
  · intro j x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e ∘ γ j) x)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp))
        ((hs j).mdifferentiableAt (by simp))]
    exact (e.mfderivToContinuousLinearEquiv (by simp) (γ j x)).injective.comp (hi j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hiy hjy
    obtain ⟨x, hx⟩ := hiy
    obtain ⟨z, hz⟩ := hjy
    have hsame : γ i x = γ j z := e.injective (hx.trans hz.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨z, hsame.symm⟩
  · intro j y
    have hmem : y ∈ Set.range (equalCutSection hlevel (γ j)) ↔ e.symm y ∈ Set.range (γ j) := by
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply e.injective
        exact hx.trans (e.apply_symm_apply y).symm
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem, hfull j]
    rw [hflow]
    rfl

theorem MorseCancel.native_index_order_of_equal_index_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ}
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hequal : nativeMorseIndex E f p = nativeMorseIndex E f q)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g x = f x)
    (hindices :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    ∀ x y : Smale.ManifoldMorse.criticalPoints E g,
      g x < g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y := by
  classical
  have hform (x : Smale.ManifoldMorse.criticalPoints E f) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using
      hothers x x.property (fun h => hxp (Subtype.ext h)) (fun h => hxq (Subtype.ext h))
  have hind (x : Smale.ManifoldMorse.criticalPoints E f) :
    nativeMorseIndex E f (Equiv.swap p q x) = nativeMorseIndex E f x := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hequal.symm
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hequal
    simp only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq]
  intro x y hxy
  let x' : Smale.ManifoldMorse.criticalPoints E f := ⟨x.val, hcrit ▸ x.property⟩
  let y' : Smale.ManifoldMorse.criticalPoints E f := ⟨y.val, hcrit ▸ y.property⟩
  have hxy' : f (Equiv.swap p q x') < f (Equiv.swap p q y') := by
    rw [← hform, ← hform]
    exact hxy
  have hh := horder (Equiv.swap p q x') (Equiv.swap p q y') hxy'
  rw [hind, hind] at hh
  rw [hindices x x'.property, hindices y y'.property]
  exact hh

theorem AdaptedWindows.exists_middle_family_value_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
    [Nonempty M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (i j : Fin n)
    (hij : f (p i) < f (p j))
    (hconsecutive :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, ¬(f (p i) < f z ∧ f z < f (p j))) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
              g (p i) = f (p j) ∧
                g (p j) = f (p i) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      z ≠ (p i).val → z ≠ (p j).val → g z = f z) ∧
                    (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                        g x < g y →
                          MorseCancel.nativeMorseIndex E g x ≤
                            MorseCancel.nativeMorseIndex E g y) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          MorseCancel.nativeMorseIndex E g z =
                            MorseCancel.nativeMorseIndex E f z) ∧
                        (∀ k,
                            MorseCancel.nativeMorseCount E g k =
                              MorseCancel.nativeMorseCount E f k) ∧
                          ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                            ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                              ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                                ∃ T : AdaptedWindows E g,
                                  T.field = S.field ∧
                                    T.flow = S.flow ∧
                                      (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                        let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                          fun k => ⟨(p k).val, hcrit.symm ▸ (p k).property⟩
                                        let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                        let γ' := fun k =>
                                          MorseCancel.equalCutSection hlevel (γ k)
                                        (∀ k, MorseCancel.nativeMorseIndex E g (p' k) = 3) ∧
                                          (∀ k, a < T.toSurgeryWindows.lower (p' k)) ∧
                                            MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                                (fun k => γ' k) ∧
                                              (∀ k x, (γ' k x).val = (γ k x).val) ∧
                                                MorseCancel.canonicalMiddleMatrix B' γ' =
                                                    MorseCancel.canonicalMiddleMatrix B γ ∧
                                                  Function.Surjective
                                                    (MorseCancel.canonicalMiddleMatrix B'
                                                        γ').mulVec := by
  obtain ⟨δ, -, -, -, -, horbit, -⟩ :=
    S.exists_canonical_basin_sphere hf (p j) (hp j) ha (γ j)
      (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩) (hγ.2.2.2.2 j)
  obtain
    ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, -, hothers, hindices, hcounts, hsub, hlevel, hgerm, hga,
      T, hfield, hflow, -, habove⟩ :=
    S.exists_common_cut_value_exchange hf hm ha (p i) (p j) hij hconsecutive (hp j) (hlower i) δ
      horbit
  have hneworder :=
    MorseCancel.native_index_order_of_equal_index_exchange horder (p i) (p j)
      ((hp i).trans (hp j).symm) hcrit hgp hgq
      (fun x hx hxi hxj => (hothers x hx hxi hxj).self_of_nhds) hindices
  have hheight (k : Fin n) : a < g (p k) := by
    by_cases hki : (p k).val = (p i).val
    · rw [hki, hgp]
      exact (hlower j).trans (S.toSurgeryWindows.lower_lt_value (p j))
    by_cases hkj : (p k).val = (p j).val
    · rw [hkj, hgq]
      exact (hlower i).trans (S.toSurgeryWindows.lower_lt_value (p i))
    rw [(hothers (p k) (p k).property hki hkj).self_of_nhds]
    exact (hlower k).trans (S.toSurgeryWindows.lower_lt_value (p k))
  have hmatrix := MorseCancel.canonicalMiddleMatrix_equalCut hsub hlevel B γ
  refine
    ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, (fun z hz hzi hzj => (hothers z hz hzi hzj).self_of_nhds),
      hneworder, hindices, hcounts, hsub, hlevel, hga, T, hfield, hflow, hgerm, ?_, ?_, ?_, ?_,
      hmatrix, ?_⟩
  · intro k
    exact (hindices (p k) (p k).property).trans (hp k)
  · intro k
    exact habove ⟨(p k).val, hcrit.symm ▸ (p k).property⟩ (hheight k)
  · exact MorseCancel.nativeMiddleBasinFamily_equalCut S T hf hg ha hga hcrit hlevel hflow p γ hγ
  · intro k x
    rfl
  · rw [hmatrix]
    exact hsurj

theorem MorseCancel.nativeMiddleBasinFamily_labels_injective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) : Function.Injective p := by
  intro i j hij
  by_contra hne
  let x : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  have hbasin := (hγ.2.2.2.2 i (γ i x)).mp (Set.mem_range_self x)
  have hj : γ i x ∈ Set.range (γ j) := by
    apply (hγ.2.2.2.2 j (γ i x)).mpr
    simpa only [hij] using hbasin
  exact Set.disjoint_left.mp (hγ.2.2.2.1 hne) (Set.mem_range_self x) hj

theorem AdaptedWindows.exists_first_middle_pivot {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
    [Nonempty M] (S₀ : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S₀.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S₀ hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (q : Fin n) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                  MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                (∀ k, MorseCancel.nativeMorseCount E g k = MorseCancel.nativeMorseCount E f k) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ j, j ≠ q → g (p q) < g (p j)) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              T.field = S₀.field ∧
                                T.flow = S₀.flow ∧
                                  (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                    let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                    let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                    let γ' := fun j => MorseCancel.equalCutSection hlevel (γ j)
                                    (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                            (fun j => γ' j) ∧
                                          (∀ j x, (γ' j x).val = (γ j x).val) ∧
                                            MorseCancel.canonicalMiddleMatrix B' γ' =
                                                MorseCancel.canonicalMiddleMatrix B γ ∧
                                              Function.Surjective
                                                (MorseCancel.canonicalMiddleMatrix B'
                                                    γ').mulVec := by
  classical
  have hpinj := MorseCancel.nativeMiddleBasinFamily_labels_injective S₀ hf ha p γ hγ
  let P : ℕ → Prop := fun m =>
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hc : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            ∃ hs : ∀ y, g y ≤ a ↔ f y ≤ a,
              ∃ hl : ∀ y, g y = a ↔ f y = a,
                ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                  ∃ T : AdaptedWindows E g,
                    (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                        g x < g y →
                          MorseCancel.nativeMorseIndex E g x ≤
                            MorseCancel.nativeMorseIndex E g y) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          MorseCancel.nativeMorseIndex E g z =
                            MorseCancel.nativeMorseIndex E f z) ∧
                        (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                            (∀ j, z ≠ (p j).val) → g z = f z) ∧
                          T.field = S₀.field ∧
                            T.flow = S₀.flow ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                (∀ j,
                                    a <
                                      T.toSurgeryWindows.lower
                                        ⟨(p j).val, hc.symm ▸ (p j).property⟩) ∧
                                  Degree.MorseRearrangement.beforeValueRank (fun j => g (p j)) q =
                                    m
  have hex : ∃ m, P m :=
    ⟨Degree.MorseRearrangement.beforeValueRank (fun j => f (p j)) q, f, hf, hm, rfl, fun _ =>
      Iff.rfl, fun _ => Iff.rfl, ha, S₀, horder, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
      fun _ _ => Filter.EventuallyEq.rfl, hlower, rfl⟩
  obtain
    ⟨g, hg, hmg, hcrit, hsub, hlevel, hga, T, hgorder, hindices, houtside, hfield, hflow, hgerm,
      hglower, hrank⟩ :=
    Nat.find_spec hex
  let pg : Fin n → Smale.ManifoldMorse.criticalPoints E g := fun j =>
    ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
  let Bg := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
  let γg := fun j => MorseCancel.equalCutSection hlevel (γ j)
  have hpg (j : Fin n) : MorseCancel.nativeMorseIndex E g (pg j) = 3 :=
    (hindices (p j) (p j).property).trans (hp j)
  have hfamily : MorseCancel.IsNativeMiddleBasinFamily T hg hga pg (fun j => γg j) :=
    MorseCancel.nativeMiddleBasinFamily_equalCut S₀ T hf hg ha hga hcrit hlevel hflow p γ hγ
  have hmatrix :
    MorseCancel.canonicalMiddleMatrix Bg γg = MorseCancel.canonicalMiddleMatrix B γ :=
    MorseCancel.canonicalMiddleMatrix_equalCut hsub hlevel B γ
  have hgsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix Bg γg).mulVec := by
    rw [hmatrix]
    exact hsurj
  have hvalueinj : Function.Injective (fun j => g (p j)) := by
    intro i j hij
    exact hpinj (Subtype.ext (T.distinct (pg i).property (pg j).property hij))
  have hfirst : ∀ j, j ≠ q → g (p q) < g (p j) := by
    intro j hj
    by_contra hnot
    have hjq : g (p j) < g (p q) :=
      lt_of_le_of_ne (le_of_not_gt hnot) (fun heq => hj (hvalueinj heq))
    let K := Finset.univ.filter (fun k => g (p k) < g (p q))
    have hjK : j ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjq⟩
    obtain ⟨i, hi, hmax⟩ := K.exists_max_image (fun k => g (p k)) ⟨j, hjK⟩
    have hiq : g (p i) < g (p q) := (Finset.mem_filter.mp hi).2
    have hconsecutive : ∀ k, ¬(g (p i) < g (p k) ∧ g (p k) < g (p q)) := by
      intro k hk
      exact (not_lt_of_ge (hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.2⟩))) hk.1
    have hglobal :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g (pg i) < g z ∧ g z < g (pg q)) := by
      intro z hz
      have hidx : MorseCancel.nativeMorseIndex E g z = 3 := by
        apply Nat.le_antisymm
        · exact (hgorder z (pg q) hz.2).trans_eq (hpg q)
        · exact (hpg i).symm.trans_le (hgorder (pg i) z hz.1)
      let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : MorseCancel.nativeMorseIndex E f zf = 3 :=
        (hindices z zf.property).symm.trans hidx
      obtain ⟨k, hk⟩ := hcomplete zf hzf
      exact hconsecutive k (by simpa only [hk] using hz)
    obtain
      ⟨u, hu, hmu, hcu, -, hui, huq, huothers, huorder, huindices, -, hus, hul, hua, U, hufield,
        huflow, hugerm, -, hulower, -, -, -, -⟩ :=
      T.exists_middle_family_value_exchange hg hmg hga hgorder pg hpg hglower Bg γg hfamily hgsurj
        i q hiq hglobal
    have hdecrease :
      Degree.MorseRearrangement.beforeValueRank (fun k => u (p k)) q <
        Degree.MorseRearrangement.beforeValueRank (fun k => g (p k)) q := by
      apply
        Degree.MorseRearrangement.beforeValueRank_exchange_lt hvalueinj hiq hconsecutive hui huq
      intro k hki hkq
      apply huothers (pg k) (pg k).property
      · exact fun heq => hki (hpinj (Subtype.ext heq))
      · exact fun heq => hkq (hpinj (Subtype.ext heq))
    have hminimal :=
      Nat.find_min' hex
        (show P (Degree.MorseRearrangement.beforeValueRank (fun k => u (p k)) q) from
          ⟨u, hu, hmu, hcu.trans hcrit, fun y => (hus y).trans (hsub y), fun y =>
            (hul y).trans (hlevel y), hua, U, huorder, fun z hz =>
            (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz), fun z hz hzoutside =>
            (huothers z (hcrit.symm ▸ hz) (hzoutside i) (hzoutside q)).trans
              (houtside z hz hzoutside),
            hufield.trans hfield, huflow.trans hflow, fun y hy =>
            (hugerm y ((hsub y).mpr hy)).trans (hgerm y hy), hulower, rfl⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact
    ⟨g, hg, hmg, hcrit, hgorder, hindices,
      MorseCancel.nativeMorseCount_eq_of_preserved_indices hcrit hindices, houtside, hfirst, hsub,
      hlevel, hga, T, hfield, hflow, hgerm, hpg, hglower, hfamily, fun _ _ => rfl, hmatrix,
      hgsurj⟩

theorem AdaptedWindows.backward_basin_reaches_compact_section {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (α : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val))
    {x : M} (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)) :
    x ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach :=
    S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α
      (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩) hfull
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p hx hback
  let y : (S.data p).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 p.val) :=
    (MorseCancel.flow_time_atBot_limit_iff S.flow t x p.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p y).mp hyback
  apply (Degree.FlowCancellation.levelBasin_flow_iff S.flow f a t x).mp
  change y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a
  rw [← hu]
  exact hreach u

theorem AdaptedWindows.backward_basin_reaches_intermediate_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x p : M}
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) {b : ℝ} (hxb : f x < b)
    (hbp : b < f p) : x ∈ Degree.FlowCancellation.levelBasin S.flow f b := by
  have hh : Filter.Tendsto (fun t => f (S.flow t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hback
  obtain ⟨t, ht⟩ := (hh.eventually (eventually_gt_nhds hbp)).exists
  apply
    mem_range_of_exists_le_of_exists_ge
      (hf.continuous.comp (S.flow.continuous continuous_id continuous_const))
  · refine ⟨0, ?_⟩
    change f (S.flow 0 x) ≤ b
    rw [S.flow.map_zero_apply]
    exact hxb.le
  · exact ⟨t, ht.le⟩

theorem AdaptedWindows.transported_basin_image_of_reaching {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {X : Type} {a b : ℝ}
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M)
    (α : X → { y : M // f y = a }) (β : X → { y : M // f y = b })
    (hfull : ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (α x).val = (β x).val)
    (hreach :
      ∀ y : { z : M // f z = b },
        Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) →
          y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a) :
    ∀ y, y ∈ Set.range β ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact
      (MorseCancel.flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
        ((hfull (α z)).mp (Set.mem_range_self z))
  · intro hy
    obtain ⟨s, hs⟩ := hreach y hy
    let x : { z : M // f z = a } := ⟨S.flow s y.val, hs⟩
    have hx : Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) :=
      (MorseCancel.flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hfull x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

theorem AdaptedWindows.exists_higher_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (j₀ : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3) (hpb : ∀ j, b < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) :
    ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }),
      MorseCancel.IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have hreach (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :
    (α j x).val ∈ Degree.FlowCancellation.levelBasin S.flow f b := by
    apply
      S.backward_basin_reaches_intermediate_cut hf ((hfull j (α j x)).mp (Set.mem_range_self x))
    · simpa only [(α j x).property] using hab
    · exact hpb j
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨t₀, ht₀⟩ := hreach j₀ x₀
  obtain ⟨β, hβs, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb (α j₀ x₀) ⟨S.flow t₀ (α j₀ x₀).val, ht₀⟩
      (fun j => α j) hs (fun j => (he j).injective) hi hpair hreach
  refine ⟨fun j => ⟨β j, (hβs j).continuous⟩, ⟨hβs, hβe, hβi, hβpair, ?_⟩, horbit⟩
  intro j
  apply S.transported_basin_image_of_reaching hf hb (p j).val (α j) (β j) (hfull j) (horbit j)
  intro y hy
  exact
    S.backward_basin_reaches_compact_section hf (p j) (hp j) ha (α j) (hfull j)
      (hb y.val y.property) hy

theorem AdaptedWindows.upper_point_not_on_belt_of_lower_orbit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (ha : a < f q) (x : { y : M // f y = a }) (y : (S.data q).UpperLevel)
    (horbit : ∃ t : ℝ, S.flow t x.val = y.val) : y ∉ Set.range (S.data q).surgery.beltSphere := by
  intro hy
  have hyforward := (S.belt_basin_iff hf q y).mpr hy
  obtain ⟨t, ht⟩ := horbit
  have hxforward : Filter.Tendsto (fun s => S.flow s x.val) Filter.atTop (𝓝 q.val) := by
    rw [← ht] at hyforward
    exact (MorseCancel.flow_time_atTop_limit_iff S.flow t x.val q.val).mp hyforward
  have hheight : Filter.Tendsto (fun s => f (S.flow s x.val)) Filter.atTop (𝓝 (f q)) :=
    hf.continuous.continuousAt.tendsto.comp hxforward
  have hh :=
    (Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
          x.val).le_of_tendsto
      hheight 0
  have hqa : f q ≤ a := by simpa only [S.flow.map_zero_apply, x.property] using hh
  exact ha.not_ge hqa

theorem MorseCancel.lower_backward_basins_preserved {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry :
      ∀ x,
        Set.range (fun t => H t x) = Set.range (fun t => S.flow t x) ∧
          (∀ p,
              Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
                Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p)) ∧
            ∀ p,
              Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p) ↔
                Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y) (p : M) (hp : f p ≤ l) :
    (∀ x,
        Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) ∧
      ∀ x,
        Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p) →
          Set.range (fun t => T.flow t x) = Set.range (fun t => S.flow t x) := by
  have hnew (x : M) (hx : Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p)) :
    ∀ t, T.flow t x = H t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x
    have hagree (t : ℝ) : T.field (T.flow t x) = W (T.flow t x) :=
      hout _ ((hmono.ge_of_tendsto hheight t).trans hp)
    intro t
    rcases le_total 0 t with ht | ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp)) H T.flow
          hH T.integral (fun s _ => hagree s) t ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_negative_halfline (hW.of_le (by simp)) H T.flow
          hH T.integral (fun s _ => hagree s) t ht
  have hold (x : M) (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) :
    ∀ t, H t x = T.flow t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    have hbound (t : ℝ) : f (H t x) ≤ l := by
      have hm : H t x ∈ Set.range (fun s => S.flow s x) := (hgeometry x).1 ▸ Set.mem_range_self t
      obtain ⟨s, hs⟩ := hm
      rw [← hs]
      exact (hmono.ge_of_tendsto hheight s).trans hp
    have hagree (t : ℝ) : W (H t x) = T.field (H t x) := (hout _ (hbound t)).symm
    intro t
    rcases le_total 0 t with ht | ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_positive_halfline (T.smooth.of_le (by simp))
          T.flow H T.integral hH (fun s _ => hagree s) t ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_negative_halfline (T.smooth.of_le (by simp))
          T.flow H T.integral hH (fun s _ => hagree s) t ht
  refine ⟨?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have heq : (fun t => T.flow t x) = fun t => H t x := funext (hnew x hx)
      rw [heq] at hx
      exact ((hgeometry x).2.2 p).mp hx
    · intro hx
      have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
      have hh := ((hgeometry x).2.2 p).mpr hx
      rwa [heq] at hh
  · intro x hx
    have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
    rw [← heq]
    exact (hgeometry x).1

theorem MorseCancel.lower_forward_basins_preserved {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y) (y : M) (hy : f y ≤ l) :
    ∀ p,
      Filter.Tendsto (fun t => T.flow t y) Filter.atTop (𝓝 p) ↔
        Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p) := by
  have hmono :=
    Smale.FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent y
  have hbound (t : ℝ) (ht : 0 ≤ t) : f (T.flow t y) ≤ l := by
    have hh := hmono ht
    change f (T.flow t y) ≤ f (T.flow 0 y) at hh
    rw [T.flow.map_zero_apply] at hh
    exact hh.trans hy
  have heq : (fun t => T.flow t y) =ᶠ[Filter.atTop] (fun t => H t y) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact
      Degree.FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp)) H T.flow hH
        T.integral (fun s hs => hout _ (hbound s hs)) t ht
  intro p
  exact (Filter.tendsto_congr' heq).trans (hgeometry y p)

theorem AdaptedWindows.reaches_cut_of_forward_holonomy {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (D : { y : M // f y = b } → { y : M // f y = b })
    (hforward :
      ∀ x : { y : M // f y = b },
        ∀ p : M,
          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p))
    (x : { y : M // f y = b }) (y : { z : M // f z = a })
    (horbit : ∃ t : ℝ, S.flow t (D x).val = y.val) :
    x.val ∈ Degree.FlowCancellation.levelBasin T.flow f a := by
  obtain ⟨p, hp, q, hq, -, hytop, hyheight⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hqa : f q < a := by simpa only [y.property] using (hyheight (ha y.val y.property)).1
  obtain ⟨t, ht⟩ := horbit
  have hDx : Filter.Tendsto (fun s => S.flow s (D x).val) Filter.atTop (𝓝 q) := by
    rw [← ht] at hytop
    exact (MorseCancel.flow_time_atTop_limit_iff S.flow t (D x).val q).mp hytop
  have hxtop := (hforward x q).mpr hDx
  obtain ⟨r, hr, s, hs, hxback, -, hxheight⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
      T.descent T.distinct x.val
  have hbr : b < f r := by simpa only [x.property] using (hxheight (hb x.val x.property)).2
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits T.flow hf.continuous hxback
      hxtop (hab.trans hbr) hqa

theorem AdaptedWindows.exists_relative_surgery_cut_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (z : (S.data q).UpperLevel)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K P : Set (S.data q).UpperLevel),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K P →
          ∃ T : AdaptedWindows E f,
            (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < ε p) ∧
                (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f,
                    ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
                  (∀ x : (S.data q).UpperLevel,
                      ∀ p : M,
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
                          Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p)) ∧
                    (∀ x : (S.data q).UpperLevel,
                        ∀ p : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
                            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        (∀ x : (S.data q).UpperLevel,
                            ∀ {b : ℝ},
                              b < f q →
                                (∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) →
                                  ∀ y : { z : M // f z = b },
                                    (∃ t : ℝ, T.flow t x.val = y.val) ↔
                                      ∃ t : ℝ, S.flow t (D x).val = y.val) ∧
                          ∀ p : M,
                            f p ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t p) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t p) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro D K P hK I
  obtain ⟨l, u, hl, hu, hband⟩ := S.regular_interval_around_level (S.data q).upper_regular
  have hql : f q < l := by
    by_contra h
    exact
      hband q ⟨le_of_not_gt h, (S.toSurgeryWindows.value_lt_upper q).le.trans hu.le⟩ q.property
  obtain
    ⟨r, C, W, V, H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright, hprotected⟩ :=
    Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hu hband (S.data q).upper_regular z D K P hK I
  have hmodel (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct hV G hG
      (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback₀, hforward₀⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val D
      (fun x p => (hgeometry x).2.1 p) (fun x p => (hgeometry x).2.2 p) hend hleft hright
  have hback (x : (S.data q).UpperLevel) (p : M) :
    Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
      Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) := by
    rw [hflow]
    exact hback₀ x p
  have hforward (x : (S.data q).UpperLevel) (p : M) :
    Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
      Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p) := by
    rw [hflow]
    exact hforward₀ x p
  have hlowexit {b : ℝ} (hb : b < f q) : b < S.toSurgeryWindows.upper q - r := by
    have hr' : r < S.toSurgeryWindows.upper q - l := hrbound
    linarith
  have htransport (x : (S.data q).UpperLevel) {b : ℝ} (hb : b < f q) (y : { z : M // f z = b })
    (hxy : ∃ t : ℝ, T.flow t x.val = y.val) : ∃ t : ℝ, S.flow t (D x).val = y.val := by
    obtain ⟨t, ht⟩ := hxy
    have hstart : f (T.flow 1 x.val) = S.toSurgeryWindows.upper q - r := by
      rw [hflow, hend, hheight]
      rfl
    have htone : 1 < t := by
      by_contra h
      have hh :=
        (Smale.FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x.val)
          (le_of_not_gt h)
      change f (T.flow 1 x.val) ≤ f (T.flow t x.val) at hh
      rw [hstart, ht, y.property] at hh
      exact (hlowexit hb).not_ge hh
    have heq : G t x.val = H t (D x).val := by
      calc
        G t x.val = G (t - 1) (G 1 x.val) := by rw [← G.map_add, sub_add_cancel]
        _ = H (t - 1) (H 1 (D x).val) := by
          rw [hend, hright (D x) (t - 1) (sub_nonneg.mpr htone.le)]
        _ = H t (D x).val := by rw [← H.map_add, sub_add_cancel]
    have hmem : H t (D x).val ∈ Set.range (fun s => S.flow s (D x).val) :=
      (hgeometry (D x).val).1 ▸ Set.mem_range_self t
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.trans (heq.symm.trans (hflow ▸ ht))⟩
  refine ⟨T, hcharts, hradii, ?_, hback, hforward, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = fun t => H t x.val := funext (hprotected x hx)
    rw [heq]
    exact (hgeometry x.val).1
  · intro x b hbq hb y
    refine ⟨htransport x hbq y, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ :=
      S.reaches_cut_of_forward_holonomy T hf (hbq.trans (S.toSurgeryWindows.value_lt_upper q)) hb
        (S.data q).upper_regular D hforward x y ⟨t, ht⟩
    let y' : { z : M // f z = b } := ⟨T.flow s x.val, hs⟩
    obtain ⟨v, hv⟩ := htransport x hbq y' ⟨s, rfl⟩
    have hshared : S.flow 0 y'.val = S.flow (v - t) y.val := by
      rw [S.flow.map_zero_apply, ← hv, ← ht, ← S.flow.map_add, sub_add_cancel]
    have heq : y'.val = y.val :=
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) y'.property y.property hshared
    exact ⟨s, heq⟩
  · intro p hp
    have hlow (y : M) (hy : f y ≤ l) : T.field y = W y := by
      rw [hfield]
      exact (houtside y (fun h => (hCband h).1.not_ge hy)).self_of_nhds
    have hb :=
      MorseCancel.lower_backward_basins_preserved S T hf hW H hH hgeometry hlow p
        (hp.trans hql.le)
    exact
      ⟨hb.1, hb.2,
        MorseCancel.lower_forward_basins_preserved S T hf hW H hH (fun x v => (hgeometry x).2.1 v)
          hlow p (hp.trans hql.le)⟩

theorem AdaptedWindows.exists_relative_family_lower_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => α j))
    (havoid : ∀ j, Disjoint (Set.range (α j)) (Set.range (S.data q).surgery.beltSphere))
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K : Set (S.data q).UpperLevel),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K
            (Degree.MorseRearrangement.otherSheetImages (fun j => α j) i) →
          (∀ j, Disjoint (Set.range (D ∘ α j)) (Set.range (S.data q).surgery.beltSphere)) →
            ∃ T : AdaptedWindows E f,
              (∀ z, (T.data z).chart = (S.data z).chart) ∧
                (∀ z, (T.data z).radius < ε z) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                    ∃ β δ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel),
                      MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p
                          (fun j => β j) ∧
                        MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p
                            (fun j => δ j) ∧
                          (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                            (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (δ j x).val) ∧
                              (∀ j x, ∃ t : ℝ, S.flow t (D (α j x)).val = (δ j x).val) ∧
                                (∀ j, j ≠ i → δ j = β j) ∧
                                  (∀ j,
                                      j ≠ i →
                                        ∀ x,
                                          Set.range (fun t => T.flow t (α j x).val) =
                                            Set.range (fun t => S.flow t (α j x).val)) ∧
                                    ∀ z : M,
                                      f z ≤ f q →
                                        (∀ x,
                                            Filter.Tendsto (fun t => T.flow t x) Filter.atBot
                                                (𝓝 z) ↔
                                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot
                                                (𝓝 z)) ∧
                                          (∀ x,
                                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot
                                                  (𝓝 z) →
                                                Set.range (fun t => T.flow t x) =
                                                  Set.range (fun t => S.flow t x)) ∧
                                            ∀ v,
                                              Filter.Tendsto (fun t => T.flow t z) Filter.atTop
                                                  (𝓝 v) ↔
                                                Filter.Tendsto (fun t => S.flow t z) Filter.atTop
                                                  (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  dsimp only
  intro D K hK I hDavoid
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  let u :=
    Smale.SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected, hcut, hkeep⟩ :=
    S.exists_relative_surgery_cut_transport hf hm q (α i x₀) ε hε D K
      (Degree.MorseRearrangement.otherSheetImages (fun j => α j) i) hK I
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have holdreach (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :=
    S.belt_complement_reaches_lower_level hf q (α j x)
      (fun h => Set.disjoint_left.mp (havoid j) (Set.mem_range_self x) h)
  have hnewreach (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :=
    S.reaches_old_lower_of_belt_avoidance T hf q D hforward (α j x)
      (fun h => Set.disjoint_left.mp (hDavoid j) (Set.mem_range_self x) h)
  obtain ⟨β₀, hβs, hβe, hβi, hβpair, hβflow⟩ :=
    S.exists_native_family_level_transport hf (S.data q).upper_regular (S.data q).lower_regular
      (α i x₀) ((S.data q).surgery.attachingSphere u) (fun j => α j) hs
      (fun j => (he j).injective) hi hpair holdreach
  obtain ⟨δ₀, hδs, hδe, hδi, hδpair, hδflow⟩ :=
    T.exists_native_family_level_transport hf (S.data q).upper_regular (S.data q).lower_regular
      (α i x₀) ((S.data q).surgery.attachingSphere u) (fun j => α j) hs
      (fun j => (he j).injective) hi hpair hnewreach
  let β : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel) := fun j =>
    ⟨β₀ j, (hβs j).continuous⟩
  let δ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel) := fun j =>
    ⟨δ₀ j, (hδs j).continuous⟩
  have hδold (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :
    ∃ t : ℝ, S.flow t (D (α j x)).val = (δ j x).val :=
    (hcut (α j x) (S.toSurgeryWindows.lower_lt_value q) (S.data q).lower_regular (δ j x)).mp
      (hδflow j x)
  have hab := (S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q)
  refine ⟨T, hcharts, hradii, hgerms, β, δ, ?_, ?_, hβflow, hδflow, hδold, ?_, ?_, hkeep⟩
  · refine ⟨hβs, hβe, hβi, hβpair, ?_⟩
    intro j
    exact
      S.transported_backward_basin_image hf hab (S.data q).lower_regular (p j).val (hhigh j) (α j)
        (β j) (hfull j) (hβflow j)
  · refine ⟨hδs, hδe, hδi, hδpair, ?_⟩
    intro j
    apply
      T.transported_backward_basin_image hf hab (S.data q).lower_regular (p j).val (hhigh j) (α j)
        (δ j) ?_ (hδflow j)
    intro x
    exact (hfull j x).trans (hback x (p j).val).symm
  · intro j hji
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, hs⟩ := hδold j x
    have hfix : D (α j x) = α j x :=
      I.endpoint_fixed_on (α j x)
        (Degree.MorseRearrangement.mem_otherSheetImages (fun j => α j) i j hji x)
    rw [hfix] at hs
    obtain ⟨t, ht⟩ := hβflow j x
    change S.flow t (α j x).val = (β j x).val at ht
    have hshared : S.flow 0 (δ j x).val = S.flow (s - t) (β j x).val := by
      rw [S.flow.map_zero_apply, ← hs, ← ht, ← S.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z ((S.data q).lower_regular z hz)) (δ j x).property
        (β j x).property hshared
  · intro j hji x
    exact
      hprotected (α j x) (Degree.MorseRearrangement.mem_otherSheetImages (fun j => α j) i j hji x)

theorem AdaptedWindows.section_class_of_flow_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (β : C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }))
    (α : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val) :
    SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab.le) 2
        (MorseCancel.middleSectionClass α) =
      MorseCancel.middleSectionClass β := by
  have hm :=
    PeriodTorusHigherHomology.homotopic_homologyMap
      (S.level_transport_homotopic_in_sublevel hf hab ha β α horbit) 2
  have hmaps :
    (MorseCancel.sublevelMap f hab.le).comp ((MorseCancel.levelSublevelMap f le_rfl).comp α) =
      (MorseCancel.levelSublevelMap f hab.le).comp α := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [MorseCancel.middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, hmaps, ← hm]
  rfl

theorem MorseCancel.signed_relation_of_regular_cut_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (β δ γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }))
    (α ζ θ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (k : ℤ)
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val)
    (hδ : ∀ x, ∃ t : ℝ, T.flow t (δ x).val = (ζ x).val)
    (hγ : ∀ x, ∃ t : ℝ, S.flow t (γ x).val = (θ x).val)
    (hmap :
      SingularMayerVietoris.singularHomologyMap δ 2 =
        SingularMayerVietoris.singularHomologyMap β 2 +
          k • SingularMayerVietoris.singularHomologyMap γ 2) :
    middleSectionClass ζ = middleSectionClass α + k • middleSectionClass θ := by
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap γ 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap γ 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap γ 2)
  have hclasses : middleSectionClass δ = middleSectionClass β + k • middleSectionClass γ := by
    simp only [middleSectionClass, PeriodTorusHigherHomology.singularHomologyMap_comp,
      LinearMap.comp_apply, hmap, LinearMap.add_apply, heval, map_add, map_zsmul]
  apply (regular_sublevel_inclusion_bijective hf hab.le hband 2).1
  rw [map_add, map_zsmul, T.section_class_of_flow_transport hf hab ha δ ζ hδ,
    S.section_class_of_flow_transport hf hab ha β α hβ,
    S.section_class_of_flow_transport hf hab ha γ θ hγ]
  exact hclasses

theorem MorseCancel.same_image_sphere_maps_unit {Y : Type} [TopologicalSpace Y]
    (α β : C((Smale.Hemisphere.Sphere 2), Y)) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap β 2 =
          k • SingularMayerVietoris.singularHomologyMap α 2 := by
  let e : (Smale.Hemisphere.Sphere 2) ≃ₜ (Smale.Hemisphere.Sphere 2) :=
    hβ.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans hα.toHomeomorph.symm)
  have heq : α.comp (e : C((Smale.Hemisphere.Sphere 2), (Smale.Hemisphere.Sphere 2))) = β := by
    apply ContinuousMap.ext
    intro x
    have hh :=
      congrArg Subtype.val
        (hα.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hβ.toHomeomorph x)))
    exact hh
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (e : C((Smale.Hemisphere.Sphere 2), (Smale.Hemisphere.Sphere 2))) 2) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv e 2).bijective
  obtain ⟨k, hk, hu⟩ :=
    two_sphere_map_unit_of_homology_bijective (Homeomorph.refl (Smale.Hemisphere.Sphere 2))
      (e : C((Smale.Hemisphere.Sphere 2), (Smale.Hemisphere.Sphere 2))) hbij
  rcases hk with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul] at hu ⊢
    rw [← heq, PeriodTorusHigherHomology.singularHomologyMap_comp, hu]
    change
      (SingularMayerVietoris.singularHomologyMap α 2).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.id (Smale.Hemisphere.Sphere 2)) 2) =
        _
    rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.comp_id]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_zsmul] at hu ⊢
    rw [← heq, PeriodTorusHigherHomology.singularHomologyMap_comp, hu, LinearMap.comp_neg]
    change
      -((SingularMayerVietoris.singularHomologyMap α 2).comp
            (SingularMayerVietoris.singularHomologyMap
              (ContinuousMap.id (Smale.Hemisphere.Sphere 2)) 2)) =
        _
    rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.comp_id]

theorem MorseCancel.same_image_section_classes_unit {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} {a : ℝ}
    (α β : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ middleSectionClass β = k • middleSectionClass α := by
  obtain ⟨k, hk, hm⟩ := same_image_sphere_maps_unit α β hα hβ hrange
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap α 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap α 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap α 2)
  refine ⟨k, hk, ?_⟩
  simp only [middleSectionClass, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, hm, heval, map_zsmul]

theorem MorseCancel.nativeMiddleBasinFamily_replace_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (αq βq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily : IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (hrange : Set.range βq = Set.range αq) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ βq →
      Topology.IsClosedEmbedding βq →
        (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) βq x)) →
          IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases βq (fun j => α j)) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  dsimp only
  intro hβs hβe hβi
  have hr (j : Fin (n + 1)) :
    Set.range (Fin.cases βq (fun j => α j) j) = Set.range (Fin.cases αq (fun j => α j) j) := by
    cases j using Fin.cases with
    | zero => exact hrange
    | succ j => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hβs
    | succ j => exact hfamily.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβe
    | succ j => exact hfamily.2.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβi
    | succ j => exact hfamily.2.2.1 j.succ
  · intro j k hjk
    rw [hr j, hr k]
    exact hfamily.2.2.2.1 hjk
  · intro j y
    rw [hr j]
    exact hfamily.2.2.2.2 j y

theorem MorseCancel.mul_transvection_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (hij : i ≠ j) (k : ℤ) (hA : Function.Surjective A.mulVec) :
    Function.Surjective (A * Matrix.transvection i j k).mulVec := by
  intro y
  obtain ⟨z, hz⟩ := hA y
  refine ⟨(Matrix.transvection i j (-k)).mulVec z, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.transvection_mul_transvection_same i j hij,
    add_neg_cancel, Matrix.transvection_zero, Matrix.mul_one]
  exact hz

theorem MorseCancel.eq_mul_transvection_of_columns {r n : ℕ} (A A' : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (k : ℤ) (hchanged : ∀ u, A' u j = A u j + k * A u i)
    (hother : ∀ u v, v ≠ j → A' u v = A u v) : A' = A * Matrix.transvection i j k := by
  funext u v
  by_cases hv : v = j
  · subst v
    exact (hchanged u).trans (Matrix.mul_transvection_apply_same i j u k A).symm
  · exact (hother u v hv).trans (Matrix.mul_transvection_apply_of_ne i j u v hv k A).symm

theorem MorseCancel.exists_sheet_arc_tube_with_normal_change {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O)
    (C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart (C.prodCongr R) Φ₁) ∧
                  Φ.target ⊆ O := by
  let Φ₂ :=
    linearTransverseChart (C.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))))
      Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hright₂ : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₂ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.trans (linearTransverseChart_axis _ Φ₁ t).symm
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, htarget⟩ :=
    exists_sheet_arc_tube ha hinj hi hdim Φ₀ Φ₂ hΦ₀ hΦ₂ hleft hright₂ hO haO
  refine ⟨R, ε, hε, Φ, hprod, haxis, hgl, ?_, htarget⟩
  filter_upwards [hgr] with z hz
  exact hz

theorem MorseCancel.exists_clean_sheet_arc_tube_with_normal_change {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {S T O : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (hrec₀ : ∀ z ∈ Φ₀.source, Φ₀ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrec₁ : ∀ z ∈ Φ₁.source, Φ₁ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0)
    (hcount₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ S ↔ t = 0)
    (hcount₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ T ↔ t = 1) (hO : IsOpen O)
    (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O)
    (C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart (C.prodCongr R) Φ₁) ∧
                  (∀ z ∈ Φ.source, Φ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                    (∀ z ∈ Φ.source, Φ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0) ∧ Φ.target ⊆ O := by
  obtain ⟨R, r, hr, Ψ, hΨprod, haxis, hgl, hgr, hΨO⟩ :=
    exists_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright hO haO C
  let Φ₂ := linearTransverseChart (C.prodCongr R) Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hrec₂ : ∀ z ∈ Φ₂.source, Φ₂ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Φ₁ (z.1, (C z.2.1, R z.2.2)) ∈ T ↔ _
    rw [hrec₁ (z.1, (C z.2.1, R z.2.2)) hz.2, map_eq_zero_iff C C.injective]
  have hlocal₀ :
    ∀ᶠ z : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) in
      𝓝 (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))),
      Ψ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0 := by
    filter_upwards [hgl, Φ₀.open_source.mem_nhds hΦ₀] with z he hz
    rw [he]
    exact hrec₀ z hz
  have hlocal₁ :
    ∀ᶠ z : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) in
      𝓝 ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))),
      Ψ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    filter_upwards [hgr, Φ₂.open_source.mem_nhds hΦ₂] with z he hz
    rw [he]
    exact hrec₂ z hz
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΨprod ⟨ht, Metric.mem_closedBall_self hr.le⟩
  have haway₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ 0 → Ψ (t, 0) ∉ S := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₀ t ht).mp hh)
  have haway₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ 1 → Ψ (t, 0) ∉ T := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₁ t ht).mp hh)
  obtain ⟨ε, hε, Φ, hprod, hformula, hΦΨ, hrecS, hrecT⟩ :=
    exists_clean_axis_tube_restriction Ψ CompactIccSpace.isCompact_Icc hzero hS hT 0 1
      {v : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) | v.2 = 0}
      {v : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) | v.1 = 0} hlocal₀ hlocal₁
      haway₀ haway₁
  refine
    ⟨R, ε, hε, Φ, hprod, fun t => (hformula _).trans (haxis t), ?_, ?_, hrecS, hrecT,
      hΦΨ.trans hΨO⟩
  · filter_upwards [hgl] with z hz
    exact (hformula z).trans hz
  · filter_upwards [hgr] with z hz
    exact (hformula z).trans hz

theorem MorseCancel.exists_relative_sheet_passages_with_normal_change {E M X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    {f : X → M} {g : Y → M} {b : Z → M} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g) (hfe : Topology.IsEmbedding f)
    (hge : Topology.IsEmbedding g) (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (Set.range f) (Set.range g)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hbx : f x ∉ Set.range b) (hby : g y ∉ Set.range b) (γ : Path (f x) (g y)) :
    ∃ Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source ∧
        ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source ∧
          Φ₀ 0 = f x ∧
            Φ₁ (1, 0) = g y ∧
              (∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                (∀ z ∈ Φ₁.source, Φ₁ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                  ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
                    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
                      0 < ε ∧
                        ∃ Φ :
                          PartialDiffeomorph
                            𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
                            𝓘(ℝ, E)
                            (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
                          ∃ A : LongitudinalTubeMotion Φ,
                            Set.Icc (0 : ℝ) 1 ×ˢ
                                  Metric.closedBall
                                    (0 :
                                      ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                                    ε ⊆
                                Φ.source ∧
                              Φ 0 = f x ∧
                                Φ (1, 0) = g y ∧
                                  ((Φ :
                                        (ℝ ×
                                            ((EuclideanSpace ℝ (Fin 2)) ×
                                              (EuclideanSpace ℝ (Fin 2)))) →
                                          M) =ᶠ[𝓝
                                        (0 :
                                          (ℝ ×
                                            ((EuclideanSpace ℝ (Fin 2)) ×
                                              (EuclideanSpace ℝ (Fin 2)))))]
                                      Φ₀) ∧
                                    ((Φ :
                                          (ℝ ×
                                              ((EuclideanSpace ℝ (Fin 2)) ×
                                                (EuclideanSpace ℝ (Fin 2)))) →
                                            M) =ᶠ[𝓝
                                          ((1 : ℝ),
                                            (0 :
                                              ((EuclideanSpace ℝ (Fin 2)) ×
                                                (EuclideanSpace ℝ (Fin 2)))))]
                                        linearTransverseChart (C.prodCongr R) Φ₁) ∧
                                      (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                                        (∀ z ∈ Φ.source,
                                            Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                                          Φ.target ⊆ (Set.range b)ᶜ ∧
                                            (∀ t z, z ∈ Set.range b → A.family (t, z) = z) ∧
                                              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                                  ∀ u : X,
                                                    ∀ v : Y,
                                                      A.family (t, f u) = g v ↔
                                                        t = A.time ∧ u = x ∧ v = y) ∧
                                                Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2))
                                                  (𝓡 2) 𝓘(ℝ, E)
                                                  (fun p : ℝ × X => A.family (p.1, f p.2)) g
                                                  (A.time, x) y := by
  have hx : f x ∉ Set.range g := fun h => (Set.disjoint_left.mp hdisj) ⟨x, rfl⟩ h
  have hy : g y ∉ Set.range f := fun h => (Set.disjoint_left.mp hdisj) h ⟨y, rfl⟩
  obtain
    ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, a, ha, hleft, hright, hemb, hi, hcount₀, hcount₁,
      haO⟩ :=
    exists_clean_two_sheet_arc_avoiding hf hg hfe hge hfi hgi hb hbc hdim x y hx hy hbx hby γ
  refine ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, ?_⟩
  intro C
  have hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, hrecf, hrecg, hΦO⟩ :=
    exists_clean_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright
      (isCompact_range hf.continuous).isClosed (isCompact_range hg.continuous).isClosed hrec₀
      hrec₁ hcount₀ hcount₁ hbc.isOpen_compl haO C
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, Metric.mem_closedBall_self hε.le⟩
  have h0 : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source :=
    hzero ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have hfx : Φ 0 = f x := (haxis 0).trans (hleft.eq_of_nhds.trans hΦx)
  have hgy : Φ (1, 0) = g y := (haxis 1).trans (hright.eq_of_nhds.trans hΦy)
  obtain ⟨A⟩ := nonempty_longitudinalTubeMotion Φ hzero
  refine
    ⟨R, ε, hε, Φ, A, hprod, hfx, hgy, hgl, hgr, hrecf, hrecg, hΦO, ?_,
      A.whole_sheet_crossing_iff hfe.injective hge.injective hdisj hrecf hrecg x y hfx hgy h0,
      A.whole_sheet_transverse (hf.mdifferentiable (by simp) x) (hg.mdifferentiable (by simp) y)
        (hfi x) (hgi y) hrecf hrecg hfx hgy h0⟩
  intro t z hz
  exact A.fixed_outside_target t z (fun h => hΦO h hz)

theorem MorseCancel.LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs {U V E M X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace X] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞) (C : U ≃L[ℝ] U)
    (R : V ≃L[ℝ] V) {f : X → M} {x : X} (hf : ContinuousAt f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright :
      (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
        MorseCancel.linearTransverseChart (C.prodCongr R) Φ₁) :
    (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)] fun p =>
      Φ₁ (Real.smoothTransition p.1 * A.destination, (C (Φ₀.symm (f p.2)).2.1, 0)) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : ContinuousAt a x :=
    (Φ₀.symm.contMDiffOn_toFun.continuousOn.continuousAt (Φ₀.open_target.mem_nhds hfx)).comp hf
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hat : Filter.Tendsto a (𝓝 x) (𝓝 (0 : W)) := by simpa only [ha0] using ha.tendsto
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ₀.target := hf.eventually (Φ₀.open_target.mem_nhds hfx)
  have hplane : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrec (a q) (Φ₀.map_target hq)).mp ⟨q, (Φ₀.right_inv hq).symm⟩
  have hat' : Filter.Tendsto (fun p : ℝ × X => a p.2) (𝓝 (A.time, x)) (𝓝 (0 : W)) :=
    hat.comp continuous_snd.continuousAt
  have hpair :
    Filter.Tendsto (fun p : ℝ × X => (p.1, a p.2)) (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) :=
    continuous_fst.continuousAt.prodMk_nhds hat'
  let z : ℝ × X → W := fun p => (Real.smoothTransition p.1 * A.destination, ((a p.2).2.1, 0))
  have hap : ContinuousAt (fun p : ℝ × X => a p.2) (A.time, x) :=
    ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha continuousAt_snd
  have hz : ContinuousAt z (A.time, x) :=
    ((Real.smoothTransition.continuous.continuousAt.comp continuousAt_fst).mul
          continuousAt_const).prodMk
      (hap.snd.fst.prodMk continuousAt_const)
  have hz0 : z (A.time, x) = (1, 0) := by
    simp only [z, A.time_value, ha0, Prod.fst_zero, Prod.snd_zero]
    rfl
  have hzt : Filter.Tendsto z (𝓝 (A.time, x)) (𝓝 ((1 : ℝ), (0 : U × V))) := by
    simpa only [hz0] using hz.tendsto
  filter_upwards [hpair.eventually (A.native_germ h0 A.time), hat'.eventually hleft,
    continuous_snd.continuousAt.eventually hfn, continuous_snd.continuousAt.eventually hplane,
    hzt.eventually hright] with p hm hl hf' hp hr
  have hpoint : Φ (a p.2) = f p.2 := hl.trans (Φ₀.right_inv hf')
  calc
    A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
      congrArg (fun y => A.family (p.1, y)) hpoint.symm
    _ = Φ ((a p.2).1 + Real.smoothTransition p.1 * A.destination, (a p.2).2) := hm
    _ = Φ (z p) := by
      apply congrArg Φ
      rw [hp.1, zero_add]
      exact Prod.ext rfl (Prod.ext rfl hp.2)
    _ = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (Φ₀.symm (f p.2)).2.1, 0)) := by
      change Φ (z p) = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, 0))
      rw [hr]
      change Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, R 0)) = _
      rw [map_zero]

theorem MorseCancel.exists_centered_passage_clock {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D 0 = 0 ∧
        D 1 = 1 ∧
          D (1 / 2) = τ ∧
            StrictMono D ∧
              Set.MapsTo D (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ∧
                ((D : ℝ → ℝ) =ᶠ[𝓝 (1 / 2 : ℝ)] fun t => t + (τ - 1 / 2)) ∧
                  HasDerivAt (D : ℝ → ℝ) 1 (1 / 2) := by
  obtain ⟨D, hfix, hgerm, hpoint, hmono, -⟩ :=
    Degree.MorseRearrangement.exists_increasing_interval_translation
      (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by constructor <;> norm_num) hτ
  have h0 : D 0 = 0 := hfix 0 (by simp)
  have h1 : D 1 = 1 := hfix 1 (by simp)
  refine ⟨D, h0, h1, hpoint, hmono, ?_, hgerm, ?_⟩
  · intro t ht
    exact ⟨h0 ▸ hmono.monotone ht.1, h1 ▸ hmono.monotone ht.2⟩
  · exact ((hasDerivAt_id (1 / 2 : ℝ)).add_const (τ - 1 / 2)).congr_of_eventuallyEq hgerm

theorem MorseCancel.exists_radial_link_meridian_with_derivative {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    (H : C(ℝ × (Smale.Hemisphere.Sphere 2), d.UpperLevel)) {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (x₀ : (Smale.Hemisphere.Sphere 2)) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (hpoint : d.surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Smale.Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range d.surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) => d.beltNormal (H (radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (τ, x₀) →
      ∃ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
        ∃ (w : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (β :
          C((Smale.Hemisphere.Sphere 2), Metric.sphere (0 : d.chart.NegativeCoordinates) 1)),
          SingularMayerVietoris.singularHomologyMap β 2 =
              SingularMayerVietoris.singularHomologyMap
                (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 ∧
            ((Degree.PassageHomology.puncturedPassageTrace H (Set.range d.surgery.beltSphere) hτ
                      x₀ hcross).comp
                  (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)).Homotopic
              ((nativeBeltTubeMeridian d w (1 / 2) (by norm_num) (by norm_num)).comp β) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hg
  let Ψ := radialParameterChart τ x₀
  have hΨ0 : (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Ψ.source :=
    radialParameterChart_zero_mem_source τ x₀
  have hΨ : ContMDiffAt (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Ψ 0 :=
    Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hΨ0)
  have hΨc : ContinuousAt Ψ 0 := hΨ.continuousAt
  have htime :
    (fun z : (EuclideanSpace ℝ (Fin 3)) => (Ψ z).1) ⁻¹' Set.Ioo (0 : ℝ) 1 ∈
      𝓝 (0 : (EuclideanSpace ℝ (Fin 3))) := by
    apply hΨc.fst.preimage_mem_nhds
    apply isOpen_Ioo.mem_nhds
    simpa only [Ψ, radialParameterChart_zero] using hτ
  let t :=
    Ψ.source ∩
      (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) (Real.exp τ) ∩
        (fun z : (EuclideanSpace ℝ (Fin 3)) => (Ψ z).1) ⁻¹' Set.Ioo (0 : ℝ) 1)
  have ht : t ∈ 𝓝 (0 : (EuclideanSpace ℝ (Fin 3))) :=
    Filter.inter_mem (Ψ.open_source.mem_nhds hΨ0)
      (Filter.inter_mem (Metric.ball_mem_nhds _ (Real.exp_pos τ)) htime)
  have hc : ContinuousOn (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) t :=
    H.continuous.comp_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono Set.inter_subset_left)
  have hcenter : H (Ψ 0) = d.surgery.beltSphere v := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hpoint.symm
  obtain ⟨s, hs, hst, hcs, hdomain, hsmall⟩ :=
    exists_small_native_belt_neighborhood d (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) v ht
      hc hcenter
  have hgΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (Ψ 0) := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hg
  have hnormal :=
    d.contMDiffOn_beltNormal hf |>.contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have hnormal' :
    ContMDiffAt 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal
      (H (Ψ 0)) := by
    rw [hcenter]
    exact hnormal
  have hF : ContDiffAt ℝ ∞ (fun z : (EuclideanSpace ℝ (Fin 3)) => d.beltNormal (H (Ψ z))) 0 :=
    (ContMDiffAt.comp (g := d.beltNormal) (f := fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) 0
        hnormal' (hgΨ.comp 0 hΨ)).contDiffAt
  have hF0 : d.beltNormal (H (Ψ 0)) = 0 := by rw [hcenter, d.beltNormal_belt]
  obtain ⟨b⟩ := Smale.LocalDegree.nonempty_boundaryData_of_contDiffAt L hL hF0 hs hF
  have hball (u : (Smale.Hemisphere.Sphere 2)) : b.radius • u.val ∈ s := by
    apply b.ball_subset
    rw [mem_closedBall_zero_iff, Smale.LocalDegree.norm_radius_smul b.radius b.radius_pos u]
  have hεx : b.radius < Real.exp τ := by
    have hh := (hst (hball x₀)).2.1
    rwa [mem_ball_zero_iff, Smale.LocalDegree.norm_radius_smul b.radius b.radius_pos x₀] at hh
  obtain ⟨J, hJ, w, hmeridian⟩ :=
    normal_boundary_homotopic_native_meridian d (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) b
      hcs hdomain hsmall (1 / 2) (by norm_num) (by norm_num)
  have hlink :
    (Degree.PassageHomology.puncturedPassageTrace H (Set.range d.surgery.beltSphere) hτ x₀
            hcross).comp
        (Degree.PassageHomology.cylinderLink τ x₀ b.radius b.radius_pos hεx) =
      J := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    have htimeu :
      (Degree.PassageHomology.cylinderLink τ x₀ b.radius b.radius_pos hεx u).val.1 ∈
        Set.Icc (0 : ℝ) 1 := by
      rw [← radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
      exact ⟨(hst (hball u)).2.2.1.le, (hst (hball u)).2.2.2.le⟩
    rw [ContinuousMap.comp_apply,
      Degree.PassageHomology.puncturedPassageTrace_on_interval H (Set.range d.surgery.beltSphere)
        hτ x₀ hcross _ htimeu,
      hJ]
    rw [show Ψ (b.radius • u.val) = _ from
        radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
  refine ⟨b.radius, b.radius_pos, hεx, w, b.normalizedMap, b.normalized_homology_compare 2, ?_⟩
  rw [hlink]
  exact hmeridian

theorem AdaptedWindows.exists_passage_derivative_class_addition {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × (Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (hpoint : (S.data p).surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Smale.Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data p).chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          (S.data p).beltNormal (H (MorseCancel.radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (τ, x₀) →
      ∃ D :
        C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
          (S.data p).LowerLevel),
        (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
          (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
            let G :=
              D.comp
                (Degree.PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            SingularMayerVietoris.singularHomologyMap
                (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
              SingularMayerVietoris.singularHomologyMap
                  (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                SingularMayerVietoris.singularHomologyMap
                  ((S.data p).surgery.attachingSphere.comp
                    (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
                  2 := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro hg
  let e :
    (Smale.Hemisphere.Sphere 2) ≃ₜ Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1 :=
    (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
        2).toHomeomorph
  obtain ⟨D, horbit, hunique, hmeridian, _, hrelation⟩ :=
    S.exists_lower_passage_homology_relation hf p (e x₀) v H hτ x₀ hcross
  obtain ⟨ε, hε, hεx, w, β, hβ, hlink⟩ :=
    MorseCancel.exists_radial_link_meridian_with_derivative (S.data p) hf H hτ x₀ v hpoint hcross
      L hL hg
  let σ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hσ : 0 < (σ : ℝ) := by norm_num [σ]
  have htube :
    MorseCancel.nativeBeltTubeMeridian (S.data p) w (1 / 2) (by norm_num) (by norm_num) =
      MorseCancel.nativeUpperMeridianInComplement S p w σ hσ :=
    MorseCancel.nativeBeltTubeMeridian_eq S p w (1 / 2) (by norm_num) (by norm_num)
  rw [htube] at hlink
  let G :=
    D.comp
      (Degree.PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere) hτ
        x₀ hcross)
  have hDlink :
    (G.comp (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)).Homotopic
      ((D.comp (MorseCancel.nativeUpperMeridianInComplement S p w σ hσ)).comp β) :=
    (ContinuousMap.Homotopic.refl D).comp hlink
  have hatt :
    ((D.comp (MorseCancel.nativeUpperMeridianInComplement S p w σ hσ)).comp β).Homotopic
      ((S.data p).surgery.attachingSphere.comp β) :=
    (hmeridian w σ hσ).comp (ContinuousMap.Homotopic.refl β)
  have hlinkMap := PeriodTorusHigherHomology.homotopic_homologyMap (hDlink.trans hatt) 2
  have hderivativeMap :
    SingularMayerVietoris.singularHomologyMap ((S.data p).surgery.attachingSphere.comp β) 2 =
      SingularMayerVietoris.singularHomologyMap
        ((S.data p).surgery.attachingSphere.comp
          (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
        2 := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hβ]
  refine ⟨D, horbit, hunique, ?_⟩
  have hh := hrelation ε hε hεx
  change
    SingularMayerVietoris.singularHomologyMap
        (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
      SingularMayerVietoris.singularHomologyMap
          (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
        SingularMayerVietoris.singularHomologyMap
          (G.comp (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 at hh
  rw [hlinkMap, hderivativeMap] at hh
  exact hh

theorem MorseCancel.attaching_contributions_opposite_of_relative_det_neg {N Y : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y]
    (a : C(Metric.sphere (0 : N) 1, Y)) (L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N)
    (hdet : (L₁.trans L₀.symm).toLinearEquiv.toLinearMap.det < 0) :
    SingularMayerVietoris.singularHomologyMap
        (a.comp (Smale.LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)) 2 =
      -SingularMayerVietoris.singularHomologyMap
          (a.comp (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)) 2 :=
  by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  apply LinearMap.ext
  intro u
  have h := Smale.LinearSphereAction.homology_relative_sign 1 L₁ L₀ 1 u
  rw [sign_eq_neg_one_iff.mpr hdet] at h
  simp only [SignType.coe_neg, SignType.coe_one, neg_one_zsmul] at h
  change
    SingularMayerVietoris.singularHomologyMap a 2
        (SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 u) =
      -SingularMayerVietoris.singularHomologyMap a 2
          (SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 u)
  rw [h, map_neg]

def MorseCancel.passageNormalProduct {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] (c : ℝ)
    (hc : c ≠ 0) (C : U ≃L[ℝ] U) : (ℝ × U) ≃L[ℝ] (ℝ × U) :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.prodCongr C

theorem MorseCancel.passageNormalProduct_det {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (c : ℝ) (hc : c ≠ 0) (C : U ≃L[ℝ] U) :
    (passageNormalProduct c hc C).toLinearMap.det = c * C.toLinearMap.det := by
  have hscale :
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap = c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    ext
    rfl
  change LinearMap.det ((LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap.prodMap C.toLinearMap) = _
  rw [LinearMap.det_prodMap, hscale, LinearMap.det_smul, Module.finrank_self, pow_one,
    LinearMap.det_id, mul_one]

theorem MorseCancel.relative_normal_frame_det {U N : Type} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    (Q₀ Q₁ : (ℝ × U) ≃L[ℝ] (ℝ × U)) :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap.det =
      Q₀.toLinearMap.det⁻¹ * Q₁.toLinearMap.det := by
  have heq :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap =
      P.symm.toLinearMap.comp ((Q₀.symm.toLinearMap.comp Q₁.toLinearMap).comp P.toLinearMap) := by
    apply LinearMap.ext
    intro z
    change P.symm (Q₀.symm (B.symm (B (Q₁ (P z))))) = P.symm (Q₀.symm (Q₁ (P z)))
    rw [B.symm_apply_apply]
  rw [heq]
  have hconj := LinearMap.det_conj (Q₀.symm.toLinearMap.comp Q₁.toLinearMap) P.symm.toLinearEquiv
  calc
    _ = (Q₀.symm.toLinearMap.comp Q₁.toLinearMap).det := hconj
    _ = _ := by
      rw [LinearMap.det_comp]
      exact
        congrArg (fun t : ℝ => t * Q₁.toLinearMap.det) (LinearEquiv.det_coe_symm Q₀.toLinearEquiv)

theorem MorseCancel.passage_normal_relative_det_neg {U N : Type} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (C : U ≃L[ℝ] U) (hC : C.toLinearMap.det < 0) :
    (((P.trans (passageNormalProduct c₁ hc₁.ne' C)).trans B).trans
          ((P.trans (passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ U))).trans
              B).symm).toLinearMap.det <
      0 := by
  rw [relative_normal_frame_det, passageNormalProduct_det, passageNormalProduct_det]
  change (c₀ * (LinearMap.id : U →ₗ[ℝ] U).det)⁻¹ * (c₁ * C.toLinearMap.det) < 0
  rw [LinearMap.det_id, mul_one]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hc₀) (mul_neg_of_pos_of_neg hc₁ hC)

theorem MorseCancel.mfderiv_normal_trace_model {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {α : X → U} {x : X}
    (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hα0 : α x = 0) {η : ℝ → ℝ} {τ κ : ℝ}
    (hη : HasDerivAt η κ τ) (hη1 : η τ = 1) (C : U ≃L[ℝ] U) {G : (ℝ × U) → N}
    {B : (ℝ × U) →L[ℝ] N} (hG : HasFDerivAt G B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => G (η p.1 - 1, C (α p.2))) (τ, x) :
        (ℝ × U) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
          (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by
  have ht :=
    (hη.sub_const 1).hasFDerivAt.hasMFDerivAt.comp (τ, x)
      (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hu := C.hasFDerivAt.hasMFDerivAt.comp x hα.hasMFDerivAt
  have hu' := hu.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hpair :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × U) (fun p : ℝ × X => (η p.1 - 1, C (α p.2))) (τ, x)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
        (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by convert! ht.prodMk hu' using 1
  have hcenter : (η τ - 1, C (α x)) = (0 : ℝ × U) := by
    rw [hη1, hα0, map_zero, sub_self]
    rfl
  have hG' : HasFDerivAt G B (η τ - 1, C (α x)) := by rw [hcenter]; exact hG
  exact (hG'.hasMFDerivAt.comp (τ, x) hpair).mfderiv

theorem MorseCancel.LongitudinalTubeMotion.normal_trace_mfderiv {U H X N : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H}
    [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞) (C : U ≃L[ℝ] U)
    (R : V ≃L[ℝ] V) {f : X → M} {x : X} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright :
      (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
        MorseCancel.linearTransverseChart (C.prodCongr R) Φ₁)
    (n : M → N) (B : (ℝ × U) →L[ℝ] N)
    (hB : HasFDerivAt (fun z : ℝ × U => n (Φ₁ (1 + z.1, (z.2, 0)))) B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => n (A.family (p.1, f p.2))) (A.time, x) :
        (ℝ × U) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (deriv Real.smoothTransition A.time * A.destination)).prodMap
          (C.toContinuousLinearMap.comp
            (mfderiv I 𝓘(ℝ, U) (fun q : X => (Φ₀.symm (f q)).2.1) x))) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let α : X → U := P ∘ a
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x := (Φ₀.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x := P.differentiableAt.mdifferentiableAt.comp x ha
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hα0 : α x = 0 := by change P (a x) = 0; rw [ha0, map_zero]
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
          A.time).hasDerivAt.mul_const
      _
  let G : (ℝ × U) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  have htrace :=
    A.sheet_trace_germ_of_endpoint_germs Φ₀ Φ₁ C R hf.continuousAt h0 hΦ₀ hx hrec hleft hright
  have heq :
    (fun p : ℝ × X => n (A.family (p.1, f p.2))) =ᶠ[𝓝 (A.time, x)] fun p =>
      G (η p.1 - 1, C (α p.2)) := by
    filter_upwards [htrace] with p hp
    rw [hp]
    change n (Φ₁ (η p.1, (C (α p.2), 0))) = n (Φ₁ (1 + (η p.1 - 1), (C (α p.2), 0)))
    rw [show 1 + (η p.1 - 1) = η p.1 by ring]
  rw [heq.mfderiv_eq]
  exact MorseCancel.mfderiv_normal_trace_model hα hα0 hη A.time_value C hB

theorem MorseCancel.mfderiv_retime_unit_rate {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)) {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ)
    (hpoint : D σ = τ) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) :
        (ℝ × U) →L[ℝ] N) =
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) := by
  subst τ
  have hDmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D σ (ContinuousLinearMap.id ℝ ℝ) := by
    have hid : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) = ContinuousLinearMap.id ℝ ℝ := by
      ext
      simp
    have h := hD.hasFDerivAt
    change HasFDerivAt D (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) σ at h
    rw [hid] at h
    exact h.hasMFDerivAt
  have ht := hDmf.comp (σ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x))
  have hp :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (fun p : ℝ × X => (D p.1, p.2)) (σ, x)
      (ContinuousLinearMap.id ℝ (ℝ × U)) := by
    convert! ht.prodMk (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x)) using 1
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := hF
  have hc := (hF'.hasMFDerivAt.comp (σ, x) hp).mfderiv
  change
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) :
        (ℝ × U) →L[ℝ] N) =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) : (ℝ × U) →L[ℝ] N).comp
        (ContinuousLinearMap.id ℝ (ℝ × U)) at hc
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg (fun L : (ℝ × U) →L[ℝ] N => L z) hc

theorem MorseCancel.fderiv_retimed_trace_parameter {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)) {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ)
    (hpoint : D σ = τ) (Ψ : PartialDiffeomorph 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) A (ℝ × X) ∞)
    (hΨ : (0 : A) ∈ Ψ.source) (hcenter : Ψ 0 = (σ, x)) :
    fderiv ℝ (fun z : A => F (D (Ψ z).1, (Ψ z).2)) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) : (ℝ × U) →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) Ψ 0) := by
  let G : ℝ × X → N := fun p => F (D p.1, p.2)
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := by
    rw [hpoint]
    exact hF
  have hG : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) :=
    hF'.comp (σ, x)
      ((hD.differentiableAt.mdifferentiableAt.comp (σ, x) mdifferentiableAt_fst).prodMk
        mdifferentiableAt_snd)
  have hG' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (Ψ 0) := by
    rw [hcenter]
    exact hG
  change fderiv ℝ (G ∘ Ψ) 0 = _
  rw [← mfderiv_eq_fderiv, mfderiv_comp 0 hG' (Ψ.mdifferentiableAt (by simp) hΨ), hcenter]
  rw [show
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) : (ℝ × U) →L[ℝ] N) =
        mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)
      from mfderiv_retime_unit_rate hF hD hpoint]
  rfl

theorem MorseCancel.exists_shared_passage_frames {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N)
    (Q : (ℝ × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (hdim : Module.finrank ℝ N = 3)
    (hbij : Function.Bijective (B.comp (Q.toContinuousLinearMap.comp P))) :
    ∃ (P' : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2)))) (B' :
      (ℝ × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] N),
      P'.toContinuousLinearMap = P ∧ B'.toContinuousLinearMap = B := by
  have hPi : Function.Injective P := by
    intro x y hxy
    apply hbij.injective
    change B (Q (P x)) = B (Q (P y))
    rw [hxy]
  have hBs : Function.Surjective B := by
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact ⟨Q (P x), hx⟩
  have hdimP :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2))) := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  have hdimB : Module.finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2))) = Module.finrank ℝ N := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim]
  have hPb : Function.Bijective P :=
    ⟨hPi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimP).mp hPi⟩
  have hBb : Function.Bijective B :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimB).mpr hBs, hBs⟩
  exact
    ⟨(LinearEquiv.ofBijective P.toLinearMap hPb).toContinuousLinearEquiv,
      (LinearEquiv.ofBijective B.toLinearMap hBb).toContinuousLinearEquiv, rfl, rfl⟩

structure MorseCancel.CenteredSheetPassage (E : Type*) {M : Type*} {X : Type*} {Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : X → M)
    (g : Y → M) (x : X) (y : Y) (O : Set M) where
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  avoids : support ⊆ Oᶜ
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ family
  zero : ∀ z, family (0, z) = z
  slices : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = family (t, z)
  fixedOutside : ∀ t z, z ∉ support → family (t, z) = z
  crossing :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y, family (t, f u) = g v ↔ t = 1 / 2 ∧ u = x ∧ v = y

def MorseCancel.LongitudinalTubeMotion.centeredSheetPassage {E M X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ) (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hD0 : D 0 = 0) (hpoint : D (1 / 2) = A.time)
    (hinterval : Set.MapsTo D (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) {f : X → M} {g : Y → M}
    {x : X} {y : Y} {O : Set M} (havoid : Φ.target ⊆ Oᶜ)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ u : X, ∀ v : Y, A.family (t, f u) = g v ↔ t = A.time ∧ u = x ∧ v = y) :
    MorseCancel.CenteredSheetPassage E f g x y O
    where
  family := fun p => A.family (D p.1, p.2)
  support := A.support
  compact_support := A.compact_support
  avoids := A.support_subset.trans havoid
  smooth := A.smooth.comp ((D.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  zero := by intro z; change A.family (D 0, z) = z; rw [hD0, A.zero]
  slices := fun t => A.slices (D t)
  fixedOutside := fun t z hz => A.fixedOutside (D t) z hz
  crossing := by
    intro t ht u v
    rw [hcross (D t) (hinterval ht) u v]
    constructor
    · rintro ⟨h, hu, hv⟩
      exact ⟨D.injective (h.trans hpoint.symm), hu, hv⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨hpoint, rfl, rfl⟩

theorem MorseCancel.bijective_trace_normal_of_native_transverse {E M U H X V H' Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'} [TopologicalSpace Y]
    [ChartedSpace H' Y] [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {f : X → M} {g : Y → M} {n : M → N} {x : X} {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)) (hpoint : g y = f x)
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) f g x y)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp (mfderiv I' 𝓘(ℝ, E) g y) = 0)
    (hdim : Module.finrank ℝ U = Module.finrank ℝ N) :
    Function.Bijective (mfderiv I 𝓘(ℝ, N) (n ∘ f) x) := by
  let Q : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)
  let B : V →L[ℝ] E := mfderiv I' 𝓘(ℝ, E) g y
  let A : U →L[ℝ] E := mfderiv I 𝓘(ℝ, E) f x
  have hbij : Function.Bijective (Q.comp A) :=
    Smale.TransverseCoordinates.bijective_normal_comp Q B A hsurj
      (Smale.TransverseCoordinates.surjective_coprod_swap A B (htrans hpoint)) hzero hdim
  have hn' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (f x) := hpoint ▸ hn
  have hder : (mfderiv I 𝓘(ℝ, N) (n ∘ f) x : U →L[ℝ] N) = Q.comp A := by
    rw [mfderiv_comp x hn' hf, ← hpoint]
    rfl
  rw [hder]
  exact hbij

theorem MorseCancel.hasFDerivAt_terminal_normal_factor {E M U V N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup U]
    [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N]
    [NormedSpace ℝ N] (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞)
    (hΦ : ((1 : ℝ), (0 : U × V)) ∈ Φ.source) {n : M → N}
    (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (1, 0))) :
    HasFDerivAt (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0))))
      (fderiv ℝ (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0)))) 0) 0 := by
  let Q : (ℝ × U) → ℝ × (U × V) := fun z => (1 + z.1, (z.2, 0))
  have hQ : ContDiff ℝ ∞ Q :=
    (contDiff_const.add contDiff_fst).prodMk (contDiff_snd.prodMk contDiff_const)
  have hQ0 : Q 0 = (1, 0) := by
    change ((1 : ℝ) + 0, ((0 : U), (0 : V))) = (1, 0)
    rw [add_zero]
    rfl
  have hΦ' : ContMDiffAt 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) ∞ Φ (Q 0) := by
    rw [hQ0]
    exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hΦ)
  have hn' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (Q 0)) := by rw [hQ0]; exact hn
  have hs : ContDiffAt ℝ ∞ (fun z : ℝ × U => n (Φ (Q z))) 0 :=
    (ContMDiffAt.comp (g := n) (f := fun z : ℝ × U => Φ (Q z)) 0 hn'
        (hΦ'.comp 0 hQ.contMDiff.contMDiffAt)).contDiffAt
  exact (hs.differentiableAt (by simp)).hasFDerivAt

theorem MorseCancel.exists_centered_passage_normal_factors {E M Y Z N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y] [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y]
    [SecondCountableTopology Y] [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z]
    [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {f : (Smale.Hemisphere.Sphere 2) → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : Topology.IsEmbedding f) (hge : Topology.IsEmbedding g)
    (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (Set.range f) (Set.range g)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5)
    (x : (Smale.Hemisphere.Sphere 2)) (y : Y) (hbx : f x ∉ Set.range b) (hby : g y ∉ Set.range b)
    (γ : Path (f x) (g y)) (n : M → N) (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (g y))
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) g y) = 0)
    (hdimN : Module.finrank ℝ N = 3) :
    ∃ (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2)))) (B :
      (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N),
      ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
        ∃ (c : ℝ) (hc : 0 < c),
          ∃ A : CenteredSheetPassage E f g x y (Set.range b),
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  n
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        f (radialParameterChart (1 / 2) x z).2)))
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
              Function.Bijective
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) := by
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, _, hchoices⟩ :=
    exists_relative_sheet_passages_with_normal_change hf hg hfe hge hfi hgi hdisj hb hbc hdim x y
      hbx hby γ
  let Ψ := radialParameterChart (1 / 2) x
  have hΨ0 : (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Ψ.source :=
    radialParameterChart_zero_mem_source (1 / 2) x
  have hΨpoint : Ψ 0 = ((1 / 2 : ℝ), x) := radialParameterChart_zero (1 / 2) x
  let J : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))) :=
    mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Ψ 0
  let K : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] (EuclideanSpace ℝ (Fin 2)) :=
    mfderiv (𝓡 2) 𝓘(ℝ, (EuclideanSpace ℝ (Fin 2)))
      (fun q : (Smale.Hemisphere.Sphere 2) => (Φ₀.symm (f q)).2.1) x
  let P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))) :=
    ((ContinuousLinearMap.id ℝ ℝ).prodMap K).comp J
  let G : (ℝ × (EuclideanSpace ℝ (Fin 2))) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  let B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N := fderiv ℝ G 0
  have hnΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ₁ (1, 0)) := by rw [hΦy]; exact hn
  have hB : HasFDerivAt G B 0 := hasFDerivAt_terminal_normal_factor Φ₁ hΦ₁ hnΦ
  refine ⟨P, B, ?_⟩
  intro C
  obtain ⟨R, ε, hε, Φ, A, hprod, _, _, hleft, hright, _, _, havoid, _, hcross, htrans⟩ :=
    hchoices C
  have h0 : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source :=
    hprod ⟨⟨le_rfl, zero_le_one⟩, Metric.mem_closedBall_self hε.le⟩
  obtain ⟨D, hD0, _, hDpoint, _, hDinterval, _, hDder⟩ := exists_centered_passage_clock A.time_mem
  let T := A.centeredSheetPassage D hD0 hDpoint hDinterval havoid hcross
  let c : ℝ := deriv Real.smoothTransition A.time * A.destination
  have hc : 0 < c := A.time_rate
  let F : ℝ × (Smale.Hemisphere.Sphere 2) → M := fun p => A.family (p.1, f p.2)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ F :=
    A.smooth.comp (contMDiff_fst.prodMk (hf.comp contMDiff_snd))
  have hpoint : F (A.time, x) = g y :=
    (hcross A.time ⟨A.time_mem.1.le, A.time_mem.2.le⟩ x y).mpr ⟨rfl, rfl, rfl⟩
  have hnF : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (F (A.time, x)) := by rw [hpoint]; exact hn
  let NF : ℝ × (Smale.Hemisphere.Sphere 2) → N := n ∘ F
  have hNF : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :=
    (hnF.comp (A.time, x) hF.contMDiffAt).mdifferentiableAt (by simp)
  have hNFbij : Function.Bijective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x)) :=
    bijective_trace_normal_of_native_transverse (hF.mdifferentiable (by simp) (A.time, x))
      (hn.mdifferentiableAt (by simp)) hpoint.symm htrans hsurj hzero
      (by simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdimN])
  have hret :
    fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
            (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N).comp
        J :=
    fderiv_retimed_trace_parameter hNF hDder hDpoint Ψ hΨ0 hΨpoint
  have hfactor :
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
        (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).prodMap
          (C.toContinuousLinearMap.comp K)) :=
    A.normal_trace_mfderiv Φ₀ Φ₁ C R (hf.mdifferentiable (by simp) x) h0 hΦ₀ hΦx hrec₀ hleft
      hright n B hB
  have heq :
    fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P) := by
    rw [hret, hfactor]
    apply ContinuousLinearMap.ext
    intro z
    change B ((J z).1 * c, C (K (J z).2)) = B (c * (J z).1, C (K (J z).2))
    rw [mul_comm]
  let H : ℝ × (Smale.Hemisphere.Sphere 2) → N := fun p => NF (D p.1, p.2)
  have hNF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (D (1 / 2), x) := by
    rw [hDpoint]
    exact hNF
  have hH : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (1 / 2, x) :=
    MDifferentiableAt.comp (g := NF) (f := fun p : ℝ × (Smale.Hemisphere.Sphere 2) =>
      (D p.1, p.2)) (1 / 2, x) hNF'
      ((hDder.differentiableAt.mdifferentiableAt.comp (1 / 2, x) mdifferentiableAt_fst).prodMk
        mdifferentiableAt_snd)
  have hH' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (Ψ 0) := by
    rw [hΨpoint]
    exact hH
  have hdiff :
    DifferentiableAt ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2)))
      0 :=
    (hH'.comp 0 (Ψ.mdifferentiableAt (by simp) hΨ0)).differentiableAt
  have hder :
    HasFDerivAt (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2)))
      (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 := by
    rw [← heq]
    exact hdiff.hasFDerivAt
  have hbij :
    Function.Bijective
      (fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0) := by
    rw [hret]
    exact hNFbij.comp (Smale.PartialChart.bijective_mfderiv Ψ hΨ0)
  exact ⟨c, hc, T, hder, heq ▸ hbij⟩

theorem MorseCancel.opposite_centered_passages_of_normal_factors {E M Y N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {f : (Smale.Hemisphere.Sphere 2) → M} {g : Y → M} {x : (Smale.Hemisphere.Sphere 2)} {y : Y}
    {O : Set M} (n : M → N) (hdim : Module.finrank ℝ N = 3)
    (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N)
    (hchoices :
      ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
        ∃ (c : ℝ) (hc : 0 < c),
          ∃ A : CenteredSheetPassage E f g x y O,
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  n
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        f (radialParameterChart (1 / 2) x z).2)))
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
              Function.Bijective
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P))) :
    ∃ A₀ A₁ : CenteredSheetPassage E f g x y O,
      ∃ L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N,
        HasFDerivAt
            (fun z : (EuclideanSpace ℝ (Fin 3)) =>
              n
                (A₀.family
                  ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
            L₀.toContinuousLinearMap 0 ∧
          HasFDerivAt
              (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                n
                  (A₁.family
                    ((radialParameterChart (1 / 2) x z).1,
                      f (radialParameterChart (1 / 2) x z).2)))
              L₁.toContinuousLinearMap 0 ∧
            (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  obtain ⟨C, hC⟩ :=
    Degree.SupportedGerms.exists_linearEquiv_with_det (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (0 : Fin 2) (show (-1 : ℝ) ≠ 0 by norm_num)
  have hCneg : C.toLinearMap.det < 0 := by rw [hC]; norm_num
  obtain ⟨c₀, hc₀, A₀, hA₀, hbij₀⟩ :=
    hchoices (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨c₁, hc₁, A₁, hA₁, _⟩ := hchoices C
  let Q₀ :=
    passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
  let Q₁ := passageNormalProduct c₁ hc₁.ne' C
  obtain ⟨P', B', hP, hB⟩ := exists_shared_passage_frames P B Q₀ hdim hbij₀
  let L₀ := (P'.trans Q₀).trans B'
  let L₁ := (P'.trans Q₁).trans B'
  have hL₀ : L₀.toContinuousLinearMap = B.comp (Q₀.toContinuousLinearMap.comp P) := by
    change
      B'.toContinuousLinearMap.comp (Q₀.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  have hL₁ : L₁.toContinuousLinearMap = B.comp (Q₁.toContinuousLinearMap.comp P) := by
    change
      B'.toContinuousLinearMap.comp (Q₁.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  refine ⟨A₀, A₁, L₀, L₁, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact hA₀
  · rw [hL₁]
    exact hA₁
  · exact passage_normal_relative_det_neg P' B' hc₀ hc₁ C hCneg

theorem MorseCancel.exists_native_opposite_centered_passages {E M Z : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C((Smale.Hemisphere.Sphere 2), d.UpperLevel)) (hαe : Topology.IsEmbedding α)
    (hdisj : Disjoint (Set.range α) (Set.range d.surgery.beltSphere)) (b : Z → d.UpperLevel)
    (hbc : IsClosed (Set.range b)) (x : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (hx : α x ∉ Set.range b)
    (hv : d.surgery.beltSphere v ∉ Set.range b) (γ : Path (α x) (d.surgery.beltSphere v)) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) α z)) →
        ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ b →
          ∃ A₀ A₁ :
            CenteredSheetPassage (Smale.RegularLevel.Model E) α d.surgery.beltSphere x v
              (Set.range b),
            ∃ L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
              HasFDerivAt
                  (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                    d.beltNormal
                      (A₀.family
                        ((radialParameterChart (1 / 2) x z).1,
                          α (radialParameterChart (1 / 2) x z).2)))
                  L₀.toContinuousLinearMap 0 ∧
                HasFDerivAt
                    (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                      d.beltNormal
                        (A₁.family
                          ((radialParameterChart (1 / 2) x z).1,
                            α (radialParameterChart (1 / 2) x z).2)))
                    L₁.toContinuousLinearMap 0 ∧
                  (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  dsimp only
  intro hα hαi hb
  have hleveldim : Module.finrank ℝ (Smale.RegularLevel.Model E) = 5 := by
    simp [Smale.RegularLevel.Model, hdim]
  have hn :=
    d.contMDiffOn_beltNormal hf |>.contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  obtain ⟨P, B, hchoices⟩ :=
    exists_centered_passage_normal_factors hα (d.belt_smooth hf 2) hαe
      d.belt_isClosedEmbedding.isEmbedding hαi (d.belt_derivative_injective hf 2) hdisj hb hbc
      hleveldim x v hx hv γ d.beltNormal hn (d.surjective_beltNormal_derivative hf v)
      (d.beltNormal_derivative_comp_belt hf 2 v) (by exact Fact.out)
  exact opposite_centered_passages_of_normal_factors d.beltNormal (by exact Fact.out) P B hchoices

theorem MorseCancel.choose_prescribed_normal_passage {E M Y N : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup N]
    [NormedSpace ℝ N] {f : (Smale.Hemisphere.Sphere 2) → M} {g : Y → M}
    {x : (Smale.Hemisphere.Sphere 2)} {y : Y} {O : Set M} (n : M → N)
    (e : (Smale.Hemisphere.Sphere 2) ≃ₜ Metric.sphere (0 : N) 1)
    (A₀ A₁ : CenteredSheetPassage E f g x y O) (L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N)
    (hL₀ :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          n
            (A₀.family
              ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
        L₀.toContinuousLinearMap 0)
    (hL₁ :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          n
            (A₁.family
              ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
        L₁.toContinuousLinearMap 0)
    (hdet : (L₁.trans L₀.symm).toLinearMap.det < 0) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ (A : CenteredSheetPassage E f g x y O) (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N),
      HasFDerivAt
          (fun z : (EuclideanSpace ℝ (Fin 3)) =>
            n
              (A.family
                ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
          L.toContinuousLinearMap 0 ∧
        SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
          k •
            SingularMayerVietoris.singularHomologyMap
              (e : C((Smale.Hemisphere.Sphere 2), Metric.sphere (0 : N) 1)) 2 := by
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2) := by
    have heq :
      (Smale.LinearSphereAction.homologyEquiv L₀ 2 :
          SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere 2) 2 →
            SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 2) =
        SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 :=
      funext (Smale.LinearSphereAction.homologyEquiv_apply L₀ 2)
    rw [← heq]
    exact (Smale.LinearSphereAction.homologyEquiv L₀ 2).bijective
  obtain ⟨u, hu, hunit⟩ :=
    two_sphere_map_unit_of_homology_bijective e
      (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) hbij
  have hopp :
    SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 =
      -SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 := by
    simpa using
      attaching_contributions_opposite_of_relative_det_neg
        (ContinuousMap.id (Metric.sphere (0 : N) 1)) L₀ L₁ hdet
  by_cases huk : u = k
  · exact ⟨A₀, L₀, hL₀, huk ▸ hunit⟩
  · have hneg : -u = k := by
      rcases hu with rfl | rfl <;> rcases hk with rfl | rfl <;> norm_num at *
    refine ⟨A₁, L₁, hL₁, ?_⟩
    rw [hopp, hunit, ← neg_zsmul, hneg]

theorem MorseCancel.exists_native_prescribed_centered_passage {E M Z : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z]
    [SecondCountableTopology Z] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C((Smale.Hemisphere.Sphere 2), d.UpperLevel)) (hαe : Topology.IsEmbedding α)
    (hdisj : Disjoint (Set.range α) (Set.range d.surgery.beltSphere)) (b : Z → d.UpperLevel)
    (hbc : IsClosed (Set.range b)) (x : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (hx : α x ∉ Set.range b)
    (hv : d.surgery.beltSphere v ∉ Set.range b) (γ : Path (α x) (d.surgery.beltSphere v)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) α z)) →
        ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ b →
          ∃ A :
            CenteredSheetPassage (Smale.RegularLevel.Model E) α d.surgery.beltSphere x v
              (Set.range b),
            ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
              HasFDerivAt
                  (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                    d.beltNormal
                      (A.family
                        ((radialParameterChart (1 / 2) x z).1,
                          α (radialParameterChart (1 / 2) x z).2)))
                  L.toContinuousLinearMap 0 ∧
                SingularMayerVietoris.singularHomologyMap
                    (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
                  k •
                    SingularMayerVietoris.singularHomologyMap
                      ((Smale.SphereCoordinates.standardParametrization
                            d.chart.NegativeCoordinates 2).toHomeomorph :
                        C((Smale.Hemisphere.Sphere 2),
                          Metric.sphere (0 : d.chart.NegativeCoordinates) 1))
                      2 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hα hαi hb
  obtain ⟨A₀, A₁, L₀, L₁, hL₀, hL₁, hdet⟩ :=
    exists_native_opposite_centered_passages d hf hdim α hαe hdisj b hbc x v hx hv γ hα hαi hb
  exact
    choose_prescribed_normal_passage d.beltNormal
      (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
      A₀ A₁ L₀ L₁ hL₀ hL₁ hdet k hk

theorem MorseCancel.exists_native_prescribed_finite_family_passage {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (a : ι → C((Smale.Hemisphere.Sphere 2), d.UpperLevel))
    (hpair : Pairwise (fun j k => Disjoint (Set.range (a j)) (Set.range (a k)))) (i : ι)
    (hfe : Topology.IsEmbedding (a i))
    (hdisj : Disjoint (Set.range (a i)) (Set.range d.surgery.beltSphere))
    (x : (Smale.Hemisphere.Sphere 2)) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (hv : d.surgery.beltSphere v ∉ Degree.MorseRearrangement.otherSheetImages (fun j => a j) i)
    (γ : Path (a i x) (d.surgery.beltSphere v)) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (a j)) →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (a i) z)) →
        ∃ A :
          CenteredSheetPassage (Smale.RegularLevel.Model E) (a i) d.surgery.beltSphere x v
            (Degree.MorseRearrangement.otherSheetImages (fun j => a j) i),
          ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  d.beltNormal
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        a i (radialParameterChart (1 / 2) x z).2)))
                L.toContinuousLinearMap 0 ∧
              SingularMayerVietoris.singularHomologyMap
                  (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
                k •
                  SingularMayerVietoris.singularHomologyMap
                    ((Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
                          2).toHomeomorph :
                      C((Smale.Hemisphere.Sphere 2),
                        Metric.sphere (0 : d.chart.NegativeCoordinates) 1))
                    2 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro ha hfi
  obtain ⟨n, b, hb, hbrange⟩ :=
    Degree.MorseRearrangement.exists_sheetSumMap_for_finite_family
      (fun j : { j : ι // j ≠ i } => a j.val) (fun j => ha j.val)
  have hrange : Set.range b = Degree.MorseRearrangement.otherSheetImages (fun j => a j) i :=
    hbrange
  have hbc : IsClosed (Set.range b) := (isCompact_range hb.continuous).isClosed
  have hx : a i x ∉ Set.range b := by
    rw [hrange]
    intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hpair (Ne.symm j.property)) (Set.mem_range_self x) hj
  have hvb : d.surgery.beltSphere v ∉ Set.range b := by rwa [hrange]
  obtain ⟨A, L, hL, hunit⟩ :=
    exists_native_prescribed_centered_passage d hf hdim (a i) hfe hdisj b hbc x v hx hvb γ k hk
      (ha i) hfi hb
  let A' :
    CenteredSheetPassage (Smale.RegularLevel.Model E) (a i) d.surgery.beltSphere x v
      (Degree.MorseRearrangement.otherSheetImages (fun j => a j) i) :=
    { A with avoids := by rw [← hrange]; exact A.avoids }
  exact ⟨A', L, hL, hunit⟩

theorem AdaptedWindows.exists_higher_family_prescribed_passage {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
    let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
      ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
    ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel),
      MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
          (∀ j, Disjoint (Set.range (β j)) (Set.range (S.data q).surgery.beltSphere)) ∧
            ∃ (x : (Smale.Hemisphere.Sphere 2)) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1),
              ∃ A :
                MorseCancel.CenteredSheetPassage (Smale.RegularLevel.Model E) (β i)
                  (S.data q).surgery.beltSphere x v
                  (Degree.MorseRearrangement.otherSheetImages (fun j => β j) i),
                ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data q).chart.NegativeCoordinates,
                  HasFDerivAt
                      (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                        (S.data q).beltNormal
                          (A.family
                            ((MorseCancel.radialParameterChart (1 / 2) x z).1,
                              β i (MorseCancel.radialParameterChart (1 / 2) x z).2)))
                      L.toContinuousLinearMap 0 ∧
                    SingularMayerVietoris.singularHomologyMap
                        (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)
                        2 =
                      k •
                        SingularMayerVietoris.singularHomologyMap
                          ((Smale.SphereCoordinates.standardParametrization
                                (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                            C((Smale.Hemisphere.Sphere 2),
                              Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1))
                          2 := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : CompactSpace (S.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hsplit := (S.data q).chart.finrank_negative_add_positive
      have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
      omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨β₀, hβ₀, horbit₀⟩ :=
    S.exists_higher_middle_family hf (haq.trans (S.toSurgeryWindows.value_lt_upper q)) ha
      (S.data q).upper_regular p i hp hhigh α hα
  let β : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel) := β₀
  have hβ :
    MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) := hβ₀
  have horbit : ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := horbit₀
  have hdisj (j : Fin n) : Disjoint (Set.range (β j)) (Set.range (S.data q).surgery.beltSphere) :=
    by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ hy
    exact S.upper_point_not_on_belt_of_lower_orbit hf q haq (α j x) (β j x) (horbit j x) hy
  let x : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  let v :=
    Smale.SphereCoordinates.standardParametrization (S.data q).chart.PositiveCoordinates 2 x
  have hv :
    (S.data q).surgery.beltSphere v ∉
      Degree.MorseRearrangement.otherSheetImages (fun j => β j) i := by
    intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdisj j.val) hj (Set.mem_range_self v)
  let _ : PathConnectedSpace (S.data q).UpperLevel :=
    S.pathConnectedSpace_index_three_upper_level hf hdim horder q hq (β i x)
  obtain ⟨A, L, hL, hunit⟩ :=
    MorseCancel.exists_native_prescribed_finite_family_passage (S.data q) hf hdim β hβ.2.2.2.1 i
      (hβ.2.1 i).isEmbedding (hdisj i) x v hv
      (PathConnectedSpace.somePath (β i x) ((S.data q).surgery.beltSphere v)) k hk hβ.1
      (hβ.2.2.1 i)
  exact ⟨β, hβ, horbit, hdisj, x, v, A, L, hL, hunit⟩

theorem AdaptedWindows.prescribed_passage_actual_endpoint_classes {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × (Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Smale.Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (β δ : C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel))
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (H (0, x)).val = (β x).val)
    (hδ : ∀ x, ∃ t : ℝ, S.flow t (H (1, x)).val = (δ x).val) (k : ℤ)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data q).chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          (S.data q).beltNormal (H (MorseCancel.radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0)
    (hunit :
      SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
        k •
          SingularMayerVietoris.singularHomologyMap
            ((Smale.SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates
                  2).toHomeomorph :
              C((Smale.Hemisphere.Sphere 2),
                Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1))
            2) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (τ, x₀) →
      SingularMayerVietoris.singularHomologyMap δ 2 =
        SingularMayerVietoris.singularHomologyMap β 2 +
          k •
            SingularMayerVietoris.singularHomologyMap
              (MorseCancel.nativeIndexThreeAttachingSphere S q hq) 2 := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro hH
  obtain ⟨D, _, hunique, hrelation⟩ :=
    S.exists_passage_derivative_class_addition hf q H hτ x₀ v hpoint hcross L hL hH
  let G :=
    D.comp
      (Degree.PassageHomology.puncturedPassageTrace H (Set.range (S.data q).surgery.beltSphere) hτ
        x₀ hcross)
  have hmap (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hsτ : s ≠ τ)
    (σ : C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel))
    (hσ : ∀ x, ∃ t : ℝ, S.flow t (H (s, x)).val = (σ x).val) :
    G.comp (Degree.PassageHomology.cylinderSlice τ x₀ s hsτ) = σ := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨t, ht⟩ := hσ x
    apply hunique _ (σ x) t
    have heq :=
      Degree.PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data q).surgery.beltSphere) hτ x₀ hcross
        (Degree.PassageHomology.cylinderSlice τ x₀ s hsτ x) hs
    change
      S.flow t
          (Degree.PassageHomology.puncturedPassageTrace H
              (Set.range (S.data q).surgery.beltSphere) hτ x₀ hcross
              (Degree.PassageHomology.cylinderSlice τ x₀ s hsτ x)).val.val =
        (σ x).val
    rw [heq]
    exact ht
  have hzero := hmap 0 ⟨le_rfl, zero_le_one⟩ hτ.1.ne β hβ
  have hone := hmap 1 ⟨zero_le_one, le_rfl⟩ hτ.2.ne' δ hδ
  have hcoef :
    SingularMayerVietoris.singularHomologyMap
        ((S.data q).surgery.attachingSphere.comp
          (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
        2 =
      k •
        SingularMayerVietoris.singularHomologyMap
          (MorseCancel.nativeIndexThreeAttachingSphere S q hq) 2 := by
    change
      SingularMayerVietoris.singularHomologyMap
          ((S.data q).surgery.attachingSphere.comp
            (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
          2 =
        k •
          SingularMayerVietoris.singularHomologyMap
            ((S.data q).surgery.attachingSphere.comp
              ((Smale.SphereCoordinates.standardParametrization
                    (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                C((Smale.Hemisphere.Sphere 2),
                  Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)))
            2
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hunit]
    apply LinearMap.ext
    intro a
    exact
      map_zsmul (SingularMayerVietoris.singularHomologyMap (S.data q).surgery.attachingSphere 2) k
        _
  change
    SingularMayerVietoris.singularHomologyMap
        (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
      SingularMayerVietoris.singularHomologyMap
          (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
        SingularMayerVietoris.singularHomologyMap
          ((S.data q).surgery.attachingSphere.comp
            (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
          2 at hrelation
  rw [hone, hzero, hcoef] at hrelation
  exact hrelation

theorem AdaptedWindows.exists_prescribed_family_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ β δ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel),
              MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p
                  (fun j => β j) ∧
                MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p
                    (fun j => δ j) ∧
                  (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                    (∀ j, j ≠ i → δ j = β j) ∧
                      (∀ j, j ≠ i → ∀ x, ∃ t : ℝ, T.flow t (δ j x).val = (α j x).val) ∧
                        (SingularMayerVietoris.singularHomologyMap (δ i) 2 =
                            SingularMayerVietoris.singularHomologyMap (β i) 2 +
                              k •
                                SingularMayerVietoris.singularHomologyMap
                                  (MorseCancel.nativeIndexThreeAttachingSphere S q hq) 2) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hsplit := (S.data q).chart.finrank_negative_add_positive
      have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
      omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨γ, hγ, hαγ, havoid, x₀, v, A, L, hL, hunit⟩ :=
    S.exists_higher_family_prescribed_passage hf hdim horder q hq ha haq p i hp hhigh α hα k hk
  let τ : ℝ := 1 / 2
  have hτ : τ ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num [τ]
  let F := A.family
  let K := A.support
  have hK := A.compact_support
  have hKU := A.avoids
  have hF := A.smooth
  have hF0 := A.zero
  have hFd := A.slices
  have hFfix := A.fixedOutside
  have hcount := A.crossing
  obtain ⟨D, hD⟩ := hFd 1
  have I :
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K
      (Degree.MorseRearrangement.otherSheetImages (fun j => γ j) i) :=
    { family := F
      smooth := hF
      zero := hF0
      one := fun x => (hD x).symm
      slices := hFd
      fixedOutside := hFfix
      fixedOn := fun t x hx => hFfix t x (fun h => hKU h hx) }
  have hDavoid (j : Fin n) :
    Disjoint (Set.range (D ∘ γ j)) (Set.range (S.data q).surgery.beltSphere) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ ⟨w, hw⟩
    by_cases hji : j = i
    · subst j
      have heq : F (1, γ i x) = (S.data q).surgery.beltSphere w := (hD _).symm.trans hw.symm
      exact hτ.2.ne' ((hcount 1 ⟨zero_le_one, le_rfl⟩ x w).mp heq).1
    · have heq : D (γ j x) = γ j x :=
        I.endpoint_fixed_on (γ j x)
          (Degree.MorseRearrangement.mem_otherSheetImages (fun j => γ j) i j hji x)
      exact Set.disjoint_left.mp (havoid j) (Set.mem_range_self x) ⟨w, hw.trans heq⟩
  obtain
    ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hβflow, hδflow, hδold, hother, hprotected,
      hkeep⟩ :=
    S.exists_relative_family_lower_transport hf hm q hq p i hhigh γ hγ havoid ε hε D K hK I
      hDavoid
  let H : C(ℝ × (Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel) :=
    ⟨fun z => F (z.1, γ i z.2),
      hF.continuous.comp (continuous_fst.prodMk ((γ i).continuous.comp continuous_snd))⟩
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H :=
    hF.comp (contMDiff_fst.prodMk ((hγ.1 i).comp contMDiff_snd))
  have hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀) :=
    ((hcount τ ⟨hτ.1.le, hτ.2.le⟩ x₀ v).mpr ⟨rfl, rfl, rfl⟩).symm
  have hcross :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ x : (Smale.Hemisphere.Sphere 2),
        H (t, x) ∈ Set.range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀ := by
    intro t ht x
    constructor
    · rintro ⟨w, hw⟩
      have hh := (hcount t ht x w).mp hw.symm
      exact ⟨hh.1, hh.2.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨v, hpoint⟩
  have hstart (x : (Smale.Hemisphere.Sphere 2)) :
    ∃ t : ℝ, S.flow t (H (0, x)).val = (β i x).val := by
    change ∃ t : ℝ, S.flow t (A.family (0, γ i x)).val = (β i x).val
    rw [hF0]
    exact hβflow i x
  have hend (x : (Smale.Hemisphere.Sphere 2)) : ∃ t : ℝ, S.flow t (H (1, x)).val = (δ i x).val := by
    change ∃ t : ℝ, S.flow t (A.family (1, γ i x)).val = (δ i x).val
    rw [← hD]
    exact hδold i x
  have hclasses :=
    S.prescribed_passage_actual_endpoint_classes hf q hq H hτ x₀ v hpoint hcross (β i) (δ i)
      hstart hend k L hL hunit hH.contMDiffAt
  refine ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, ?_, hother, ?_, hclasses, hkeep⟩
  · intro j x
    obtain ⟨s, hs⟩ := hαγ j x
    obtain ⟨t, ht⟩ := hβflow j x
    exact ⟨t + s, by rw [S.flow.map_add, hs, ht]⟩
  · intro j hji x
    obtain ⟨s, hs⟩ := hαγ j x
    have hm : (α j x).val ∈ Set.range (fun t => S.flow t (γ j x).val) := by
      refine ⟨-s, ?_⟩
      change S.flow (-s) (γ j x).val = (α j x).val
      rw [← hs, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    rw [← hprotected j hji x] at hm
    obtain ⟨t, ht⟩ := hm
    change T.flow t (γ j x).val = (α j x).val at ht
    obtain ⟨u, hu⟩ := hδflow j x
    exact ⟨t - u, by rw [← hu, ← T.flow.map_add, sub_add_cancel, ht]⟩

theorem AdaptedWindows.exists_common_cut_prescribed_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (hαq :
      ∀ x,
        ∃ t : ℝ, S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (αq x).val)
    (k : ℤ) (hk : k = 1 ∨ k = -1) (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ)
    (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
              MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                  (Fin.cases αq (fun j => Γ j)) ∧
                (∀ j, j ≠ i → Γ j = α j) ∧
                  (MorseCancel.middleSectionClass (Γ i) =
                      MorseCancel.middleSectionClass (α i) +
                        k • MorseCancel.middleSectionClass αq) ∧
                    ∀ z : M,
                      f z ≤ f q →
                        (∀ x,
                            Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                Set.range (fun t => T.flow t x) =
                                  Set.range (fun t => S.flow t x)) ∧
                            ∀ v,
                              Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hfamily
  have hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j) := by
    refine ⟨fun j => hs j.succ, fun j => he j.succ, fun j => hi j.succ, ?_, fun j => hfull j.succ⟩
    intro j k hjk
    exact hpair (fun h => hjk (Fin.succ_inj.mp h))
  obtain ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hαβ, hother, hprotected, hmaps, hkeep⟩ :=
    S.exists_prescribed_family_slide hf hm hdim horder q hq ha
      (hal.trans (S.toSurgeryWindows.lower_lt_value q)) p i hp hhigh α hα k hk ε hε
  have hgap :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∉ Set.Icc a (S.toSurgeryWindows.lower q) :=
    fun z hz h => hband z h hz
  have hpabove (j : Fin n) : S.toSurgeryWindows.lower q < f (p j) :=
    (S.toSurgeryWindows.lower_lt_value q).trans
      ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j))
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨Γ₀, hΓ₀, hδΓ⟩ :=
    T.exists_regular_band_middle_basin_family hf hal (S.data q).lower_regular ha hgap (δ i x₀) p
      hpabove (fun j => δ j) hδ
  let Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }) := fun j =>
    ⟨Γ₀ j, (hΓ₀.1 j).continuous⟩
  have hΓ : MorseCancel.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := hΓ₀
  have hαqfull (y : { z : M // f z = a }) :
    y ∈ Set.range αq ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot (𝓝 q.val) :=
    (hfull 0 y).trans ((hkeep q.val le_rfl).1 y.val).symm
  have hdisj (j : Fin n) : Disjoint (Set.range αq) (Set.range (Γ j)) := by
    apply Set.disjoint_left.mpr
    intro y hyq hyj
    have heq : q.val = (p j).val :=
      tendsto_nhds_unique ((hαqfull y).mp hyq) ((hΓ.2.2.2.2 j y).mp hyj)
    exact ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j)).ne (congrArg f heq)
  have hΓpair :
    Pairwise
      (fun j k =>
        Disjoint (Set.range (Fin.cases αq (fun j => Γ j) j))
          (Set.range (Fin.cases αq (fun j => Γ j) k))) := by
    intro j k hjk
    cases j using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => exact (hjk rfl).elim
      | succ k => exact hdisj k
    | succ j =>
      cases k using Fin.cases with
      | zero => exact (hdisj j).symm
      | succ k => exact hΓ.2.2.2.1 (fun h => hjk (congrArg Fin.succ h))
  refine ⟨T, hcharts, hradii, hgerms, Γ, ?_, ?_, ?_, hkeep⟩
  · refine ⟨?_, ?_, ?_, hΓpair, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero => exact hs 0
      | succ j => exact hΓ.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact he 0
      | succ j => exact hΓ.2.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact hi 0
      | succ j => exact hΓ.2.2.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact hαqfull
      | succ j => exact hΓ.2.2.2.2 j
  · intro j hji
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, hs⟩ := hδΓ j x
    change T.flow s (δ j x).val = (Γ j x).val at hs
    obtain ⟨t, ht⟩ := hprotected j hji x
    have hshared : T.flow 0 (Γ j x).val = T.flow (s - t) (α j x).val := by
      rw [T.flow.map_zero_apply, ← hs, ← ht, ← T.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact
      MorseCancel.native_same_level_orbit_points hf T.smooth T.flow T.integral
        (fun z hz => T.descent z (ha z hz)) (Γ j x).property (α j x).property hshared
  · have hβα (x : (Smale.Hemisphere.Sphere 2)) : ∃ t : ℝ, S.flow t (β i x).val = (α i x).val := by
      obtain ⟨t, ht⟩ := hαβ i x
      exact ⟨-t, by rw [← ht, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]⟩
    exact
      MorseCancel.signed_relation_of_regular_cut_transport S T hf hal ha hband (β i) (δ i)
        (MorseCancel.nativeIndexThreeAttachingSphere S q hq) (α i) (Γ i) αq k hβα (hδΓ i) hαq
        hmaps

theorem AdaptedWindows.exists_common_cut_prescribed_family_slide {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ)
    (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
              MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                  (Fin.cases αq (fun j => Γ j)) ∧
                (∀ j, j ≠ i → Γ j = α j) ∧
                  (MorseCancel.middleSectionClass (Γ i) =
                      MorseCancel.middleSectionClass (α i) +
                        k • MorseCancel.middleSectionClass αq) ∧
                    ∀ z : M,
                      f z ≤ f q →
                        (∀ x,
                            Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                Set.range (fun t => T.flow t x) =
                                  Set.range (fun t => S.flow t x)) ∧
                            ∀ v,
                              Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  obtain ⟨βq, hβs, hβe, hβi, hrange, horbit, -⟩ :=
    S.exists_canonical_basin_sphere hf q hq ha αq (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩)
      (hfamily.2.2.2.2 0)
  have hβfamily :=
    MorseCancel.nativeMiddleBasinFamily_replace_zero S hf ha q p αq βq α hfamily hrange hβs hβe
      hβi
  obtain ⟨u, hu, hunit⟩ :=
    MorseCancel.same_image_section_classes_unit αq βq (hfamily.2.1 0).isEmbedding hβe.isEmbedding
      hrange
  have hku : k * u = 1 ∨ k * u = -1 := by
    rcases hk with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_prescribed_slide hf hm hdim horder q hq ha hal hband p i hp hhigh βq α
      hβfamily horbit (k * u) hku ε hε
  have hrestored :=
    MorseCancel.nativeMiddleBasinFamily_replace_zero T hf ha q p βq αq Γ hΓ hrange.symm
      (hfamily.1 0) (hfamily.2.1 0) (hfamily.2.2.1 0)
  have hcancel : (k * u) * u = k := by rcases hu with rfl | rfl <;> ring
  refine ⟨T, hcharts, hradii, hgerms, Γ, hrestored, hother, ?_, hkeep⟩
  rw [hclass, hunit, ← SemigroupAction.mul_smul, hcancel]

theorem MorseCancel.regular_below_pivot_of_regular_lower_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    {a : ℝ}
    (hband : ∀ y, f y ∈ Set.Icc a (S.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∀ y, f y ∈ Set.Ico a (f q) → y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro y hy hcrit
  by_cases hlow : f y ≤ S.lower q
  · exact hband y ⟨hy.1, hlow⟩ hcrit
  · have heq : y = q.val :=
      S.isolated q y hcrit ⟨(lt_of_not_ge hlow).le, hy.2.le.trans (S.value_lt_upper q).le⟩
    exact hy.2.ne (congrArg f heq)

theorem MorseCancel.lower_window_le_of_radius_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : Smale.ManifoldMorse.SurgeryWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) : S.lower q ≤ T.lower q := by
  have hs : (T.data q).radius ^ 2 ≤ (S.data q).radius ^ 2 :=
    (sq_le_sq₀ (T.data q).radius_pos.le (S.data q).radius_pos.le).mpr hr
  exact sub_le_sub_left hs (f q)

theorem MorseCancel.common_cut_band_of_smaller_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : Smale.ManifoldMorse.SurgeryWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    {a : ℝ} (hal : a < S.lower q)
    (hband : ∀ y, f y ∈ Set.Icc a (S.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) :
    a < T.lower q ∧
      ∀ y, f y ∈ Set.Icc a (T.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  refine ⟨hal.trans_le (lower_window_le_of_radius_le S T q hr), ?_⟩
  intro y hy
  exact
    regular_below_pivot_of_regular_lower_band S q hband y
      ⟨hy.1, hy.2.trans_lt (T.lower_lt_value q)⟩

theorem MorseCancel.higher_window_separation_of_value_order {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : Smale.ManifoldMorse.SurgeryWindows E f) (q p : Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : S.upper q < f p) : T.upper q < f p :=
  (T.upper_lt_lower q p ((S.value_lt_upper q).trans hhigh)).trans (T.lower_lt_value p)

theorem AdaptedWindows.exists_repeatable_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancel.middleSectionClass (Γ i) =
                            MorseCancel.middleSectionClass (α i) +
                              k • MorseCancel.middleSectionClass αq) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_prescribed_family_slide hf hm hdim horder q hq ha hal hband p i hp hhigh
      αq α hfamily k hk (fun z => (S.data z).radius) (fun z => (S.data z).radius_pos)
  obtain ⟨hcut, hregular⟩ :=
    MorseCancel.common_cut_band_of_smaller_radius S.toSurgeryWindows T.toSurgeryWindows q hal
      hband (hradii q).le
  have hseparated : ∀ j, T.toSurgeryWindows.upper q < f (p j) := fun j =>
    MorseCancel.higher_window_separation_of_value_order S.toSurgeryWindows T.toSurgeryWindows q
      (p j) (hhigh j)
  exact
    ⟨T, hcharts, fun z => (hradii z).le, hgerms, hcut, hregular, hseparated, Γ, hΓ, hother,
      hclass, hkeep⟩

theorem AdaptedWindows.exists_iterated_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) (m : ℕ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancel.middleSectionClass (Γ i) =
                            MorseCancel.middleSectionClass (α i) +
                              ((m : ℤ) * k) • MorseCancel.middleSectionClass αq) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  induction m with
  |
    zero =>
    refine
      ⟨S, fun _ => rfl, fun _ => le_rfl, ?_, hal, hband, hhigh, α, hfamily, fun _ _ => rfl, ?_,
        ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · simp only [Nat.cast_zero, MulZeroClass.zero_mul, zero_smul, add_zero]
    · intro z hz
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | succ m
    ih =>
    obtain
      ⟨T, hcharts, hradii, hgerms, hcut, hregular, hseparated, Γ, hΓ, hother, hclass, hkeep⟩ := ih
    obtain
      ⟨U, ucharts, uradii, ugerms, ucut, uregular, useparated, Δ, hΔ, uother, uclass, ukeep⟩ :=
      T.exists_repeatable_column_slide hf hm hdim horder q hq ha hcut hregular p i hp hseparated
        αq Γ hΓ k hk
    refine
      ⟨U, fun z => (ucharts z).trans (hcharts z), fun z => (uradii z).trans (hradii z), ?_, ucut,
        uregular, useparated, Δ, hΔ, fun j hji => (uother j hji).trans (hother j hji), ?_, ?_⟩
    · intro z hz
      filter_upwards [ugerms z hz, hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · rw [uclass, hclass, add_assoc, ← add_zsmul]
      have hcoef : (m : ℤ) * k + k = ((m + 1 : ℕ) : ℤ) * k := by
        push_cast
        ring
      rw [hcoef]
    · intro z hz
      have hUT := ukeep z hz
      have hTS := hkeep z hz
      exact
        ⟨fun x => (hUT.1 x).trans (hTS.1 x), fun x hx =>
          (hUT.2.1 x ((hTS.1 x).mpr hx)).trans (hTS.2.1 x hx), fun v =>
          (hUT.2.2 v).trans (hTS.2.2 v)⟩

theorem AdaptedWindows.exists_integer_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancel.middleSectionClass (Γ i) =
                            MorseCancel.middleSectionClass (α i) +
                              k • MorseCancel.middleSectionClass αq) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [mul_one] using
      S.exists_iterated_column_slide hf hm hdim horder q hq ha hal hband p i hp hhigh αq α hfamily
        1 (Or.inl rfl) m
  · simpa only [mul_neg_one] using
      S.exists_iterated_column_slide hf hm hdim horder q hq ha hal hband p i hp hhigh αq α hfamily
        (-1) (Or.inr rfl) m

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem MorseCancel.nativeMiddleBasinFamily_reindex {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n m : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a })
    (hγ : IsNativeMiddleBasinFamily S hf ha p γ) (e : Fin m → Fin n) (he : Function.Injective e) :
    IsNativeMiddleBasinFamily S hf ha (p ∘ e) (γ ∘ e) := by
  obtain ⟨hs, hi, hd, hpair, hfull⟩ := hγ
  exact
    ⟨fun j => hs (e j), fun j => hi (e j), fun j => hd (e j), fun i j hij =>
      hpair (fun h => hij (he h)), fun j => hfull (e j)⟩

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem MorseCancel.canonicalMiddleMatrix_single_class_addition {M : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} [Nonempty M] {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (α Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (q i : Fin n) (k : ℤ)
    (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass :
      middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass (α q)) :
    canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B Γ =
      canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B α *
        Matrix.transvection q i k := by
  refine eq_mul_transvection_of_columns _ _ q i k ?_ ?_
  · intro u
    simp only [canonicalMiddleMatrix, classCoordinateMatrix]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    simp only [canonicalMiddleMatrix, classCoordinateMatrix, hother j hji]

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem MorseCancel.SurgeryWindows.regular_before_first_middle_pivot {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ}
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (q : Fin n) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j)) :
    ∀ y, f y ∈ Set.Icc a (S.lower (p q)) → y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro y hy hcrit
  let z : Smale.ManifoldMorse.criticalPoints E f := ⟨y, hcrit⟩
  have hlt : f z < f (p q) := hy.2.trans_lt (S.lower_lt_value (p q))
  have hle : MorseCancel.nativeMorseIndex E f z ≤ 3 := (horder z (p q) hlt).trans_eq (hp q)
  have heq : MorseCancel.nativeMorseIndex E f z = 3 := by
    apply Nat.le_antisymm hle
    by_contra hnot
    exact (hcut z (lt_of_not_ge hnot)).not_ge hy.1
  obtain ⟨j, hj⟩ := hcomplete z heq
  by_cases hjq : j = q
  · exact (ne_of_lt hlt) (congrArg f (congrArg Subtype.val (hj.symm.trans (congrArg p hjq))))
  · have hreverse : f (p q) < f z := by simpa only [hj] using hfirst j hjq
    exact hlt.not_gt hreverse

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem MorseCancel.low_index_cut_of_preserved_other_values {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {g : M → ℝ} {a : ℝ}
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindices :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (houtside : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z)
    (hcut : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z < 3 → f z < a) :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z < 3 → g z < a := by
  intro z hz
  let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
  have hidx : nativeMorseIndex E f zf < 3 := by
    rw [← hindices z zf.property]
    exact hz
  have hother : ∀ j, z.val ≠ (p j).val := by
    intro j hj
    have heq : zf = p j := Subtype.ext hj
    rw [heq, hp j] at hidx
    exact (lt_irrefl _ hidx)
  rw [houtside z zf.property hother]
  exact hcut zf hidx

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_labelled_integer_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {r n : ℕ}
    (p : Fin (n + 1) → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin (n + 1) → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (q i : Fin (n + 1)) (hqi : q ≠ i) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j))
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower (p q)) →
          y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (k : ℤ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            (∀ j, a < T.toSurgeryWindows.lower (p j)) ∧
              ∃ Γ : Fin (n + 1) → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                MorseCancel.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) ∧
                  (∀ j, j ≠ i → Γ j = γ j) ∧
                    MorseCancel.middleSectionClass (Γ i) =
                        MorseCancel.middleSectionClass (γ i) +
                          k • MorseCancel.middleSectionClass (γ q) ∧
                      MorseCancel.canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n :=
                            n + 1) B Γ =
                          MorseCancel.canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r)
                              (n := n + 1) B γ *
                            Matrix.transvection q i k ∧
                        Function.Surjective (MorseCancel.canonicalMiddleMatrix B Γ).mulVec ∧
                          ∀ z : M,
                            f z ≤ f (p q) →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  classical
  let e := Equiv.swap (0 : Fin (n + 1)) q
  have he0 : e 0 = q := Equiv.swap_apply_left _ _
  have heq : e q = 0 := Equiv.swap_apply_right _ _
  have hee (j : Fin (n + 1)) : e (e j) = j := Equiv.swap_apply_self _ _ _
  have hne : e i ≠ 0 := fun hi => hqi (e.injective (heq.trans hi.symm))
  obtain ⟨l, hl⟩ := Fin.exists_succ_eq_of_ne_zero hne
  have hel : e l.succ = i := by rw [hl, hee]
  have hpcases : Fin.cases (p q) (fun j => p (e j.succ)) = p ∘ e := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
    | succ j => rfl
  have hγcases : Fin.cases (γ q) (fun j => γ (e j.succ)) = γ ∘ e := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
    | succ j => rfl
  have hfamily :
    MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases (p q) (fun j => p (e j.succ)))
      (Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x)) := by
    have hmaps :
      Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x) = (fun j x => γ j x) ∘ e := by
      funext j x
      cases j using Fin.cases with
      | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
      | succ j => rfl
    rw [hpcases, hmaps]
    exact MorseCancel.nativeMiddleBasinFamily_reindex S hf ha p (fun j => γ j) hγ e e.injective
  have hhigh (j : Fin n) : S.toSurgeryWindows.upper (p q) < f (p (e j.succ)) := by
    have hjq : e j.succ ≠ q := by
      intro hj
      have hzero : j.succ = 0 := e.injective (hj.trans he0.symm)
      exact Fin.succ_ne_zero j hzero
    exact
      (S.toSurgeryWindows.upper_lt_lower (p q) (p (e j.succ)) (hfirst _ hjq)).trans
        (S.toSurgeryWindows.lower_lt_value _)
  obtain ⟨T, hcharts, hradii, hgerms, -, -, -, Δ, hΔ, hother, hclass, hkeep⟩ :=
    S.exists_integer_column_slide hf hm hdim horder (p q) (hp q) ha (hlower q) hband
      (fun j => p (e j.succ)) l (fun j => hp (e j.succ)) hhigh (γ q) (fun j => γ (e j.succ))
      hfamily k
  let δ : Fin (n + 1) → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }) := Fin.cases (γ q) Δ
  let Γ := δ ∘ e
  have hΓ : MorseCancel.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := by
    have hh :=
      MorseCancel.nativeMiddleBasinFamily_reindex T hf ha
        (Fin.cases (p q) (fun j => p (e j.succ))) (Fin.cases (fun x => γ q x) (fun j x => Δ j x))
        hΔ e e.injective
    have hlabels : (Fin.cases (p q) (fun j => p (e j.succ))) ∘ e = p := by
      rw [hpcases]
      funext j
      exact congrArg p (hee j)
    rw [hlabels] at hh
    have hmaps : (Fin.cases (fun x => γ q x) (fun j x => Δ j x)) ∘ e = (fun j x => Γ j x) := by
      funext j x
      change
        Fin.cases (motive := fun _ : Fin (n + 1) =>
            (Smale.Hemisphere.Sphere 2) → { y : M // f y = a }) (fun x => γ q x)
            (fun j x => Δ j x) (e j) x =
          (Fin.cases (motive := fun _ : Fin (n + 1) =>
              C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (γ q) Δ (e j))
            x
      cases e j using Fin.cases <;> rfl
    rw [hmaps] at hh
    exact hh
  have hΓother (j : Fin (n + 1)) (hji : j ≠ i) : Γ j = γ j := by
    change Fin.cases (γ q) Δ (e j) = γ j
    by_cases hjzero : e j = 0
    · have hjq : j = q := e.injective (hjzero.trans heq.symm)
      rw [hjzero, Fin.cases_zero, hjq]
    · obtain ⟨v, hv⟩ := Fin.exists_succ_eq_of_ne_zero hjzero
      have hvl : v ≠ l := by
        intro hvl
        apply hji
        exact e.injective (hv.symm.trans ((congrArg Fin.succ hvl).trans hl))
      rw [← hv, Fin.cases_succ, hother v hvl]
      exact congrArg γ (by rw [hv, hee])
  have hΓclass :
    MorseCancel.middleSectionClass (Γ i) =
      MorseCancel.middleSectionClass (γ i) + k • MorseCancel.middleSectionClass (γ q) := by
    change MorseCancel.middleSectionClass (Fin.cases (γ q) Δ (e i)) = _
    rw [← hl, Fin.cases_succ]
    simpa only [hel] using hclass
  have hmatrix :=
    MorseCancel.canonicalMiddleMatrix_single_class_addition (f := f) (a := a) B γ Γ q i k hΓother
      hΓclass
  refine ⟨T, hcharts, hradii, hgerms, ?_, Γ, hΓ, hΓother, hΓclass, hmatrix, ?_, hkeep⟩
  · intro j
    exact
      (hlower j).trans_le
        (MorseCancel.lower_window_le_of_radius_le S.toSurgeryWindows T.toSurgeryWindows (p j)
          (hradii _))
  · rw [hmatrix]
    exact MorseCancel.mul_transvection_surjective _ q i hqi k hsurj

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_arbitrary_column_addition {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (q i : Fin n)
    (hqi : q ≠ i) (k : ℤ) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                  MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                (∀ d, MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                        MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                  ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                  let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                  let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                  (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                        MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        ∃ Γ :
                                          Fin n →
                                            C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }),
                                          MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                              (fun j => Γ j) ∧
                                            (∀ j,
                                                j ≠ i →
                                                  Γ j =
                                                    MorseCancel.equalCutSection hlevel (γ j)) ∧
                                              MorseCancel.canonicalMiddleMatrix (M := M) (f := g)
                                                    (a := a) (r := r) (n := n) B' Γ =
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                      f) (a := a) (r := r) (n := n) B γ *
                                                    Matrix.transvection q i k ∧
                                                Function.Surjective
                                                    (MorseCancel.canonicalMiddleMatrix B'
                                                        Γ).mulVec ∧
                                                  ∀ z : M,
                                                    f z ≤ a →
                                                      (∀ x,
                                                          Filter.Tendsto (fun t => T.flow t x)
                                                              Filter.atBot (𝓝 z) ↔
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                              Filter.atBot (𝓝 z)) ∧
                                                        (∀ x,
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                                Filter.atBot (𝓝 z) →
                                                              Set.range (fun t => T.flow t x) =
                                                                Set.range (fun t => S.flow t x)) ∧
                                                          ∀ v,
                                                            Filter.Tendsto (fun t => T.flow t z)
                                                                Filter.atTop (𝓝 v) ↔
                                                              Filter.Tendsto (fun t => S.flow t z)
                                                                Filter.atTop (𝓝 v) := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ
    n =>
    obtain
      ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hfirst, hsub, hlevel, hga, T,
        hfield, hflow, hgerm, hpg, hglower, hfamily, -, hmatrix, hgsurj⟩ :=
      S.exists_first_middle_pivot hf hm ha horder p hp hcomplete hlower B γ hγ hsurj q
    let pg : Fin (n + 1) → Smale.ManifoldMorse.criticalPoints E g := fun j =>
      ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
    let γg := fun j => MorseCancel.equalCutSection hlevel (γ j)
    have hgcut :=
      MorseCancel.low_index_cut_of_preserved_other_values hcrit hindices p hp houtside hcut
    have hgcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g,
        MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, pg j = z := by
      intro z hz
      let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : MorseCancel.nativeMorseIndex E f zf = 3 := (hindices z zf.property).symm.trans hz
      obtain ⟨j, hj⟩ := hcomplete zf hzf
      exact
        ⟨j, Subtype.ext (congrArg (fun z : Smale.ManifoldMorse.criticalPoints E f => z.val) hj)⟩
    have hband :=
      MorseCancel.SurgeryWindows.regular_before_first_middle_pivot T.toSurgeryWindows hgorder
        hgcut pg hpg hgcomplete q hfirst
    obtain ⟨U, -, -, ugerms, ulower, Γ, hΓ, uother, -, umatrix, usurj, ukeep⟩ :=
      T.exists_labelled_integer_slide hg hmg hdim hgorder hga pg hpg hglower Bg γg hfamily hgsurj
        q i hqi hfirst hband k
    refine
      ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, U, ?_,
        hgerm, hpg, hgcomplete, ulower, Γ, hΓ, uother, ?_, usurj, ?_⟩
    · intro z hz
      filter_upwards [ugerms z (hcrit.symm ▸ hz)] with y hy
      exact hy.trans (congrFun hfield y)
    · exact umatrix.trans (congrArg (fun A => A * Matrix.transvection q i k) hmatrix)
    · intro z hz
      have hheight : g z ≤ g (pg q) :=
        ((hsub z).mpr hz).trans ((hglower q).trans (T.toSurgeryWindows.lower_lt_value (pg q))).le
      simpa only [hflow] using ukeep z hheight

theorem MorseCancel.equalCutSection_trans {M : Type} [TopologicalSpace M] {f g h : M → ℝ} {a : ℝ}
    (hfg : ∀ y, g y = a ↔ f y = a) (hgh : ∀ y, h y = a ↔ g y = a)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    equalCutSection hgh (equalCutSection hfg γ) =
      equalCutSection (fun y => (hgh y).trans (hfg y)) γ :=
  rfl

theorem MorseCancel.equalCutHomologyEquiv_refl {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} :
    equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl) =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2) := by
  apply LinearEquiv.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun 2
        x =
      x
  have hmap :
    (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun =
      ContinuousMap.id { y : M // f y ≤ a } :=
    rfl
  rw [hmap, PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

theorem MorseCancel.equalCutHomologyEquiv_trans {M : Type} [TopologicalSpace M] {f g h : M → ℝ}
    {a : ℝ} (hfg : ∀ y, g y ≤ a ↔ f y ≤ a) (hgh : ∀ y, h y ≤ a ↔ g y ≤ a) :
    (equalCutHomologyEquiv hfg).trans (equalCutHomologyEquiv hgh) =
      equalCutHomologyEquiv (fun y => (hgh y).trans (hfg y)) := by
  apply LinearEquiv.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph hgh).toHomotopyEquiv.toFun 2
        (SingularMayerVietoris.singularHomologyMap
          (equalCutSublevelHomeomorph hfg).toHomotopyEquiv.toFun 2 x) =
      SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph (fun y => (hgh y).trans (hfg y))).toHomotopyEquiv.toFun 2 x
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_arbitrary_column_sequence {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (ops : List (Fin n × Fin n × ℤ)) (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                  MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                (∀ d, MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                        MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                  ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                  let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                  let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                  (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                        MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        ∃ Γ :
                                          Fin n →
                                            C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }),
                                          MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                              (fun j => Γ j) ∧
                                            (∀ j,
                                                (∀ op ∈ ops, op.2.1 ≠ j) →
                                                  Γ j =
                                                    MorseCancel.equalCutSection hlevel (γ j)) ∧
                                              MorseCancel.canonicalMiddleMatrix (M := M) (f := g)
                                                    (a := a) (r := r) (n := n) B' Γ =
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                      f) (a := a) (r := r) (n := n) B γ *
                                                    (ops.map
                                                        (fun op =>
                                                          Matrix.transvection op.1 op.2.1
                                                            op.2.2)).prod ∧
                                                Function.Surjective
                                                    (MorseCancel.canonicalMiddleMatrix B'
                                                        Γ).mulVec ∧
                                                  ∀ z : M,
                                                    f z ≤ a →
                                                      (∀ x,
                                                          Filter.Tendsto (fun t => T.flow t x)
                                                              Filter.atBot (𝓝 z) ↔
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                              Filter.atBot (𝓝 z)) ∧
                                                        (∀ x,
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                                Filter.atBot (𝓝 z) →
                                                              Set.range (fun t => T.flow t x) =
                                                                Set.range (fun t => S.flow t x)) ∧
                                                          ∀ v,
                                                            Filter.Tendsto (fun t => T.flow t z)
                                                                Filter.atTop (𝓝 v) ↔
                                                              Filter.Tendsto (fun t => S.flow t z)
                                                                Filter.atTop (𝓝 v) := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro hvalid
    have hB :
      B.trans (MorseCancel.equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl)) = B := by
      rw [MorseCancel.equalCutHomologyEquiv_refl, LinearEquiv.trans_refl]
    refine
      ⟨f, hf, hm, rfl, horder, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, hcut, fun _ =>
        Iff.rfl, fun _ => Iff.rfl, ha, S, ?_, fun _ _ => Filter.EventuallyEq.rfl, hp, hcomplete,
        hlower, γ, hγ, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · rw [hB]
      simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
    · rw [hB]
      exact hsurj
    · intro z hz
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 := fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop : op.1 ≠ op.2.1 :=
      hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    obtain
      ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, T,
        hgerms, hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
      ih hprev
    let pg : Fin n → Smale.ManifoldMorse.criticalPoints E g := fun j =>
      ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
    obtain
      ⟨u, hu, hmu, hcu, huorder, huindices, hucounts, huoutside, hucut, husub, hulevel, hua, U,
        hugerms, hufgerms, hpu, hucomplete, hulower, Δ, hΔ, huother, humatrix, husurj, hukeep⟩ :=
      T.exists_arbitrary_column_addition hg hmg hdim hgorder hga hgcut pg hpg hgcomplete hglower
        Bg Γ hΓ hgsurj op.1 op.2.1 hop op.2.2
    let hsub' : ∀ y, u y ≤ a ↔ f y ≤ a := fun y => (husub y).trans (hsub y)
    let hlevel' : ∀ y, u y = a ↔ f y = a := fun y => (hulevel y).trans (hlevel y)
    have hB :
      Bg.trans (MorseCancel.equalCutHomologyEquiv husub) =
        B.trans (MorseCancel.equalCutHomologyEquiv hsub') := by
      change
        (B.trans (MorseCancel.equalCutHomologyEquiv hsub)).trans
            (MorseCancel.equalCutHomologyEquiv husub) =
          _
      rw [LinearEquiv.trans_assoc, MorseCancel.equalCutHomologyEquiv_trans]
    refine
      ⟨u, hu, hmu, hcu.trans hcrit, huorder,
        (fun z hz => (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)),
        (fun d => (hucounts d).trans (hcounts d)),
        (fun z hz hzo => (huoutside z (hcrit.symm ▸ hz) hzo).trans (houtside z hz hzo)), hucut,
        hsub', hlevel', hua, U, ?_, ?_, hpu, hucomplete, hulower, Δ, hΔ, ?_, ?_, ?_, ?_⟩
    · intro z hz
      filter_upwards [hugerms z (hcrit.symm ▸ hz), hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · intro y hy
      exact (hufgerms y ((hsub y).mpr hy)).trans (hfgerms y hy)
    · intro j hj
      have hlast : j ≠ op.2.1 := fun heq =>
        hj op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op))) heq.symm
      have hbefore : ∀ e ∈ ops, e.2.1 ≠ j := fun e he => hj e (List.mem_append.mpr (Or.inl he))
      rw [huother j hlast, hother j hbefore]
      exact MorseCancel.equalCutSection_trans hlevel hulevel (γ j)
    · rw [← hB, humatrix, hmatrix, Matrix.mul_assoc]
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    · rw [← hB]
      exact husurj
    · intro z hz
      have hUT := hukeep z ((hsub z).mpr hz)
      have hTS := hkeep z hz
      exact
        ⟨fun x => (hUT.1 x).trans (hTS.1 x), fun x hx =>
          (hUT.2.1 x ((hTS.1 x).mpr hx)).trans (hTS.2.1 x hx), fun v =>
          (hUT.2.2 v).trans (hTS.2.2 v)⟩

theorem MorseCancel.mul_transvection_list_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : Function.Surjective A.mulVec) (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    Function.Surjective
      (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod).mulVec := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro hvalid
    simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hA
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 := fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop := hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    simpa only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      ← Matrix.mul_assoc] using mul_transvection_surjective _ op.1 op.2.1 hop op.2.2 (ih hprev)

theorem MorseCancel.primitive_row_has_unit_after_column_additions {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℤ) (hA : Function.Surjective A.mulVec) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = 1 ∨
            (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = -1 := by
  classical
  have hnonzero : ∃ j, A 0 j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨x, hx⟩ := hA 1
    have hh := congrFun hx 0
    change ∑ j, A 0 j * x j = 1 at hh
    simp only [hnot, MulZeroClass.zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  let P : ℕ → Prop := fun m =>
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i ≠ 0 ∧
            ((A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i).natAbs =
              m
  obtain ⟨j₀, hj₀⟩ := hnonzero
  have hex : ∃ m, P m := by
    refine ⟨(A 0 j₀).natAbs, [], ?_, j₀, ?_, ?_⟩
    · intro op hop
      simp only [List.not_mem_nil] at hop
    · simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hj₀
    · simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
  obtain ⟨ops, hvalid, i, hi, hrank⟩ := Nat.find_spec hex
  let C := A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod
  have hC : Function.Surjective C.mulVec := mul_transvection_list_surjective A hA ops hvalid
  have hdiv (j : Fin n) : C 0 i ∣ C 0 j := by
    by_cases hij : i = j
    · subst j
      exact dvd_refl _
    apply Int.dvd_of_emod_eq_zero
    by_contra hrem
    let op : Fin n × Fin n × ℤ := (i, j, -(C 0 j / C 0 i))
    let ops' := ops ++ [op]
    have hvalid' : ∀ e ∈ ops', e.1 ≠ e.2.1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hvalid e he
      · have heq : e = op := List.mem_singleton.mp he
        subst e
        exact hij
    have hnew :
      A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod =
        C * Matrix.transvection i j (-(C 0 j / C 0 i)) := by
      simp only [ops', List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        ← Matrix.mul_assoc]
      rfl
    have hentry :
      (A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod) 0 j = C 0 j % C 0 i := by
      rw [hnew, Matrix.mul_transvection_apply_same, Int.emod_def]
      ring
    have hsmall : (C 0 j % C 0 i).natAbs < (C 0 i).natAbs := by
      have hh :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (C 0 j) hi)
          (Int.emod_lt_abs (C 0 j) hi)
      simpa only [Int.natAbs_abs] using hh
    have hminimal :=
      Nat.find_min' hex
        (show P (C 0 j % C 0 i).natAbs from
          ⟨ops', hvalid', j, (by rw [hentry]; exact hrem), congrArg Int.natAbs hentry⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hsmall) hminimal
  obtain ⟨x, hx⟩ := hC 1
  have hsum := congrFun hx 0
  change ∑ j, C 0 j * x j = 1 at hsum
  have hdvd : C 0 i ∣ 1 := by
    rw [← hsum]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (hdiv j) (x j))
  obtain ⟨v, hv⟩ := hdvd
  exact ⟨ops, hvalid, i, Int.eq_one_or_neg_one_of_mul_eq_one hv.symm⟩

theorem MorseCancel.functional_class_row_surjective {H : Type} [AddCommGroup H] [Module ℤ H]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (v : Fin n → H)
    (hA : Function.Surjective (classCoordinateMatrix B v).mulVec) (L : H →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    Function.Surjective (Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j))).mulVec := by
  intro y
  obtain ⟨h, hh⟩ := hL (y 0)
  obtain ⟨x, hx⟩ := hA (B.symm h)
  have hsum : (∑ j, x j • v j) = h := by
    rw [← classCoordinateMatrix_mulVec B v x, hx, LinearEquiv.apply_symm_apply]
  refine ⟨x, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have heq := congrArg L hsum
  rw [map_sum] at heq
  simp only [map_zsmul, smul_eq_mul] at heq
  change ∑ j, L (v j) * x j = y 0
  rw [← hh, ← heq]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem MorseCancel.transported_classes_of_matrix_product {H K : Type} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P) (j : Fin n) :
    e.symm (w j) = ∑ i, P i j • v i := by
  have hvec : (classCoordinateMatrix B v).mulVec (fun i => P i j) = (B.trans e).symm (w j) := by
    funext i
    exact (congrFun (congrFun hmatrix i) j).symm
  calc
    e.symm (w j) = B ((classCoordinateMatrix B v).mulVec (fun i => P i j)) := by
      rw [hvec]
      exact (B.apply_symm_apply (e.symm (w j))).symm
    _ = _ := classCoordinateMatrix_mulVec B v _

theorem MorseCancel.functional_rows_of_matrix_product {H K : Type} [AddCommGroup H] [Module ℤ H]
    [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (L : H →ₗ[ℤ] ℤ) :
    Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (e.symm (w j))) =
      Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j)) * P := by
  funext u j
  change L (e.symm (w j)) = ∑ i, L (v i) * P i j
  rw [transported_classes_of_matrix_product B e v w P hmatrix j, map_sum]
  simp only [map_zsmul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_primitive_functional_unit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (L : SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ g : M → ℝ,
          ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
            Smale.ManifoldMorse.IsMorse E g ∧
              ∃ hcrit :
                Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
                (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                    g x < g y →
                      MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                    (∀ d,
                        MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          (∀ j, z ≠ (p j).val) → g z = f z) ∧
                        (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                            MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                          ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                            ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                              ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                                ∃ T : AdaptedWindows E g,
                                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                    (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                      let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                        fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                      let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                      (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                        (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                            MorseCancel.nativeMorseIndex E g z = 3 →
                                              ∃ j, p' j = z) ∧
                                          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                            ∃ Γ :
                                              Fin n →
                                                C((Smale.Hemisphere.Sphere 2),
                                                  { y : M // g y = a }),
                                              MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                                  (fun j => Γ j) ∧
                                                (∀ j,
                                                    (∀ op ∈ ops, op.2.1 ≠ j) →
                                                      Γ j =
                                                        MorseCancel.equalCutSection hlevel
                                                          (γ j)) ∧
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                        g) (a := a) (r := r) (n := n) B' Γ =
                                                      MorseCancel.canonicalMiddleMatrix (M := M)
                                                          (f := f) (a := a) (r := r) (n := n) B
                                                          γ *
                                                        (ops.map
                                                            (fun op =>
                                                              Matrix.transvection op.1 op.2.1
                                                                op.2.2)).prod ∧
                                                    Function.Surjective
                                                        (MorseCancel.canonicalMiddleMatrix B'
                                                            Γ).mulVec ∧
                                                      (∃ i : Fin n,
                                                          L
                                                                ((MorseCancel.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancel.middleSectionClass
                                                                    (Γ i))) =
                                                              1 ∨
                                                            L
                                                                ((MorseCancel.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancel.middleSectionClass
                                                                    (Γ i))) =
                                                              -1) ∧
                                                        ∀ z : M,
                                                          f z ≤ a →
                                                            (∀ x,
                                                                Filter.Tendsto
                                                                    (fun t => T.flow t x)
                                                                    Filter.atBot (𝓝 z) ↔
                                                                  Filter.Tendsto
                                                                    (fun t => S.flow t x)
                                                                    Filter.atBot (𝓝 z)) ∧
                                                              (∀ x,
                                                                  Filter.Tendsto
                                                                      (fun t => S.flow t x)
                                                                      Filter.atBot (𝓝 z) →
                                                                    Set.range
                                                                        (fun t => T.flow t x) =
                                                                      Set.range
                                                                        (fun t => S.flow t x)) ∧
                                                                ∀ v,
                                                                  Filter.Tendsto
                                                                      (fun t => T.flow t z)
                                                                      Filter.atTop (𝓝 v) ↔
                                                                    Filter.Tendsto
                                                                      (fun t => S.flow t z)
                                                                      Filter.atTop (𝓝 v) := by
  let A : Matrix (Fin 1) (Fin n) ℤ := fun _ j => L (MorseCancel.middleSectionClass (γ j))
  have hsurj' :
    Function.Surjective
      (MorseCancel.classCoordinateMatrix B
          (fun j => MorseCancel.middleSectionClass (γ j))).mulVec := by
    simpa only [MorseCancel.canonicalMiddleMatrix] using hsurj
  have hA : Function.Surjective A.mulVec :=
    MorseCancel.functional_class_row_surjective B (fun j => MorseCancel.middleSectionClass (γ j))
      hsurj' L hL
  obtain ⟨ops, hvalid, i, hi⟩ := MorseCancel.primitive_row_has_unit_after_column_additions A hA
  obtain
    ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, T, hgerms,
      hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
    S.exists_arbitrary_column_sequence hf hm hdim horder ha hcut p hp hcomplete hlower B γ hγ
      hsurj ops hvalid
  have hcoord :
    MorseCancel.classCoordinateMatrix (B.trans (MorseCancel.equalCutHomologyEquiv hsub))
        (fun j => MorseCancel.middleSectionClass (Γ j)) =
      MorseCancel.classCoordinateMatrix B (fun j => MorseCancel.middleSectionClass (γ j)) *
        (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod := by
    simpa only [MorseCancel.canonicalMiddleMatrix] using hmatrix
  have hrows :=
    MorseCancel.functional_rows_of_matrix_product B (MorseCancel.equalCutHomologyEquiv hsub)
      (fun j => MorseCancel.middleSectionClass (γ j))
      (fun j => MorseCancel.middleSectionClass (Γ j)) _ hcoord L
  have hentry := congrFun (congrFun hrows 0) i
  refine
    ⟨ops, hvalid, g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel,
      hga, T, hgerms, hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, ⟨i, ?_⟩,
      hkeep⟩
  exact hi.elim (fun h => Or.inl (hentry.trans h)) (fun h => Or.inr (hentry.trans h))

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
def MorseCancel.regularCutHomologyEquiv {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a ≤ b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ b } 2 :=
  LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) 2)
    (regular_sublevel_inclusion_bijective hf hab hband 2)

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_lower_cut_geometric_matrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hba : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hband : ∀ y, f y ∈ Set.Icc b a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (za : { y : M // f y = a }) {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) :
    ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }),
      MorseCancel.IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (γ j x).val = (β j x).val) ∧
          (∀ j,
              MorseCancel.regularCutHomologyEquiv hf hba.le hband
                  (MorseCancel.middleSectionClass (β j)) =
                MorseCancel.middleSectionClass (γ j)) ∧
            let B' := B.trans (MorseCancel.regularCutHomologyEquiv hf hba.le hband).symm
            MorseCancel.canonicalMiddleMatrix B' β = MorseCancel.canonicalMiddleMatrix B γ ∧
              Function.Surjective (MorseCancel.canonicalMiddleMatrix B' β).mulVec := by
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨β₀, hβ, horbit⟩ :=
    S.exists_regular_band_middle_basin_family hf hba ha hb (fun y hy h => hband y h hy) za p hp
      (fun j => γ j) hγ
  let β : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }) := fun j =>
    ⟨β₀ j, (hβ.1 j).continuous⟩
  have hclass (j : Fin n) :
    MorseCancel.regularCutHomologyEquiv hf hba.le hband (MorseCancel.middleSectionClass (β j)) =
      MorseCancel.middleSectionClass (γ j) :=
    S.section_class_of_flow_transport hf hba hb (γ j) (β j) (horbit j)
  let B' := B.trans (MorseCancel.regularCutHomologyEquiv hf hba.le hband).symm
  have hmatrix : MorseCancel.canonicalMiddleMatrix B' β = MorseCancel.canonicalMiddleMatrix B γ :=
    by
    funext i j
    simp only [MorseCancel.canonicalMiddleMatrix, MorseCancel.classCoordinateMatrix]
    change
      B.symm
          (MorseCancel.regularCutHomologyEquiv hf hba.le hband
            (MorseCancel.middleSectionClass (β j)))
          i =
        B.symm (MorseCancel.middleSectionClass (γ j)) i
    rw [hclass j]
  refine ⟨β, hβ, horbit, hclass, hmatrix, ?_⟩
  rw [hmatrix]
  exact hsurj

theorem MorseCancel.native_middle_block_complete_and_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    (∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, nativeMiddleBlockPoint S r n hrc j = z) ∧
      (∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < nativeMiddleBaseCut S r n hrc) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr] at htwo
  rw [hrr, hnn] at hthree hafter
  let W := S.toSurgeryWindows
  have hrcW : r + n < W.count := hrc
  have hpos := W.count_pos hf
  have hi0 (i : Fin W.count) (hi : i.val = 0) : nativeMorseIndex E f (W.point i) = 0 := by
    have he : i = ⟨0, hpos⟩ := Fin.ext hi
    rw [he]
    exact
      (nativeMorseIndex_eq_chart (S.data (W.first hpos)).chart).trans (W.first_index_zero hf hpos)
  have hi2 (i : Fin W.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
    nativeMorseIndex E f (W.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin W.count) (hri : r < i.val) (hin : i.val ≤ r + n) :
    nativeMorseIndex E f (W.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (hthree i hri hin)
  have hi4 (i : Fin W.count) (hin : r + n < i.val) : 4 ≤ nativeMorseIndex E f (W.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (W.point i)).chart]
    exact hafter i hin
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hiz : i.val ≠ 0 := by
      intro hi
      have hh := hi0 i hi
      omega
    have hri : r < i.val := by
      by_contra hnot
      have hh := hi2 i (by omega) (le_of_not_gt hnot)
      omega
    have hin : i.val ≤ r + n := by
      by_contra hnot
      have hh := hi4 i (lt_of_not_ge hnot)
      omega
    refine ⟨⟨i.val - (r + 1), by omega⟩, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (i.val - (r + 1)) + 1 = i.val
    omega
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hir : i.val ≤ r := by
      by_contra hnot
      by_cases hin : i.val ≤ r + n
      · have hh := hi3 i (lt_of_not_ge hnot) hin
        omega
      · have hh := hi4 i (lt_of_not_ge hin)
        omega
    exact
      (W.point_strictMono.monotone (show i ≤ ⟨r, by omega⟩ from hir)).trans_lt
        (W.value_lt_upper _)

theorem Smale.HomologyTransport.integerEquiv_one_natAbs (e : ℤ ≃ₗ[ℤ] ℤ) : (e 1).natAbs = 1 := by
  have h : e.symm 1 * e 1 = 1 := by
    calc
      e.symm 1 * e 1 = e (e.symm 1 • (1 : ℤ)) := by
        rw [map_zsmul, zsmul_eq_mul]
        simp
      _ = 1 := by simp
  exact Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one_right _ h)

theorem Smale.SpherePoint.sourceCountMark_topClass_natAbs (n : ℕ) {N : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    (sourceCountMark n j B (SphereHomology.unitSphereTopClass (n + 1))).natAbs = 1 :=
  Smale.HomologyTransport.integerEquiv_one_natAbs
    ((SphereHomology.unitSphereHomologyTopEquiv (n + 1)).symm.trans (sourceCountMark n j B))

theorem Smale.OnePointCover.overlapHomologyEquiv_symm_include {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.PuncturedRadial.Space N) k) :
    (overlapHomologyEquiv r hr k).symm
        (SingularMayerVietoris.singularHomologyMap overlapHomeomorph.toHomotopyEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap Smale.PuncturedRadial.toSphere k a := by
  change
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k).symm _ = _
  rw [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply]
  have heq :
    (overlapSphereEquiv (N := N) r hr).symm.toFun.comp overlapHomeomorph.toHomotopyEquiv.toFun =
      Smale.PuncturedRadial.toSphere := by
    apply ContinuousMap.ext
    intro x
    change Smale.PuncturedRadial.toSphere (overlapHomeomorph.symm (overlapHomeomorph x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, heq]

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.collapseComponentConnecting {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1) →ₗ[ℤ]
      (∀ i : d.beltIntersectionPoints m g,
        SingularMayerVietoris.SingularHomology
          (↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i)) k) :=
  Smale.CoverLocalContributions.componentConnecting (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    k

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.collapseLocalClass {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) k :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm
    (d.collapseComponentConnecting m g D k a i)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_overlaps {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism Smale.OnePointCover.oldPatch
        Smale.OnePointCover.finitePatch Smale.OnePointCover.oldPatch_open
        Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (d.collapseOverlapMap hf m g D i) k
          (d.collapseComponentConnecting m g D k a i) :=
  Smale.CoverLocalContributions.connecting_sum (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    Smale.OnePointCover.oldPatch Smale.OnePointCover.finitePatch (d.attachingCollapse hf m g)
    (d.attachingCollapse_maps_old hf m g) (d.attachingCollapse_maps_neighborhood hf m g D)
    Smale.OnePointCover.oldPatch_open Smale.OnePointCover.finitePatch_open
    Smale.OnePointCover.cover k a

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_boundaries {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism Smale.OnePointCover.oldPatch
        Smale.OnePointCover.finitePatch Smale.OnePointCover.oldPatch_open
        Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap
          (Smale.OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
            (D.data i).innerBoundary.map)
          k (d.collapseLocalClass m g D k a i) := by
  rw [d.collapseConnecting_sum_overlaps hf m g D k a]
  apply Finset.sum_congr rfl
  intro i _
  have h :
    SingularMayerVietoris.singularHomologyMap (D.overlapSphereEquiv i).toFun k
        (d.collapseLocalClass m g D k a i) =
      d.collapseComponentConnecting m g D k a i :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv i)
          k).apply_symm_apply
      _
  rw [← h, ← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    d.collapseOverlapMap_sphereEquiv hf m g D i]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_sum {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1)) :
    Smale.OnePointCover.sphereConnecting r hr k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (D.data i).innerBoundary.normalizedMap k
          (d.collapseLocalClass m g D k a i) := by
  change
    (Smale.OnePointCover.overlapHomologyEquiv (N := d.chart.NegativeCoordinates) r hr k).symm
        (SingularMayerVietoris.connectingHomomorphism Smale.OnePointCover.oldPatch
          Smale.OnePointCover.finitePatch Smale.OnePointCover.oldPatch_open
          Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a)) =
      _
  rw [d.collapseConnecting_sum_boundaries hf m g D k a, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    Smale.OnePointCover.overlapHomologyEquiv_symm_include]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

theorem Smale.CoverOverlapHomology.homologyEquiv_symm_single {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (k : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k a := by
  rw [homologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

theorem Smale.CoverOverlapHomology.homologyEquiv_inclusion {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (k : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    homologyEquiv U V hU hV hd k
        (SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k a) =
      Pi.single i a := by
  apply (homologyEquiv U V hU hV hd k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_single]

def Smale.CoverOverlapHomology.componentMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y) (f : C(X, Y))
    (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) (i : ι) :
    C(↥(U ∩ V i), ↥(U' ∩ V' i)) :=
  Smale.CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

def Smale.CoverOverlapHomology.overlapMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y) (f : C(X, Y))
    (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) :
    C(↥(U ∩ ⋃ i, V i), ↥(U' ∩ ⋃ i, V' i)) :=
  Smale.CoverNaturality.mapOn f _ _
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx.2
      exact ⟨hfU hx.1, Set.mem_iUnion.mpr ⟨i, hfV i hi⟩⟩)

theorem Smale.CoverOverlapHomology.overlapMap_component {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) (i : ι) :
    (overlapMap U V U' V' f hfU hfV).comp (componentInclusion U V i) =
      (componentInclusion U' V' i).comp (componentMap U V U' V' f hfU hfV i) :=
  rfl

theorem Smale.CoverOverlapHomology.homologyEquiv_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) [Fintype ι]
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hU' : IsOpen U')
    (hV' : ∀ i, IsOpen (V' i)) (hd' : Pairwise (Disjoint on V')) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    homologyEquiv U' V' hU' hV' hd' k
        (SingularMayerVietoris.singularHomologyMap (overlapMap U V U' V' f hfU hfV) k a) =
      fun i =>
      SingularMayerVietoris.singularHomologyMap (componentMap U V U' V' f hfU hfV i) k
        (homologyEquiv U V hU hV hd k a i) := by
  apply (homologyEquiv U' V' hU' hV' hd' k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_apply, homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [overlapMap_component, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]

theorem Smale.CoverLocalContributions.componentConnecting_enlarge {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] (U U' : Set X) (V : ι → Set X) (hU : IsOpen U) (hU' : IsOpen U')
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    (hsub : U ⊆ U') (i : ι) (hci : U' ∪ V i = Set.univ) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.singularHomologyMap
        (Smale.CoverOverlapHomology.componentMap U V U' V (ContinuousMap.id X) hsub
          (fun _ _ hx => hx) i)
        k (componentConnecting U V hU hV hd hc k a i) =
      SingularMayerVietoris.connectingHomomorphism U' (V i) hU' (hV i) hci k a := by
  classical
  have hc' : U' ∪ (⋃ j, V j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ U ∪ (⋃ j, V j) := hc.symm ▸ Set.mem_univ x
    exact hx.elim (fun hu => Or.inl (hsub hu)) Or.inr
  have hbig :=
    Smale.CoverNaturality.connecting_naturality_apply U (⋃ j, V j) U' (⋃ j, V j)
      (ContinuousMap.id X) hsub (fun _ hx => hx) hU (isOpen_iUnion hV) hc hU' (isOpen_iUnion hV)
      hc' k a
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at hbig
  change
    SingularMayerVietoris.singularHomologyMap
        (Smale.CoverOverlapHomology.overlapMap U V U' V (ContinuousMap.id X) hsub
          (fun _ _ hx => hx))
        k
        (SingularMayerVietoris.connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a) =
      SingularMayerVietoris.connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k
        a at hbig
  have hcoord :=
    congrArg (fun b => Smale.CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hbig
  have hnat :=
    congrFun
      (Smale.CoverOverlapHomology.homologyEquiv_map U V U' V (ContinuousMap.id X) hsub
        (fun _ _ hx => hx) hU hV hd hU' hV hd k
        (SingularMayerVietoris.connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a))
      i
  rw [hnat] at hcoord
  have hsmall :=
    Smale.CoverNaturality.connecting_naturality_apply U' (V i) U' (⋃ j, V j) (ContinuousMap.id X)
      (fun _ hx => hx) (Set.subset_iUnion V i) hU' (hV i) hci hU' (isOpen_iUnion hV) hc' k a
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at hsmall
  change
    SingularMayerVietoris.singularHomologyMap
        (Smale.CoverOverlapHomology.componentInclusion U' V i) k
        (SingularMayerVietoris.connectingHomomorphism U' (V i) hU' (hV i) hci k a) =
      SingularMayerVietoris.connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k
        a at hsmall
  have hsingle :=
    congrArg (fun b => Smale.CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hsmall
  rw [Smale.CoverOverlapHomology.homologyEquiv_inclusion, Pi.single_eq_same] at hsingle
  exact hcoord.trans hsingle.symm

def Smale.LocalDegree.SeparatedNeighborhoods.pointComplementInclusion {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), ↥({(x : M)}ᶜ ∩ D.neighborhood x)) :=
  (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

theorem Smale.LocalDegree.SeparatedNeighborhoods.pointComplementInclusion_sphereEquiv
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M}
    {f : M → F} {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun =
      (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun := by
  apply ContinuousMap.ext
  intro u
  rfl

theorem Smale.LocalDegree.SeparatedNeighborhoods.componentConnecting_singlePoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    SingularMayerVietoris.singularHomologyMap (D.pointComplementInclusion x) k
        (Smale.CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a := by
  have hsub : Pᶜ ⊆ {(x : M)}ᶜ := by
    intro y hy hxy
    exact hy (hxy ▸ x.property)
  exact
    Smale.CoverLocalContributions.componentConnecting_enlarge Pᶜ {(x : M)}ᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl isClosed_singleton.isOpen_compl D.isOpen_neighborhood
      D.pairwise_disjoint D.open_cover hsub x
      (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a

theorem Smale.LocalDegree.SeparatedNeighborhoods.sphereConnecting_component {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
        (Smale.CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      Smale.LocalDegree.NativeNeighborhood.sphereConnecting (x : M) (D.data x) k a := by
  let c :=
    Smale.CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
      D.open_cover k a x
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).injective
  change
    SingularMayerVietoris.singularHomologyMap
        (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k)
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
              (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).symm
          _)
  rw [LinearEquiv.apply_symm_apply, ← D.pointComplementInclusion_sphereEquiv x]
  change
    SingularMayerVietoris.singularHomologyMap
        ((D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun) k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply]
  have h :
    SingularMayerVietoris.singularHomologyMap (D.overlapSphereEquiv x).toFun k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      c :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x)
          k).apply_symm_apply
      c
  rw [h]
  exact D.componentConnecting_singlePoint k a x

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalClass_singlePoint {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    d.collapseLocalClass m g D k a i =
      Smale.LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) k a :=
  D.sphereConnecting_component k a i

theorem Smale.SphereNormalCoordinates.localBoundary_homology_outward {V F : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) [Fact (Module.finrank ℝ V = (n + 2) + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 2))) (𝓡 (n + 2))
        (EuclideanSpace ℝ (Fin (n + 2))) (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (hz : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))
    (hA : (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0)).IsInvertible)
    (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (hL : L.toContinuousLinearMap = fderiv ℝ (f ∘ c) 0) {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (b : Smale.LocalDegree.BoundaryData (f ∘ c) L s) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1)
        ((SignType.sign (chartJacobian c j B 0) : ℤ) • a) =
      (SignType.sign (normalJacobian j (c 0) (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))) : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  have hs := chartJacobian_sign_factor c j B hz f hf hA
  have hd :
    (L.trans B.symm).toLinearEquiv.toLinearMap.det =
      (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) 0)).det := by
    rw [← hL]
    rfl
  rw [← hd] at hs
  have hi := congrArg (fun v : SignType => (v : ℤ)) hs
  simp only [SignType.coe_mul] at hi
  rw [map_zsmul, b.normalized_homology_eq_sign_smul n B k a, smul_smul, hi]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_homology_sign_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : Smale.Hemisphere.Sphere (n + 2) → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere (n + 2)),
      x ∈ d.beltIntersectionPoints (n + 2) g →
        ∀ (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates),
          L.toContinuousLinearMap =
              fderiv ℝ ((d.collapseNormal ∘ g) ∘ Smale.NativeParametrization.centered x) 0 →
            ∀ {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
              (b :
                Smale.LocalDegree.BoundaryData
                  ((d.collapseNormal ∘ g) ∘ Smale.NativeParametrization.centered x) L s)
              (k : ℕ)
              (a :
                SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1))
                  (k + 1)),
              SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1)
                  ((SignType.sign
                        (Smale.SphereNormalCoordinates.chartJacobian
                          (Smale.NativeParametrization.centered x) j B 0) :
                      ℤ) •
                    a) =
                (d.beltIntersectionSign (n + 2) j g x : ℤ) •
                  SingularMayerVietoris.singularHomologyMap
                    (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
                    (k + 1) a := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx L hL s b k a
  have hs := d.contMDiffAt_collapseNormal_comp hf (n + 2) g hg x hx
  have hA := d.isInvertible_collapseNormal_comp_of_transverse hf q (n + 2) hdim g hg ht x hx
  have hc0 := Smale.NativeParametrization.centered_zero (D := EuclideanSpace ℝ (Fin (n + 2))) x
  have h :=
    Smale.SphereNormalCoordinates.localBoundary_homology_outward n
      (Smale.NativeParametrization.centered x) j B
      (Smale.NativeParametrization.zero_mem_centered_source x) (d.collapseNormal ∘ g)
      (hc0.symm ▸ hs.mdifferentiableAt (by simp)) (hc0.symm ▸ hA) L hL b k a
  rw [hc0, d.collapseNormal_comp_sign_of_transverse hf q (n + 2) hdim j g hg ht x hx] at h
  exact h

theorem Smale.ManifoldMorse.MorseSurgeryData.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalClass_eq_outward {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (n : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Fintype (d.beltIntersectionPoints (n + 2) g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2))
    (i : d.beltIntersectionPoints (n + 2) g) :
    d.collapseLocalClass (n + 2) g D (k + 1) a i =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian
              (Smale.NativeParametrization.centered i.val) j B 0) :
          ℤ) •
        Smale.SpherePoint.outwardClass n j B k a := by
  rw [d.collapseLocalClass_singlePoint]
  exact Smale.SpherePoint.pointConnecting_eq_outward n j B i.val (D.data i) k a

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_outward {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Fintype (d.beltIntersectionPoints (n + 2) g)] :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2))
      (i : d.beltIntersectionPoints (n + 2) g),
      SingularMayerVietoris.singularHomologyMap (D.data i).innerBoundary.normalizedMap (k + 1)
          (d.collapseLocalClass (n + 2) g D (k + 1) a i) =
        (d.beltIntersectionSign (n + 2) j g i.val : ℤ) •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (Smale.SpherePoint.outwardClass n j B k a) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht k a i
  rw [d.collapseLocalClass_eq_outward n j B g D k a i]
  exact
    d.collapseLocalBoundary_homology_sign_of_transverse hf q n hdim j B g hg ht i.val i.property
      (D.linear i) (D.derivative_eq i) (D.data i).innerBoundary k _

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) [Fintype (d.beltIntersectionPoints m g)]
    (hfin : (d.beltIntersectionPoints m g).Finite) {A : Type*} [AddCommGroup A] (a : A) :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ) • a) =
      d.beltIntersectionCount m j g hfin • a := by
  have hcount :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ)) =
      d.beltIntersectionCount m j g hfin :=
    (Finset.sum_subtype hfin.toFinset (fun _ => hfin.mem_toFinset)
        (fun x => (d.beltIntersectionSign m j g x : ℤ))).symm
  exact Finset.sum_smul.symm.trans (congrArg (fun z : ℤ => z • a) hcount)

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Finite (d.beltIntersectionPoints (n + 2) g)] :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)),
      Smale.OnePointCover.sphereConnecting r hr (k + 1)
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g)
            (k + 2) a) =
        d.beltIntersectionCount (n + 2) j g (Set.toFinite _) •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (Smale.SpherePoint.outwardClass n j B k a) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) := Fintype.ofFinite _
  intro hg ht r hr k a
  apply (d.collapseSphereConnecting_sum hf.continuous (n + 2) g D r hr (k + 1) a).trans
  apply
    Eq.trans
      (Finset.sum_congr rfl
        (fun i _ => d.collapseLocalBoundary_outward hf q n hdim j B g D hg ht k a i))
  exact d.beltIntersectionCount_smul (n + 2) j g (Set.toFinite _) _

theorem Smale.ManifoldMorse.MorseSurgeryData.collapse_homology_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)),
      Smale.OnePointCover.sphereConnecting r hr (k + 1)
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g)
            (k + 2) a) =
        d.beltIntersectionCount (n + 2) j g
            (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht) •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (Smale.SpherePoint.outwardClass n j B k a) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht r hr k a
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) :=
    (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht).fintype
  obtain ⟨D⟩ := d.nonempty_collapseNeighborhoods hf q (n + 2) hdim g hg hinj ht
  exact d.collapseSphereConnecting_signed_count hf q n hdim j B g D hg ht r hr k a

theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere 2) 2),
      d.indexTwoCollapseCoordinate hf.continuous hindex
          (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2 a) =
        d.beltIntersectionCount 2 j g
            (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht) *
          Smale.SpherePoint.sourceCountMark 0 j (d.indexTwoNormalModel hindex) a := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht a
  have h :=
    Smale.SpherePoint.countMark_of_connecting 0 j (d.indexTwoNormalModel hindex) _ a _
      (d.collapse_homology_signed_count hf q 0 hindex j (d.indexTwoNormalModel hindex) g hg hinj
        ht 1 zero_lt_one 0 a)
  have hc :
    d.attachingCollapse hf.continuous 2 g =
      (d.upperCollapseMap hf.continuous).comp (d.upperLevelInclusion.comp g) :=
    rfl
  rw [hc, PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact h

theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_topClass_natAbs {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
            (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2
              (SphereHomology.unitSphereTopClass 1))).natAbs =
        (d.beltIntersectionCount 2 j g
            (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht)).natAbs := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  rw [d.indexTwoCoordinate_signed_count hf q hindex j g hg hinj ht, Int.natAbs_mul,
    Smale.SpherePoint.sourceCountMark_topClass_natAbs, mul_one]

theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_transverse_natAbs {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel))
    (hgood : d.IsTransverseBeltSphere hf hdim hindex g) :
    (d.indexTwoCollapseCoordinate hf.continuous hindex
          (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2
            (SphereHomology.unitSphereTopClass 1))).natAbs =
      (d.beltIntersectionCount 2 j g
          (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, _, ht⟩ := hgood
  exact d.indexTwoCoordinate_topClass_natAbs hf 3 hindex j g hg hinj ht

theorem MorseCancel.last_index_two_collapse_is_primitive {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hrpos : 0 < r) (hrc : r + n < S.toSurgeryWindows.count) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2,
      Function.Surjective ((S.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
        ∀ γ : C(Smale.Hemisphere.Sphere 1, (S.data q).LowerLevel),
          ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', -⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  rw [hrr] at htwo
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 :=
    htwo ⟨r, by omega⟩ hrpos le_rfl
  let _ :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f q - (S.data q).radius ^ 2 } 1) :=
    S.toSurgeryWindows.lower_homologyOne_subsingleton_of_indices hf ⟨r, by omega⟩ hrpos
      (fun i hi hir => by have hh := htwo i hi hir.le; omega)
  have hnidx : nativeMorseIndex E f q = 2 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).trans hindex
  exact
    ⟨hindex, (S.data q).indexTwoCoordinate_surjective hf.continuous hindex,
      lower_circle_nullhomotopies_of_ordered_native_indices S.toSurgeryWindows hf hdim q hnidx
        hzero hone (fun z hz => (horder z q hz).trans_eq hnidx)⟩

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem MorseCancel.exists_native_belt_cut_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n) (hrpos : 0 < r)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hradii : ∀ z, (T.data z).radius < (S.data z).radius) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let a := nativeMiddleBaseCut S r n hrc
    let p := nativeMiddleBlockPoint S r n hrc
    ∀ (_ : ∀ j, a < T.toSurgeryWindows.lower (p j))
      (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
      (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })),
      IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) →
        Function.Surjective (canonicalMiddleMatrix B γ).mulVec →
          ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2,
            Function.Surjective ((T.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
              (∀ δ : C(Smale.Hemisphere.Sphere 1, (T.data q).LowerLevel),
                  ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
                (∀ z : Smale.ManifoldMorse.criticalPoints E f,
                    nativeMorseIndex E f z < 3 → f z < T.toSurgeryWindows.upper q) ∧
                  (∀ z : Smale.ManifoldMorse.criticalPoints E f,
                      nativeMorseIndex E f z = 3 → ∃ j, p j = z) ∧
                    (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
                      ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), (T.data q).UpperLevel),
                        IsNativeMiddleBasinFamily T hf (T.data q).upper_regular p (fun j => β j) ∧
                          (∀ j x, ∃ t : ℝ, T.flow t (γ j x).val = (β j x).val) ∧
                            ∃ B' :
                              (Fin r → ℤ) ≃ₗ[ℤ]
                                SingularMayerVietoris.SingularHomology
                                  { y : M // f y ≤ T.toSurgeryWindows.upper q } 2,
                              canonicalMiddleMatrix B' β = canonicalMiddleMatrix B γ ∧
                                Function.Surjective (canonicalMiddleMatrix B' β).mulVec := by
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := nativeMiddleBaseCut S r n hrc
  let p := nativeMiddleBlockPoint S r n hrc
  dsimp only
  intro hlower B γ hγ hsurj
  have hrcT : r + n < T.toSurgeryWindows.count := hrc
  obtain ⟨hindex, hprimitive, hnull⟩ :=
    last_index_two_collapse_is_primitive T hf hdim horder hzero hone r n hr hrpos hrcT
  obtain ⟨hcomplete, hcut⟩ :=
    native_middle_block_complete_and_cut T hf hdim horder hzero hone r n hr hn hrcT
  have hba : T.toSurgeryWindows.upper q < a := by
    change f q + (T.data q).radius ^ 2 < f q + (S.data q).radius ^ 2
    have hh := hradii q
    nlinarith [(T.data q).radius_pos, (S.data q).radius_pos]
  have hband :
    ∀ y,
      f y ∈ Set.Icc (T.toSurgeryWindows.upper q) a → y ∉ Smale.ManifoldMorse.criticalPoints E f :=
    by
    intro y hy hcrit
    have hqy : f q < f y := (T.toSurgeryWindows.value_lt_upper q).trans_le hy.1
    have heq : y = q.val :=
      S.isolated q y hcrit ⟨((S.toSurgeryWindows.lower_lt_value q).trans hqy).le, hy.2⟩
    exact hqy.ne (congrArg f heq).symm
  have hnpos : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    obtain ⟨x, hx⟩ := hsurj 1
    have hh := congrFun hx ⟨0, hrpos⟩
    let _ : IsEmpty (Fin n) := ⟨fun j => by have hj := j.isLt; omega⟩
    simp only [Matrix.mulVec, dotProduct, Finset.univ_eq_empty, Finset.sum_empty,
      Pi.one_apply] at hh
    exact zero_ne_one hh
  let za := γ ⟨0, hnpos⟩ (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩)
  obtain ⟨β, hβ, horbit, -, hmatrix, hsurj'⟩ :=
    T.exists_lower_cut_geometric_matrix hf hba (S.data q).upper_regular (T.data q).upper_regular
      hband za p (fun j => (hlower j).trans (T.toSurgeryWindows.lower_lt_value (p j))) B γ hγ
      hsurj
  exact
    ⟨hindex, hprimitive, hnull, hcut, hcomplete, fun j => hba.trans (hlower j), β, hβ, horbit,
      B.trans (regularCutHomologyEquiv hf hba.le hband).symm, hmatrix, hsurj'⟩

theorem Smale.SupportedDiffeomorph.IsotopicToIdentity.homotopic {F H M : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e) :
    (ContinuousMap.id M).Homotopic e.toHomeomorph.toHomotopyEquiv.toFun := by
  obtain ⟨A, hA, hA₀, hA₁, _⟩ := he
  exact
    ⟨{  toFun := fun p => A (p.1.val, p.2)
        continuous_toFun :=
          hA.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        map_zero_left := hA₀
        map_one_left := hA₁ }⟩

theorem Smale.SupportedDiffeomorph.IsotopicToIdentity.comp_homotopic {F H M : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {X : Type*}
    [TopologicalSpace X] (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e) (g : C(X, M)) :
    g.Homotopic (e.toHomeomorph.toHomotopyEquiv.toFun.comp g) := by
  simpa using he.homotopic.comp (ContinuousMap.Homotopic.refl g)

theorem Smale.ManifoldMorse.MorseSurgeryData.exists_transverse_representative {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (g₀ : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg₀ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g₀)
      (_hinj : Function.Injective g₀)
      (_himm : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g₀ x)),
      ∃ e :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) d.UpperLevel
          d.UpperLevel ∞,
        ∃ g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel),
          Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g x = e (g₀ x)) ∧ d.IsTransverseBeltSphere hf hdim hindex g ∧ g₀.Homotopic g := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  intro hg₀ hinj himm
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by simp [Smale.RegularLevel.Model, hdim]
  obtain ⟨e, hiso, ht⟩ :=
    Smale.NativeTransversality.exists_ambient_transverse_diffeomorph hg₀ (d.belt_smooth hf 3)
      hdim'
  let g := e.toHomeomorph.toHomotopyEquiv.toFun.comp g₀
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g := e.contMDiff.comp hg₀
  have hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e ∘ g₀) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg₀.mdifferentiable (by simp) x)]
    exact
      ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by trivial)).comp
        (himm x)
  exact ⟨e, g, hiso, fun _ => rfl, ⟨hg, e.injective.comp hinj, hi, ht⟩, hiso.comp_homotopic g₀⟩

theorem MorseCancel.exists_single_intersection_of_unit_coordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, d.LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (γ : C((Smale.Hemisphere.Sphere 2), d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
              (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ)).natAbs =
          1 →
        ∃ D :
          Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
            d.UpperLevel d.UpperLevel ∞,
          ∃ δ : C((Smale.Hemisphere.Sphere 2), d.UpperLevel),
            Smale.SupportedDiffeomorph.IsotopicToIdentity D ∧
              (∀ x, δ x = D (γ x)) ∧
                d.IsTransverseBeltSphere hf hdim hindex δ ∧
                  (Set.range δ ∩ Set.range d.surgery.beltSphere).ncard = 1 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hγ hinj himm hunit
  obtain ⟨D₀, γ₀, hD₀, hγ₀, hgood₀, hhom⟩ :=
    d.exists_transverse_representative hf hdim hindex γ hγ hinj himm
  have hmaps := PeriodTorusHigherHomology.homotopic_homologyMap hhom 2
  have hclass :
    middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ₀ =
      middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ := by
    simp only [middleSectionClass, PeriodTorusHigherHomology.singularHomologyMap_comp,
      LinearMap.comp_apply]
    rw [← hmaps]
  have hcount :
    (d.beltIntersectionCount 2 (d.beltNormalReference 2 hindex) γ₀
          (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood₀)).natAbs =
      1 := by
    rw [←
      d.indexTwoCoordinate_transverse_natAbs hf hdim hindex (d.beltNormalReference 2 hindex) γ₀
        hgood₀]
    change
      (d.indexTwoCollapseCoordinate hf.continuous hindex
            (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ₀)).natAbs =
        1
    rw [hclass]
    exact hunit
  obtain ⟨D₁, δ, x, hD₁, hδ, hgood, -, hinter⟩ :=
    d.exists_single_belt_intersection_of_unit_count hf hdim hindex hnull
      (d.beltNormalReference 2 hindex) γ₀ hgood₀ hcount
  refine ⟨D₀.trans D₁, δ, hD₀.trans hD₁, (fun x => (hδ x).trans (congrArg D₁ (hγ₀ x))), hgood, ?_⟩
  rw [hinter, Set.ncard_singleton]

theorem AdaptedWindows.cancel_single_basin_section_isotopy {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hp : MorseCancel.nativeMorseIndex E f p = 2) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {c : ℝ} (hpc : f p < c) (hcq : c < f q)
    (hc : ∀ z, f z = c → z ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := Smale.RegularLevel.chartedSpace hf hc
    ∀ (α : Smale.Hemisphere.Sphere 2 → { z : M // f z = c }) (β : Y → { z : M // f z = c }),
      ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α →
        ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ β →
          (∀ z,
              z ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t z.val) Filter.atBot (𝓝 q.val)) →
            (∀ z,
                z ∈ Set.range β ↔
                  Filter.Tendsto (fun t => S.flow t z.val) Filter.atTop (𝓝 p.val)) →
              ∀ D :
                Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                  { z : M // f z = c } { z : M // f z = c } ∞,
                Smale.SupportedDiffeomorph.IsotopicToIdentity D →
                  (∀ x y,
                      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E)
                        (D ∘ α) β x y) →
                    (Set.range (D ∘ α) ∩ Set.range β).ncard = 1 →
                      ∃ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                          Smale.ManifoldMorse.IsMorse E g ∧
                            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
                                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
                              (∀ z,
                                  z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                    z ∈ Smale.ManifoldMorse.criticalPoints E f ∧
                                      z ≠ p.val ∧ z ≠ q.val) ∧
                                ∀ z,
                                  f z ∉
                                      Set.Ioo (S.toSurgeryWindows.lower p)
                                        (S.toSurgeryWindows.upper q) →
                                    g =ᶠ[𝓝 z] f := by
  let _ := Smale.RegularLevel.chartedSpace hf hc
  intro α β hα hβ hback hforward D hD htrans hsingle
  let δ := D.symm ∘ β
  have hδ : ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ := D.symm.contMDiff.comp hβ
  have hDα : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (D ∘ α) := D.contMDiff.comp hα
  have hαeq : D.symm ∘ (D ∘ α) = α := by
    funext x
    exact D.symm_apply_apply (α x)
  have hrange (z : { w : M // f w = c }) : z ∈ Set.range α ↔ D z ∈ Set.range (D ∘ α) := by
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_range_self x
    · rintro ⟨x, hx⟩
      exact ⟨x, D.injective hx⟩
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hsingle
  have hzmem : z ∈ Set.range (D ∘ α) ∩ Set.range β := by
    rw [hz]
    exact Set.mem_singleton z
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hzmem
  have hcross : β y = (D ∘ α) x := hy.trans hx.symm
  have hcross' : δ y = α x := by exact (congrArg D.symm hcross).trans (D.symm_apply_apply (α x))
  have ht : Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) α δ x y := by
    have hh :=
      (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff
            D.symm.toPartialDiffeomorph (hDα.mdifferentiableAt (by simp))
            (hβ.mdifferentiableAt (by simp)) hcross (Set.mem_univ _)).mp
        (htrans x y)
    change
      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E)
        (D.symm ∘ (D ∘ α)) δ x y at hh
    rwa [hαeq] at hh
  have hcount :
    {w : { z : M // f z = c } |
          Filter.Tendsto (fun t => S.flow t w.val) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => S.flow t (D w).val) Filter.atTop (𝓝 p.val)}.ncard =
      1 := by
    have heq :
      {w : { z : M // f z = c } |
          Filter.Tendsto (fun t => S.flow t w.val) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => S.flow t (D w).val) Filter.atTop (𝓝 p.val)} =
        {D.symm z} := by
      ext w
      change (_ ∧ _) ↔ w = D.symm z
      rw [← hback w, ← hforward (D w), hrange w]
      change D w ∈ Set.range (D ∘ α) ∩ Set.range β ↔ w = D.symm z
      rw [hz, Set.mem_singleton_iff]
      exact
        ⟨fun h => (D.symm_apply_apply w).symm.trans (congrArg D.symm h), fun h =>
          (congrArg D h).trans (D.apply_symm_apply z)⟩
    rw [heq, Set.ncard_singleton]
  have hαbasin :
    ∀ᶠ w in 𝓝 x, Filter.Tendsto (fun t => S.flow t (α w).val) Filter.atBot (𝓝 q.val) :=
    Filter.Eventually.of_forall (fun w => (hback (α w)).mp (Set.mem_range_self w))
  have hδbasin :
    ∀ᶠ w in 𝓝 y, Filter.Tendsto (fun t => S.flow t (D (δ w)).val) Filter.atTop (𝓝 p.val) := by
    apply Filter.Eventually.of_forall
    intro w
    change Filter.Tendsto (fun t => S.flow t (D (D.symm (β w))).val) Filter.atTop (𝓝 p.val)
    rw [D.apply_symm_apply]
    exact (hforward (β w)).mp (Set.mem_range_self w)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b, hcb, hbq⟩ := exists_between hcq
  have hweightp : Fintype.card { i // (S.data p).chart.weights i = -1 } = 2 := by
    have hh := (MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using hh
  have hweightq : Fintype.card { i // (S.data q).chart.weights i = -1 } = 3 := by
    have hh := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using hh
  exact
    MorseCancel.cancel_of_transverse_level_isotopy (m := 5) (S.data p).chart (S.data q).chart hf
      hm hdim (by omega) S.field S.smooth S.zero S.descent S.flow S.integral S.distinct p.property
      q.property (S.toSurgeryWindows.lower_lt_value p) (S.toSurgeryWindows.value_lt_upper q)
      (MorseCancel.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hac hcb hpc
      hcq (MorseCancel.surgery_pair_inner_band_regular p q hconsecutive hpa hbq) hc
      (S.critical_model_germ p) (S.critical_model_germ q) D hD hcount α δ x y
      (hα.mdifferentiableAt (by simp)) (hδ.mdifferentiableAt (by simp)) hcross' ht hαbasin hδbasin

theorem MorseCancel.conjugate_level_isotopy {V H X Y : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace H] {J : ModelWithCorners ℝ V H} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H Y] (e : Diffeomorph J J X Y ∞)
    (D : Diffeomorph J J X X ∞) (hD : Smale.SupportedDiffeomorph.IsotopicToIdentity D) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity (e.symm.trans (D.trans e)) := by
  obtain ⟨A, hA, hzero, hone, hslices⟩ := hD
  refine
    ⟨fun z : ℝ × Y => e (A (z.1, e.symm z.2)),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hzero, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (D (e.symm y))
    rw [hone]
  · intro t
    obtain ⟨Dt, hDt⟩ := hslices t
    refine ⟨e.symm.trans (Dt.trans e), ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (Dt (e.symm y))
    rw [hDt]

theorem MorseCancel.intersection_count_under_injective_map {A B X Y : Type*} (e : X → Y)
    (he : Function.Injective e) (α : A → X) (β : B → X) :
    (Set.range (e ∘ α) ∩ Set.range (e ∘ β)).ncard = (Set.range α ∩ Set.range β).ncard := by
  have hset : Set.range (e ∘ α) ∩ Set.range (e ∘ β) = e '' (Set.range α ∩ Set.range β) := by
    ext y
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hab : α a = β b := he (ha.trans hb.symm)
      exact ⟨α a, ⟨Set.mem_range_self a, ⟨b, hab.symm⟩⟩, ha⟩
    · rintro ⟨x, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hx⟩
      exact ⟨⟨a, (congrArg e ha).trans hx⟩, ⟨b, (congrArg e hb).trans hx⟩⟩
  rw [hset]
  exact Set.ncard_image_of_injective _ he

theorem MorseCancel.cancel_from_preserved_unit_belt_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hpcg : p.val ∈ Smale.ManifoldMorse.criticalPoints E g) (hpg : nativeMorseIndex E g p = 2)
    (q : Smale.ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hconsecutive : ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q))
    (hpc : g p < (f p + (S.data p).radius ^ 2)) (hcq : (f p + (S.data p).radius ^ 2) < g q)
    (hsub : ∀ y, g y ≤ (f p + (S.data p).radius ^ 2) ↔ f y ≤ (f p + (S.data p).radius ^ 2))
    (hlevel : ∀ y, g y = (f p + (S.data p).radius ^ 2) ↔ f y = (f p + (S.data p).radius ^ 2))
    (hga : ∀ y, g y = (f p + (S.data p).radius ^ 2) → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (hforward :
      ∀ y : (S.data p).UpperLevel,
        Filter.Tendsto (fun t => T.flow t y.val) Filter.atTop (𝓝 p.val) ↔
          Filter.Tendsto (fun t => S.flow t y.val) Filter.atTop (𝓝 p.val))
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // g y = (f p + (S.data p).radius ^ 2) })) :
    letI := Smale.RegularLevel.chartedSpace hg hga
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)),
      (∀ y, y ∈ Set.range γ ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot (𝓝 q.val)) →
        ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex
                ((equalCutHomologyEquiv hsub).symm (middleSectionClass γ))).natAbs =
            1 →
          ∃ v : M → ℝ,
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
              Smale.ManifoldMorse.IsMorse E v ∧
                (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
                    (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
                  (∀ z,
                      z ∈ Smale.ManifoldMorse.criticalPoints E v ↔
                        z ∈ Smale.ManifoldMorse.criticalPoints E g ∧ z ≠ p.val ∧ z ≠ q.val) ∧
                    ∀ z,
                      g z ∉
                          Set.Ioo (T.toSurgeryWindows.lower ⟨p.val, hpcg⟩)
                            (T.toSurgeryWindows.upper q) →
                        v =ᶠ[𝓝 z] g := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hg hga
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := (S.data p).chart.finrank_negative_add_positive; omega⟩
  intro hγ hinj himm hback hunit
  let e := equalLevelDiffeomorph hf hg (S.data p).upper_regular hga hlevel
  let α : C((Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel) :=
    equalCutSection (fun y => (hlevel y).symm) γ
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (e.symm ∘ γ)
    exact e.symm.contMDiff.comp hγ
  have hαinj : Function.Injective α := e.symm.injective.comp hinj
  have hαimm (x : (Smale.Hemisphere.Sphere 2)) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) α x) := by
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e.symm ∘ γ) x)
    rw [mfderiv_comp x (e.symm.contMDiff.mdifferentiableAt (by simp))
        (hγ.mdifferentiableAt (by simp))]
    exact (e.symm.mfderivToContinuousLinearEquiv (by simp) (γ x)).injective.comp (himm x)
  have hsection : equalCutSection hlevel α = γ := rfl
  have hclass := equalCutSection_class hsub hlevel α
  rw [hsection] at hclass
  have hpull : (equalCutHomologyEquiv hsub).symm (middleSectionClass γ) = middleSectionClass α := by
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hαunit :
    ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex (middleSectionClass α)).natAbs =
      1 := by rwa [hpull] at hunit
  obtain ⟨D, δ, hD, hδ, hgood, hsingle⟩ :=
    exists_single_intersection_of_unit_coordinate (S.data p) hf hdim hindex hnull α hα hαinj hαimm
      hαunit
  let β₀ := (S.data p).surgery.beltSphere
  let β := e ∘ β₀
  have hβ₀ : ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ β₀ := (S.data p).belt_smooth hf 3
  have hβ : ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ β := e.contMDiff.comp hβ₀
  let D' := e.symm.trans (D.trans e)
  have hD' : Smale.SupportedDiffeomorph.IsotopicToIdentity D' := conjugate_level_isotopy e D hD
  have hDγ : D' ∘ γ = e ∘ δ := by
    funext x
    change e (D (α x)) = e (δ x)
    exact congrArg e (hδ x).symm
  have hβfull (y : { z : M // g z = (f p + (S.data p).radius ^ 2) }) :
    y ∈ Set.range β ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atTop (𝓝 p.val) := by
    have hmem : y ∈ Set.range β ↔ e.symm y ∈ Set.range β₀ := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, e.injective (hx.trans (e.apply_symm_apply y).symm)⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem]
    exact (S.belt_basin_iff hf p (e.symm y)).symm.trans (hforward (e.symm y)).symm
  have ht :
    ∀ x y,
      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) (D' ∘ γ) β x y :=
    by
    rw [hDγ]
    intro x y hxy
    have hold : β₀ y = δ x := e.injective hxy
    have hh :=
      (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff e.toPartialDiffeomorph
            (hgood.1.mdifferentiableAt (by simp)) (hβ₀.mdifferentiableAt (by simp)) hold
            (Set.mem_univ _)).mp
        (hgood.2.2.2 x y)
    exact hh hxy
  have hcount : (Set.range (D' ∘ γ) ∩ Set.range β).ncard = 1 := by
    rw [hDγ]
    exact (intersection_count_under_injective_map e e.injective δ β₀).trans hsingle
  exact
    T.cancel_single_basin_section_isotopy hg hmg hdim ⟨p.val, hpcg⟩ q hconsecutive hpg hq hpc hcq
      hga γ β hγ hβ hback hβfull D' hD' ht hcount

theorem MorseCancel.consecutive_last_two_first_three {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f g : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : nativeMorseIndex E f p = 2)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindices :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (hfixed :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 3 → g z = f z)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z < 3 → f z < S.upper p)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E g,
        g x < g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y)
    (q : Smale.ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hfirst :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = 3 → z ≠ q → g q < g z) :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q) := by
  let pg : Smale.ManifoldMorse.criticalPoints E g := ⟨p.val, hcrit.symm ▸ p.property⟩
  have hpg : nativeMorseIndex E g pg = 2 := (hindices p p.property).trans hp
  have hgp : g p = f p := hfixed p p.property (by omega)
  intro z hz
  have hle : nativeMorseIndex E g z ≤ 3 := (horder z q hz.2).trans_eq hq
  have hge : 2 ≤ nativeMorseIndex E g z := hpg.symm.trans_le (horder pg z hz.1)
  have hcases : nativeMorseIndex E g z = 2 ∨ nativeMorseIndex E g z = 3 := by omega
  rcases hcases with hi2 | hi3
  · let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
    have hfidx : nativeMorseIndex E f zf = 2 := (hindices z zf.property).symm.trans hi2
    have hgz : g z = f z := hfixed z zf.property (by change nativeMorseIndex E f zf ≠ 3; omega)
    have hvalue : f p < f z := by
      have hh := hz.1
      rwa [hgp, hgz] at hh
    have hupper : f z < S.upper p := hcut zf (by omega)
    have heq : z.val = p.val :=
      S.isolated p z zf.property ⟨((S.lower_lt_value p).trans hvalue).le, hupper.le⟩
    exact hvalue.ne (congrArg f heq).symm
  · have hne : z ≠ q := fun heq =>
      hz.2.ne (congrArg (fun x : Smale.ManifoldMorse.criticalPoints E g => g x) heq)
    exact (hfirst z hi3 hne).not_gt hz.2

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
theorem MorseCancel.cancel_from_complete_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive :
      Function.Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex))
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < f p + (S.data p).radius ^ 2)
    {r n : ℕ} (labels : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, labels j = z)
    (hlower : ∀ j, f p + (S.data p).radius ^ 2 < S.toSurgeryWindows.lower (labels j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + (S.data p).radius ^ 2 } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel))
    (hγ : IsNativeMiddleBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Function.Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
        Smale.ManifoldMorse.IsMorse E v ∧
          Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) ∧
            (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard := by
  let c := f p + (S.data p).radius ^ 2
  let L := (S.data p).indexTwoCollapseCoordinate hf.continuous hindex
  have hpold : nativeMorseIndex E f p = 2 :=
    (nativeMorseIndex_eq_chart (S.data p).chart).trans hindex
  obtain
    ⟨ops, -, g, hg, hmg, hcrit, hgorder, hindices, -, houtside, hgcut, hsub, hlevel, hga, T, -, -,
      hpg, hgcomplete, hglower, Γ, hΓ, -, -, hgsurj, ⟨i, hi⟩, hkeep⟩ :=
    S.exists_primitive_functional_unit hf hm hdim horder (S.data p).upper_regular hcut labels
      hlabels hcomplete hlower B γ hγ hsurj L hprimitive
  let pg : Fin n → Smale.ManifoldMorse.criticalPoints E g := fun j =>
    ⟨(labels j).val, hcrit.symm ▸ (labels j).property⟩
  let Bg := B.trans (equalCutHomologyEquiv hsub)
  obtain
    ⟨u, hu, hmu, hcu, huorder, huindices, -, huoutside, hfirst, husub, hulevel, hua, U, -, huflow,
      -, hpu, hulower, hfamily, -, -, -⟩ :=
    T.exists_first_middle_pivot hg hmg hga hgorder pg hpg hgcomplete hglower Bg Γ hΓ hgsurj i
  let hcrit' := hcu.trans hcrit
  let hsub' : ∀ y, u y ≤ c ↔ f y ≤ c := fun y => (husub y).trans (hsub y)
  let hlevel' : ∀ y, u y = c ↔ f y = c := fun y => (hulevel y).trans (hlevel y)
  let q : Smale.ManifoldMorse.criticalPoints E u :=
    ⟨(labels i).val, hcrit'.symm ▸ (labels i).property⟩
  let Δ := fun j => equalCutSection hulevel (Γ j)
  have hids (z : M) (hz : z ∈ Smale.ManifoldMorse.criticalPoints E f) :
    nativeMorseIndex E u z = nativeMorseIndex E f z :=
    (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)
  have hfixed (z : M) (hz : z ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hidx : nativeMorseIndex E f z ≠ 3) : u z = f z := by
    have hnotlabel (j : Fin n) : z ≠ (labels j).val := by
      intro heq
      apply hidx
      rw [heq]
      exact hlabels j
    exact (huoutside z (hcrit.symm ▸ hz) hnotlabel).trans (houtside z hz hnotlabel)
  have hpcrit : p.val ∈ Smale.ManifoldMorse.criticalPoints E u := hcrit'.symm ▸ p.property
  have hpnew : nativeMorseIndex E u p = 2 := (hids p p.property).trans hpold
  have hq : nativeMorseIndex E u q = 3 := (hids (labels i) (labels i).property).trans (hlabels i)
  have hfirstcrit (z : Smale.ManifoldMorse.criticalPoints E u) (hz : nativeMorseIndex E u z = 3)
    (hne : z ≠ q) : u q < u z := by
    let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit' ▸ z.property⟩
    have hzidx : nativeMorseIndex E f zf = 3 := (hids z zf.property).symm.trans hz
    obtain ⟨j, hj⟩ := hcomplete zf hzidx
    have hji : j ≠ i := by
      intro hji
      apply hne
      apply Subtype.ext
      exact
        (congrArg (fun z : Smale.ManifoldMorse.criticalPoints E f => z.val) hj).symm.trans
          (congrArg (fun k => (labels k).val) hji)
    have hh := hfirst j hji
    change u (labels i) < u (labels j) at hh
    simpa only [hj] using hh
  have hconsecutive :=
    consecutive_last_two_first_three S.toSurgeryWindows p hpold hcrit' hids hfixed hcut huorder q
      hq hfirstcrit
  have hpc : u p < c := by
    rw [hfixed p p.property (by omega)]
    exact S.toSurgeryWindows.value_lt_upper p
  have hcq : c < u q := (hulower i).trans (U.toSurgeryWindows.lower_lt_value q)
  have hclass := equalCutSection_class husub hulevel (Γ i)
  have hpull :
    (equalCutHomologyEquiv hsub').symm (middleSectionClass (Δ i)) =
      (equalCutHomologyEquiv hsub).symm (middleSectionClass (Γ i)) := by
    rw [← equalCutHomologyEquiv_trans hsub husub]
    change
      (equalCutHomologyEquiv hsub).symm
          ((equalCutHomologyEquiv husub).symm (middleSectionClass (Δ i))) =
        _
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hunit : (L ((equalCutHomologyEquiv hsub').symm (middleSectionClass (Δ i)))).natAbs = 1 := by
    rw [hpull]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  have hforward (y : (S.data p).UpperLevel) :
    Filter.Tendsto (fun t => U.flow t y.val) Filter.atTop (𝓝 p.val) ↔
      Filter.Tendsto (fun t => S.flow t y.val) Filter.atTop (𝓝 p.val) := by
    rw [huflow]
    exact (hkeep y.val y.property.le).2.2 p.val
  let _ := Smale.RegularLevel.chartedSpace hu hua
  obtain ⟨v, hv, hmv, hcard, hcv, hext⟩ :=
    cancel_from_preserved_unit_belt_cut S U hf hu hmu hdim p hindex hnull hpcrit hpnew q hq
      hconsecutive hpc hcq hsub' hlevel' hua hforward (Δ i) (hfamily.1 i)
      (hfamily.2.1 i).injective (hfamily.2.2.1 i) (hfamily.2.2.2.2 i) hunit
  obtain ⟨-, hinj, -⟩ :=
    adapted_surgeries_after_pair_removal U.toSurgeryWindows ⟨p.val, hpcrit⟩ q hconsecutive hv hmv
      hcv hext
  refine ⟨v, hv, hmv, hinj, ?_⟩
  rwa [hcrit'] at hcard

theorem MorseCancel.minimal_ordered_index_two_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          Smale.ManifoldMorse.IsMorse E v →
            Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 2 = 0 := by
  obtain ⟨r, n, htwo, hrc, hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr, hn⟩ := native_middle_block_counts S.toSurgeryWindows hf r n htwo hrc hthree hafter
  rw [hr]
  by_contra hnot
  have hrpos : 0 < r := Nat.pos_of_ne_zero hnot
  obtain ⟨T, -, hradii, -, α, hα⟩ :=
    S.exists_ordered_middle_family hf hm hdim r n hrc hthree (fun p => (S.data p).radius)
      (fun p => (S.data p).radius_pos)
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := S.toSurgeryWindows.upper q
  let p := nativeMiddleBlockPoint S r n hrc
  have hp (j : Fin n) : nativeMorseIndex E f (p j) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have hlower (j : Fin n) : a < T.toSurgeryWindows.lower (p j) := by
    have hqj : f q < f (p j) :=
      S.toSurgeryWindows.point_strictMono (by change r < r + j.val + 1; omega)
    have hsep := S.separated q (p j) hqj
    have hh :=
      mul_pos (sub_pos.mpr (hradii (p j)))
        (add_pos (S.data (p j)).radius_pos (T.data (p j)).radius_pos)
    change a < f (p j) - (T.data (p j)).radius ^ 2
    change a < f (p j) - (S.data (p j)).radius ^ 2 at hsep
    nlinarith
  obtain ⟨β, hβ, -, hβflow⟩ :=
    T.exists_canonical_middle_family hf (S.data q).upper_regular p hp α hα
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }) := fun j =>
    ⟨β j, (hβ.1 j).continuous⟩
  let B := S.toSurgeryWindows.indexTwoBasis hf r (by omega) htwo
  have hsurj :=
    canonical_middle_matrix_surjective S T hf hdim e horder hzero hone r n hr hn hrc hp hlower B γ
      hβflow
  obtain ⟨hindex, hprimitive, hnull, hcut, hcomplete, hbelow, δ, hδ, -, B', -, hsurj'⟩ :=
    exists_native_belt_cut_family S T hf hdim horder hzero hone r n hr hn hrpos hrc hradii hlower
      B γ hβ hsurj
  obtain ⟨v, hv, hmv, hinj, hcard⟩ :=
    cancel_from_complete_middle_family T hf hm hdim horder q hindex hnull hprimitive hcut p hp
      hcomplete hbelow B' δ hδ hsurj'
  have hmin := hminimal v hv hmv hinj
  omega

theorem MorseCancel.minimal_ordered_index_four_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          Smale.ManifoldMorse.IsMorse E v →
            Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 4 = 0 := by
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have horderN :
    ∀ p q : Smale.ManifoldMorse.criticalPoints E (fun x => -f x),
      -f p < -f q → nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q :=
    by
    intro p q hpq
    let pf : Smale.ManifoldMorse.criticalPoints E f :=
      ⟨p.val, by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using p.property⟩
    let qf : Smale.ManifoldMorse.criticalPoints E f :=
      ⟨q.val, by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using q.property⟩
    have hrev := horder qf pf (neg_lt_neg_iff.mp hpq)
    have hp := nativeMorseIndex_neg_add (S.data pf).chart
    have hq := nativeMorseIndex_neg_add (S.data qf).chart
    change nativeMorseIndex E f q.val ≤ nativeMorseIndex E f p.val at hrev
    change nativeMorseIndex E (fun x => -f x) p.val + nativeMorseIndex E f p.val = _ at hp
    change nativeMorseIndex E (fun x => -f x) q.val + nativeMorseIndex E f q.val = _ at hq
    omega
  have hn6 := nativeMorseCount_neg hf hm (k := 6) (by omega)
  have hn5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hn4 := nativeMorseCount_neg hf hm (k := 4) (by omega)
  simp only [hdim, Nat.reduceSub] at hn6 hn5 hn4
  have hh :=
    minimal_ordered_index_two_count_zero T hf.neg (isMorse_neg hm) hdim e horderN (hn6.trans hsix)
      (hn5.trans hfive) (minimal_excellent_morse_neg hminimal)
  rwa [hn4] at hh

theorem Smale.ManifoldMorse.MorseSurgeryData.coreBoundary_two_injective_of_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    (hf : Continuous f) : Function.Injective (d.coreBoundaryHomologyMap 2) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_attachingSphere hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.morseConnectingMap hf 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem Smale.ManifoldMorse.MorseSurgeryData.indexThreeAttaching_zsmul_eq_zero {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    (hf : Continuous f) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) (z : ℤ)
    (hz : z • d.indexThreeAttachingClass hindex = 0) : z = 0 := by
  have hcore : d.coreBoundaryHomologyMap 2 (z • (d.indexThreeBoundaryEquiv hindex).symm 1) = 0 := by
    rw [map_zsmul]
    exact hz
  have hs : z • (d.indexThreeBoundaryEquiv hindex).symm 1 = 0 :=
    d.coreBoundary_two_injective_of_upper hf (hcore.trans (map_zero _).symm)
  have h := congrArg (d.indexThreeBoundaryEquiv hindex) hs
  rw [map_zsmul, LinearEquiv.apply_symm_apply, map_zero, zsmul_eq_mul, mul_one] at h
  simpa using h

theorem Smale.IntegerPresentation.ofEquiv_matrix_injective {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r : ℕ} (e : (Fin r → ℤ) ≃ₗ[ℤ] B) :
    Function.Injective (ofEquiv e).matrix.mulVec := fun _ _ _ => Subsingleton.elim _ _

theorem Smale.IntegerPresentation.adjoin_mulVec {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c) (q : B →ₗ[ℤ] C)
    (hq : Function.Surjective q) (b : B) (hker : LinearMap.ker q = Submodule.span ℤ { b })
    (z : Fin (c + 1) → ℤ) :
    (P.adjoin q hq b hker).matrix.mulVec z =
      z 0 • P.liftRelation b + P.matrix.mulVec (Fin.tail z) := by
  rw [← (P.adjoin q hq b hker).columns_sum_eq_mulVec, Fin.sum_univ_succ]
  change z 0 • P.liftRelation b + (∑ i, z i.succ • P.columns i) = _
  rw [P.columns_sum_eq_mulVec]
  rfl

theorem Smale.IntegerPresentation.adjoin_coefficient {B C : Type*} [AddCommGroup B]
    [AddCommGroup C] [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c)
    (q : B →ₗ[ℤ] C) (hq : Function.Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ { b }) (z : Fin (c + 1) → ℤ) :
    P.map ((P.adjoin q hq b hker).matrix.mulVec z) = z 0 • b := by
  rw [P.adjoin_mulVec q hq b hker, map_add, map_zsmul, P.map_liftRelation, P.matrix_relation,
    add_zero]

theorem Smale.IntegerPresentation.adjoin_matrix_injective {B C : Type*} [AddCommGroup B]
    [AddCommGroup C] [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c)
    (q : B →ₗ[ℤ] C) (hq : Function.Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ { b }) (hP : Function.Injective P.matrix.mulVec)
    (hb : ∀ z : ℤ, z • b = 0 → z = 0) : Function.Injective (P.adjoin q hq b hker).matrix.mulVec :=
  by
  have hzero (z : Fin (c + 1) → ℤ) (hz : (P.adjoin q hq b hker).matrix.mulVec z = 0) : z = 0 := by
    have hcoeff : z 0 • b = 0 :=
      (P.adjoin_coefficient q hq b hker z).symm.trans ((congrArg P.map hz).trans (map_zero P.map))
    have hz0 := hb (z 0) hcoeff
    have htail : P.matrix.mulVec (Fin.tail z) = 0 := by
      rw [P.adjoin_mulVec q hq b hker, hz0, zero_smul, zero_add] at hz
      exact hz
    have hzero' : P.matrix.mulVec (0 : Fin c → ℤ) = 0 := by simp
    have ht : Fin.tail z = 0 := hP (htail.trans hzero'.symm)
    funext i
    exact Fin.cases hz0 (fun j => congrFun ht j) i
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self]

theorem Smale.ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    {r c : ℕ}
    (P :
      Smale.IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c)
    (hP : Function.Injective P.matrix.mulVec) :
    Function.Injective (d.indexThreePresentation hf hindex P).matrix.mulVec :=
  P.adjoin_matrix_injective _ _ _ _ hP (d.indexThreeAttaching_zsmul_eq_zero hf hindex)

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
    (htwo : S.HasIndexTwoPrefix r) :
    ∀ (c : ℕ) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c),
      (∀ i : Fin S.count,
          r < i.val →
            i.val ≤ r + c →
              Subsingleton
                (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point i) }
                  3)) →
        Function.Injective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  intro c
  induction c with
  | zero =>
    intro hc hthree _
    exact Smale.IntegerPresentation.ofEquiv_matrix_injective (S.indexTwoBasis hf r hc htwo)
  | succ c ih =>
    intro hc hthree hvan
    let P :=
      S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
    have hP : Function.Injective P.matrix.mulVec :=
      ih (Nat.lt_of_succ_lt hc) (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
        (fun i hi him => hvan i hi (him.trans (Nat.le_succ (r + c))))
    let :
      Subsingleton
        (SingularMayerVietoris.SingularHomology
          { x : M //
            f x ≤
              f (S.point ⟨r + (c + 1), hc⟩) + (S.data (S.point ⟨r + (c + 1), hc⟩)).radius ^ 2 }
          3) :=
      hvan ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl
    exact
      (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation_matrix_injective hf.continuous
        (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2)) hP

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Injective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_injective_of_upper_third hf r htwo c hc hthree
  intro i hri hic
  have hi : i.val + 1 < S.count := by omega
  apply
    S.upper_homology_subsingleton_of_later_indices hf hdim hM i hi 3 (by norm_num) (by norm_num)
  intro j hij hj
  have h3 := hthree j (hri.trans hij) (by omega)
  exact ⟨by omega, by omega⟩

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_bijective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Bijective (S.middleMatrix hf r c htwo hc hthree).mulVec :=
  ⟨S.middleMatrix_injective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount,
    S.middleMatrix_surjective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount⟩

theorem Smale.HomologyTransport.matrix_sizes_eq_of_bijective {R : Type*} [CommRing R]
    [Nontrivial R] [StrongRankCondition R] {r c : ℕ} (A : Matrix (Fin r) (Fin c) R)
    (hA : Function.Bijective A.mulVec) : c = r := by
  let e := LinearEquiv.ofBijective A.mulVecLin hA
  simpa using e.finrank_eq

theorem Smale.ManifoldMorse.SurgeryWindows.middle_counts_equal {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) : r = c :=
  (Smale.HomologyTransport.matrix_sizes_eq_of_bijective (S.middleMatrix hf r c htwo hc hthree)
      (S.middleMatrix_bijective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount)).symm

theorem MorseCancel.native_index_excluded_of_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) {k : ℕ} (hcount : nativeMorseCount E f k = 0) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ k := by
  have hfinite :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

theorem MorseCancel.middle_blocks_complete_of_no_four_five {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (htwo : S.HasIndexTwoPrefix r)
    (hrc : r + n < S.count) (hthree : S.HasIndexThreeBlock r n)
    (hafter :
      ∀ i : Fin S.count,
        r + n < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates)
    (hsix : nativeMorseCount E f 6 = 1) (hfour : nativeMorseCount E f 4 = 0)
    (hfive : nativeMorseCount E f 5 = 0) : r + n + 2 = S.count := by
  have hpos := S.count_pos hf
  have hidx (i : Fin S.count) :
    nativeMorseIndex E f (S.point i) = 6 ↔ r + n + 1 ≤ i.val ∧ i.val < S.count := by
    have hle : nativeMorseIndex E f (S.point i) ≤ 6 := by
      simpa only [hdim] using (nativeMorseIndex_le (E := E) (f := f) (p := (S.point i).val))
    have hne4 := native_index_excluded_of_count_zero S hfour _ (S.point i).property
    have hne5 := native_index_excluded_of_count_zero S hfive _ (S.point i).property
    by_cases ha : r + n < i.val
    · have hh := hafter i ha
      rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart] at hh
      have hi := i.isLt
      omega
    · have hh : nativeMorseIndex E f (S.point i) ≤ 3 := by
        by_cases hz : i.val = 0
        · have he : i = ⟨0, hpos⟩ := Fin.ext hz
          have hzidx : nativeMorseIndex E f (S.point i) = 0 := by
            rw [he]
            exact
              (nativeMorseIndex_eq_chart (S.data (S.first hpos)).chart).trans
                (S.first_index_zero hf hpos)
          omega
        · by_cases hr : i.val ≤ r
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart, htwo i (by omega) hr]
            omega
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart,
              hthree i (by omega) (by omega)]
      omega
  have hcount :=
    nativeMorseCount_eq_interval_length S 6 (r + n + 1) S.count (by omega) le_rfl hidx
  omega

theorem MorseCancel.ordered_no_middle_indices_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0)
    (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) :
    nativeMorseCount E f 3 = 0 ∧ S.count = 2 := by
  obtain ⟨r, n, hprefix, hrc, hblock, -, hafter⟩ :=
    exists_middle_index_blocks S hf hdim horder hzero hone
  obtain ⟨hr, hn⟩ := native_middle_block_counts S hf r n hprefix hrc hblock hafter
  have hcount :=
    middle_blocks_complete_of_no_four_five S hf hdim r n hprefix hrc hblock hafter hsix hfour
      hfive
  have heq := S.middle_counts_equal hf hdim e r n hprefix hrc hblock hcount
  omega

def Smale.negLevelHomeomorph {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) :
    { x : M // -f x = -a } ≃ₜ { x : M // f x = a }
    where
  toFun x := ⟨x.1, neg_inj.mp x.2⟩
  invFun x := ⟨x.1, congrArg Neg.neg x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def Smale.twoDiskDecompositionOfSublevels {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) :
    TwoDiskDecomposition n M := by
  let B := L.boundaryHomeomorph
  let C := R.boundaryHomeomorph.trans (negLevelHomeomorph f a)
  let e := B.trans C.symm
  refine
    { boundaryEquiv := e
      left := L.map
      right := R.map
      left_injective := L.map_injective
      right_injective := R.map_injective
      covers := ?_
      overlap := ?_ }
  · intro y
    by_cases hy : f y ≤ a
    · left
      exact
        ⟨L.homeomorph.symm ⟨y, hy⟩, congrArg Subtype.val (L.homeomorph.apply_symm_apply ⟨y, hy⟩)⟩
    · right
      have hy' : -f y ≤ -a := neg_le_neg (le_of_not_ge hy)
      exact
        ⟨R.homeomorph.symm ⟨y, hy'⟩,
          congrArg Subtype.val (R.homeomorph.apply_symm_apply ⟨y, hy'⟩)⟩
  · intro x y
    constructor
    · intro h
      have hL : f (L.map x) ≤ a := (L.homeomorph x).2
      have hR : -f (R.map y) ≤ -a := (R.homeomorph y).2
      have hxlevel : f (L.map x) = a := by rw [← h] at hR; linarith
      have hylevel : -f (R.map y) = -a := by rw [← h, hxlevel]
      have hxnorm := (L.boundary_iff x).mp hxlevel
      have hynorm := (R.boundary_iff y).mp hylevel
      let z : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨x.1, mem_sphere_zero_iff_norm.mpr hxnorm⟩
      let w : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨y.1, mem_sphere_zero_iff_norm.mpr hynorm⟩
      have hbc : B z = C w := Subtype.ext h
      have hew : e z = w := by
        apply C.injective
        change C (C.symm (B z)) = C w
        rw [C.apply_symm_apply]
        exact hbc
      refine ⟨z, rfl, ?_⟩
      rw [hew]
      rfl
    · rintro ⟨z, rfl, rfl⟩
      have heq := congrArg Subtype.val (C.apply_symm_apply (B z))
      exact heq.symm

def Smale.homeomorphSphereOfSublevelDisks {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) :
    M ≃ₜ Hemisphere.Sphere n :=
  (twoDiskDecompositionOfSublevels L R).homeomorphSphere

theorem Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p q : M} (hpq : f p < f q)
    (hcrit : criticalPoints E f = { p, q }) :
    Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E)) := by
  have hcover : ∀ x ∈ criticalPoints E f, x = p ∨ x = q := by
    intro x hx
    rw [hcrit] at hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have hp : p ∈ criticalPoints E f := by rw [hcrit]; simp
  have hq : q ∈ criticalPoints E f := by rw [hcrit]; simp
  obtain ⟨hmin, hmax⟩ := unique_extrema_of_two_critical_values hf hpq hcover
  obtain ⟨cp⟩ := nonempty_signedMorseChart hf hm p hp
  obtain ⟨cq⟩ := nonempty_signedMorseChart hf hm q hq
  let a := (f p + f q) / 2
  have hpa : f p < a := by dsimp [a]; linarith
  have haq : a < f q := by dsimp [a]; linarith
  have hregularL : ∀ x, f p < f x → f x ≤ a → x ∉ criticalPoints E f := by
    intro x hxlo hxhi hxcrit
    rcases hcover x hxcrit with h | h
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
    · rw [h] at hxhi
      exact not_le_of_gt haq hxhi
  obtain ⟨L⟩ := cp.nonempty_sublevelDisk_before_next_critical hf hmin hpa hregularL
  have hminNeg : ∀ x, -f x ≤ -f q → x = q := fun x hx => hmax x (neg_le_neg_iff.mp hx)
  have hregularR : ∀ x, -f q < -f x → -f x ≤ -a → x ∉ criticalPoints E (fun y => -f y) := by
    intro x hxlo hxhi hxcrit
    have hxcrit' : x ∈ criticalPoints E f := by
      rw [← criticalPoints_neg (E := E) f]
      exact hxcrit
    rcases hcover x hxcrit' with h | h
    · rw [h] at hxhi
      linarith
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
  obtain ⟨R⟩ :=
    cq.neg.nonempty_sublevelDisk_before_next_critical hf.neg hminNeg (neg_lt_neg haq) hregularR
  exact ⟨Smale.homeomorphSphereOfSublevelDisks L R⟩

theorem MorseCancel.critical_pair_of_surgery_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hcount : S.count = 2) :
    ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q } := by
  let p := S.point ⟨0, by omega⟩
  let q := S.point ⟨1, by omega⟩
  refine ⟨p.val, q.val, S.point_strictMono (by change (0 : ℕ) < 1; omega), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := S.point.surjective ⟨z, hz⟩
    have hib := i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 := by omega
    rcases hcases with hzero | hone
    · have he : i = ⟨0, by omega⟩ := Fin.ext hzero
      have hv := congrArg (fun x : Smale.ManifoldMorse.criticalPoints E f => x.val) hi
      rw [he] at hv
      exact Set.mem_insert_iff.mpr (Or.inl hv.symm)
    · have he : i = ⟨1, by omega⟩ := Fin.ext hone
      have hv := congrArg (fun x : Smale.ManifoldMorse.criticalPoints E f => x.val) hi
      rw [he] at hv
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hv.symm))
  · intro hz
    rcases Set.mem_insert_iff.mp hz with hp | hq
    · exact hp ▸ p.property
    · exact (Set.mem_singleton_iff.mp hq) ▸ q.property

theorem MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q } := by
  let _ := Smale.pathConnectedSpace_of_homotopySixSphere e
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_system_without_outer_indices E M e hdim
  have htwo := minimal_ordered_index_two_count_zero S hf hm hdim e horder hzero hone hminimal
  have hfour := minimal_ordered_index_four_count_zero S hf hm hdim e horder hsix hfive hminimal
  obtain ⟨-, hcount⟩ :=
    ordered_no_middle_indices_count_two S.toSurgeryWindows hf hdim e horder hzero hsix hone htwo
      hfour hfive
  exact ⟨f, hf, hm, critical_pair_of_surgery_count_two S.toSurgeryWindows hcount⟩

theorem MorseCancel.nonempty_homeomorph_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) : Nonempty (M ≃ₜ SixSphere) := by
  obtain ⟨f, hf, hm, p, q, hpq, hcrit⟩ :=
    exists_two_critical_point_morse_of_homotopySixSphere E M hdim e
  have hh := Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points hf hm hpq hcrit
  change Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E)) at hh
  rw [hdim] at hh
  exact hh

theorem Smale.homeomorphic_sixSphere_of_homotopySixSphere (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) :
    Nonempty (M ≃ₜ Smale.SixSphere) :=
  MorseCancel.nonempty_homeomorph_of_homotopySixSphere E M hdim hM

end Mathoverflow1973

end
