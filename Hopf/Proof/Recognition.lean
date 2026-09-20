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
import Hopf.Recognition
import Hopf.Proof.LCP.IntegralHomology
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.Compact
import Lib.Geometry.Manifold.RegularLevel
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Morse.Existence
import Lib.Analysis.ODE.SmoothFlow
import Lib.Geometry.Manifold.WhitneyEmbedding
import Lib.Geometry.Manifold.VectorBundle.ProjectionBundle
import Lib.Geometry.Manifold.Collar
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Mathlib
import Lib.Topology.Homotopy.HandleRetraction
import Lib.Algebra.Homology.MayerVietorisShortExact
import Lib.AlgebraicTopology.SingularHomology.Chains
import Lib.AlgebraicTopology.SingularHomology.ModuleHomology
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.Topology.Homotopy.LoopSubdivision
import Lib.AlgebraicTopology.FundamentalGroupoid.SimplyConnectedSphere
import Lib.Geometry.Manifold.Whitney.BigonModel
import Hopf.Proof.Geometry.Manifold.Morse.MinimalSystem
import Lib.Topology.Homotopy.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.AlgebraicTopology.SingularHomology.Sum
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
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
import Lib.Topology.Homotopy.BasedDiskLifting
import Lib.Topology.Homotopy.RelativeDiskLifting
import Lib.LinearAlgebra.SquareZero
import Lib.Topology.MappingTorus.Basic
import Lib.Topology.Covering.Quotient
import Lib.Topology.Homotopy.SublevelRetraction
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.AlgebraicTopology.SingularHomology.Torus
import Lib.Topology.Homotopy.LocalCollapse
import Lib.Topology.Covering.InvariantSubset
import Lib.AlgebraicTopology.SingularHomology.Pontryagin
import Lib.LinearAlgebra.ExteriorPower.MinorCoordinates
import Lib.Topology.Algebra.FreeActionLocus
import Lib.Geometry.Manifold.Quotient.LocalOrbit
import Lib.Geometry.Manifold.Quotient.Atlas
import Lib.Geometry.Manifold.Instances.RiemannSphere
import Lib.Analysis.Complex.Cousin
import Lib.Analysis.Complex.SquareRoot
import Lib.Analysis.Complex.Mobius
import Lib.Analysis.Complex.SchwarzReflection
import Lib.Analysis.Complex.RiemannMapping
import Lib.Analysis.Complex.RiemannMapping.Steps
import Lib.Geometry.Manifold.Complex.Biholomorph
import Lib.Topology.Covering.DiagonalQuotient
import Lib.GroupTheory.Abelianization.SemidirectProduct
import Lib.Topology.MappingTorus.HomologyCover
import Lib.GroupTheory.SplitExtension
import Lib.GroupTheory.PresentedGroup.CentralTwist
import Lib.Topology.FiberBundle.TwoOpenTransition
import S6.TwoExceptionalGluing
import S6Shortcuts
import Lib.AlgebraicTopology.Hurewicz.Straightening
import Lib.Topology.Homotopy.CellAttachment
import Lib.AlgebraicTopology.Hurewicz.CubeSphere
import Lib.AlgebraicTopology.Hurewicz.Naturality
import Lib.AlgebraicTopology.Hurewicz.SphereGenerator
import Lib.Topology.Homotopy.CellFilling
import Lib.Geometry.Manifold.ChartedSpace.Transport
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.LinearAlgebra.Matrix.TransvectionReduction
import Lib.Algebra.Module.IntegerPresentation

/-! Proof-specific part of `Hopf.Recognition` (split by lean-agent-ide `split_module`); the stock part that is
still to be moved into `Lib/` stays in `Hopf/Recognition.lean`. Declarations, names and namespaces are unchanged. -/

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

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

abbrev MetricSixSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1

def SixSphereHomology.homologyZeroEquiv :
    SingularMayerVietoris.SingularHomology MetricSixSphere 0 ≃ₗ[ℤ] ℤ :=
  SphereHomology.unitSphereHomologyZeroEquiv 5

def SixSphereHomology.homologySixEquiv :
    SingularMayerVietoris.SingularHomology MetricSixSphere 6 ≃ₗ[ℤ] ℤ :=
  SphereHomology.unitSphereHomologyTopEquiv 5

theorem SixSphereHomology.homology_subsingleton (k : ℕ) (hk : k ≠ 0) (hk6 : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology MetricSixSphere k) :=
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
      SingularMayerVietoris.SingularHomology MetricSixSphere 0 :=
  SpecialPeriods.Threefold.LowDegrees.singularH0Equiv.trans
    SixSphereHomology.homologyZeroEquiv.symm

def SpecialPeriods.Threefold.HomologySphere.homologySixEquivSixSphere :
    SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space 6 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology MetricSixSphere 6 :=
  ThreefoldHomology.TopDegree.homologySixEquiv.trans SixSphereHomology.homologySixEquiv.symm

theorem SpecialPeriods.Threefold.SphereHomologyMap.six_surjective_of_topClass_preimage
    (f : C(MetricSixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology MetricSixSphere 6)
    (ha :
      SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f 6) := by
  intro b
  refine ⟨ThreefoldHomology.TopDegree.homologySixEquiv b • a, ?_⟩
  rw [map_zsmul, ha]
  exact (ThreefoldHomology.TopDegree.eq_smul_topClass b).symm

theorem SpecialPeriods.Threefold.SphereHomologyMap.six_bijective_of_topClass_preimage
    (f : C(MetricSixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology MetricSixSphere 6)
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
    (f : C(MetricSixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology MetricSixSphere 6)
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
    (f : C(MetricSixSphere, SpecialPeriods.Threefold.Space))
    (a : SingularMayerVietoris.SingularHomology MetricSixSphere 6)
    (ha : SingularMayerVietoris.singularHomologyMap f 6 a = ThreefoldHomology.TopDegree.topClass)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology MetricSixSphere n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n :=
  LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap f n)
    (homologyMap_bijective_of_topClass_preimage f a ha n)


def SpecialPeriods.Threefold.SphereHomologyEquivalence.sourceCubeClass :
    SingularMayerVietoris.SingularHomology MetricSixSphere 6 :=
  SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop

def SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap
    (x : SpecialPeriods.Threefold.Space) : C(MetricSixSphere, SpecialPeriods.Threefold.Space) :=
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
    SingularMayerVietoris.SingularHomology MetricSixSphere n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.Space n :=
  SpecialPeriods.Threefold.SphereHomologyMap.homologyEquivOfTopClassPreimage (sphereMap x)
    sourceCubeClass (sphereMap_sourceCubeClass x) n

theorem sphereMap_piSix_bijective (x : SpecialPeriods.Threefold.Space) :
    Function.Bijective
      (SixthHurewicz.homotopyMap (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
        SixSphereCube.sphereBasePoint) := by
  let := SpecialPeriods.Threefold.space_simplyConnected
  apply SixthHurewicz.homotopyMap_bijective_of_homologyMap_bijective
    (fun k hk hk6 y => ?_)
    (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    (SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyMap_bijective x 6)
  interval_cases k
  · exact SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton y
  · exact SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton y
  · exact SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton y
  · exact SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton y

theorem BasedDiskLifting.exists_based_disk_lift {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (x : SpecialPeriods.Threefold.Space)
    (L : V ≃L[ℝ] (Fin 6 → ℝ))
    (u : C(DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space))
    (hu :
      ∀ z : DiskCylinder.Disk (E := V),
        ‖(z : V)‖ = 1 →
          u z =
            SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
              SixSphereCube.sphereBasePoint) :
    ∃ v : C(DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere),
      (∀ z : DiskCylinder.Disk (E := V),
          ‖(z : V)‖ = 1 → v z = SixSphereCube.sphereBasePoint) ∧
        ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp v).HomotopicRel u
          {z : DiskCylinder.Disk (E := V) | ‖(z : V)‖ = 1} := by
  exact BasedDiskLifting.exists_based_disk_lift_of_surjective
    (n := 6) (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    SixSphereCube.sphereBasePoint (sphereMap_piSix_bijective x).2 L u hu

theorem Sphere.pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6)
    (x : SixSphereCube.StandardSphere) : Subsingleton (π_ n SixSphereCube.StandardSphere x) := by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact piTwo_subsingleton x
  · exact piThree_subsingleton x
  · exact piFour_subsingleton x
  · exact piFive_subsingleton x

theorem Sphere.boundary_homotopic_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V ≤ 6)
    (u : C(DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (x : SixSphereCube.StandardSphere) : u.Homotopic (ContinuousMap.const _ x) :=
  boundary_homotopic_const_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

theorem Sphere.exists_boundary_extension {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V ≤ 6)
    (u : C(DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (x : SixSphereCube.StandardSphere) :
    ∃ v : C(DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere),
      (∀ s, v (DiskCylinder.boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x :=
  exists_boundary_extension_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

theorem LowCellLifting.relativeDiskLifting_five {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (F : C(SixSphereCube.StandardSphere, Y))
    (hpi : ∀ n, 0 < n → n < 6 → ∀ y : Y, Subsingleton (π_ n Y y)) :
    FiniteCells.RelativeDiskLifting F 5 := by
  exact LowCellLifting.relativeDiskLifting_of_pi_vanishing
    F SixSphereCube.sphereBasePoint
    (fun k hk hkd => Sphere.pi_subsingleton hk (by omega)) hpi

attribute [local instance] SpecialPeriods.Threefold.space_simplyConnected in
theorem LowCellLifting.threefold_pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6)
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
theorem LowCellLifting.sphereMap_relativeDiskLifting_five
    (x : SpecialPeriods.Threefold.Space) :
    FiniteCells.RelativeDiskLifting
      (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) 5 :=
  relativeDiskLifting_five _ (fun _ hn hn6 => threefold_pi_subsingleton hn hn6)

theorem TopCellLifting.exists_top_disk_lift {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (x : SpecialPeriods.Threefold.Space)
    (L : V ≃L[ℝ] (Fin 6 → ℝ)) (hd : Module.finrank ℝ V ≤ 6)
    (a : C(DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (u : C(DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space))
    (H : C((unitInterval) × DiskCylinder.Sphere (E := V), SpecialPeriods.Threefold.Space))
    (h0 : ∀ s, H (0, s) = SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x (a s))
    (h1 : ∀ s, H (1, s) = u (DiskCylinder.boundaryToDisk s)) :
    ∃ (v : C(DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere)) (G :
      C((unitInterval) × DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space)),
      (∀ s, v (DiskCylinder.boundaryToDisk s) = a s) ∧
        (∀ z, G (0, z) = SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x (v z)) ∧
          (∀ z, G (1, z) = u z) ∧ ∀ t s, G (t, DiskCylinder.boundaryToDisk s) = H (t, s) :=
  by
  exact TopCellLifting.exists_disk_lift_of_boundary_nullhomotopic
    (n := 6) (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    SixSphereCube.sphereBasePoint (sphereMap_piSix_bijective x).2 L a
    (Sphere.boundary_homotopic_const hd a SixSphereCube.sphereBasePoint) u H h0 h1

theorem TopCellLifting.sphereMap_relativeDiskLifting_six
    (x : SpecialPeriods.Threefold.Space) :
    FiniteCells.RelativeDiskLifting
      (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) 6 := by
  letI := SpecialPeriods.Threefold.space_simplyConnected
  exact TopCellLifting.relativeDiskLifting_of_pi_vanishing_of_surjective
    (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    SixSphereCube.sphereBasePoint
    (fun k hk hkn => Sphere.pi_subsingleton hk hkn)
    (fun k hk hkn => LowCellLifting.threefold_pi_subsingleton hk hkn)
    (sphereMap_piSix_bijective x).2

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_isSmoothRealManifold in
theorem Threefold.finite_homotopy_cells :
    FiniteCells.Built 6 SpecialPeriods.Threefold.Space := by
  simpa only [SpecialPeriods.Threefold.real_dimension] using
    (MorseCells.built_of_compact_smooth_manifold (E := ℂ × ComplexPlane₂) (M :=
      SpecialPeriods.Threefold.Space))

theorem exists_right_homotopy_inverse (x : SpecialPeriods.Threefold.Space) :
    ∃ g : C(SpecialPeriods.Threefold.Space, SixSphereCube.StandardSphere),
      ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
        (ContinuousMap.id SpecialPeriods.Threefold.Space) :=
  FiniteCells.mapsLift_of_built (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    (TopCellLifting.sphereMap_relativeDiskLifting_six x) Threefold.finite_homotopy_cells
    (ContinuousMap.id SpecialPeriods.Threefold.Space)


theorem Sphere.based_homotopicRel_id_of_topClass
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
    sphere_homotopicRel_of_topClass_eq g (ContinuousMap.id SixSphereCube.StandardSphere) hg
      rfl
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] using hd


theorem right_inverse_is_left_inverse (x : SpecialPeriods.Threefold.Space)
    (g : C(SpecialPeriods.Threefold.Space, SixSphereCube.StandardSphere))
    (hfg :
      ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
        (ContinuousMap.id SpecialPeriods.Threefold.Space)) :
    (g.comp (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)).Homotopic
      (ContinuousMap.id SixSphereCube.StandardSphere) :=
  HigherHurewicz.right_inverse_is_left_inverse
    (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) g
    (SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyMap_bijective x 6).1 hfg

def sphereHomotopyEquiv (x : SpecialPeriods.Threefold.Space) :
    SixSphereCube.StandardSphere ≃ₕ SpecialPeriods.Threefold.Space := by
  let g := Classical.choose (exists_right_homotopy_inverse x)
  have hfg := Classical.choose_spec (exists_right_homotopy_inverse x)
  exact
    { toFun := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
      invFun := g
      left_inv := right_inverse_is_left_inverse x g hfg
      right_inv := hfg }

def threefoldHomotopyEquiv :
    SpecialPeriods.Threefold.Space ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1 :=
  (sphereHomotopyEquiv (Classical.choice SpecialPeriods.Threefold.space_nonempty)).symm


theorem MorseCancellation.native_middle_terminal_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
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

theorem MorseCancellation.nativeMiddleCutSequence_terminal_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
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

theorem MorseCancellation.middle_section_classes_span {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hrc <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
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


theorem MorseCancellation.canonical_middle_matrix_surjective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
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
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
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


theorem MorseCancellation.minimal_ordered_index_two_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          ManifoldMorse.IsMorse E v →
            Set.InjOn v (ManifoldMorse.criticalPoints E v) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E v).ncard) :
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
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }) := fun j =>
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

theorem MorseCancellation.minimal_ordered_index_four_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          ManifoldMorse.IsMorse E v →
            Set.InjOn v (ManifoldMorse.criticalPoints E v) →
              (ManifoldMorse.criticalPoints E f).ncard ≤
                (ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 4 = 0 := by
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have horderN :
    ∀ p q : ManifoldMorse.criticalPoints E (fun x => -f x),
      -f p < -f q → nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q :=
    by
    intro p q hpq
    let pf : ManifoldMorse.criticalPoints E f :=
      ⟨p.val, by simpa only [ManifoldMorse.criticalPoints_neg] using p.property⟩
    let qf : ManifoldMorse.criticalPoints E f :=
      ⟨q.val, by simpa only [ManifoldMorse.criticalPoints_neg] using q.property⟩
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


theorem ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ MetricSixSphere) (r c : ℕ)
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

theorem ManifoldMorse.SurgeryWindows.middleMatrix_bijective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ MetricSixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Bijective (S.middleMatrix hf r c htwo hc hthree).mulVec :=
  ⟨S.middleMatrix_injective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount,
    S.middleMatrix_surjective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount⟩

theorem ManifoldMorse.SurgeryWindows.middle_counts_equal {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ MetricSixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) : r = c :=
  (HomologyTransport.matrix_sizes_eq_of_bijective (S.middleMatrix hf r c htwo hc hthree)
      (S.middleMatrix_bijective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount)).symm


theorem MorseCancellation.ordered_no_middle_indices_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
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


theorem MorseCancellation.exists_two_critical_point_morse_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        ManifoldMorse.IsMorse E f ∧
          ∃ p q : M, f p < f q ∧ ManifoldMorse.criticalPoints E f = { p, q } := by
  let _ := pathConnectedSpace_of_homotopySixSphere e
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_system_without_outer_indices E M e hdim
  have htwo := minimal_ordered_index_two_count_zero S hf hm hdim e horder hzero hone hminimal
  have hfour := minimal_ordered_index_four_count_zero S hf hm hdim e horder hsix hfive hminimal
  obtain ⟨-, hcount⟩ :=
    ordered_no_middle_indices_count_two S.toSurgeryWindows hf hdim e horder hzero hsix hone htwo
      hfour hfive
  exact ⟨f, hf, hm, critical_pair_of_surgery_count_two S.toSurgeryWindows hcount⟩

theorem MorseCancellation.nonempty_homeomorph_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ MetricSixSphere) : Nonempty (M ≃ₜ MetricSixSphere) := by
  obtain ⟨f, hf, hm, p, q, hpq, hcrit⟩ :=
    exists_two_critical_point_morse_of_homotopySixSphere E M hdim e
  have hh := ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points hf hm hpq hcrit
  change Nonempty (M ≃ₜ Hemisphere.Sphere (Module.finrank ℝ E)) at hh
  rw [hdim] at hh
  exact hh

theorem homeomorphic_sixSphere_of_homotopySixSphere (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ MetricSixSphere) :
    Nonempty (M ≃ₜ MetricSixSphere) :=
  MorseCancellation.nonempty_homeomorph_of_homotopySixSphere E M hdim hM


end
