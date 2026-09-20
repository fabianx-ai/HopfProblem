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
import Lib.Geometry.Manifold.Morse.MinimalSystem
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
import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Surjectivity
import Lib.Topology.Homeomorph.DiskCube
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
import Lib.Topology.Homotopy.CellFilling
import Lib.Geometry.Manifold.ChartedSpace.Transport
import Lib.Topology.Homotopy.CylinderHEP
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.LinearAlgebra.Matrix.TransvectionReduction
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.Hurewicz.DegreeSix
import Lib.AlgebraicTopology.SingularHomology.LocalContributionsNaturality
import Lib.Geometry.Manifold.Morse.CutTransport
import Lib.Geometry.Manifold.Morse.MiddleBlocks

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section


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
  SphereCube.compactification 6

@[simp]
theorem SixSphereCube.cubeInteriorSphereHomeomorph_infty :
    cubeInteriorSphereHomeomorph (OnePoint.infty) = sphereBasePoint :=
  rfl

def SixSphereCube.cubeSphereMap : C(Fin 6 → (unitInterval), StandardSphere) :=
  SphereCube.quotient 6

@[simp]
theorem SixSphereCube.cubeSphereMap_apply (u : Fin 6 → (unitInterval)) :
    cubeSphereMap u = cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u) :=
  rfl

theorem SixSphereCube.cubeSphereMap_boundary (u : Fin 6 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 6)) : cubeSphereMap u = sphereBasePoint :=
  SphereCube.quotient_boundary 6 u hu

theorem SixSphereCube.cubeSphereMap_eq_iff (u v : Fin 6 → (unitInterval)) :
    cubeSphereMap u = cubeSphereMap v ↔
      u = v ∨ u ∈ Cube.boundary (Fin 6) ∧ v ∈ Cube.boundary (Fin 6) :=
  SphereCube.quotient_eq_iff 6 u v

theorem SixSphereCube.cubeSphereMap_surjective : Function.Surjective cubeSphereMap :=
  SphereCube.quotient_surjective (by decide)

def SixSphereCube.cubeSphereLoop : GenLoop (Fin 6) StandardSphere sphereBasePoint :=
  SphereCube.quotientLoop 6

@[simp]
theorem SixSphereCube.cubeSphereLoop_val : cubeSphereLoop.val = cubeSphereMap :=
  rfl

def SixSphereCube.factorMap {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 6) X x) :
    C(StandardSphere, X) :=
  SphereCube.factorMap (by decide) p

@[simp]
theorem SixSphereCube.factorMap_cubeSphereMap {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (u : Fin 6 → (unitInterval)) :
    factorMap p (cubeSphereMap u) = p u :=
  SphereCube.factorMap_quotient (by decide) p u

@[simp]
theorem SixSphereCube.factorMap_comp_cubeSphereMap {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) : (factorMap p).comp cubeSphereMap = p.val :=
  SphereCube.factorMap_comp_quotient (by decide) p

theorem SixSphereCube.factorMap_unique {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 6) X x) (f : C(StandardSphere, X)) (hf : f.comp cubeSphereMap = p.val) :
    f = factorMap p :=
  SphereCube.factorMap_unique (by decide) p f hf


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


def cylinderQuotient :
    C((unitInterval) × (Fin 6 → (unitInterval)), (unitInterval) × SixSphereCube.StandardSphere) :=
  (ContinuousMap.id (unitInterval)).prodMap SixSphereCube.cubeSphereMap

theorem cylinderQuotient_surjective : Function.Surjective cylinderQuotient := by
  rintro ⟨t, z⟩
  obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
  exact ⟨(t, u), rfl⟩

theorem cylinderQuotient_isQuotientMap : Topology.IsQuotientMap cylinderQuotient :=
  .of_surjective_continuous cylinderQuotient_surjective cylinderQuotient.continuous

theorem cubeHomotopy_constant_on_cylinderFibres {X : Type*} [TopologicalSpace X] {x : X}
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

def cubeHomotopyLift {X : Type*} [TopologicalSpace X] {x : X} {p q : GenLoop (Fin 6) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6))) :
    C((unitInterval) × SixSphereCube.StandardSphere, X) :=
  cylinderQuotient_isQuotientMap.lift H.toHomotopy.toContinuousMap
    (cubeHomotopy_constant_on_cylinderFibres H)

@[simp]
theorem cubeHomotopyLift_apply {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6)))
    (t : (unitInterval)) (u : Fin 6 → (unitInterval)) :
    cubeHomotopyLift H (t, SixSphereCube.cubeSphereMap u) = H (t, u) :=
  ContinuousMap.congr_fun
    (cylinderQuotient_isQuotientMap.lift_comp H.toHomotopy.toContinuousMap
      (cubeHomotopy_constant_on_cylinderFibres H))
    (t, u)

def factorHomotopy {X : Type*} [TopologicalSpace X] {x : X} {p q : GenLoop (Fin 6) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6))) :
    (SixSphereCube.factorMap p).HomotopyRel (SixSphereCube.factorMap q)
      { SixSphereCube.sphereBasePoint } :=
  HigherHurewicz.factorMap_homotopyRel (by decide) H

theorem factorMap_homotopicRel {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (h : GenLoop.Homotopic p q) :
    (SixSphereCube.factorMap p).HomotopicRel (SixSphereCube.factorMap q)
      { SixSphereCube.sphereBasePoint } := by
  obtain ⟨H⟩ := h
  exact ⟨factorHomotopy H⟩

theorem SphereBasepoint.exists_adjustment {Y : Type*} [TopologicalSpace Y] {y : Y}
    (u : C(SixSphereCube.StandardSphere, Y)) (P : Path (u SixSphereCube.sphereBasePoint) y) :
    ∃ v : C(SixSphereCube.StandardSphere, Y),
      v SixSphereCube.sphereBasePoint = y ∧ u.Homotopic v :=
  HigherHurewicz.exists_basepoint_adjustment (by decide) u P

def basedSphereCube {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    GenLoop (Fin 6) X x :=
  HigherHurewicz.basedSphereCube f hf

@[simp]
theorem factorMap_basedSphereCube {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    SixSphereCube.factorMap (basedSphereCube f hf) = f :=
  HigherHurewicz.factorMap_basedSphereCube (by decide) f hf

theorem basedSphereCube_homologyClass {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    SixthHurewicz.cubeHomologyClass (basedSphereCube f hf) =
      SingularMayerVietoris.singularHomologyMap f 6
        (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) :=
  HigherHurewicz.basedSphereCube_homologyClass f hf

theorem sphere_homotopicRel_of_topClass_eq {X : Type} [TopologicalSpace X] {x : X}
    [SimplyConnectedSpace X] [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (f g : C(SixSphereCube.StandardSphere, X))
    (hf : f SixSphereCube.sphereBasePoint = x) (hg : g SixSphereCube.sphereBasePoint = x)
    (h :
      SingularMayerVietoris.singularHomologyMap f 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop)) :
    f.HomotopicRel g { SixSphereCube.sphereBasePoint } :=
  Hurewicz.sphere_homotopicRel_of_topClass_eq
    (by intro j hj hjn; interval_cases j <;> infer_instance) f g hf hg h


theorem Sphere.homotopic_id_of_topClass
    (g : C(SixSphereCube.StandardSphere, SixSphereCube.StandardSphere))
    (hd :
      SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) :
    g.Homotopic (ContinuousMap.id SixSphereCube.StandardSphere) :=
  Hurewicz.sphere_homotopic_id_of_topClass g hd


theorem AdaptedWindows.exists_canonical_basin_sphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) {X : Type} [TopologicalSpace X] [CompactSpace X]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (α : C(X, { y : M // f y = a })) (x₀ : X)
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val)) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ γ : C((Hemisphere.Sphere 2), { y : M // f y = a }),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧
        Topology.IsClosedEmbedding γ ∧
          (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ x)) ∧
            Set.range γ = Set.range α ∧
              (∀ x,
                  ∃ t : ℝ,
                    S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S p hp x).val =
                      (γ x).val) ∧
                ∀ y,
                  y ∈ Set.range γ ↔
                    Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach := S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α x₀ hfull
  obtain ⟨hs, he, hi⟩ := MorseCancellation.nativeIndexThreeAttachingSphere_regular S hf p hp
  let z₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨D, -, -, γ, hγ, hγi, hγd, -, -, horbit⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha
      (MorseCancellation.nativeIndexThreeAttachingSphere S p hp) z₀ hs he.injective hi
      (fun z => hreach _)
  have hγfull (y : { x : M // f x = a }) :
    y ∈ Set.range γ ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) :=
    S.transported_attaching_range_iff hf p ha
      (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2)
      (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
          2).surjective
      γ horbit y
  exact
    ⟨γ, hγ, hγ.continuous.isClosedEmbedding hγi, hγd,
      Set.ext (fun y => (hγfull y).trans (hfull y).symm), horbit, hγfull⟩

theorem AdaptedWindows.exists_canonical_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (α : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = a })
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ γ : Fin n → (Hemisphere.Sphere 2) → { y : M // f y = a },
      MorseCancellation.IsNativeMiddleBasinFamily S hf ha p γ ∧
        (∀ j, Set.range (γ j) = Set.range (α j)) ∧
          ∀ j x,
            ∃ t : ℝ,
              S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
                (γ j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  obtain ⟨hαs, -, -, hαpair, hαfull⟩ := hα
  let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
  have hex (j : Fin n) :=
    S.exists_canonical_basin_sphere hf (p j) (hp j) ha ⟨α j, (hαs j).continuous⟩ x₀ (hαfull j)
  choose γ hγs hγe hγi hγrange hγflow hγfull using hex
  refine ⟨fun j => γ j, ⟨hγs, hγe, hγi, ?_, hγfull⟩, hγrange, hγflow⟩
  intro i j hij
  rw [hγrange i, hγrange j]
  exact hαpair hij


theorem ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass_parametrized {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    d.indexThreeAttachingClass hindex.out =
      SingularMayerVietoris.singularHomologyMap
        (d.coreBoundaryMap.comp
          (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
              2).toHomeomorph.toHomotopyEquiv.toFun)
        2 (SphereHomology.unitSphereTopClass 1) := by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl


theorem AdaptedWindows.native_attaching_class_of_flow_section {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hab : a < S.toSurgeryWindows.lower p)
    (γ : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val) :
    SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hab.le) 2
        (MorseCancellation.middleSectionClass γ) =
      (S.data p).indexThreeAttachingClass
        ((MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hh :=
    S.level_transport_homotopic_in_sublevel hf hab ha
      (MorseCancellation.nativeIndexThreeAttachingSphere S p hp) γ horbit
  have hm := PeriodTorusHigherHomology.homotopic_homologyMap hh 2
  have hparam :
    SingularMayerVietoris.singularHomologyMap
        ((MorseCancellation.levelSublevelMap f (le_refl (S.toSurgeryWindows.lower p))).comp
          (MorseCancellation.nativeIndexThreeAttachingSphere S p hp))
        2 (SphereHomology.unitSphereTopClass 1) =
      (S.data p).indexThreeAttachingClass
        ((MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) :=
    (S.data p).indexThreeAttachingClass_parametrized.symm
  rw [← hparam, hm]
  rw [MorseCancellation.middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

theorem AdaptedWindows.exists_core_inclusion_homology_comparison {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : ManifoldMorse.criticalPoints E f) (k : ℕ) :
    ∃ A :
      SingularMayerVietoris.SingularHomology
          (↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range (S.data p).coreMap)) k ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ S.toSurgeryWindows.upper p } k,
      ∀ a,
        A
            (((S.data p).coreCellPresentation hf.continuous).oldHomologyMap k
              ((S.data p).cellOldHomologyEquiv hf.continuous k a)) =
          SingularMayerVietoris.singularHomologyMap
            (MorseCancellation.sublevelMap f
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
      MorseCancellation.sublevelMap f
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
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range ((S.data p).coreBoundaryHomologyMap k) =
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (MorseCancellation.sublevelMap f
            ((S.toSurgeryWindows.lower_lt_value p).trans
                (S.toSurgeryWindows.value_lt_upper p)).le)
          k) := by
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p k
  let d := S.data p
  refine
    HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
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
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) :
    let I :=
      SingularMayerVietoris.singularHomologyMap
        (MorseCancellation.sublevelMap f
          ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le)
        2
    Function.Surjective I ∧
      LinearMap.ker I =
        Submodule.span ℤ
          {(S.data p).indexThreeAttachingClass
              ((MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp)} := by
  let d := S.data p
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3 :=
    (MorseCancellation.nativeMorseIndex_eq_chart d.chart).symm.trans hp
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


theorem AdaptedWindows.middle_inclusion_step {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hbp : b < S.toSurgeryWindows.lower p)
    (hband :
      ∀ y,
        f y ∈ Set.Icc b (S.toSurgeryWindows.lower p) → y ∉ ManifoldMorse.criticalPoints E f)
    (γ : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ, S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val)
    (hsurj :
      Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hab) 2)) :
    let hau :=
      (hab.trans hbp.le).trans
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le
    Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hau) 2) ∧
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hau) 2) =
        LinearMap.ker
            (SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hab) 2) ⊔
          Submodule.span ℤ {MorseCancellation.middleSectionClass γ} := by
  let hl := (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  let P := SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hab) 2
  let J := SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hbp.le) 2
  let Q := SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hl.le) 2
  have hJ : Function.Bijective J :=
    MorseCancellation.regular_sublevel_inclusion_bijective hf hbp.le hband 2
  obtain ⟨hQ, hkerQ⟩ := S.native_index_three_inclusion_relation hf p hp
  have hclass := S.native_attaching_class_of_flow_section hf p hp ha (hab.trans_lt hbp) γ horbit
  have hcomp :
    J.comp P =
      SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f (hab.trans hbp.le))
        2 :=
    MorseCancellation.sublevelHomologyMap_comp f hab hbp.le 2
  have htotal :
    Q.comp (J.comp P) =
      SingularMayerVietoris.singularHomologyMap
        (MorseCancellation.sublevelMap f ((hab.trans hbp.le).trans hl.le)) 2 := by
    rw [hcomp]
    exact MorseCancellation.sublevelHomologyMap_comp f (hab.trans hbp.le) hl.le 2
  have hkerJ : LinearMap.ker (J.comp P) = LinearMap.ker P := by
    ext v
    change J (P v) = 0 ↔ P v = 0
    exact ⟨fun h => hJ.injective (h.trans (map_zero J).symm), fun h => by rw [h, map_zero]⟩
  have hker :
    LinearMap.ker Q = Submodule.span ℤ {(J.comp P) (MorseCancellation.middleSectionClass γ)} := by
    rw [hcomp, hclass]
    exact hkerQ
  constructor
  · rw [← htotal]
    exact hQ.comp (hJ.surjective.comp hsurj)
  · rw [← htotal,
      HomologyTransport.ker_comp_span_singleton (J.comp P) Q
        (MorseCancellation.middleSectionClass γ) hker,
      hkerJ]


theorem AdaptedWindows.finite_middle_inclusion_relations {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3) (cut : Fin (n + 1) → ℝ)
    (ha : ∀ y, f y = cut 0 → y ∉ ManifoldMorse.criticalPoints E f)
    (hbase : ∀ i, cut 0 ≤ cut i) (hnext : ∀ j, cut j.succ = S.toSurgeryWindows.upper (p j))
    (hlower : ∀ j, cut j.castSucc < S.toSurgeryWindows.lower (p j))
    (hband :
      ∀ j y,
        f y ∈ Set.Icc (cut j.castSucc) (S.toSurgeryWindows.lower (p j)) →
          y ∉ ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = cut 0 }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
            (γ j x).val) :
    Function.Surjective
        (SingularMayerVietoris.singularHomologyMap
          (MorseCancellation.sublevelMap f (hbase (Fin.last n))) 2) ∧
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (MorseCancellation.sublevelMap f (hbase (Fin.last n))) 2) =
        Submodule.span ℤ (Set.range (fun j => MorseCancellation.middleSectionClass (γ j))) := by
  have hprefix (k : ℕ) :
    ∀ hk : k ≤ n,
      Function.Surjective
          (SingularMayerVietoris.singularHomologyMap
            (MorseCancellation.sublevelMap f (hbase ⟨k, by omega⟩)) 2) ∧
        LinearMap.ker
            (SingularMayerVietoris.singularHomologyMap
              (MorseCancellation.sublevelMap f (hbase ⟨k, by omega⟩)) 2) =
          Submodule.span ℤ
            (Set.range
              (fun j : Fin k =>
                MorseCancellation.middleSectionClass (γ ⟨j.val, j.isLt.trans_le hk⟩))) := by
    induction k with
    | zero =>
      intro hk
      have hid :
        SingularMayerVietoris.singularHomologyMap
            (MorseCancellation.sublevelMap f (hbase ⟨0, by omega⟩)) 2 =
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
              (MorseCancellation.sublevelMap f (hbase ⟨k + 1, by omega⟩)) 2) ∧
          LinearMap.ker
              (SingularMayerVietoris.singularHomologyMap
                (MorseCancellation.sublevelMap f (hbase ⟨k + 1, by omega⟩)) 2) =
            LinearMap.ker
                (SingularMayerVietoris.singularHomologyMap
                  (MorseCancellation.sublevelMap f (hbase j.castSucc)) 2) ⊔
              Submodule.span ℤ {MorseCancellation.middleSectionClass (γ j)} := by
        have heq : cut ⟨k + 1, by omega⟩ = S.toSurgeryWindows.upper (p j) := hnext j
        have aux (b : ℝ) (hb : cut 0 ≤ b) (he : b = S.toSurgeryWindows.upper (p j)) :
          Function.Surjective
              (SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hb) 2) ∧
            LinearMap.ker
                (SingularMayerVietoris.singularHomologyMap (MorseCancellation.sublevelMap f hb) 2) =
              LinearMap.ker
                  (SingularMayerVietoris.singularHomologyMap
                    (MorseCancellation.sublevelMap f (hbase j.castSucc)) 2) ⊔
                Submodule.span ℤ {MorseCancellation.middleSectionClass (γ j)} := by
          subst b
          exact hstep
        exact aux _ _ heq
      refine ⟨hstep'.1, ?_⟩
      rw [hstep'.2, hkernel]
      exact MorseCancellation.span_prefix_succ (fun i => MorseCancellation.middleSectionClass (γ i)) hkn
  simpa only using hprefix n le_rfl

theorem MorseCancellation.ordered_middle_inclusion_relations {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hn <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hn }))
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


theorem AdaptedWindows.exists_middle_family_value_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
    [Nonempty M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec) (i j : Fin n)
    (hij : f (p i) < f (p j))
    (hconsecutive :
      ∀ z : ManifoldMorse.criticalPoints E f, ¬(f (p i) < f z ∧ f z < f (p j))) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f,
            Set.InjOn g (ManifoldMorse.criticalPoints E g) ∧
              g (p i) = f (p j) ∧
                g (p j) = f (p i) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      z ≠ (p i).val → z ≠ (p j).val → g z = f z) ∧
                    (∀ x y : ManifoldMorse.criticalPoints E g,
                        g x < g y →
                          MorseCancellation.nativeMorseIndex E g x ≤
                            MorseCancellation.nativeMorseIndex E g y) ∧
                      (∀ z ∈ ManifoldMorse.criticalPoints E f,
                          MorseCancellation.nativeMorseIndex E g z =
                            MorseCancellation.nativeMorseIndex E f z) ∧
                        (∀ k,
                            MorseCancellation.nativeMorseCount E g k =
                              MorseCancellation.nativeMorseCount E f k) ∧
                          ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                            ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                              ∃ hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g,
                                ∃ T : AdaptedWindows E g,
                                  T.field = S.field ∧
                                    T.flow = S.flow ∧
                                      (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                        let p' : Fin n → ManifoldMorse.criticalPoints E g :=
                                          fun k => ⟨(p k).val, hcrit.symm ▸ (p k).property⟩
                                        let B' := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
                                        let γ' := fun k =>
                                          MorseCancellation.equalCutSection hlevel (γ k)
                                        (∀ k, MorseCancellation.nativeMorseIndex E g (p' k) = 3) ∧
                                          (∀ k, a < T.toSurgeryWindows.lower (p' k)) ∧
                                            MorseCancellation.IsNativeMiddleBasinFamily T hg hga p'
                                                (fun k => γ' k) ∧
                                              (∀ k x, (γ' k x).val = (γ k x).val) ∧
                                                MorseCancellation.canonicalMiddleMatrix B' γ' =
                                                    MorseCancellation.canonicalMiddleMatrix B γ ∧
                                                  Function.Surjective
                                                    (MorseCancellation.canonicalMiddleMatrix B'
                                                        γ').mulVec := by
  obtain ⟨δ, -, -, -, -, horbit, -⟩ :=
    S.exists_canonical_basin_sphere hf (p j) (hp j) ha (γ j)
      (Hemisphere.point Bool.true ⟨0, by simp⟩) (hγ.2.2.2.2 j)
  obtain
    ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, -, hothers, hindices, hcounts, hsub, hlevel, hgerm, hga,
      T, hfield, hflow, -, habove⟩ :=
    S.exists_common_cut_value_exchange hf hm ha (p i) (p j) hij hconsecutive (hp j) (hlower i) δ
      horbit
  have hneworder :=
    MorseCancellation.native_index_order_of_equal_index_exchange horder (p i) (p j)
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
  have hmatrix := MorseCancellation.canonicalMiddleMatrix_equalCut hsub hlevel B γ
  refine
    ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, (fun z hz hzi hzj => (hothers z hz hzi hzj).self_of_nhds),
      hneworder, hindices, hcounts, hsub, hlevel, hga, T, hfield, hflow, hgerm, ?_, ?_, ?_, ?_,
      hmatrix, ?_⟩
  · intro k
    exact (hindices (p k) (p k).property).trans (hp k)
  · intro k
    exact habove ⟨(p k).val, hcrit.symm ▸ (p k).property⟩ (hheight k)
  · exact MorseCancellation.nativeMiddleBasinFamily_equalCut S T hf hg ha hga hcrit hlevel hflow p γ hγ
  · intro k x
    rfl
  · rw [hmatrix]
    exact hsurj

theorem AdaptedWindows.exists_first_middle_pivot {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
    [Nonempty M] (S₀ : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S₀.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S₀ hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec) (q : Fin n) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f,
            (∀ x y : ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancellation.nativeMorseIndex E g x ≤ MorseCancellation.nativeMorseIndex E g y) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f,
                  MorseCancellation.nativeMorseIndex E g z = MorseCancellation.nativeMorseIndex E f z) ∧
                (∀ k, MorseCancellation.nativeMorseCount E g k = MorseCancellation.nativeMorseCount E f k) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ j, j ≠ q → g (p q) < g (p j)) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              T.field = S₀.field ∧
                                T.flow = S₀.flow ∧
                                  (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                    let p' : Fin n → ManifoldMorse.criticalPoints E g :=
                                      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                    let B' := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
                                    let γ' := fun j => MorseCancellation.equalCutSection hlevel (γ j)
                                    (∀ j, MorseCancellation.nativeMorseIndex E g (p' j) = 3) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        MorseCancellation.IsNativeMiddleBasinFamily T hg hga p'
                                            (fun j => γ' j) ∧
                                          (∀ j x, (γ' j x).val = (γ j x).val) ∧
                                            MorseCancellation.canonicalMiddleMatrix B' γ' =
                                                MorseCancellation.canonicalMiddleMatrix B γ ∧
                                              Function.Surjective
                                                (MorseCancellation.canonicalMiddleMatrix B'
                                                    γ').mulVec := by
  classical
  have hpinj := MorseCancellation.nativeMiddleBasinFamily_labels_injective S₀ hf ha p γ hγ
  let P : ℕ → Prop := fun m =>
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        ManifoldMorse.IsMorse E g ∧
          ∃ hc : ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f,
            ∃ hs : ∀ y, g y ≤ a ↔ f y ≤ a,
              ∃ hl : ∀ y, g y = a ↔ f y = a,
                ∃ hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g,
                  ∃ T : AdaptedWindows E g,
                    (∀ x y : ManifoldMorse.criticalPoints E g,
                        g x < g y →
                          MorseCancellation.nativeMorseIndex E g x ≤
                            MorseCancellation.nativeMorseIndex E g y) ∧
                      (∀ z ∈ ManifoldMorse.criticalPoints E f,
                          MorseCancellation.nativeMorseIndex E g z =
                            MorseCancellation.nativeMorseIndex E f z) ∧
                        (∀ z ∈ ManifoldMorse.criticalPoints E f,
                            (∀ j, z ≠ (p j).val) → g z = f z) ∧
                          T.field = S₀.field ∧
                            T.flow = S₀.flow ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                (∀ j,
                                    a <
                                      T.toSurgeryWindows.lower
                                        ⟨(p j).val, hc.symm ▸ (p j).property⟩) ∧
                                  MorseRearrangement.beforeValueRank (fun j => g (p j)) q =
                                    m
  have hex : ∃ m, P m :=
    ⟨MorseRearrangement.beforeValueRank (fun j => f (p j)) q, f, hf, hm, rfl, fun _ =>
      Iff.rfl, fun _ => Iff.rfl, ha, S₀, horder, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
      fun _ _ => Filter.EventuallyEq.rfl, hlower, rfl⟩
  obtain
    ⟨g, hg, hmg, hcrit, hsub, hlevel, hga, T, hgorder, hindices, houtside, hfield, hflow, hgerm,
      hglower, hrank⟩ :=
    Nat.find_spec hex
  let pg : Fin n → ManifoldMorse.criticalPoints E g := fun j =>
    ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
  let Bg := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
  let γg := fun j => MorseCancellation.equalCutSection hlevel (γ j)
  have hpg (j : Fin n) : MorseCancellation.nativeMorseIndex E g (pg j) = 3 :=
    (hindices (p j) (p j).property).trans (hp j)
  have hfamily : MorseCancellation.IsNativeMiddleBasinFamily T hg hga pg (fun j => γg j) :=
    MorseCancellation.nativeMiddleBasinFamily_equalCut S₀ T hf hg ha hga hcrit hlevel hflow p γ hγ
  have hmatrix :
    MorseCancellation.canonicalMiddleMatrix Bg γg = MorseCancellation.canonicalMiddleMatrix B γ :=
    MorseCancellation.canonicalMiddleMatrix_equalCut hsub hlevel B γ
  have hgsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix Bg γg).mulVec := by
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
      ∀ z : ManifoldMorse.criticalPoints E g, ¬(g (pg i) < g z ∧ g z < g (pg q)) := by
      intro z hz
      have hidx : MorseCancellation.nativeMorseIndex E g z = 3 := by
        apply Nat.le_antisymm
        · exact (hgorder z (pg q) hz.2).trans_eq (hpg q)
        · exact (hpg i).symm.trans_le (hgorder (pg i) z hz.1)
      let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : MorseCancellation.nativeMorseIndex E f zf = 3 :=
        (hindices z zf.property).symm.trans hidx
      obtain ⟨k, hk⟩ := hcomplete zf hzf
      exact hconsecutive k (by simpa only [hk] using hz)
    obtain
      ⟨u, hu, hmu, hcu, -, hui, huq, huothers, huorder, huindices, -, hus, hul, hua, U, hufield,
        huflow, hugerm, -, hulower, -, -, -, -⟩ :=
      T.exists_middle_family_value_exchange hg hmg hga hgorder pg hpg hglower Bg γg hfamily hgsurj
        i q hiq hglobal
    have hdecrease :
      MorseRearrangement.beforeValueRank (fun k => u (p k)) q <
        MorseRearrangement.beforeValueRank (fun k => g (p k)) q := by
      apply
        MorseRearrangement.beforeValueRank_exchange_lt hvalueinj hiq hconsecutive hui huq
      intro k hki hkq
      apply huothers (pg k) (pg k).property
      · exact fun heq => hki (hpinj (Subtype.ext heq))
      · exact fun heq => hkq (hpinj (Subtype.ext heq))
    have hminimal :=
      Nat.find_min' hex
        (show P (MorseRearrangement.beforeValueRank (fun k => u (p k)) q) from
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
      MorseCancellation.nativeMorseCount_eq_of_preserved_indices hcrit hindices, houtside, hfirst, hsub,
      hlevel, hga, T, hfield, hflow, hgerm, hpg, hglower, hfamily, fun _ _ => rfl, hmatrix,
      hgsurj⟩


theorem AdaptedWindows.exists_higher_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → ManifoldMorse.criticalPoints E f) (j₀ : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3) (hpb : ∀ j, b < f (p j))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) :
    ∃ β : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = b }),
      MorseCancellation.IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have hreach (j : Fin n) (x : (Hemisphere.Sphere 2)) :
    (α j x).val ∈ FlowCancellation.levelBasin S.flow f b := by
    apply
      S.backward_basin_reaches_intermediate_cut hf ((hfull j (α j x)).mp (Set.mem_range_self x))
    · simpa only [(α j x).property] using hab
    · exact hpb j
  let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
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


theorem AdaptedWindows.exists_relative_family_lower_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Hemisphere.Sphere 2), (S.data q).UpperLevel))
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => α j))
    (havoid : ∀ j, Disjoint (Set.range (α j)) (Set.range (S.data q).surgery.beltSphere))
    (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K : Set (S.data q).UpperLevel),
      IsCompact K →
        SupportedDiffeomorph.SupportedRelativeIsotopy D K
            (MorseRearrangement.otherSheetImages (fun j => α j) i) →
          (∀ j, Disjoint (Set.range (D ∘ α j)) (Set.range (S.data q).surgery.beltSphere)) →
            ∃ T : AdaptedWindows E f,
              (∀ z, (T.data z).chart = (S.data z).chart) ∧
                (∀ z, (T.data z).radius < ε z) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                    ∃ β δ : Fin n → C((Hemisphere.Sphere 2), (S.data q).LowerLevel),
                      MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p
                          (fun j => β j) ∧
                        MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p
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
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  dsimp only
  intro D K hK I hDavoid
  let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
  let u :=
    SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected, hcut, hkeep⟩ :=
    S.exists_relative_surgery_cut_transport hf hm q (α i x₀) ε hε D K
      (MorseRearrangement.otherSheetImages (fun j => α j) i) hK I
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have holdreach (j : Fin n) (x : (Hemisphere.Sphere 2)) :=
    S.belt_complement_reaches_lower_level hf q (α j x)
      (fun h => Set.disjoint_left.mp (havoid j) (Set.mem_range_self x) h)
  have hnewreach (j : Fin n) (x : (Hemisphere.Sphere 2)) :=
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
  let β : Fin n → C((Hemisphere.Sphere 2), (S.data q).LowerLevel) := fun j =>
    ⟨β₀ j, (hβs j).continuous⟩
  let δ : Fin n → C((Hemisphere.Sphere 2), (S.data q).LowerLevel) := fun j =>
    ⟨δ₀ j, (hδs j).continuous⟩
  have hδold (j : Fin n) (x : (Hemisphere.Sphere 2)) :
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
        (MorseRearrangement.mem_otherSheetImages (fun j => α j) i j hji x)
    rw [hfix] at hs
    obtain ⟨t, ht⟩ := hβflow j x
    change S.flow t (α j x).val = (β j x).val at ht
    have hshared : S.flow 0 (δ j x).val = S.flow (s - t) (β j x).val := by
      rw [S.flow.map_zero_apply, ← hs, ← ht, ← S.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z ((S.data q).lower_regular z hz)) (δ j x).property
        (β j x).property hshared
  · intro j hji x
    exact
      hprotected (α j x) (MorseRearrangement.mem_otherSheetImages (fun j => α j) i j hji x)


theorem MorseCancellation.exists_radial_link_meridian_with_derivative {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    (H : C(ℝ × (Hemisphere.Sphere 2), d.UpperLevel)) {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (x₀ : (Hemisphere.Sphere 2)) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (hpoint : d.surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range d.surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) => d.beltNormal (H (radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
      ∃ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
        ∃ (w : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (β :
          C((Hemisphere.Sphere 2), Metric.sphere (0 : d.chart.NegativeCoordinates) 1)),
          SingularMayerVietoris.singularHomologyMap β 2 =
              SingularMayerVietoris.singularHomologyMap
                (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 ∧
            ((PassageHomology.puncturedPassageTrace H (Set.range d.surgery.beltSphere) hτ
                      x₀ hcross).comp
                  (PassageHomology.cylinderLink τ x₀ ε hε hεx)).Homotopic
              ((nativeBeltTubeMeridian d w (1 / 2) (by norm_num) (by norm_num)).comp β) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
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
  have hgΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (Ψ 0) := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hg
  have hnormal :=
    d.contMDiffOn_beltNormal hf |>.contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have hnormal' :
    ContMDiffAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal
      (H (Ψ 0)) := by
    rw [hcenter]
    exact hnormal
  have hF : ContDiffAt ℝ ∞ (fun z : (EuclideanSpace ℝ (Fin 3)) => d.beltNormal (H (Ψ z))) 0 :=
    (ContMDiffAt.comp (g := d.beltNormal) (f := fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) 0
        hnormal' (hgΨ.comp 0 hΨ)).contDiffAt
  have hF0 : d.beltNormal (H (Ψ 0)) = 0 := by rw [hcenter, d.beltNormal_belt]
  obtain ⟨b⟩ := LocalDegree.nonempty_boundaryData_of_contDiffAt L hL hF0 hs hF
  have hball (u : (Hemisphere.Sphere 2)) : b.radius • u.val ∈ s := by
    apply b.ball_subset
    rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul b.radius b.radius_pos u]
  have hεx : b.radius < Real.exp τ := by
    have hh := (hst (hball x₀)).2.1
    rwa [mem_ball_zero_iff, LocalDegree.norm_radius_smul b.radius b.radius_pos x₀] at hh
  obtain ⟨J, hJ, w, hmeridian⟩ :=
    normal_boundary_homotopic_native_meridian d (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) b
      hcs hdomain hsmall (1 / 2) (by norm_num) (by norm_num)
  have hlink :
    (PassageHomology.puncturedPassageTrace H (Set.range d.surgery.beltSphere) hτ x₀
            hcross).comp
        (PassageHomology.cylinderLink τ x₀ b.radius b.radius_pos hεx) =
      J := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    have htimeu :
      (PassageHomology.cylinderLink τ x₀ b.radius b.radius_pos hεx u).val.1 ∈
        Set.Icc (0 : ℝ) 1 := by
      rw [← radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
      exact ⟨(hst (hball u)).2.2.1.le, (hst (hball u)).2.2.2.le⟩
    rw [ContinuousMap.comp_apply,
      PassageHomology.puncturedPassageTrace_on_interval H (Set.range d.surgery.beltSphere)
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
    (p : ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × (Hemisphere.Sphere 2), (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : (Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (hpoint : (S.data p).surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data p).chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          (S.data p).beltNormal (H (MorseCancellation.radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
      ∃ D :
        C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
          (S.data p).LowerLevel),
        (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
          (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
            let G :=
              D.comp
                (PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            SingularMayerVietoris.singularHomologyMap
                (G.comp (PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
              SingularMayerVietoris.singularHomologyMap
                  (G.comp (PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                SingularMayerVietoris.singularHomologyMap
                  ((S.data p).surgery.attachingSphere.comp
                    (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
                  2 := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro hg
  let e :
    (Hemisphere.Sphere 2) ≃ₜ Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1 :=
    (SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
        2).toHomeomorph
  obtain ⟨D, horbit, hunique, hmeridian, _, hrelation⟩ :=
    S.exists_lower_passage_homology_relation hf p (e x₀) v H hτ x₀ hcross
  obtain ⟨ε, hε, hεx, w, β, hβ, hlink⟩ :=
    MorseCancellation.exists_radial_link_meridian_with_derivative (S.data p) hf H hτ x₀ v hpoint hcross
      L hL hg
  let σ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hσ : 0 < (σ : ℝ) := by norm_num [σ]
  have htube :
    MorseCancellation.nativeBeltTubeMeridian (S.data p) w (1 / 2) (by norm_num) (by norm_num) =
      MorseCancellation.nativeUpperMeridianInComplement S p w σ hσ :=
    MorseCancellation.nativeBeltTubeMeridian_eq S p w (1 / 2) (by norm_num) (by norm_num)
  rw [htube] at hlink
  let G :=
    D.comp
      (PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere) hτ
        x₀ hcross)
  have hDlink :
    (G.comp (PassageHomology.cylinderLink τ x₀ ε hε hεx)).Homotopic
      ((D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w σ hσ)).comp β) :=
    (ContinuousMap.Homotopic.refl D).comp hlink
  have hatt :
    ((D.comp (MorseCancellation.nativeUpperMeridianInComplement S p w σ hσ)).comp β).Homotopic
      ((S.data p).surgery.attachingSphere.comp β) :=
    (hmeridian w σ hσ).comp (ContinuousMap.Homotopic.refl β)
  have hlinkMap := PeriodTorusHigherHomology.homotopic_homologyMap (hDlink.trans hatt) 2
  have hderivativeMap :
    SingularMayerVietoris.singularHomologyMap ((S.data p).surgery.attachingSphere.comp β) 2 =
      SingularMayerVietoris.singularHomologyMap
        ((S.data p).surgery.attachingSphere.comp
          (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
        2 := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hβ]
  refine ⟨D, horbit, hunique, ?_⟩
  have hh := hrelation ε hε hεx
  change
    SingularMayerVietoris.singularHomologyMap
        (G.comp (PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
      SingularMayerVietoris.singularHomologyMap
          (G.comp (PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
        SingularMayerVietoris.singularHomologyMap
          (G.comp (PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 at hh
  rw [hlinkMap, hderivativeMap] at hh
  exact hh


theorem MorseCancellation.choose_prescribed_normal_passage {E M Y N : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup N]
    [NormedSpace ℝ N] {f : (Hemisphere.Sphere 2) → M} {g : Y → M}
    {x : (Hemisphere.Sphere 2)} {y : Y} {O : Set M} (n : M → N)
    (e : (Hemisphere.Sphere 2) ≃ₜ Metric.sphere (0 : N) 1)
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
            (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
          k •
            SingularMayerVietoris.singularHomologyMap
              (e : C((Hemisphere.Sphere 2), Metric.sphere (0 : N) 1)) 2 := by
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2) := by
    have heq :
      (LinearSphereAction.homologyEquiv L₀ 2 :
          SingularMayerVietoris.SingularHomology (Hemisphere.Sphere 2) 2 →
            SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 2) =
        SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 :=
      funext (LinearSphereAction.homologyEquiv_apply L₀ 2)
    rw [← heq]
    exact (LinearSphereAction.homologyEquiv L₀ 2).bijective
  obtain ⟨u, hu, hunit⟩ :=
    two_sphere_map_unit_of_homology_bijective e
      (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) hbij
  have hopp :
    SingularMayerVietoris.singularHomologyMap
        (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 =
      -SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 := by
    simpa using
      attaching_contributions_opposite_of_relative_det_neg
        (ContinuousMap.id (Metric.sphere (0 : N) 1)) L₀ L₁ hdet
  by_cases huk : u = k
  · exact ⟨A₀, L₀, hL₀, huk ▸ hunit⟩
  · have hneg : -u = k := by
      rcases hu with rfl | rfl <;> rcases hk with rfl | rfl <;> norm_num at *
    refine ⟨A₁, L₁, hL₁, ?_⟩
    rw [hopp, hunit, ← neg_zsmul, hneg]

theorem MorseCancellation.exists_native_prescribed_centered_passage {E M Z : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z]
    [SecondCountableTopology Z] (d : ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C((Hemisphere.Sphere 2), d.UpperLevel)) (hαe : Topology.IsEmbedding α)
    (hdisj : Disjoint (Set.range α) (Set.range d.surgery.beltSphere)) (b : Z → d.UpperLevel)
    (hbc : IsClosed (Set.range b)) (x : (Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (hx : α x ∉ Set.range b)
    (hv : d.surgery.beltSphere v ∉ Set.range b) (γ : Path (α x) (d.surgery.beltSphere v)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) α z)) →
        ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ b →
          ∃ A :
            CenteredSheetPassage (RegularLevel.Model E) α d.surgery.beltSphere x v
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
                    (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
                  k •
                    SingularMayerVietoris.singularHomologyMap
                      ((SphereCoordinates.standardParametrization
                            d.chart.NegativeCoordinates 2).toHomeomorph :
                        C((Hemisphere.Sphere 2),
                          Metric.sphere (0 : d.chart.NegativeCoordinates) 1))
                      2 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hα hαi hb
  obtain ⟨A₀, A₁, L₀, L₁, hL₀, hL₁, hdet⟩ :=
    exists_native_opposite_centered_passages d hf hdim α hαe hdisj b hbc x v hx hv γ hα hαi hb
  exact
    choose_prescribed_normal_passage d.beltNormal
      (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
      A₀ A₁ L₀ L₁ hL₀ hL₁ hdet k hk

theorem MorseCancellation.exists_native_prescribed_finite_family_passage {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (a : ι → C((Hemisphere.Sphere 2), d.UpperLevel))
    (hpair : Pairwise (fun j k => Disjoint (Set.range (a j)) (Set.range (a k)))) (i : ι)
    (hfe : Topology.IsEmbedding (a i))
    (hdisj : Disjoint (Set.range (a i)) (Set.range d.surgery.beltSphere))
    (x : (Hemisphere.Sphere 2)) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (hv : d.surgery.beltSphere v ∉ MorseRearrangement.otherSheetImages (fun j => a j) i)
    (γ : Path (a i x) (d.surgery.beltSphere v)) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (a j)) →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (a i) z)) →
        ∃ A :
          CenteredSheetPassage (RegularLevel.Model E) (a i) d.surgery.beltSphere x v
            (MorseRearrangement.otherSheetImages (fun j => a j) i),
          ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  d.beltNormal
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        a i (radialParameterChart (1 / 2) x z).2)))
                L.toContinuousLinearMap 0 ∧
              SingularMayerVietoris.singularHomologyMap
                  (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
                k •
                  SingularMayerVietoris.singularHomologyMap
                    ((SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
                          2).toHomeomorph :
                      C((Hemisphere.Sphere 2),
                        Metric.sphere (0 : d.chart.NegativeCoordinates) 1))
                    2 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro ha hfi
  obtain ⟨n, b, hb, hbrange⟩ :=
    MorseRearrangement.exists_sheetSumMap_for_finite_family
      (fun j : { j : ι // j ≠ i } => a j.val) (fun j => ha j.val)
  have hrange : Set.range b = MorseRearrangement.otherSheetImages (fun j => a j) i :=
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
    CenteredSheetPassage (RegularLevel.Model E) (a i) d.surgery.beltSphere x v
      (MorseRearrangement.otherSheetImages (fun j => a j) i) :=
    { A with avoids := by rw [← hrange]; exact A.avoids }
  exact ⟨A', L, hL, hunit⟩

theorem AdaptedWindows.exists_higher_family_prescribed_passage {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
    let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
      ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
    ∃ β : Fin n → C((Hemisphere.Sphere 2), (S.data q).UpperLevel),
      MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
          (∀ j, Disjoint (Set.range (β j)) (Set.range (S.data q).surgery.beltSphere)) ∧
            ∃ (x : (Hemisphere.Sphere 2)) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1),
              ∃ A :
                MorseCancellation.CenteredSheetPassage (RegularLevel.Model E) (β i)
                  (S.data q).surgery.beltSphere x v
                  (MorseRearrangement.otherSheetImages (fun j => β j) i),
                ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data q).chart.NegativeCoordinates,
                  HasFDerivAt
                      (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                        (S.data q).beltNormal
                          (A.family
                            ((MorseCancellation.radialParameterChart (1 / 2) x z).1,
                              β i (MorseCancellation.radialParameterChart (1 / 2) x z).2)))
                      L.toContinuousLinearMap 0 ∧
                    SingularMayerVietoris.singularHomologyMap
                        (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)
                        2 =
                      k •
                        SingularMayerVietoris.singularHomologyMap
                          ((SphereCoordinates.standardParametrization
                                (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                            C((Hemisphere.Sphere 2),
                              Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1))
                          2 := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : CompactSpace (S.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hsplit := (S.data q).chart.finrank_negative_add_positive
      have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
      omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨β₀, hβ₀, horbit₀⟩ :=
    S.exists_higher_middle_family hf (haq.trans (S.toSurgeryWindows.value_lt_upper q)) ha
      (S.data q).upper_regular p i hp hhigh α hα
  let β : Fin n → C((Hemisphere.Sphere 2), (S.data q).UpperLevel) := β₀
  have hβ :
    MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) := hβ₀
  have horbit : ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := horbit₀
  have hdisj (j : Fin n) : Disjoint (Set.range (β j)) (Set.range (S.data q).surgery.beltSphere) :=
    by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ hy
    exact S.upper_point_not_on_belt_of_lower_orbit hf q haq (α j x) (β j x) (horbit j x) hy
  let x : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
  let v :=
    SphereCoordinates.standardParametrization (S.data q).chart.PositiveCoordinates 2 x
  have hv :
    (S.data q).surgery.beltSphere v ∉
      MorseRearrangement.otherSheetImages (fun j => β j) i := by
    intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdisj j.val) hj (Set.mem_range_self v)
  let _ : PathConnectedSpace (S.data q).UpperLevel :=
    S.pathConnectedSpace_index_three_upper_level hf hdim horder q hq (β i x)
  obtain ⟨A, L, hL, hunit⟩ :=
    MorseCancellation.exists_native_prescribed_finite_family_passage (S.data q) hf hdim β hβ.2.2.2.1 i
      (hβ.2.1 i).isEmbedding (hdisj i) x v hv
      (PathConnectedSpace.somePath (β i x) ((S.data q).surgery.beltSphere v)) k hk hβ.1
      (hβ.2.2.1 i)
  exact ⟨β, hβ, horbit, hdisj, x, v, A, L, hL, hunit⟩

theorem AdaptedWindows.prescribed_passage_actual_endpoint_classes {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × (Hemisphere.Sphere 2), (S.data q).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : (Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (β δ : C((Hemisphere.Sphere 2), (S.data q).LowerLevel))
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (H (0, x)).val = (β x).val)
    (hδ : ∀ x, ∃ t : ℝ, S.flow t (H (1, x)).val = (δ x).val) (k : ℤ)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data q).chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          (S.data q).beltNormal (H (MorseCancellation.radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0)
    (hunit :
      SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
        k •
          SingularMayerVietoris.singularHomologyMap
            ((SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates
                  2).toHomeomorph :
              C((Hemisphere.Sphere 2),
                Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1))
            2) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
      SingularMayerVietoris.singularHomologyMap δ 2 =
        SingularMayerVietoris.singularHomologyMap β 2 +
          k •
            SingularMayerVietoris.singularHomologyMap
              (MorseCancellation.nativeIndexThreeAttachingSphere S q hq) 2 := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro hH
  obtain ⟨D, _, hunique, hrelation⟩ :=
    S.exists_passage_derivative_class_addition hf q H hτ x₀ v hpoint hcross L hL hH
  let G :=
    D.comp
      (PassageHomology.puncturedPassageTrace H (Set.range (S.data q).surgery.beltSphere) hτ
        x₀ hcross)
  have hmap (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hsτ : s ≠ τ)
    (σ : C((Hemisphere.Sphere 2), (S.data q).LowerLevel))
    (hσ : ∀ x, ∃ t : ℝ, S.flow t (H (s, x)).val = (σ x).val) :
    G.comp (PassageHomology.cylinderSlice τ x₀ s hsτ) = σ := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨t, ht⟩ := hσ x
    apply hunique _ (σ x) t
    have heq :=
      PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data q).surgery.beltSphere) hτ x₀ hcross
        (PassageHomology.cylinderSlice τ x₀ s hsτ x) hs
    change
      S.flow t
          (PassageHomology.puncturedPassageTrace H
              (Set.range (S.data q).surgery.beltSphere) hτ x₀ hcross
              (PassageHomology.cylinderSlice τ x₀ s hsτ x)).val.val =
        (σ x).val
    rw [heq]
    exact ht
  have hzero := hmap 0 ⟨le_rfl, zero_le_one⟩ hτ.1.ne β hβ
  have hone := hmap 1 ⟨zero_le_one, le_rfl⟩ hτ.2.ne' δ hδ
  have hcoef :
    SingularMayerVietoris.singularHomologyMap
        ((S.data q).surgery.attachingSphere.comp
          (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
        2 =
      k •
        SingularMayerVietoris.singularHomologyMap
          (MorseCancellation.nativeIndexThreeAttachingSphere S q hq) 2 := by
    change
      SingularMayerVietoris.singularHomologyMap
          ((S.data q).surgery.attachingSphere.comp
            (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
          2 =
        k •
          SingularMayerVietoris.singularHomologyMap
            ((S.data q).surgery.attachingSphere.comp
              ((SphereCoordinates.standardParametrization
                    (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                C((Hemisphere.Sphere 2),
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
        (G.comp (PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
      SingularMayerVietoris.singularHomologyMap
          (G.comp (PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
        SingularMayerVietoris.singularHomologyMap
          ((S.data q).surgery.attachingSphere.comp
            (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
          2 at hrelation
  rw [hone, hzero, hcoef] at hrelation
  exact hrelation

theorem AdaptedWindows.exists_prescribed_family_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) (ε : ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ β δ : Fin n → C((Hemisphere.Sphere 2), (S.data q).LowerLevel),
              MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p
                  (fun j => β j) ∧
                MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p
                    (fun j => δ j) ∧
                  (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                    (∀ j, j ≠ i → δ j = β j) ∧
                      (∀ j, j ≠ i → ∀ x, ∃ t : ℝ, T.flow t (δ j x).val = (α j x).val) ∧
                        (SingularMayerVietoris.singularHomologyMap (δ i) 2 =
                            SingularMayerVietoris.singularHomologyMap (β i) 2 +
                              k •
                                SingularMayerVietoris.singularHomologyMap
                                  (MorseCancellation.nativeIndexThreeAttachingSphere S q hq) 2) ∧
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
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hsplit := (S.data q).chart.finrank_negative_add_positive
      have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
      omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
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
    SupportedDiffeomorph.SupportedRelativeIsotopy D K
      (MorseRearrangement.otherSheetImages (fun j => γ j) i) :=
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
          (MorseRearrangement.mem_otherSheetImages (fun j => γ j) i j hji x)
      exact Set.disjoint_left.mp (havoid j) (Set.mem_range_self x) ⟨w, hw.trans heq⟩
  obtain
    ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hβflow, hδflow, hδold, hother, hprotected,
      hkeep⟩ :=
    S.exists_relative_family_lower_transport hf hm q hq p i hhigh γ hγ havoid ε hε D K hK I
      hDavoid
  let H : C(ℝ × (Hemisphere.Sphere 2), (S.data q).UpperLevel) :=
    ⟨fun z => F (z.1, γ i z.2),
      hF.continuous.comp (continuous_fst.prodMk ((γ i).continuous.comp continuous_snd))⟩
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H :=
    hF.comp (contMDiff_fst.prodMk ((hγ.1 i).comp contMDiff_snd))
  have hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀) :=
    ((hcount τ ⟨hτ.1.le, hτ.2.le⟩ x₀ v).mpr ⟨rfl, rfl, rfl⟩).symm
  have hcross :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ x : (Hemisphere.Sphere 2),
        H (t, x) ∈ Set.range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀ := by
    intro t ht x
    constructor
    · rintro ⟨w, hw⟩
      have hh := (hcount t ht x w).mp hw.symm
      exact ⟨hh.1, hh.2.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨v, hpoint⟩
  have hstart (x : (Hemisphere.Sphere 2)) :
    ∃ t : ℝ, S.flow t (H (0, x)).val = (β i x).val := by
    change ∃ t : ℝ, S.flow t (A.family (0, γ i x)).val = (β i x).val
    rw [hF0]
    exact hβflow i x
  have hend (x : (Hemisphere.Sphere 2)) : ∃ t : ℝ, S.flow t (H (1, x)).val = (δ i x).val := by
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
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancellation.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (hαq :
      ∀ x,
        ∃ t : ℝ, S.flow t (MorseCancellation.nativeIndexThreeAttachingSphere S q hq x).val = (αq x).val)
    (k : ℤ) (hk : k = 1 ∨ k = -1) (ε : ManifoldMorse.criticalPoints E f → ℝ)
    (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }),
              MorseCancellation.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                  (Fin.cases αq (fun j => Γ j)) ∧
                (∀ j, j ≠ i → Γ j = α j) ∧
                  (MorseCancellation.middleSectionClass (Γ i) =
                      MorseCancellation.middleSectionClass (α i) +
                        k • MorseCancellation.middleSectionClass αq) ∧
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
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hfamily
  have hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => α j) := by
    refine ⟨fun j => hs j.succ, fun j => he j.succ, fun j => hi j.succ, ?_, fun j => hfull j.succ⟩
    intro j k hjk
    exact hpair (fun h => hjk (Fin.succ_inj.mp h))
  obtain ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hαβ, hother, hprotected, hmaps, hkeep⟩ :=
    S.exists_prescribed_family_slide hf hm hdim horder q hq ha
      (hal.trans (S.toSurgeryWindows.lower_lt_value q)) p i hp hhigh α hα k hk ε hε
  have hgap :
    ∀ z ∈ ManifoldMorse.criticalPoints E f, f z ∉ Set.Icc a (S.toSurgeryWindows.lower q) :=
    fun z hz h => hband z h hz
  have hpabove (j : Fin n) : S.toSurgeryWindows.lower q < f (p j) :=
    (S.toSurgeryWindows.lower_lt_value q).trans
      ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j))
  let x₀ : (Hemisphere.Sphere 2) := Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨Γ₀, hΓ₀, hδΓ⟩ :=
    T.exists_regular_band_middle_basin_family hf hal (S.data q).lower_regular ha hgap (δ i x₀) p
      hpabove (fun j => δ j) hδ
  let Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }) := fun j =>
    ⟨Γ₀ j, (hΓ₀.1 j).continuous⟩
  have hΓ : MorseCancellation.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := hΓ₀
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
      MorseCancellation.native_same_level_orbit_points hf T.smooth T.flow T.integral
        (fun z hz => T.descent z (ha z hz)) (Γ j x).property (α j x).property hshared
  · have hβα (x : (Hemisphere.Sphere 2)) : ∃ t : ℝ, S.flow t (β i x).val = (α i x).val := by
      obtain ⟨t, ht⟩ := hαβ i x
      exact ⟨-t, by rw [← ht, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]⟩
    exact
      MorseCancellation.signed_relation_of_regular_cut_transport S T hf hal ha hband (β i) (δ i)
        (MorseCancellation.nativeIndexThreeAttachingSphere S q hq) (α i) (Γ i) αq k hβα (hδΓ i) hαq
        hmaps

theorem AdaptedWindows.exists_common_cut_prescribed_family_slide {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancellation.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) (ε : ManifoldMorse.criticalPoints E f → ℝ)
    (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }),
              MorseCancellation.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                  (Fin.cases αq (fun j => Γ j)) ∧
                (∀ j, j ≠ i → Γ j = α j) ∧
                  (MorseCancellation.middleSectionClass (Γ i) =
                      MorseCancellation.middleSectionClass (α i) +
                        k • MorseCancellation.middleSectionClass αq) ∧
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
  let _ := RegularLevel.chartedSpace hf ha
  obtain ⟨βq, hβs, hβe, hβi, hrange, horbit, -⟩ :=
    S.exists_canonical_basin_sphere hf q hq ha αq (Hemisphere.point Bool.true ⟨0, by simp⟩)
      (hfamily.2.2.2.2 0)
  have hβfamily :=
    MorseCancellation.nativeMiddleBasinFamily_replace_zero S hf ha q p αq βq α hfamily hrange hβs hβe
      hβi
  obtain ⟨u, hu, hunit⟩ :=
    MorseCancellation.same_image_section_classes_unit αq βq (hfamily.2.1 0).isEmbedding hβe.isEmbedding
      hrange
  have hku : k * u = 1 ∨ k * u = -1 := by
    rcases hk with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_prescribed_slide hf hm hdim horder q hq ha hal hband p i hp hhigh βq α
      hβfamily horbit (k * u) hku ε hε
  have hrestored :=
    MorseCancellation.nativeMiddleBasinFamily_replace_zero T hf ha q p βq αq Γ hΓ hrange.symm
      (hfamily.1 0) (hfamily.2.1 0) (hfamily.2.2.1 0)
  have hcancel : (k * u) * u = k := by rcases hu with rfl | rfl <;> ring
  refine ⟨T, hcharts, hradii, hgerms, Γ, hrestored, hother, ?_, hkeep⟩
  rw [hclass, hunit, ← SemigroupAction.mul_smul, hcancel]


theorem AdaptedWindows.exists_repeatable_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancellation.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancellation.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancellation.middleSectionClass (Γ i) =
                            MorseCancellation.middleSectionClass (α i) +
                              k • MorseCancellation.middleSectionClass αq) ∧
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
    MorseCancellation.common_cut_band_of_smaller_radius S.toSurgeryWindows T.toSurgeryWindows q hal
      hband (hradii q).le
  have hseparated : ∀ j, T.toSurgeryWindows.upper q < f (p j) := fun j =>
    MorseCancellation.higher_window_separation_of_value_order S.toSurgeryWindows T.toSurgeryWindows q
      (p j) (hhigh j)
  exact
    ⟨T, hcharts, fun z => (hradii z).le, hgerms, hcut, hregular, hseparated, Γ, hΓ, hother,
      hclass, hkeep⟩

theorem AdaptedWindows.exists_iterated_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancellation.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) (m : ℕ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancellation.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancellation.middleSectionClass (Γ i) =
                            MorseCancellation.middleSectionClass (α i) +
                              ((m : ℤ) * k) • MorseCancellation.middleSectionClass αq) ∧
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
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    (q : ManifoldMorse.criticalPoints E f) (hq : MorseCancellation.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancellation.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancellation.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancellation.middleSectionClass (Γ i) =
                            MorseCancellation.middleSectionClass (α i) +
                              k • MorseCancellation.middleSectionClass αq) ∧
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


attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_labelled_integer_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f) {r n : ℕ}
    (p : Fin (n + 1) → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin (n + 1) → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec)
    (q i : Fin (n + 1)) (hqi : q ≠ i) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j))
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower (p q)) →
          y ∉ ManifoldMorse.criticalPoints E f)
    (k : ℤ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            (∀ j, a < T.toSurgeryWindows.lower (p j)) ∧
              ∃ Γ : Fin (n + 1) → C((Hemisphere.Sphere 2), { y : M // f y = a }),
                MorseCancellation.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) ∧
                  (∀ j, j ≠ i → Γ j = γ j) ∧
                    MorseCancellation.middleSectionClass (Γ i) =
                        MorseCancellation.middleSectionClass (γ i) +
                          k • MorseCancellation.middleSectionClass (γ q) ∧
                      MorseCancellation.canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n :=
                            n + 1) B Γ =
                          MorseCancellation.canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r)
                              (n := n + 1) B γ *
                            Matrix.transvection q i k ∧
                        Function.Surjective (MorseCancellation.canonicalMiddleMatrix B Γ).mulVec ∧
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
    MorseCancellation.IsNativeMiddleBasinFamily S hf ha (Fin.cases (p q) (fun j => p (e j.succ)))
      (Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x)) := by
    have hmaps :
      Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x) = (fun j x => γ j x) ∘ e := by
      funext j x
      cases j using Fin.cases with
      | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
      | succ j => rfl
    rw [hpcases, hmaps]
    exact MorseCancellation.nativeMiddleBasinFamily_reindex S hf ha p (fun j => γ j) hγ e e.injective
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
  let δ : Fin (n + 1) → C((Hemisphere.Sphere 2), { y : M // f y = a }) := Fin.cases (γ q) Δ
  let Γ := δ ∘ e
  have hΓ : MorseCancellation.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := by
    have hh :=
      MorseCancellation.nativeMiddleBasinFamily_reindex T hf ha
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
            (Hemisphere.Sphere 2) → { y : M // f y = a }) (fun x => γ q x)
            (fun j x => Δ j x) (e j) x =
          (Fin.cases (motive := fun _ : Fin (n + 1) =>
              C((Hemisphere.Sphere 2), { y : M // f y = a })) (γ q) Δ (e j))
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
    MorseCancellation.middleSectionClass (Γ i) =
      MorseCancellation.middleSectionClass (γ i) + k • MorseCancellation.middleSectionClass (γ q) := by
    change MorseCancellation.middleSectionClass (Fin.cases (γ q) Δ (e i)) = _
    rw [← hl, Fin.cases_succ]
    simpa only [hel] using hclass
  have hmatrix :=
    MorseCancellation.canonicalMiddleMatrix_single_class_addition (f := f) (a := a) B γ Γ q i k hΓother
      hΓclass
  refine ⟨T, hcharts, hradii, hgerms, ?_, Γ, hΓ, hΓother, hΓclass, hmatrix, ?_, hkeep⟩
  · intro j
    exact
      (hlower j).trans_le
        (MorseCancellation.lower_window_le_of_radius_le S.toSurgeryWindows T.toSurgeryWindows (p j)
          (hradii _))
  · rw [hmatrix]
    exact MorseCancellation.mul_transvection_surjective _ q i hqi k hsurj

attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_arbitrary_column_addition {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec) (q i : Fin n)
    (hqi : q ≠ i) (k : ℤ) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f,
            (∀ x y : ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancellation.nativeMorseIndex E g x ≤ MorseCancellation.nativeMorseIndex E g y) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f,
                  MorseCancellation.nativeMorseIndex E g z = MorseCancellation.nativeMorseIndex E f z) ∧
                (∀ d, MorseCancellation.nativeMorseCount E g d = MorseCancellation.nativeMorseCount E f d) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ z : ManifoldMorse.criticalPoints E g,
                        MorseCancellation.nativeMorseIndex E g z < 3 → g z < a) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              (∀ z ∈ ManifoldMorse.criticalPoints E f,
                                  ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                  let p' : Fin n → ManifoldMorse.criticalPoints E g :=
                                    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                  let B' := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
                                  (∀ j, MorseCancellation.nativeMorseIndex E g (p' j) = 3) ∧
                                    (∀ z : ManifoldMorse.criticalPoints E g,
                                        MorseCancellation.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        ∃ Γ :
                                          Fin n →
                                            C((Hemisphere.Sphere 2), { y : M // g y = a }),
                                          MorseCancellation.IsNativeMiddleBasinFamily T hg hga p'
                                              (fun j => Γ j) ∧
                                            (∀ j,
                                                j ≠ i →
                                                  Γ j =
                                                    MorseCancellation.equalCutSection hlevel (γ j)) ∧
                                              MorseCancellation.canonicalMiddleMatrix (M := M) (f := g)
                                                    (a := a) (r := r) (n := n) B' Γ =
                                                  MorseCancellation.canonicalMiddleMatrix (M := M) (f :=
                                                      f) (a := a) (r := r) (n := n) B γ *
                                                    Matrix.transvection q i k ∧
                                                Function.Surjective
                                                    (MorseCancellation.canonicalMiddleMatrix B'
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
    let pg : Fin (n + 1) → ManifoldMorse.criticalPoints E g := fun j =>
      ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
    let γg := fun j => MorseCancellation.equalCutSection hlevel (γ j)
    have hgcut :=
      MorseCancellation.low_index_cut_of_preserved_other_values hcrit hindices p hp houtside hcut
    have hgcomplete :
      ∀ z : ManifoldMorse.criticalPoints E g,
        MorseCancellation.nativeMorseIndex E g z = 3 → ∃ j, pg j = z := by
      intro z hz
      let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : MorseCancellation.nativeMorseIndex E f zf = 3 := (hindices z zf.property).symm.trans hz
      obtain ⟨j, hj⟩ := hcomplete zf hzf
      exact
        ⟨j, Subtype.ext (congrArg (fun z : ManifoldMorse.criticalPoints E f => z.val) hj)⟩
    have hband :=
      MorseCancellation.SurgeryWindows.regular_before_first_middle_pivot T.toSurgeryWindows hgorder
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


attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_arbitrary_column_sequence {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec)
    (ops : List (Fin n × Fin n × ℤ)) (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f,
            (∀ x y : ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancellation.nativeMorseIndex E g x ≤ MorseCancellation.nativeMorseIndex E g y) ∧
              (∀ z ∈ ManifoldMorse.criticalPoints E f,
                  MorseCancellation.nativeMorseIndex E g z = MorseCancellation.nativeMorseIndex E f z) ∧
                (∀ d, MorseCancellation.nativeMorseCount E g d = MorseCancellation.nativeMorseCount E f d) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ z : ManifoldMorse.criticalPoints E g,
                        MorseCancellation.nativeMorseIndex E g z < 3 → g z < a) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              (∀ z ∈ ManifoldMorse.criticalPoints E f,
                                  ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                  let p' : Fin n → ManifoldMorse.criticalPoints E g :=
                                    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                  let B' := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
                                  (∀ j, MorseCancellation.nativeMorseIndex E g (p' j) = 3) ∧
                                    (∀ z : ManifoldMorse.criticalPoints E g,
                                        MorseCancellation.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        ∃ Γ :
                                          Fin n →
                                            C((Hemisphere.Sphere 2), { y : M // g y = a }),
                                          MorseCancellation.IsNativeMiddleBasinFamily T hg hga p'
                                              (fun j => Γ j) ∧
                                            (∀ j,
                                                (∀ op ∈ ops, op.2.1 ≠ j) →
                                                  Γ j =
                                                    MorseCancellation.equalCutSection hlevel (γ j)) ∧
                                              MorseCancellation.canonicalMiddleMatrix (M := M) (f := g)
                                                    (a := a) (r := r) (n := n) B' Γ =
                                                  MorseCancellation.canonicalMiddleMatrix (M := M) (f :=
                                                      f) (a := a) (r := r) (n := n) B γ *
                                                    (ops.map
                                                        (fun op =>
                                                          Matrix.transvection op.1 op.2.1
                                                            op.2.2)).prod ∧
                                                Function.Surjective
                                                    (MorseCancellation.canonicalMiddleMatrix B'
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
      B.trans (MorseCancellation.equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl)) = B := by
      rw [MorseCancellation.equalCutHomologyEquiv_refl, LinearEquiv.trans_refl]
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
    let pg : Fin n → ManifoldMorse.criticalPoints E g := fun j =>
      ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
    obtain
      ⟨u, hu, hmu, hcu, huorder, huindices, hucounts, huoutside, hucut, husub, hulevel, hua, U,
        hugerms, hufgerms, hpu, hucomplete, hulower, Δ, hΔ, huother, humatrix, husurj, hukeep⟩ :=
      T.exists_arbitrary_column_addition hg hmg hdim hgorder hga hgcut pg hpg hgcomplete hglower
        Bg Γ hΓ hgsurj op.1 op.2.1 hop op.2.2
    let hsub' : ∀ y, u y ≤ a ↔ f y ≤ a := fun y => (husub y).trans (hsub y)
    let hlevel' : ∀ y, u y = a ↔ f y = a := fun y => (hulevel y).trans (hlevel y)
    have hB :
      Bg.trans (MorseCancellation.equalCutHomologyEquiv husub) =
        B.trans (MorseCancellation.equalCutHomologyEquiv hsub') := by
      change
        (B.trans (MorseCancellation.equalCutHomologyEquiv hsub)).trans
            (MorseCancellation.equalCutHomologyEquiv husub) =
          _
      rw [LinearEquiv.trans_assoc, MorseCancellation.equalCutHomologyEquiv_trans]
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
      exact MorseCancellation.equalCutSection_trans hlevel hulevel (γ j)
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

theorem AdaptedWindows.exists_primitive_functional_unit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancellation.nativeMorseIndex E f x ≤ MorseCancellation.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec)
    (L : SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ g : M → ℝ,
          ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
            ManifoldMorse.IsMorse E g ∧
              ∃ hcrit :
                ManifoldMorse.criticalPoints E g = ManifoldMorse.criticalPoints E f,
                (∀ x y : ManifoldMorse.criticalPoints E g,
                    g x < g y →
                      MorseCancellation.nativeMorseIndex E g x ≤ MorseCancellation.nativeMorseIndex E g y) ∧
                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                      MorseCancellation.nativeMorseIndex E g z = MorseCancellation.nativeMorseIndex E f z) ∧
                    (∀ d,
                        MorseCancellation.nativeMorseCount E g d = MorseCancellation.nativeMorseCount E f d) ∧
                      (∀ z ∈ ManifoldMorse.criticalPoints E f,
                          (∀ j, z ≠ (p j).val) → g z = f z) ∧
                        (∀ z : ManifoldMorse.criticalPoints E g,
                            MorseCancellation.nativeMorseIndex E g z < 3 → g z < a) ∧
                          ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                            ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                              ∃ hga : ∀ y, g y = a → y ∉ ManifoldMorse.criticalPoints E g,
                                ∃ T : AdaptedWindows E g,
                                  (∀ z ∈ ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                    (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                      let p' : Fin n → ManifoldMorse.criticalPoints E g :=
                                        fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                      let B' := B.trans (MorseCancellation.equalCutHomologyEquiv hsub)
                                      (∀ j, MorseCancellation.nativeMorseIndex E g (p' j) = 3) ∧
                                        (∀ z : ManifoldMorse.criticalPoints E g,
                                            MorseCancellation.nativeMorseIndex E g z = 3 →
                                              ∃ j, p' j = z) ∧
                                          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                            ∃ Γ :
                                              Fin n →
                                                C((Hemisphere.Sphere 2),
                                                  { y : M // g y = a }),
                                              MorseCancellation.IsNativeMiddleBasinFamily T hg hga p'
                                                  (fun j => Γ j) ∧
                                                (∀ j,
                                                    (∀ op ∈ ops, op.2.1 ≠ j) →
                                                      Γ j =
                                                        MorseCancellation.equalCutSection hlevel
                                                          (γ j)) ∧
                                                  MorseCancellation.canonicalMiddleMatrix (M := M) (f :=
                                                        g) (a := a) (r := r) (n := n) B' Γ =
                                                      MorseCancellation.canonicalMiddleMatrix (M := M)
                                                          (f := f) (a := a) (r := r) (n := n) B
                                                          γ *
                                                        (ops.map
                                                            (fun op =>
                                                              Matrix.transvection op.1 op.2.1
                                                                op.2.2)).prod ∧
                                                    Function.Surjective
                                                        (MorseCancellation.canonicalMiddleMatrix B'
                                                            Γ).mulVec ∧
                                                      (∃ i : Fin n,
                                                          L
                                                                ((MorseCancellation.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancellation.middleSectionClass
                                                                    (Γ i))) =
                                                              1 ∨
                                                            L
                                                                ((MorseCancellation.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancellation.middleSectionClass
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
  let A : Matrix (Fin 1) (Fin n) ℤ := fun _ j => L (MorseCancellation.middleSectionClass (γ j))
  have hsurj' :
    Function.Surjective
      (MorseCancellation.classCoordinateMatrix B
          (fun j => MorseCancellation.middleSectionClass (γ j))).mulVec := by
    simpa only [MorseCancellation.canonicalMiddleMatrix] using hsurj
  have hA : Function.Surjective A.mulVec :=
    MorseCancellation.functional_class_row_surjective B (fun j => MorseCancellation.middleSectionClass (γ j))
      hsurj' L hL
  obtain ⟨ops, hvalid, i, hi⟩ := MorseCancellation.primitive_row_has_unit_after_column_additions A hA
  obtain
    ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, T, hgerms,
      hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
    S.exists_arbitrary_column_sequence hf hm hdim horder ha hcut p hp hcomplete hlower B γ hγ
      hsurj ops hvalid
  have hcoord :
    MorseCancellation.classCoordinateMatrix (B.trans (MorseCancellation.equalCutHomologyEquiv hsub))
        (fun j => MorseCancellation.middleSectionClass (Γ j)) =
      MorseCancellation.classCoordinateMatrix B (fun j => MorseCancellation.middleSectionClass (γ j)) *
        (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod := by
    simpa only [MorseCancellation.canonicalMiddleMatrix] using hmatrix
  have hrows :=
    MorseCancellation.functional_rows_of_matrix_product B (MorseCancellation.equalCutHomologyEquiv hsub)
      (fun j => MorseCancellation.middleSectionClass (γ j))
      (fun j => MorseCancellation.middleSectionClass (Γ j)) _ hcoord L
  have hentry := congrFun (congrFun hrows 0) i
  refine
    ⟨ops, hvalid, g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel,
      hga, T, hgerms, hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, ⟨i, ?_⟩,
      hkeep⟩
  exact hi.elim (fun h => Or.inl (hentry.trans h)) (fun h => Or.inr (hentry.trans h))


attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem AdaptedWindows.exists_lower_cut_geometric_matrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hba : b < a)
    (ha : ∀ y, f y = a → y ∉ ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ ManifoldMorse.criticalPoints E f)
    (hband : ∀ y, f y ∈ Set.Icc b a → y ∉ ManifoldMorse.criticalPoints E f)
    (za : { y : M // f y = a }) {r n : ℕ} (p : Fin n → ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancellation.canonicalMiddleMatrix B γ).mulVec) :
    ∃ β : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = b }),
      MorseCancellation.IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (γ j x).val = (β j x).val) ∧
          (∀ j,
              MorseCancellation.regularCutHomologyEquiv hf hba.le hband
                  (MorseCancellation.middleSectionClass (β j)) =
                MorseCancellation.middleSectionClass (γ j)) ∧
            let B' := B.trans (MorseCancellation.regularCutHomologyEquiv hf hba.le hband).symm
            MorseCancellation.canonicalMiddleMatrix B' β = MorseCancellation.canonicalMiddleMatrix B γ ∧
              Function.Surjective (MorseCancellation.canonicalMiddleMatrix B' β).mulVec := by
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨β₀, hβ, horbit⟩ :=
    S.exists_regular_band_middle_basin_family hf hba ha hb (fun y hy h => hband y h hy) za p hp
      (fun j => γ j) hγ
  let β : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = b }) := fun j =>
    ⟨β₀ j, (hβ.1 j).continuous⟩
  have hclass (j : Fin n) :
    MorseCancellation.regularCutHomologyEquiv hf hba.le hband (MorseCancellation.middleSectionClass (β j)) =
      MorseCancellation.middleSectionClass (γ j) :=
    S.section_class_of_flow_transport hf hba hb (γ j) (β j) (horbit j)
  let B' := B.trans (MorseCancellation.regularCutHomologyEquiv hf hba.le hband).symm
  have hmatrix : MorseCancellation.canonicalMiddleMatrix B' β = MorseCancellation.canonicalMiddleMatrix B γ :=
    by
    funext i j
    simp only [MorseCancellation.canonicalMiddleMatrix, MorseCancellation.classCoordinateMatrix]
    change
      B.symm
          (MorseCancellation.regularCutHomologyEquiv hf hba.le hband
            (MorseCancellation.middleSectionClass (β j)))
          i =
        B.symm (MorseCancellation.middleSectionClass (γ j)) i
    rw [hclass j]
  refine ⟨β, hβ, horbit, hclass, hmatrix, ?_⟩
  rw [hmatrix]
  exact hsurj

theorem SpherePoint.sourceCountMark_topClass_natAbs (n : ℕ) {N : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    (sourceCountMark n j B (SphereHomology.unitSphereTopClass (n + 1))).natAbs = 1 :=
  HomologyTransport.integerEquiv_one_natAbs
    ((SphereHomology.unitSphereHomologyTopEquiv (n + 1)).symm.trans (sourceCountMark n j B))

theorem OnePointCover.overlapHomologyEquiv_symm_include {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PuncturedRadial.Space N) k) :
    (overlapHomologyEquiv r hr k).symm
        (SingularMayerVietoris.singularHomologyMap overlapHomeomorph.toHomotopyEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap PuncturedRadial.toSphere k a := by
  change
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k).symm _ = _
  rw [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply]
  have heq :
    (overlapSphereEquiv (N := N) r hr).symm.toFun.comp overlapHomeomorph.toHomotopyEquiv.toFun =
      PuncturedRadial.toSphere := by
    apply ContinuousMap.ext
    intro x
    change PuncturedRadial.toSphere (overlapHomeomorph.symm (overlapHomeomorph x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, heq]

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.collapseComponentConnecting {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Hemisphere.Sphere m) (k + 1) →ₗ[ℤ]
      (∀ i : d.beltIntersectionPoints m g,
        SingularMayerVietoris.SingularHomology
          (↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i)) k) :=
  CoverLocalContributions.componentConnecting (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    k

attribute [local instance 100] Classical.propDecidable in
def ManifoldMorse.MorseSurgeryData.collapseLocalClass {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) k :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm
    (d.collapseComponentConnecting m g D k a i)

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_overlaps {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Hemisphere.Sphere m) (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism OnePointCover.oldPatch
        OnePointCover.finitePatch OnePointCover.oldPatch_open
        OnePointCover.finitePatch_open OnePointCover.cover k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (d.collapseOverlapMap hf m g D i) k
          (d.collapseComponentConnecting m g D k a i) :=
  CoverLocalContributions.connecting_sum (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    OnePointCover.oldPatch OnePointCover.finitePatch (d.attachingCollapse hf m g)
    (d.attachingCollapse_maps_old hf m g) (d.attachingCollapse_maps_neighborhood hf m g D)
    OnePointCover.oldPatch_open OnePointCover.finitePatch_open
    OnePointCover.cover k a

attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_boundaries {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Hemisphere.Sphere m) (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism OnePointCover.oldPatch
        OnePointCover.finitePatch OnePointCover.oldPatch_open
        OnePointCover.finitePatch_open OnePointCover.cover k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap
          (OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
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
theorem ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_sum {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Hemisphere.Sphere m) (k + 1)) :
    OnePointCover.sphereConnecting r hr k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (D.data i).innerBoundary.normalizedMap k
          (d.collapseLocalClass m g D k a i) := by
  change
    (OnePointCover.overlapHomologyEquiv (N := d.chart.NegativeCoordinates) r hr k).symm
        (SingularMayerVietoris.connectingHomomorphism OnePointCover.oldPatch
          OnePointCover.finitePatch OnePointCover.oldPatch_open
          OnePointCover.finitePatch_open OnePointCover.cover k
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a)) =
      _
  rw [d.collapseConnecting_sum_boundaries hf m g D k a, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    OnePointCover.overlapHomologyEquiv_symm_include]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl


theorem LocalDegree.SeparatedNeighborhoods.pointComplementInclusion_sphereEquiv
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M}
    {f : M → F} {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun =
      (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun := by
  apply ContinuousMap.ext
  intro u
  rfl

theorem LocalDegree.SeparatedNeighborhoods.sphereConnecting_component {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
        (CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      LocalDegree.NativeNeighborhood.sphereConnecting (x : M) (D.data x) k a := by
  let c :=
    CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
      D.open_cover k a x
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).injective
  change
    SingularMayerVietoris.singularHomologyMap
        (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k)
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
              (LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).symm
          _)
  rw [LinearEquiv.apply_symm_apply, ← D.pointComplementInclusion_sphereEquiv x]
  change
    SingularMayerVietoris.singularHomologyMap
        ((D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun) k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a
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
theorem ManifoldMorse.MorseSurgeryData.collapseLocalClass_singlePoint {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    d.collapseLocalClass m g D k a i =
      LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) k a :=
  D.sphereConnecting_component k a i

theorem SphereNormalCoordinates.localBoundary_homology_outward {V F : Type}
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
    (b : LocalDegree.BoundaryData (f ∘ c) L s) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1)
        ((SignType.sign (chartJacobian c j B 0) : ℤ) • a) =
      (SignType.sign (normalJacobian j (c 0) (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))) : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
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
theorem ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_homology_sign_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : Hemisphere.Sphere (n + 2) → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere (n + 2)),
      x ∈ d.beltIntersectionPoints (n + 2) g →
        ∀ (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates),
          L.toContinuousLinearMap =
              fderiv ℝ ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) 0 →
            ∀ {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
              (b :
                LocalDegree.BoundaryData
                  ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) L s)
              (k : ℕ)
              (a :
                SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1))
                  (k + 1)),
              SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1)
                  ((SignType.sign
                        (SphereNormalCoordinates.chartJacobian
                          (NativeParametrization.centered x) j B 0) :
                      ℤ) •
                    a) =
                (d.beltIntersectionSign (n + 2) j g x : ℤ) •
                  SingularMayerVietoris.singularHomologyMap
                    (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
                    (k + 1) a := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx L hL s b k a
  have hs := d.contMDiffAt_collapseNormal_comp hf (n + 2) g hg x hx
  have hA := d.isInvertible_collapseNormal_comp_of_transverse hf q (n + 2) hdim g hg ht x hx
  have hc0 := NativeParametrization.centered_zero (D := EuclideanSpace ℝ (Fin (n + 2))) x
  have h :=
    SphereNormalCoordinates.localBoundary_homology_outward n
      (NativeParametrization.centered x) j B
      (NativeParametrization.zero_mem_centered_source x) (d.collapseNormal ∘ g)
      (hc0.symm ▸ hs.mdifferentiableAt (by simp)) (hc0.symm ▸ hA) L hL b k a
  rw [hc0, d.collapseNormal_comp_sign_of_transverse hf q (n + 2) hdim j g hg ht x hx] at h
  exact h


attribute [local instance] ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseLocalClass_eq_outward {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (n : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Fintype (d.beltIntersectionPoints (n + 2) g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2))
    (i : d.beltIntersectionPoints (n + 2) g) :
    d.collapseLocalClass (n + 2) g D (k + 1) a i =
      (SignType.sign
            (SphereNormalCoordinates.chartJacobian
              (NativeParametrization.centered i.val) j B 0) :
          ℤ) •
        SpherePoint.outwardClass n j B k a := by
  rw [d.collapseLocalClass_singlePoint]
  exact SpherePoint.pointConnecting_eq_outward n j B i.val (D.data i) k a

attribute [local instance] ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_outward {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Fintype (d.beltIntersectionPoints (n + 2) g)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2))
      (i : d.beltIntersectionPoints (n + 2) g),
      SingularMayerVietoris.singularHomologyMap (D.data i).innerBoundary.normalizedMap (k + 1)
          (d.collapseLocalClass (n + 2) g D (k + 1) a i) =
        (d.beltIntersectionSign (n + 2) j g i.val : ℤ) •
          SingularMayerVietoris.singularHomologyMap
            (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (SpherePoint.outwardClass n j B k a) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht k a i
  rw [d.collapseLocalClass_eq_outward n j B g D k a i]
  exact
    d.collapseLocalBoundary_homology_sign_of_transverse hf q n hdim j B g hg ht i.val i.property
      (D.linear i) (D.derivative_eq i) (D.data i).innerBoundary k _

attribute [local instance] ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
theorem ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Finite (d.beltIntersectionPoints (n + 2) g)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)),
      OnePointCover.sphereConnecting r hr (k + 1)
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g)
            (k + 2) a) =
        d.beltIntersectionCount (n + 2) j g (Set.toFinite _) •
          SingularMayerVietoris.singularHomologyMap
            (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (SpherePoint.outwardClass n j B k a) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) := Fintype.ofFinite _
  intro hg ht r hr k a
  apply (d.collapseSphereConnecting_sum hf.continuous (n + 2) g D r hr (k + 1) a).trans
  apply
    Eq.trans
      (Finset.sum_congr rfl
        (fun i _ => d.collapseLocalBoundary_outward hf q n hdim j B g D hg ht k a i))
  exact d.beltIntersectionCount_smul (n + 2) j g (Set.toFinite _) _

theorem ManifoldMorse.MorseSurgeryData.collapse_homology_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)),
      OnePointCover.sphereConnecting r hr (k + 1)
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g)
            (k + 2) a) =
        d.beltIntersectionCount (n + 2) j g
            (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht) •
          SingularMayerVietoris.singularHomologyMap
            (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (SpherePoint.outwardClass n j B k a) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht r hr k a
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) :=
    (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht).fintype
  obtain ⟨D⟩ := d.nonempty_collapseNeighborhoods hf q (n + 2) hdim g hg hinj ht
  exact d.collapseSphereConnecting_signed_count hf q n hdim j B g D hg ht r hr k a

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere 2) 2),
      d.indexTwoCollapseCoordinate hf.continuous hindex
          (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2 a) =
        d.beltIntersectionCount 2 j g
            (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht) *
          SpherePoint.sourceCountMark 0 j (d.indexTwoNormalModel hindex) a := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht a
  have h :=
    SpherePoint.countMark_of_connecting 0 j (d.indexTwoNormalModel hindex) _ a _
      (d.collapse_homology_signed_count hf q 0 hindex j (d.indexTwoNormalModel hindex) g hg hinj
        ht 1 zero_lt_one 0 a)
  have hc :
    d.attachingCollapse hf.continuous 2 g =
      (d.upperCollapseMap hf.continuous).comp (d.upperLevelInclusion.comp g) :=
    rfl
  rw [hc, PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact h

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_topClass_natAbs {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
            (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2
              (SphereHomology.unitSphereTopClass 1))).natAbs =
        (d.beltIntersectionCount 2 j g
            (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht)).natAbs := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  rw [d.indexTwoCoordinate_signed_count hf q hindex j g hg hinj ht, Int.natAbs_mul,
    SpherePoint.sourceCountMark_topClass_natAbs, mul_one]

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_transverse_natAbs {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, d.UpperLevel))
    (hgood : d.IsTransverseBeltSphere hf hdim hindex g) :
    (d.indexTwoCollapseCoordinate hf.continuous hindex
          (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2
            (SphereHomology.unitSphereTopClass 1))).natAbs =
      (d.beltIntersectionCount 2 j g
          (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, _, ht⟩ := hgood
  exact d.indexTwoCoordinate_topClass_natAbs hf 3 hindex j g hg hinj ht

theorem MorseCancellation.last_index_two_collapse_is_primitive {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hrpos : 0 < r) (hrc : r + n < S.toSurgeryWindows.count) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2,
      Function.Surjective ((S.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
        ∀ γ : C(Hemisphere.Sphere 1, (S.data q).LowerLevel),
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

attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem MorseCancellation.exists_native_belt_cut_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
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
      (γ : Fin n → C((Hemisphere.Sphere 2), { y : M // f y = a })),
      IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) →
        Function.Surjective (canonicalMiddleMatrix B γ).mulVec →
          ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2,
            Function.Surjective ((T.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
              (∀ δ : C(Hemisphere.Sphere 1, (T.data q).LowerLevel),
                  ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
                (∀ z : ManifoldMorse.criticalPoints E f,
                    nativeMorseIndex E f z < 3 → f z < T.toSurgeryWindows.upper q) ∧
                  (∀ z : ManifoldMorse.criticalPoints E f,
                      nativeMorseIndex E f z = 3 → ∃ j, p j = z) ∧
                    (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
                      ∃ β : Fin n → C((Hemisphere.Sphere 2), (T.data q).UpperLevel),
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
      f y ∈ Set.Icc (T.toSurgeryWindows.upper q) a → y ∉ ManifoldMorse.criticalPoints E f :=
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
  let za := γ ⟨0, hnpos⟩ (Hemisphere.point Bool.true ⟨0, by simp⟩)
  obtain ⟨β, hβ, horbit, -, hmatrix, hsurj'⟩ :=
    T.exists_lower_cut_geometric_matrix hf hba (S.data q).upper_regular (T.data q).upper_regular
      hband za p (fun j => (hlower j).trans (T.toSurgeryWindows.lower_lt_value (p j))) B γ hγ
      hsurj
  exact
    ⟨hindex, hprimitive, hnull, hcut, hcomplete, fun j => hba.trans (hlower j), β, hβ, horbit,
      B.trans (regularCutHomologyEquiv hf hba.le hband).symm, hmatrix, hsurj'⟩


theorem MorseCancellation.exists_single_intersection_of_unit_coordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Hemisphere.Sphere 1, d.LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (γ : C((Hemisphere.Sphere 2), d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ x)),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
              (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ)).natAbs =
          1 →
        ∃ D :
          Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
            d.UpperLevel d.UpperLevel ∞,
          ∃ δ : C((Hemisphere.Sphere 2), d.UpperLevel),
            SupportedDiffeomorph.IsotopicToIdentity D ∧
              (∀ x, δ x = D (γ x)) ∧
                d.IsTransverseBeltSphere hf hdim hindex δ ∧
                  (Set.range δ ∩ Set.range d.surgery.beltSphere).ncard = 1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
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


theorem MorseCancellation.cancel_from_preserved_unit_belt_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : ManifoldMorse.IsMorse E g)
    (hdim : Module.finrank ℝ E = 6) (p : ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hpcg : p.val ∈ ManifoldMorse.criticalPoints E g) (hpg : nativeMorseIndex E g p = 2)
    (q : ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hconsecutive : ∀ z : ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q))
    (hpc : g p < (f p + (S.data p).radius ^ 2)) (hcq : (f p + (S.data p).radius ^ 2) < g q)
    (hsub : ∀ y, g y ≤ (f p + (S.data p).radius ^ 2) ↔ f y ≤ (f p + (S.data p).radius ^ 2))
    (hlevel : ∀ y, g y = (f p + (S.data p).radius ^ 2) ↔ f y = (f p + (S.data p).radius ^ 2))
    (hga : ∀ y, g y = (f p + (S.data p).radius ^ 2) → y ∉ ManifoldMorse.criticalPoints E g)
    (hforward :
      ∀ y : (S.data p).UpperLevel,
        Filter.Tendsto (fun t => T.flow t y.val) Filter.atTop (𝓝 p.val) ↔
          Filter.Tendsto (fun t => S.flow t y.val) Filter.atTop (𝓝 p.val))
    (γ : C((Hemisphere.Sphere 2), { y : M // g y = (f p + (S.data p).radius ^ 2) })) :
    letI := RegularLevel.chartedSpace hg hga
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) γ x)),
      (∀ y, y ∈ Set.range γ ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot (𝓝 q.val)) →
        ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex
                ((equalCutHomologyEquiv hsub).symm (middleSectionClass γ))).natAbs =
            1 →
          ∃ v : M → ℝ,
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
              ManifoldMorse.IsMorse E v ∧
                (ManifoldMorse.criticalPoints E v).ncard + 2 =
                    (ManifoldMorse.criticalPoints E g).ncard ∧
                  (∀ z,
                      z ∈ ManifoldMorse.criticalPoints E v ↔
                        z ∈ ManifoldMorse.criticalPoints E g ∧ z ≠ p.val ∧ z ≠ q.val) ∧
                    ∀ z,
                      g z ∉
                          Set.Ioo (T.toSurgeryWindows.lower ⟨p.val, hpcg⟩)
                            (T.toSurgeryWindows.upper q) →
                        v =ᶠ[𝓝 z] g := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hg hga
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := (S.data p).chart.finrank_negative_add_positive; omega⟩
  intro hγ hinj himm hback hunit
  let e := equalLevelDiffeomorph hf hg (S.data p).upper_regular hga hlevel
  let α : C((Hemisphere.Sphere 2), (S.data p).UpperLevel) :=
    equalCutSection (fun y => (hlevel y).symm) γ
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (e.symm ∘ γ)
    exact e.symm.contMDiff.comp hγ
  have hαinj : Function.Injective α := e.symm.injective.comp hinj
  have hαimm (x : (Hemisphere.Sphere 2)) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) α x) := by
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (e.symm ∘ γ) x)
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
  have hβ₀ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β₀ := (S.data p).belt_smooth hf 3
  have hβ : ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ β := e.contMDiff.comp hβ₀
  let D' := e.symm.trans (D.trans e)
  have hD' : SupportedDiffeomorph.IsotopicToIdentity D' := conjugate_level_isotopy e D hD
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
      NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (D' ∘ γ) β x y :=
    by
    rw [hDγ]
    intro x y hxy
    have hold : β₀ y = δ x := e.injective hxy
    have hh :=
      (TransverseGerms.native_transversality_partial_diffeomorph_iff e.toPartialDiffeomorph
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


attribute [local irreducible] MorseCancellation.canonicalMiddleMatrix in
theorem MorseCancellation.cancel_from_complete_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p : ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive :
      Function.Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex))
    (hcut :
      ∀ z : ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < f p + (S.data p).radius ^ 2)
    {r n : ℕ} (labels : Fin n → ManifoldMorse.criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 3)
    (hcomplete :
      ∀ z : ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, labels j = z)
    (hlower : ∀ j, f p + (S.data p).radius ^ 2 < S.toSurgeryWindows.lower (labels j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + (S.data p).radius ^ 2 } 2)
    (γ : Fin n → C((Hemisphere.Sphere 2), (S.data p).UpperLevel))
    (hγ : IsNativeMiddleBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Function.Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
        ManifoldMorse.IsMorse E v ∧
          Set.InjOn v (ManifoldMorse.criticalPoints E v) ∧
            (ManifoldMorse.criticalPoints E v).ncard + 2 =
              (ManifoldMorse.criticalPoints E f).ncard := by
  let c := f p + (S.data p).radius ^ 2
  let L := (S.data p).indexTwoCollapseCoordinate hf.continuous hindex
  have hpold : nativeMorseIndex E f p = 2 :=
    (nativeMorseIndex_eq_chart (S.data p).chart).trans hindex
  obtain
    ⟨ops, -, g, hg, hmg, hcrit, hgorder, hindices, -, houtside, hgcut, hsub, hlevel, hga, T, -, -,
      hpg, hgcomplete, hglower, Γ, hΓ, -, -, hgsurj, ⟨i, hi⟩, hkeep⟩ :=
    S.exists_primitive_functional_unit hf hm hdim horder (S.data p).upper_regular hcut labels
      hlabels hcomplete hlower B γ hγ hsurj L hprimitive
  let pg : Fin n → ManifoldMorse.criticalPoints E g := fun j =>
    ⟨(labels j).val, hcrit.symm ▸ (labels j).property⟩
  let Bg := B.trans (equalCutHomologyEquiv hsub)
  obtain
    ⟨u, hu, hmu, hcu, huorder, huindices, -, huoutside, hfirst, husub, hulevel, hua, U, -, huflow,
      -, hpu, hulower, hfamily, -, -, -⟩ :=
    T.exists_first_middle_pivot hg hmg hga hgorder pg hpg hgcomplete hglower Bg Γ hΓ hgsurj i
  let hcrit' := hcu.trans hcrit
  let hsub' : ∀ y, u y ≤ c ↔ f y ≤ c := fun y => (husub y).trans (hsub y)
  let hlevel' : ∀ y, u y = c ↔ f y = c := fun y => (hulevel y).trans (hlevel y)
  let q : ManifoldMorse.criticalPoints E u :=
    ⟨(labels i).val, hcrit'.symm ▸ (labels i).property⟩
  let Δ := fun j => equalCutSection hulevel (Γ j)
  have hids (z : M) (hz : z ∈ ManifoldMorse.criticalPoints E f) :
    nativeMorseIndex E u z = nativeMorseIndex E f z :=
    (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)
  have hfixed (z : M) (hz : z ∈ ManifoldMorse.criticalPoints E f)
    (hidx : nativeMorseIndex E f z ≠ 3) : u z = f z := by
    have hnotlabel (j : Fin n) : z ≠ (labels j).val := by
      intro heq
      apply hidx
      rw [heq]
      exact hlabels j
    exact (huoutside z (hcrit.symm ▸ hz) hnotlabel).trans (houtside z hz hnotlabel)
  have hpcrit : p.val ∈ ManifoldMorse.criticalPoints E u := hcrit'.symm ▸ p.property
  have hpnew : nativeMorseIndex E u p = 2 := (hids p p.property).trans hpold
  have hq : nativeMorseIndex E u q = 3 := (hids (labels i) (labels i).property).trans (hlabels i)
  have hfirstcrit (z : ManifoldMorse.criticalPoints E u) (hz : nativeMorseIndex E u z = 3)
    (hne : z ≠ q) : u q < u z := by
    let zf : ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit' ▸ z.property⟩
    have hzidx : nativeMorseIndex E f zf = 3 := (hids z zf.property).symm.trans hz
    obtain ⟨j, hj⟩ := hcomplete zf hzidx
    have hji : j ≠ i := by
      intro hji
      apply hne
      apply Subtype.ext
      exact
        (congrArg (fun z : ManifoldMorse.criticalPoints E f => z.val) hj).symm.trans
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
  let _ := RegularLevel.chartedSpace hu hua
  obtain ⟨v, hv, hmv, hcard, hcv, hext⟩ :=
    cancel_from_preserved_unit_belt_cut S U hf hu hmu hdim p hindex hnull hpcrit hpnew q hq
      hconsecutive hpc hcq hsub' hlevel' hua hforward (Δ i) (hfamily.1 i)
      (hfamily.2.1 i).injective (hfamily.2.2.1 i) (hfamily.2.2.2.2 i) hunit
  obtain ⟨-, hinj, -⟩ :=
    adapted_surgeries_after_pair_removal U.toSurgeryWindows ⟨p.val, hpcrit⟩ q hconsecutive hv hmv
      hcv hext
  refine ⟨v, hv, hmv, hinj, ?_⟩
  rwa [hcrit'] at hcard


theorem ManifoldMorse.MorseSurgeryData.coreBoundary_two_injective_of_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
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

theorem ManifoldMorse.MorseSurgeryData.indexThreeAttaching_zsmul_eq_zero {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
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

theorem ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    {r c : ℕ}
    (P :
      IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c)
    (hP : Function.Injective P.matrix.mulVec) :
    Function.Injective (d.indexThreePresentation hf hindex P).matrix.mulVec :=
  P.adjoin_matrix_injective _ _ _ _ hP (d.indexThreeAttaching_zsmul_eq_zero hf hindex)

theorem ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
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
    exact IntegerPresentation.ofEquiv_matrix_injective (S.indexTwoBasis hf r hc htwo)
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


