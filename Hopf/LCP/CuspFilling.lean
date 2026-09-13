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
Original source lines 115135--133801; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.Hurewicz
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
import Lib.Geometry.Manifold.Morse.ConnectionCancellation
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
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.AlgebraicTopology.SingularHomology.Coproduct
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.AlgebraicTopology.SingularHomology.CrossInsert
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
import Lib.LinearAlgebra.SquareZero
import Lib.Topology.MappingTorus.Basic
import Lib.Topology.Homotopy.SublevelRetraction
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.AlgebraicTopology.SingularHomology.Torus
import Lib.Topology.Homotopy.LocalCollapse
import Lib.Topology.Covering.InvariantSubset
import Lib.AlgebraicTopology.SingularHomology.CircleProduct
import Lib.Topology.Covering.Quotient
import Lib.AlgebraicTopology.SingularHomology.CrossProduct

set_option maxSynthPendingDepth 3

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973


theorem FirstHurewicz.basedLoopClass_triangleFacePath {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath σ i) =
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r (simplexPath (σ.comp (simplexFace 1 i))) _ _

theorem FirstHurewicz.edgeLoopCochain_boundaryTwo_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) :
    edgeLoopCochain r (boundaryTwo X (simplexChain X 2 σ)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeLoopCochain_simplex]
  change
    basedLoopClass r (simplexPath (σ.comp (simplexFace 1 0))) -
          basedLoopClass r (simplexPath (σ.comp (simplexFace 1 1))) +
        basedLoopClass r (simplexPath (σ.comp (simplexFace 1 2))) =
      0
  have he :=
    congrArg₂ (fun a c : AbelianPi1 X b => a + c)
      (congrArg₂ (fun a c : AbelianPi1 X b => a - c) (basedLoopClass_triangleFacePath r σ 0)
        (basedLoopClass_triangleFacePath r σ 1))
      (basedLoopClass_triangleFacePath r σ 2)
  exact
    he.symm.trans
      (basedLoopClass_triangle_boundary r (triangleEdge01 σ) (triangleEdge12 σ) (triangleEdge02 σ)
        (triangleEdges_homotopic σ))

theorem FirstHurewicz.edgeLoopCochain_comp_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainMap_ext X 2
  intro σ
  exact edgeLoopCochain_boundaryTwo_simplex r σ

theorem FirstHurewicz.edgeLoopCochain_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Chains X 2) : edgeLoopCochain r (boundaryTwo X c) = 0 :=
  LinearMap.congr_fun (edgeLoopCochain_comp_boundaryTwo r) c

def FirstHurewicz.inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : SingularH1 X →ₗ[ℤ] AbelianPi1 X b :=
  homologyDescOfChain X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r)

@[simp]
theorem FirstHurewicz.inverseHurewiczMap_cycleClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    inverseHurewiczMap r (cycleClass X c) = edgeLoopCochain r c.1 :=
  homologyDescOfChain_cycleClass X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r) c

@[simp]
theorem FirstHurewicz.inverseHurewiczMap_loopHomologyClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    inverseHurewiczMap r (loopHomologyClass p) = loopClass p := by
  rw [loopHomologyClass, inverseHurewiczMap_cycleClass, loopCycle_val]
  exact edgeLoopCochain_loopSimplex r p

theorem FirstHurewicz.inverseHurewiczMap_hurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : AbelianPi1 X b) : inverseHurewiczMap r (hurewiczMap b a) = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczMap_loopClass, inverseHurewiczMap_loopHomologyClass]

theorem FirstHurewicz.hurewiczMap_inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : SingularH1 X) : hurewiczMap b (inverseHurewiczMap r a) = a := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X a
  apply homologyToChainClass_injective X
  rw [inverseHurewiczMap_cycleClass, homologyToChainClass_cycleClass]
  exact edgeClosure_cycle r c

def FirstHurewicz.firstHurewiczEquivOfPaths {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X
    where
  toLinearMap := hurewiczMap b
  invFun := inverseHurewiczMap r
  left_inv := inverseHurewiczMap_hurewiczMap r
  right_inv := hurewiczMap_inverseHurewiczMap r

def FirstHurewicz.firstHurewiczEquiv {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X :=
  firstHurewiczEquivOfPaths (PathConnectedSpace.somePath b)

@[simp]
theorem FirstHurewicz.firstHurewiczEquiv_loopClass {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] (p : Path b b) :
    firstHurewiczEquiv b (loopClass p) = loopHomologyClass p :=
  hurewiczMap_loopClass b p

theorem FirstHurewicz.loopHomologyClass_surjective {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : Function.Surjective (loopHomologyClass (x := b)) := by
  intro a
  obtain ⟨c, hc⟩ := (firstHurewiczEquiv b).surjective a
  obtain ⟨p, hp⟩ := loopClass_surjective c
  refine ⟨p, ?_⟩
  rw [← firstHurewiczEquiv_loopClass, hp, hc]

def FirstHurewicz.singularH1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) : SingularH1 X ≃ₗ[ℤ] A :=
  (firstHurewiczEquiv b).symm.trans (abelianPi1EquivOfPi1 b e)

@[simp]
theorem FirstHurewicz.singularH1EquivOfPi1_hurewiczFunction {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (g : FundamentalGroup X b) :
    singularH1EquivOfPi1 b e (hurewiczFunction b g) = (e g).toAdd := by
  change
    abelianPi1EquivOfPi1 b e
        ((firstHurewiczEquiv b).symm
          (firstHurewiczEquiv b (Additive.ofMul (Abelianization.of g)))) =
      _
  rw [LinearEquiv.symm_apply_apply, abelianPi1EquivOfPi1_of]

@[simp]
theorem FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (p : Path b b) :
    singularH1EquivOfPi1 b e (loopHomologyClass p) = (e (loopQuotient p)).toAdd :=
  singularH1EquivOfPi1_hurewiczFunction b e (loopQuotient p)


def PeriodTorusHigherHomology.coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ ProductTorus n
    where
  toFun x i := (x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; exact AddCircle.coe_add (1 : ℝ) (x i) (y i)

@[simp]
theorem PeriodTorusHigherHomology.coordinateProjection_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateProjection n x i = (x i : AddCircle (1 : ℝ)) :=
  rfl

theorem PeriodTorusHigherHomology.coordinateProjection_continuous (n : ℕ) :
    Continuous (coordinateProjection n) := by
  exact continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))

theorem PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff (n : ℕ) (x : Fin n → ℝ) :
    coordinateProjection n x = 0 ↔ ∃ v : Fin n → ℤ, x = fun i => (v i : ℝ) := by
  constructor
  · intro h
    have hi : ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
      intro i
      have hz := congrFun h i
      change (x i : AddCircle (1 : ℝ)) = 0 at hz
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    choose v hv using hi
    exact ⟨v, funext fun i => (hv i).symm⟩
  · rintro ⟨v, rfl⟩
    ext i
    change ((v i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨v i, by simp⟩

theorem PeriodTorusHigherHomology.coordinateProjection_surjective (n : ℕ) :
    Function.Surjective (coordinateProjection n) := by
  intro t
  have h : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = t i := by
    intro i
    exact QuotientAddGroup.mk_surjective (t i)
  choose x hx using h
  exact ⟨x, funext hx⟩

def PeriodTorusHigherHomology.coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    Path (0 : ProductTorus n) 0 :=
  ((Path.segment (0 : Fin n → ℝ) (fun i => (v i : ℝ))).map
        (coordinateProjection_continuous n)).cast
    (map_zero (coordinateProjection n)).symm
    ((coordinateProjection_eq_zero_iff n _).mpr ⟨v, rfl⟩).symm

@[simp]
theorem PeriodTorusHigherHomology.coordinatePeriodLoop_apply (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) (i : Fin n) :
    coordinatePeriodLoop n v t i = ((t : ℝ) * (v i : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [coordinatePeriodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add,
    coordinateProjection_apply, Pi.smul_apply, smul_eq_mul]


def PeriodTorusHigherHomology.CirclePaths.circleTranslation (a : ℝ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle),
      (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  ⟨fun z => (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) + z, by
    exact
      (continuous_const :
            Continuous
              (fun _ : (PeriodTorusHigherHomology.CircleTopology.Circle) =>
                (a : (PeriodTorusHigherHomology.CircleTopology.Circle)))).add
        continuous_id⟩

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply (a : ℝ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    circleTranslation a z = (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) + z :=
  rfl

def PeriodTorusHigherHomology.CirclePaths.circleTranslationHomotopy (a : ℝ) :
    (circleTranslation a).Homotopy
      (ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle))
    where
  toFun
    p := ((((1 - (p.1 : ℝ)) * a : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) + p.2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            continuous_const)).add
      continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_singularHomologyMap (a : ℝ)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (circleTranslation a) n = LinearMap.id := by
  rw [PeriodTorusHigherHomology.homotopy_homologyMap (circleTranslationHomotopy a) n,
    PeriodTorusHigherHomology.singularHomologyMap_id]

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_inducedHomology (a : ℝ) :
    FirstHurewicz.inducedHomology (circleTranslation a) = LinearMap.id :=
  circleTranslation_singularHomologyMap a 1

theorem PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation (a : ℝ)
    {x : (PeriodTorusHigherHomology.CircleTopology.Circle)} (p : Path x x) :
    FirstHurewicz.loopHomologyClass (p.map (circleTranslation a).continuous) =
      FirstHurewicz.loopHomologyClass p := by
  rw [← FirstHurewicz.inducedHomology_loopHomologyClass (circleTranslation a) x p,
    circleTranslation_inducedHomology]
  rfl


def PeriodTorusHigherHomology.CirclePaths.positiveLoop :
    Path (0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) 0
    where
  toFun t := ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := AddCircle.coe_zero (1 : ℝ)
  target' := AddCircle.coe_period (1 : ℝ)

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply (t : unitInterval) :
    positiveLoop t = ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl


def PeriodTorusHigherHomology.positiveCircleCross (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1) :=
  crossProductHomology (PeriodTorusHigherHomology.CircleTopology.Circle) X n
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop)


theorem PeriodTorusHigherHomology.crossProductEdge_boundary_of_right_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b.1) =
      crossProductZeroLeft X Y n (((FirstHurewicz.singularComplex X).d 1 0).hom a) b.1 := by
  cases n with
  | zero => exact crossProductEdge_boundary_zero a b.1
  | succ
    n =>
    have hb : ((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b.1 = 0 := by
      simpa only [Nat.succ_sub_one] using
        SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex Y)
          (n + 1) b
    simp only [crossProductEdge_boundary, hb, map_zero, sub_zero]

theorem PeriodTorusHigherHomology.crossProductEdge_path_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) {x y : X} (p : Path x y)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 1) n).hom
        (crossProductEdge X Y n (FirstHurewicz.pathChain p) b.1) =
      FirstHurewicz.inducedChain (crossInsertLeft y) n b.1 -
        FirstHurewicz.inducedChain (crossInsertLeft x) n b.1 := by
  rw [crossProductEdge_boundary_of_right_cycle]
  change
    crossProductZeroLeft X Y n (FirstHurewicz.boundaryOne X (FirstHurewicz.pathChain p)) b.1 = _
  rw [FirstHurewicz.boundaryOne_pathChain, map_sub, LinearMap.sub_apply]
  simp only [FirstHurewicz.pointChain, crossProductZeroLeft_simplex_left]
  rfl

theorem PeriodTorusHigherHomology.const_prodMk_id_eq_crossInsertLeft_mo1973_12793
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) :
    (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y) = crossInsertLeft x := by
  apply ContinuousMap.ext
  intro y
  rfl


private def PeriodTorusHigherHomology.biprodElement_mo1973_12801
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.X n) (b : L.X n) : (K ⊞ L).X n :=
  ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
    ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b

private theorem PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (n : ℕ) (z : J.X n) :
    ((CategoryTheory.Limits.biprod.lift f g).f n).hom z =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom ((f.f n).hom z) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom ((g.f n).hom z) := by
  have htotal :=
    congrArg (fun h => h.hom (((CategoryTheory.Limits.biprod.lift f g).f n).hom z))
      (HomologicalComplex.biprod_total_f K L n)
  have hfst := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_fst_f f g n)
  have hsnd := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_snd_f f g n)
  change
    ((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (f.f n).hom z at hfst
  change
    ((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (g.f n).hom z at hsnd
  change
    ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) =
      ((CategoryTheory.Limits.biprod.lift f g).f n).hom z at htotal
  rw [hfst, hsnd] at htotal
  exact htotal.symm

private theorem PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803
    {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T) (n : ℕ) (a : K.X n)
    (b : L.X n) :
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom (biprodElement_mo1973_12801 K L n a b) =
      (f.f n).hom a + (g.f n).hom b := by
  change
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b) =
      _
  rw [map_add]
  congr 1
  · exact congrArg (fun h => h.hom a) (HomologicalComplex.biprod_inl_desc_f f g n)
  · exact congrArg (fun h => h.hom b) (HomologicalComplex.biprod_inr_desc_f f g n)

private theorem PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i j : ℕ) (a : K.X i) (b : L.X i) :
    ((K ⊞ L).d i j).hom (biprodElement_mo1973_12801 K L i a b) =
      biprodElement_mo1973_12801 K L j ((K.d i j).hom a) ((L.d i j).hom b) := by
  have hK := congrArg (fun f => f.hom a) ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).comm i j)
  have hL := congrArg (fun f => f.hom b) ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).comm i j)
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a) =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f j).hom ((K.d i j).hom a) at hK
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f j).hom ((L.d i j).hom b) at hL
  change
    ((K ⊞ L).d i j).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      _
  rw [map_add, hK, hL]
  rfl

private theorem PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (i j : ℕ) (a : K.X i)
    (b : L.X i) (z : J.X j) (ha : (K.d i j).hom a = (f.f j).hom z)
    (hb : (L.d i j).hom b = (g.f j).hom z) :
    ((CategoryTheory.Limits.biprod.lift f g).f j).hom z =
      ((K ⊞ L).d i j).hom (biprodElement_mo1973_12801 K L i a b) := by
  have hlift := biprod_lift_f_apply_mo1973_12802 f g j z
  have hboundary := biprodElement_boundary_mo1973_12804 K L i j a b
  have hab := congrArg₂ (biprodElement_mo1973_12801 K L j) ha hb
  exact hlift.trans (hab.symm.trans hboundary.symm)

def PeriodTorusHigherHomology.twoChainMiddle {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ)
    (a : FirstHurewicz.Chains U (n + 1)) (b : FirstHurewicz.Chains V (n + 1)) :
    (SingularMayerVietoris.middleComplex U V).X (n + 1) :=
  biprodElement_mo1973_12801 (FirstHurewicz.singularComplex U) (FirstHurewicz.singularComplex V)
    (n + 1) a b

theorem PeriodTorusHigherHomology.twoChainMiddle_rightMap {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1)) :
    ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) =
      ((SingularMayerVietoris.toSmallLeft U V).f (n + 1)).hom a +
        ((SingularMayerVietoris.toSmallRight U V).f (n + 1)).hom b :=
  biprodElement_desc_mo1973_12803 (SingularMayerVietoris.toSmallLeft U V)
    (SingularMayerVietoris.toSmallRight U V) (n + 1) a b

theorem PeriodTorusHigherHomology.twoChainMiddle_boundary {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.leftMap U V).f n).hom z.1 =
      ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom (twoChainMiddle U V n a b) :=
  biprod_lift_eq_boundary_mo1973_12805 (SingularMayerVietoris.intersectionToLeft U V)
    (-(SingularMayerVietoris.intersectionToRight U V)) (n + 1) n a b z.1 ha hb

theorem PeriodTorusHigherHomology.twoChainSmallCycle_condition {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.smallComplex U V).d (n + 1) n).hom
        (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b)) =
      0 := by
  have hcomm :=
    congrArg (fun f => f.hom (twoChainMiddle U V n a b))
      ((SingularMayerVietoris.rightMap U V).comm (n + 1) n)
  have hzero := congrArg (fun f => (f.f n).hom z.1) (SingularMayerVietoris.leftMap_rightMap U V)
  calc
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom
            (twoChainMiddle U V n a b)) :=
      hcomm
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.leftMap U V).f n).hom z.1) :=
      (congrArg ((SingularMayerVietoris.rightMap U V).f n).hom
        (twoChainMiddle_boundary U V n a b z ha hb).symm)
    _ = 0 := hzero

def PeriodTorusHigherHomology.twoChainSmallCycle {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : FirstHurewicz.Chains U (n + 1)) (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularMayerVietoris.smallComplex U V) (n + 1)
    (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b))
    (by
      rw [Nat.add_sub_cancel]
      exact twoChainSmallCycle_condition U V n a b z ha hb)

@[simp]
theorem PeriodTorusHigherHomology.twoChainSmallCycle_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (twoChainSmallCycle U V n a b z ha hb).1 =
      ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) :=
  rfl

theorem PeriodTorusHigherHomology.twoChainSmallCycle_ambient_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (SingularMayerVietoris.ModuleHomology.mapCycles (SingularMayerVietoris.smallInclusion U V)
          (n + 1) (twoChainSmallCycle U V n a b z ha hb)).1 =
      FirstHurewicz.inducedChain (SingularMayerVietoris.subtypeInclusion U) (n + 1) a +
        FirstHurewicz.inducedChain (SingularMayerVietoris.subtypeInclusion V) (n + 1) b := by
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, twoChainSmallCycle_val,
    twoChainMiddle_rightMap, map_add]
  have hU :=
    congrArg (fun f => (f.f (n + 1)).hom a) (SingularMayerVietoris.toSmallLeft_inclusion U V)
  have hV :=
    congrArg (fun f => (f.f (n + 1)).hom b) (SingularMayerVietoris.toSmallRight_inclusion U V)
  exact congrArg₂ (· + ·) hU hV

theorem PeriodTorusHigherHomology.connectingHomomorphism_twoChain {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : FirstHurewicz.Chains U (n + 1)) (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion U V) (n + 1)
            (twoChainSmallCycle U V n a b z ha hb))) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (U ∩ V : Set X)) n z :=
  connectingHomomorphism_cycleClass U V hU hV hcover n (twoChainSmallCycle U V n a b z ha hb)
    (twoChainMiddle U V n a b) rfl z (twoChainMiddle_boundary U V n a b z ha hb)


@[simp]
theorem PeriodTorusHigherHomology.circleProjection_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProjectionHomology X (n + 1) (positiveCircleCross X n b) = 0 :=
  crossProductHomology_snd n (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) b


end Mathoverflow1973

end
