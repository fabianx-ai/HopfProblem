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
Original source lines 182555--187882; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.Proof.LCP.AnalyticFillings
import Lib.Geometry.Manifold.Gluing.OverBase
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
import Lib.Algebra.Module.IntegerPresentation
import Lib.AlgebraicTopology.SingularHomology.LocalContributions
import Lib.Topology.OnePointCollapse
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.Index
import Lib.Geometry.Manifold.Morse.RearrangementTheorem
import Lib.Geometry.Manifold.Morse.Birth
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.Geometry.Manifold.Morse.Reeb
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

instance ThreefoldGluing.Data.spaceT2 {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [T2Space B] [∀ i, T2Space (D.piece i)] : T2Space D.Space := by
  constructor
  intro x y hxy
  by_cases hb : D.projection x = D.projection y
  · obtain ⟨i, hi⟩ := D.cover.exists_mem (D.projection x)
    have hx : x ∈ Set.range (D.inclusion i) := by rw [D.inclusion_range]; exact hi
    have hy : y ∈ Set.range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection y ∈ D.patch i
      rw [← hb]
      exact hi
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (congrArg (D.inclusion i) h)
    obtain ⟨U, V, hU, hV, ha, hb, hUV⟩ := t2_separation hab
    refine
      ⟨D.inclusion i '' U, D.inclusion i '' V, (D.inclusion_openEmbedding i).isOpenMap _ hU,
        (D.inclusion_openEmbedding i).isOpenMap _ hV, Set.mem_image_of_mem _ ha,
        Set.mem_image_of_mem _ hb, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨a', ha', hza⟩ ⟨b', hb', hzb⟩
    have hab' := (D.inclusion_openEmbedding i).injective (hza.trans hzb.symm)
    exact (Set.disjoint_left.mp hUV) ha' (hab'.symm ▸ hb')
  · obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hb
    exact
      ⟨D.projection ⁻¹' U, D.projection ⁻¹' V, hU.preimage D.projection_continuous,
        hV.preimage D.projection_continuous, hx, hy, hUV.preimage D.projection⟩


theorem ThreefoldGluing.Data.contMDiffOn_of_comp_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)] {F H N : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace N]
    [ChartedSpace H N] (I : ModelWithCorners ℂ F H) (f : D.Space → N) {U : Set D.Space}
    (hU : IsOpen U)
    (hf :
      ∀ i, ContMDiffOn (modelWithCornersSelf ℂ E) I ω (f ∘ D.inclusion i) (D.inclusion i ⁻¹' U)) :
    letI := D.chartedSpace (E := E)
    ContMDiffOn (modelWithCornersSelf ℂ E) I ω f U := by
  have hparam (i : D.J) (z : D.piece i) : D.parametrization i z = D.inclusion i z := rfl
  let := D.chartedSpace (E := E)
  intro x hxU
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (D.gluedChart (E := E) (D.representative x).1 (D.representative x).2).source :=
    mem_chart_source E x
  have hre :
    D.inclusion (D.representative x).1 ((D.parametrization (D.representative x).1).symm x) = x :=
    (D.parametrization (D.representative x).1).right_inv hx.1
  have hpre :
    (D.parametrization (D.representative x).1).symm x ∈
      D.inclusion (D.representative x).1 ⁻¹' U := by
    change D.inclusion _ _ ∈ U
    rwa [hre]
  have hlocal :=
    (hf (D.representative x).1).contMDiffAt
      ((hU.preimage (D.inclusion_openEmbedding _).continuous).mem_nhds hpre)
  have hsrc :=
    (contMDiffAt_iff_source_of_mem_source (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp
      hlocal
  have hchart : chartAt E x = D.gluedChart (D.representative x).1 (D.representative x).2 := rfl
  simpa [hparam, extChartAt, OpenPartialHomeomorph.extend, hchart, gluedChart,
    Function.comp_def] using hsrc

theorem ThreefoldGluing.Data.gluedChart_transition_holomorphic {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i j : D.J) (x : D.piece i) (y : D.piece j) :
    ContDiffOn ℂ ω ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y))
      ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E x).target := hz.1.1
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈ (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ Set.range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm, parametrization_target] using hinc.1
  obtain ⟨htr, he⟩ := D.parametrization_transition i j hrange
  have ha := (chartAt E x).map_target hza
  have hb : D.transition i j ((chartAt E x).symm z) ∈ (chartAt E y).source := by
    rw [← he]
    exact hinc.2
  have hmid := (hhol i j).contMDiffAt ((D.transition i j).open_source.mem_nhds htr)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' : ContDiffAt ℂ ω (chartAt E y ∘ D.transition i j ∘ (chartAt E x).symm) z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E x).right_inv hza] using hc
  apply hc'.contDiffWithinAt.congr_of_mem ?_ hz
  intro w hw
  exact D.gluedChart_transition_apply i j x y hw

theorem ThreefoldGluing.Data.isManifold {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source) :
    letI := D.chartedSpace (E := E)
    IsManifold (modelWithCornersSelf ℂ E) ω D.Space := by
  let := D.chartedSpace (E := E)
  apply isManifold_of_contDiffOn
  rintro e e' ⟨⟨i, x⟩, rfl⟩ ⟨⟨j, y⟩, rfl⟩
  simpa using D.gluedChart_transition_holomorphic hhol i j x y

theorem ThreefoldGluing.Data.inclusion_holomorphic {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i : D.J) :
    letI := D.chartedSpace (E := E)
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.inclusion i) := by
  let := D.chartedSpace (E := E)
  let := D.isManifold hhol
  intro x
  have he :=
    IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ E) (n := ω)
      (D.gluedChart_mem_atlas i x)
  have ht : chartAt E x x ∈ (D.gluedChart (E := E) i x).target := by
    simpa only [gluedChart_inclusion] using
      (D.gluedChart (E := E) i x).map_source (D.gluedChart_inclusion_mem_source i x)
  have hsymm := contMDiffAt_symm_of_mem_maximalAtlas he ht
  have hc : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (chartAt E x) x :=
    contMDiffOn_chart.contMDiffAt ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  apply (hsymm.comp x hc).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
  change D.inclusion i y = (D.gluedChart (E := E) i x).symm (chartAt E x y)
  rw [gluedChart_symm, Function.comp_apply, (chartAt E x).left_inv hy]

theorem ThreefoldGluing.Data.parametrization_symm_holomorphic {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i : D.J) :
    letI := D.chartedSpace (E := E)
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.parametrization i).symm
      (D.parametrization i).target := by
  let := D.chartedSpace (E := E)
  rw [parametrization_target]
  apply
    D.contMDiffOn_of_comp_inclusion (modelWithCornersSelf ℂ E) (D.parametrization i).symm
      (D.inclusion_openEmbedding i).isOpen_range
  intro j
  exact
    ((hhol j i).mono (fun x hx => (D.parametrization_transition j i hx).1)).congr
      (fun x hx => (D.parametrization_transition j i hx).2)

theorem SpecialPeriods.Threefold.Star.Input.transition_holomorphic {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [∀ i, ChartedSpace E (D.piece i)]
    (hhol :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i)
          (D.overlap i).source)
    (hinv :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i).symm
          (D.overlap i).target)
    (i j : Option I) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
      (D.transition i j).source := by
  cases i with
  | none =>
    cases j with
    | none =>
      rw [D.transition_none_none]
      change
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
          (id : D.piece Option.none → D.piece Option.none) Set.univ
      exact contMDiffOn_id
    | some j =>
      rw [D.transition_none_some]
      simpa only [OpenPartialHomeomorph.symm_source] using hinv j
  | some i =>
    cases j with
    | none =>
      rw [D.transition_some_none]
      exact hhol i
    | some j =>
      by_cases h : i = j
      · subst j
        rw [D.transition_some_self]
        change
          ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
            (id : D.piece (Option.some i) → D.piece (Option.some i)) Set.univ
        exact contMDiffOn_id
      · rw [D.transition_some_some_source_eq_empty h]
        exact contMDiffOn_empty

theorem SpecialPeriods.Threefold.Star.Input.toData_transition_holomorphic {B I : Type u}
    [TopologicalSpace B] (D : SpecialPeriods.Threefold.Star.Input B I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [∀ i, ChartedSpace E (D.piece i)]
    (hhol :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i)
          (D.overlap i).source)
    (hinv :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.overlap i).symm
          (D.overlap i).target)
    (i j : D.toData.J) :
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.toData.transition i j)
      (D.toData.transition i j).source := by
  change
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
      (D.transition i j).source
  exact D.transition_holomorphic hhol hinv i j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspRadius_le :
    specialBaseCover.radius Option.none ≤ SpecialPeriods.specialCuspData.radius :=
  specialBaseCover_cusp_radius_bounds.2.1.le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.SpecialCuspPiece :=
  CuspPiece.Space SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.specialCuspPieceChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) SpecialCuspPiece :=
  CuspPiece.commonChartedSpace SpecialPeriods.specialCuspData specialBaseCover
    specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialCuspPieceProjection :
    SpecialCuspPiece → specialBaseCover.fillingPatch Option.none :=
  CuspPiece.projection SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialCuspPieceProjectionToBase :
    SpecialCuspPiece → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  CuspPiece.projectionToBase SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPieceProjection_proper :
    IsProperMap specialCuspPieceProjection :=
  CuspPiece.projection_proper SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPiece_t2Space : T2Space SpecialCuspPiece :=
  CuspPiece.space_t2Space SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPiece_secondCountable :
    SecondCountableTopology SpecialCuspPiece :=
  CuspPiece.space_secondCountable SpecialPeriods.specialCuspData specialBaseCover
    specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPiece_isManifold :
    letI := specialCuspPieceChartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω SpecialCuspPiece :=
  CuspPiece.common_isManifold SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPiece_nonempty : Nonempty SpecialCuspPiece :=
  CuspPiece.space_nonempty SpecialPeriods.specialCuspData specialBaseCover

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.localPiece : Index → TopCat
  | none => TopCat.of SpecialRegularFamily
  | some Option.none => TopCat.of SpecialCuspPiece
  | some (Option.some j) => TopCat.of (SpecialEllipticPiece j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.localPieceChartedSpace (i : Index) :
    ChartedSpace (ℂ × ComplexPlane₂) (localPiece i) := by
  cases i with
  | none => exact specialRegularFamilyChartedSpace
  | some i =>
    cases i with
    | none => exact specialCuspPieceChartedSpace
    | some j => exact specialEllipticPieceChartedSpace j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localPiece_nonempty (i : Index) : Nonempty (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_nonempty
  | some i =>
    cases i with
    | none => exact specialCuspPiece_nonempty
    | some j => exact specialEllipticPiece_nonempty j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localPiece_t2Space (i : Index) : T2Space (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_t2Space
  | some i =>
    cases i with
    | none => exact specialCuspPiece_t2Space
    | some j => exact specialEllipticPiece_t2Space j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localPiece_secondCountable (i : Index) :
    SecondCountableTopology (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_secondCountable
  | some i =>
    cases i with
    | none => exact specialCuspPiece_secondCountable
    | some j => exact specialEllipticPiece_secondCountable j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localPiece_isManifold (i : Index) :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_isManifold
  | some i =>
    cases i with
    | none => exact specialCuspPiece_isManifold
    | some j => exact specialEllipticPiece_isManifold j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
def SpecialPeriods.Threefold.localProjection :
    (i : Index) → localPiece i → specialBaseCover.patch i
  | none => specialRegularFamilyProjection
  | some Option.none => specialCuspPieceProjection
  | some (Option.some j) => specialEllipticPieceProjection j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localProjection_proper (i : Index) :
    IsProperMap (localProjection i) := by
  cases i with
  | none => exact specialRegularFamilyProjection_proper
  | some i =>
    cases i with
    | none => exact specialCuspPieceProjection_proper
    | some j => exact specialEllipticPieceProjection_proper j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
def SpecialPeriods.Threefold.localProjectionToBase (i : Index) (x : localPiece i) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  localProjection i x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localProjectionToBase_mem (i : Index) (x : localPiece i) :
    localProjectionToBase i x ∈ specialBaseCover.patch i :=
  (localProjection i x).property

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localProjectionToBase_continuous (i : Index) :
    Continuous (localProjectionToBase i) :=
  continuous_subtype_val.comp (localProjection_proper i).continuous

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.localPieceChartedSpace in
def SpecialPeriods.Threefold.localBaseMap (i : Index) :
    C(localPiece i, SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  ⟨localProjectionToBase i, localProjectionToBase_continuous i⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.CuspGlobalOverlap.sphereRegularData
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData (SpecialPeriods.Construction.periodMapOfSphere π hπ h₀ h₁)
    (SpecialPeriods.Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (SpecialPeriods.Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.CuspGlobalOverlap.sphereCuspData
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius) :
    SpecialPeriods.CuspFamily.Data :=
  (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).shrink r hr hrD

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspData_periodPoint
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    ((sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s).val =
      SpecialPeriods.cuspPeriodPoint (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).μ
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).b
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).h (s : ℂ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.spherePeriod_point
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    ((sphereRegularData π hπ h₀ h₁).periods.point
          (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s)).val =
      SpecialPeriods.cuspPeriodPoint (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).μ
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).b
        (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).h (s : ℂ) := by
  have hz :
    ‖SpecialPeriods.Triangle.cuspQ (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ)‖ <
      (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius := by
    rw [SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ]
    exact ((SpecialPeriods.CuspFamily.mem_logBase r s).mp s.property).trans_le hrD
  have h :=
    SpecialPeriods.Construction.cuspDataOfSphere_periodPoint π hπ h₀ h₁
      (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ) hz
  rw [SpecialPeriods.CuspFamily.logBaseToRegular_coe,
    mul_div_cancel_left₀ _
      (Complex.ofReal_ne_zero.mpr SpecialPeriods.Triangle.width_ne_zero)] at h
  exact h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.spherePeriod_agreement
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    (sphereRegularData π hπ h₀ h₁).periods.point
        (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s) =
      (sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s := by
  apply Subtype.ext
  rw [sphereCuspData_periodPoint]
  exact spherePeriod_point π hπ h₀ h₁ r hrD hrcap s

def SpecialPeriods.CuspGlobalOverlap.QuotientComparison.totalMap
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (x : C.TotalSpace) : D.TotalSpace :=
  (f x.1, x.2)

theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.totalMap_injective
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hf : Function.Injective f) : Function.Injective (totalMap C D f) := by
  intro x y h
  exact Prod.ext (hf (congrArg Prod.fst h)) (congrArg (fun z : D.TotalSpace => z.2) h)

theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.totalMap_equivariant
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k)
    (k : Multiplicative ℤ) (x : C.TotalSpace) :
    letI := C.totalAction
    letI := D.totalAction
    totalMap C D f (k • x) = SpecialPeriods.triangleCuspGenerator ^ k.toAdd • totalMap C D f x := by
  let := C.totalAction
  let := D.totalAction
  change
    (f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k.toAdd x.1),
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd x.2) =
      (SpecialPeriods.triangleCuspGenerator ^ k.toAdd • f x.1,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k.toAdd)
          x.2)
  rw [hbase, htorus]

def SpecialPeriods.CuspGlobalOverlap.QuotientComparison.descend
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k) :
    C.Space → D.Space := by
  letI := C.totalAction
  letI := D.totalAction
  exact
    Quotient.lift (D.quotient ∘ totalMap C D f)
      (by
        rintro x y ⟨k, hk⟩
        change D.quotient (totalMap C D f x) = D.quotient (totalMap C D f y)
        rw [← hk, totalMap_equivariant C D f hbase htorus, D.quotient_smul])

theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.descend_injective
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k)
    (hf : Function.Injective f)
    (hreturn :
      ∀ (g : SpecialPeriods.TriangleGroup) (s t : SpecialPeriods.CuspFamily.LogBase C.radius),
        g • f t = f s → ∃ k : ℤ, SpecialPeriods.triangleCuspGenerator ^ k = g) :
    Function.Injective (descend C D f hbase htorus) := by
  let := C.totalAction
  let := D.totalAction
  intro x y hxy
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  obtain ⟨b, rfl⟩ := C.quotient_surjective y
  obtain ⟨g, hg⟩ := (D.quotient_eq_iff _ _).mp hxy
  have hb : g • f b.1 = f a.1 := congrArg Prod.fst hg
  obtain ⟨k, rfl⟩ := hreturn g a.1 b.1 hb
  apply (C.quotient_eq_iff _ _).mpr
  refine ⟨Multiplicative.ofAdd k, ?_⟩
  apply totalMap_injective C D f hf
  rw [totalMap_equivariant C D f hbase htorus]
  exact hg

theorem SpecialPeriods.CuspGlobalOverlap.QuotientComparison.range_descend
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (f : SpecialPeriods.CuspFamily.LogBase C.radius → SpecialPeriods.TriangleRegularPoint)
    (hbase :
      ∀ (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase C.radius),
        f (SpecialPeriods.CuspFamily.logBaseTranslate C.radius k s) =
          SpecialPeriods.triangleCuspGenerator ^ k • f s)
    (htorus :
      ∀ k : ℤ,
        SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.triangleCuspGenerator ^ k) =
          SpecialPeriods.CuspFamily.cuspTorusHomeomorph k) :
    Set.range (descend C D f hbase htorus) = D.projection ⁻¹' Set.range (D.baseQuotient ∘ f) := by
  let := D.totalAction
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := C.quotient_surjective x
    exact ⟨a.1, rfl⟩
  · rintro ⟨s, hs⟩
    obtain ⟨⟨b, t⟩, rfl⟩ := D.quotient_surjective y
    have hbase' : D.baseQuotient (f s) = D.baseQuotient b := hs
    have hrel : ∃ g : SpecialPeriods.TriangleGroup, g • b = f s := Quotient.eq''.mp hbase'
    obtain ⟨g, hg⟩ := hrel
    refine ⟨C.quotient (s, SpecialPeriods.triangleTorusHomeomorph g t), ?_⟩
    apply (D.quotient_eq_iff _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
def SpecialPeriods.CuspGlobalOverlap.baseCover (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    SpecialPeriods.CuspFamily.LogBase r → SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.triangleRegularProject ∘ SpecialPeriods.CuspFamily.logBaseToRegular r hrcap

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.baseCover_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (baseCover r hrcap) := by
  intro s
  exact
    (SpecialPeriods.CuspFamily.logBaseToRegular_isLocalDiffeomorph r hrcap s).comp (K := 𝓘(ℂ))
      (P := SpecialPeriods.TriangleRegularQuotient)
      (SpecialPeriods.triangleRegularProject_isLocalDiffeomorph
        (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
def SpecialPeriods.CuspGlobalOverlap.basePatch (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient :=
  ⟨Set.range (baseCover r hrcap), (baseCover_isLocalDiffeomorph r hrcap).isOpen_range⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
def SpecialPeriods.CuspGlobalOverlap.compactBase :
    SpecialPeriods.TriangleRegularQuotient → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleOpenInclusion ∘ SpecialPeriods.triangleRegularToOrbit

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
@[simp]
theorem SpecialPeriods.CuspGlobalOverlap.compactBase_baseCover (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    compactBase (baseCover r hrcap s) =
      SpecialPeriods.triangleOpenInclusion
        (SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ)) :=
  rfl

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.compactBase_baseCover_mem_chart (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    compactBase (baseCover r hrcap s) ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
  apply
    (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood SpecialPeriods.Triangle.width
        _).mpr
  exact
    ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ),
      SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap s, rfl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
@[simp]
theorem SpecialPeriods.CuspGlobalOverlap.cuspFullChart_compactBase_baseCover (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : SpecialPeriods.CuspFamily.LogBase r) :
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactBase (baseCover r hrcap s)) =
      CuspUniformization.exponential s := by
  rw [compactBase_baseCover]
  exact
    (SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl
          ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ),
            SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap s⟩).trans
      (SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ r hrcap s)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.logBaseToRegular_return (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (g : SpecialPeriods.TriangleGroup) (s t : SpecialPeriods.CuspFamily.LogBase r)
    (he :
      g • SpecialPeriods.CuspFamily.logBaseToRegular r hrcap t =
        SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s) :
    ∃ k : ℤ, SpecialPeriods.triangleCuspGenerator ^ k = g := by
  apply Subgroup.mem_zpowers_iff.mp
  apply
    SpecialPeriods.Triangle.triangle_horodisc_overlap_mem_cusp SpecialPeriods.Triangle.width
      le_rfl g
  exact
    ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap s : ℍ),
      ⟨(SpecialPeriods.CuspFamily.logBaseToRegular r hrcap t : ℍ),
        SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap t,
        congrArg Subtype.val he⟩,
      SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc r hrcap s⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.mem_basePatch_iff (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (q : SpecialPeriods.TriangleRegularQuotient) :
    q ∈ basePatch r hrcap ↔
      compactBase q ∈
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source ∧
        ‖SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (compactBase q)‖ <
          r := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨compactBase_baseCover_mem_chart r hrcap s, ?_⟩
    rw [cuspFullChart_compactBase_baseCover]
    exact (SpecialPeriods.CuspFamily.mem_logBase r s).mp s.property
  · rintro ⟨hsource, hnorm⟩
    have himage :
      SpecialPeriods.triangleRegularToOrbit q ∈
        SpecialPeriods.Triangle.cuspImage SpecialPeriods.Triangle.width :=
      (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood SpecialPeriods.Triangle.width
            _).mp
        hsource
    obtain ⟨z, hz, he⟩ := himage
    have hqz : ‖SpecialPeriods.Triangle.cuspQ z‖ < r := by
      have hcoord :=
        SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl
          (⟨z, hz⟩ : SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width)
      change
        SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
            (SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z)) =
          SpecialPeriods.Triangle.cuspQ z at hcoord
      rw [he] at hcoord
      exact hcoord ▸ hnorm
    obtain ⟨s, hs⟩ :=
      (SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_range r hrcap ▸ hqz :
        z ∈ Set.range (SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane r hrcap))
    refine ⟨s, SpecialPeriods.triangleRegularToOrbit_injective ?_⟩
    change
      SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane r hrcap s) =
        SpecialPeriods.triangleRegularToOrbit q
    rw [hs]
    exact he

theorem SpecialPeriods.triangleDualRepresentation_cusp_zpow_matrix (k : ℤ) :
    (triangleDualRepresentation (triangleCuspGenerator ^ k) : LatticeMatrix) =
      CuspFamily.cuspIntegralMatrix k := by
  let C : Multiplicative ℤ →* LatticeMatrix :=
    { toFun := fun n => CuspFamily.cuspIntegralMatrix n.toAdd
      map_one' := CuspFamily.cuspIntegralMatrix_zero
      map_mul' := fun m n => CuspFamily.cuspIntegralMatrix_add m.toAdd n.toAdd }
  let R : Multiplicative ℤ →* LatticeMatrix :=
    { toFun := fun n =>
        (triangleDualRepresentation (triangleCuspGenerator ^ n.toAdd) : LatticeMatrix)
      map_one' := by simp
      map_mul' := by
        intro m n
        change
          (triangleDualRepresentation (triangleCuspGenerator ^ (m.toAdd + n.toAdd)) :
              LatticeMatrix) =
            _
        rw [_root_.zpow_add, map_mul, Matrix.SpecialLinearGroup.coe_mul] }
  have he : R = C := by
    apply MonoidHom.ext_mint
    change
      (triangleDualRepresentation (triangleCuspGenerator ^ (1 : ℤ)) : LatticeMatrix) =
        CuspFamily.cuspIntegralMatrix 1
    rw [zpow_one, CuspFamily.cuspIntegralMatrix_one, triangleDualRepresentation_cusp_matrix]
  exact DFunLike.congr_fun he (Multiplicative.ofAdd k)

theorem SpecialPeriods.triangleRealEquiv_cusp_zpow (k : ℤ) :
    triangleRealEquiv (triangleCuspGenerator ^ k) = CuspFamily.cuspRealEquiv k := by
  apply LinearEquiv.ext
  intro x
  rw [triangleRealEquiv_apply, triangleDualRepresentation_cusp_zpow_matrix,
    CuspFamily.cuspRealEquiv_apply]

theorem SpecialPeriods.triangleTorusHomeomorph_cusp_zpow (k : ℤ) :
    triangleTorusHomeomorph (triangleCuspGenerator ^ k) = CuspFamily.cuspTorusHomeomorph k := by
  apply Homeomorph.ext
  intro x
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, CuspFamily.cuspTorusHomeomorph_mkQ,
    triangleRealEquiv_cusp_zpow]

@[instance_reducible]
def SpecialPeriods.EllipticFilling.coveringChartedSpace {A : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] : ChartedSpace (ℂ × ComplexPlane₂) (A × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (A × ComplexPlane₂))

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace in
theorem SpecialPeriods.EllipticFilling.coveringManifold {A : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [IsManifold (modelWithCornersSelf ℂ ℂ) ω A] :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (A × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := (modelWithCornersSelf ℂ ℂ)) (I' :=
      (modelWithCornersSelf ℂ ComplexPlane₂)) A ComplexPlane₂

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
theorem SpecialPeriods.EllipticFilling.localDiffeomorphAt_of_comp {E F K M N T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N] [TopologicalSpace T] [ChartedSpace K T] {q : M → N}
    {f : N → T} {x : M}
    (hq : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω q x)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ K) ω (f ∘ q) x) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ K) ω f (q x) := by
  have hx : hq.localInverse (q x) = x := hq.localInverse_left_inv hq.localInverse_mem_target
  have hf' :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ K) ω (f ∘ q)
      (hq.localInverse (q x)) := by
    rw [hx]
    exact hf
  have h := hq.localInverse_isLocalDiffeomorphAt.comp (K := modelWithCornersSelf ℂ K) (P := T) hf'
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq h
  filter_upwards [hq.localInverse_eventuallyEq_right] with y hy
  change f y = f (q (hq.localInverse y))
  rw [show q (hq.localInverse y) = y from hy]

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
def SpecialPeriods.EllipticFilling.productPartialDiffeomorph {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B]
    (e : PartialDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) A B ω) :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (A × ComplexPlane₂) (B × ComplexPlane₂) ω
    where
  toPartialEquiv :=
    (e.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl ComplexPlane₂)).toPartialEquiv
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    rw [modelWithCornersSelf_prod]
    exact
      (e.contMDiffOn_toFun.comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
        contMDiff_snd.contMDiffOn
  contMDiffOn_invFun := by
    rw [modelWithCornersSelf_prod]
    exact
      (e.contMDiffOn_invFun.comp contMDiff_fst.contMDiffOn (fun _ hx => hx.1)).prodMk
        contMDiff_snd.contMDiffOn

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
theorem SpecialPeriods.EllipticFilling.productMap_isLocalDiffeomorph {A B : Type*}
    [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B] {f : A → B}
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun x : A × ComplexPlane₂ => (f x.1, x.2)) := by
  intro x
  obtain ⟨e, hx, he⟩ := hf x.1
  refine ⟨productPartialDiffeomorph e, ⟨hx, Set.mem_univ _⟩, ?_⟩
  intro y hy
  exact Prod.ext (he hy.1) rfl

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
def SpecialPeriods.EllipticFilling.periodFamilyMap {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B] (Q : HolomorphicPeriodMap ℂ A)
    (P : HolomorphicPeriodMap ℂ B) (f : A → B) : Q.TotalSpace → P.TotalSpace := fun x =>
  (f x.1, x.2)

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
theorem SpecialPeriods.EllipticFilling.periodFamilyMap_cover {A B : Type*} [TopologicalSpace A]
    [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B] (Q : HolomorphicPeriodMap ℂ A)
    (P : HolomorphicPeriodMap ℂ B) (f : A → B) (hperiod : ∀ a, Q.point a = P.point (f a))
    (x : A × ComplexPlane₂) :
    periodFamilyMap Q P f (Q.quotientMap x) = P.quotientMap (f x.1, x.2) := by
  apply Prod.ext
  · rfl
  · change
      standardLattice.mkQ ((Q.periodEquiv x.1).symm x.2) =
        standardLattice.mkQ ((P.periodEquiv (f x.1)).symm x.2)
    rw [show Q.periodEquiv x.1 = P.periodEquiv (f x.1) by
        simp only [HolomorphicPeriodMap.periodEquiv, hperiod] ]

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
theorem SpecialPeriods.EllipticFilling.periodFamilyMap_isLocalDiffeomorph {A B : Type*}
    [TopologicalSpace A] [ChartedSpace ℂ A] [TopologicalSpace B] [ChartedSpace ℂ B]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω A] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B]
    (Q : HolomorphicPeriodMap ℂ A) (P : HolomorphicPeriodMap ℂ B) (f : A → B)
    (hperiod : ∀ a, Q.point a = P.point (f a))
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    letI := Q.totalChartedSpace
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodFamilyMap Q P f) := by
  let := Q.totalChartedSpace
  let := P.totalChartedSpace
  let := Q.coveringAction
  have hQ :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω Q.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph Q.quotientCoveringMap Q.coveringAction_holomorphic
  have hP :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω P.quotientMap := by
    let := P.coveringAction
    exact
      CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap
        P.coveringAction_holomorphic
  intro y
  obtain ⟨x, rfl⟩ := Q.quotientMap_surjective y
  apply localDiffeomorphAt_of_comp (hQ x)
  have h :=
    (productMap_isLocalDiffeomorph hf x).comp (K := (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)))
      (P := P.TotalSpace) (hP (f x.1, x.2))
  exact
    isLocalDiffeomorphAt_congr_of_eventuallyEq h
      (Filter.Eventually.of_forall (periodFamilyMap_cover Q P f hperiod))

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
def SpecialPeriods.EllipticFilling.restrictPeriods {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    HolomorphicPeriodMap ℂ U where
  point x := P.point x
  holomorphic_tau := P.holomorphic_tau.comp contMDiff_subtype_val
  holomorphic_mu := P.holomorphic_mu.comp contMDiff_subtype_val
  holomorphic_beta := P.holomorphic_beta.comp contMDiff_subtype_val

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
def SpecialPeriods.EllipticFilling.periodFamilyOpen {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    TopologicalSpace.Opens P.TotalSpace :=
  ⟨P.projection ⁻¹' (U : Set B), U.isOpen.preimage continuous_fst⟩

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
def SpecialPeriods.EllipticFilling.restrictFamilyMap {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    (restrictPeriods P U).TotalSpace → periodFamilyOpen P U := fun x => ⟨(x.1.1, x.2), x.1.2⟩

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
theorem SpecialPeriods.EllipticFilling.restrictFamilyMap_bijective {B : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] (P : HolomorphicPeriodMap ℂ B)
    (U : TopologicalSpace.Opens B) : Function.Bijective (restrictFamilyMap P U) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    exact
      Prod.ext (Subtype.ext (congrArg (fun z : B × RealTorus₄ => z.1) he))
        (congrArg (fun z : B × RealTorus₄ => z.2) he)
  · intro y
    exact ⟨(⟨y.1.1, y.2⟩, y.1.2), rfl⟩

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
theorem SpecialPeriods.EllipticFilling.restrictFamilyMap_isLocalDiffeomorph {B : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B]
    (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (restrictFamilyMap P U) := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (periodFamilyMap_isLocalDiffeomorph (restrictPeriods P U) P Subtype.val (fun _ => rfl)
        (isLocalDiffeomorph_subtypeVal (modelWithCornersSelf ℂ ℂ) U))
      (periodFamilyOpen P U) (fun x => x.1.2)

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
def SpecialPeriods.EllipticFilling.restrictFamilyBiholomorph {B : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B] (P : HolomorphicPeriodMap ℂ B)
    (U : TopologicalSpace.Opens B) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (restrictPeriods P U).TotalSpace
      (periodFamilyOpen P U) ω := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  exact
    (restrictFamilyMap_isLocalDiffeomorph P U).diffeomorphOfBijective
      (restrictFamilyMap_bijective P U)

attribute [local instance] SpecialPeriods.EllipticFilling.coveringChartedSpace
    SpecialPeriods.EllipticFilling.coveringManifold in
@[simp]
theorem SpecialPeriods.EllipticFilling.restrictFamilyBiholomorph_symm_apply {B : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold (modelWithCornersSelf ℂ ℂ) ω B]
    (P : HolomorphicPeriodMap ℂ B) (U : TopologicalSpace.Opens B) (x : periodFamilyOpen P U) :
    letI := (restrictPeriods P U).totalChartedSpace
    letI := P.totalChartedSpace
    (restrictFamilyBiholomorph P U).symm x = (⟨x.1.1, x.2⟩, x.1.2) := by
  let := (restrictPeriods P U).totalChartedSpace
  let := P.totalChartedSpace
  apply (restrictFamilyBiholomorph P U).injective
  exact (restrictFamilyBiholomorph P U).apply_symm_apply x

theorem isLocalDiffeomorphAt_of_comp_localDiffeomorph {E F F' H K K' M N R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K]
    [TopologicalSpace K'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] [TopologicalSpace R] [ChartedSpace K' R] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N} {g : N → R} {x : M}
    (hf : IsLocalDiffeomorphAt I J ω f x) (hgf : IsLocalDiffeomorphAt I L ω (g ∘ f) x) :
    IsLocalDiffeomorphAt J L ω g (f x) := by
  obtain ⟨φ, hx, he⟩ := hgf
  have hinv : hf.localInverse (f x) = x := hf.localInverse_left_inv hf.localInverse_mem_target
  refine ⟨hf.localInverse.trans φ, ⟨hf.localInverse_mem_source, ?_⟩, ?_⟩
  · change hf.localInverse (f x) ∈ φ.source
    rwa [hinv]
  · intro y hy
    change g y = φ (hf.localInverse y)
    exact (congrArg g (hf.localInverse_right_inv hy.1).symm).trans (he hy.2)

theorem isLocalDiffeomorph_of_comp_surjective {E F F' H K K' M N R : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace R] [ChartedSpace K' R] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N} {g : N → R}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f)
    (hgf : IsLocalDiffeomorph I L ω (g ∘ f)) : IsLocalDiffeomorph J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact isLocalDiffeomorphAt_of_comp_localDiffeomorph I J L (hf x) (hgf x)

@[instance_reducible]
def HolomorphicPeriodMap.periodPullbackCoveringChartedSpace {V B : Type*} [NormedAddCommGroup V]
    [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace in
theorem HolomorphicPeriodMap.periodPullbackCoveringManifold {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ V) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B
      ComplexPlane₂

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.quotientMap_isLocalDiffeomorph {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B] (P : HolomorphicPeriodMap V B) :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.quotientMap := by
  let := P.coveringAction
  let := P.totalChartedSpace
  exact
    CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap P.coveringAction_holomorphic

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
def HolomorphicPeriodMap.periodPullbackMap {B C : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [TopologicalSpace C] [ChartedSpace ℂ C] (P : HolomorphicPeriodMap ℂ B)
    (Q : HolomorphicPeriodMap ℂ C) (f : B → C) : P.TotalSpace → Q.TotalSpace := fun x =>
  (f x.1, x.2)

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
def HolomorphicPeriodMap.periodPullbackVectorMap {B C : Type*} (f : B → C) :
    (B × ComplexPlane₂) → (C × ComplexPlane₂) := fun x => (f x.1, x.2)

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.periodEquiv_pullback_eq {B C : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C] (P : HolomorphicPeriodMap ℂ B)
    (Q : HolomorphicPeriodMap ℂ C) (f : B → C) (hpoint : ∀ b, Q.point (f b) = P.point b) (b : B) :
    Q.periodEquiv (f b) = P.periodEquiv b := by simp only [periodEquiv, hpoint b]

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.periodPullbackMap_quotientMap {B C : Type*} [TopologicalSpace B]
    [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C] (P : HolomorphicPeriodMap ℂ B)
    (Q : HolomorphicPeriodMap ℂ C) (f : B → C) (hpoint : ∀ b, Q.point (f b) = P.point b)
    (x : B × ComplexPlane₂) :
    periodPullbackMap P Q f (P.quotientMap x) = Q.quotientMap (periodPullbackVectorMap f x) := by
  change
    (f x.1, standardLattice.mkQ ((P.periodEquiv x.1).symm x.2)) =
      (f x.1, standardLattice.mkQ ((Q.periodEquiv (f x.1)).symm x.2))
  rw [periodEquiv_pullback_eq P Q f hpoint]

attribute [local instance] HolomorphicPeriodMap.periodPullbackCoveringChartedSpace
    HolomorphicPeriodMap.periodPullbackCoveringManifold in
theorem HolomorphicPeriodMap.periodPullbackMap_isLocalDiffeomorph {B C : Type*}
    [TopologicalSpace B] [ChartedSpace ℂ B] [TopologicalSpace C] [ChartedSpace ℂ C]
    (P : HolomorphicPeriodMap ℂ B) (Q : HolomorphicPeriodMap ℂ C) (f : B → C)
    [IsManifold 𝓘(ℂ) ω B] [IsManifold 𝓘(ℂ) ω C] (hpoint : ∀ b, Q.point (f b) = P.point b)
    (hf : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω f) :
    letI := P.totalChartedSpace
    letI := Q.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (periodPullbackMap P Q f) := by
  let := P.totalChartedSpace
  let := Q.totalChartedSpace
  exact
    SpecialPeriods.EllipticFilling.periodFamilyMap_isLocalDiffeomorph P Q f
      (fun b => (hpoint b).symm) hf

theorem SpecialPeriods.CuspGlobalOverlap.familyCovering
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup :=
  SpecialPeriods.triangleRegularProject_covering

def SpecialPeriods.CuspGlobalOverlap.familyMap (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    C.Space → D.Space :=
  QuotientComparison.descend C D (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
    (SpecialPeriods.CuspFamily.logBaseToRegular_translate C.radius hrcap)
    SpecialPeriods.triangleTorusHomeomorph_cusp_zpow

@[simp]
theorem SpecialPeriods.CuspGlobalOverlap.familyMap_quotient (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.TotalSpace) :
    familyMap C D hrcap (C.quotient x) =
      D.quotient (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap x.1, x.2) :=
  rfl

theorem SpecialPeriods.CuspGlobalOverlap.familyMap_injective (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Injective (familyMap C D hrcap) :=
  QuotientComparison.descend_injective C D
    (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
    (SpecialPeriods.CuspFamily.logBaseToRegular_translate C.radius hrcap)
    SpecialPeriods.triangleTorusHomeomorph_cusp_zpow
    (SpecialPeriods.CuspFamily.logBaseToRegular_injective C.radius hrcap)
    (logBaseToRegular_return C.radius hrcap)

def SpecialPeriods.CuspGlobalOverlap.familyPatch (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (basePatch C.radius hrcap : Set SpecialPeriods.TriangleRegularQuotient),
    (basePatch C.radius hrcap).isOpen.preimage D.projection_continuous⟩

theorem SpecialPeriods.CuspGlobalOverlap.familyMap_range (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Set.range (familyMap C D hrcap) = (familyPatch C D hrcap : Set D.Space) :=
  QuotientComparison.range_descend C D (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap)
    (SpecialPeriods.CuspFamily.logBaseToRegular_translate C.radius hrcap)
    SpecialPeriods.triangleTorusHomeomorph_cusp_zpow

theorem SpecialPeriods.CuspGlobalOverlap.familyMap_mem_patch (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) : familyMap C D hrcap x ∈ familyPatch C D hrcap := by
  change familyMap C D hrcap x ∈ (familyPatch C D hrcap : Set D.Space)
  rw [← familyMap_range]
  exact Set.mem_range_self x

def SpecialPeriods.CuspGlobalOverlap.familyMapInto (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) : familyPatch C D hrcap :=
  ⟨familyMap C D hrcap x, familyMap_mem_patch C D hrcap x⟩

theorem SpecialPeriods.CuspGlobalOverlap.familyMapInto_bijective
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Bijective (familyMapInto C D hrcap) := by
  constructor
  · intro x y h
    exact familyMap_injective C D hrcap (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ Set.range (familyMap C D hrcap) := by
      rw [familyMap_range]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

theorem SpecialPeriods.CuspGlobalOverlap.familyMap_isLocalDiffeomorph
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (familyMap C D hrcap) := by
  let := C.periods.totalChartedSpace
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  have hmap :=
    HolomorphicPeriodMap.periodPullbackMap_isLocalDiffeomorph C.periods D.periods
      (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap) hperiod
      (SpecialPeriods.CuspFamily.logBaseToRegular_isLocalDiffeomorph C.radius hrcap)
  have hq :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
    let := D.totalAction
    exact
      CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap (familyCovering D))
        D.totalAction_holomorphic
  apply
    isLocalDiffeomorph_of_comp_surjective (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      C.quotient_isLocalDiffeomorph C.quotient_surjective
  intro x
  exact
    (hmap x).comp (K := (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))) (P := D.Space)
      (hq (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap x.1, x.2))

theorem SpecialPeriods.CuspGlobalOverlap.familyMapInto_isLocalDiffeomorph
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (familyMapInto C D hrcap) := by
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (familyMap_isLocalDiffeomorph C D hrcap hperiod) (familyPatch C D hrcap)
      (familyMap_mem_patch C D hrcap)

def SpecialPeriods.CuspGlobalOverlap.familyBiholomorph (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) C.Space (familyPatch C D hrcap) ω := by
  letI := C.chartedSpace
  letI := D.chartedSpace (familyCovering D)
  exact
    (familyMapInto_isLocalDiffeomorph C D hrcap hperiod).diffeomorphOfBijective
      (familyMapInto_bijective C D hrcap)

def SpecialPeriods.CuspGlobalOverlap.compactProjection
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) :
    D.Space → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  compactBase ∘ D.projection

def SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    Diffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspUniformization.PuncturedQuotient C.correction C.radius) (familyPatch C D hrcap) ω := by
  letI := C.chartedSpace
  letI :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  letI := D.chartedSpace (familyCovering D)
  exact C.puncturedFamilyBiholomorph.symm.trans (familyBiholomorph C D hrcap hperiod)

theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_cover
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.LogCover C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (puncturedBiholomorph C D hrcap hperiod
          (CuspUniformization.puncturedCuspCover C.correction C.radius x) :
        D.Space) =
      familyMap C D hrcap (C.iteratedCover x) := by
  let := C.chartedSpace
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  change
    familyMap C D hrcap
        (C.puncturedFamilyBiholomorph.symm
          (CuspUniformization.puncturedCuspCover C.correction C.radius x)) =
      _
  rw [← C.puncturedFamilyBiholomorph_iteratedCover, Diffeomorph.symm_apply_apply]

theorem SpecialPeriods.CuspGlobalOverlap.familyMap_compactProjection_mem_chart
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) :
    compactProjection D (familyMap C D hrcap x) ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  exact compactBase_baseCover_mem_chart C.radius hrcap a.1

theorem SpecialPeriods.CuspGlobalOverlap.familyMap_compactProjection_coordinate
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x : C.Space) :
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactProjection D (familyMap C D hrcap x)) =
      (C.projection x : ℂ) := by
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  exact cuspFullChart_compactBase_baseCover C.radius hrcap a.1

theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_coordinate
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.PuncturedQuotient C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactProjection D (puncturedBiholomorph C D hrcap hperiod x)) =
      CuspQuotient.projection C.correction C.radius x := by
  let := C.chartedSpace
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨y, rfl⟩ := C.puncturedFamilyBiholomorph.surjective x
  change
    SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
        (compactProjection D
          (familyMap C D hrcap
            (C.puncturedFamilyBiholomorph.symm (C.puncturedFamilyBiholomorph y)))) =
      _
  rw [Diffeomorph.symm_apply_apply, familyMap_compactProjection_coordinate]
  exact (C.puncturedFamilyBiholomorph_preserves_base y).symm

theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_base_mem_chart
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.PuncturedQuotient C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (puncturedBiholomorph C D hrcap hperiod x) ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
  let := C.chartedSpace
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  exact familyMap_compactProjection_mem_chart C D hrcap (C.puncturedFamilyBiholomorph.symm x)

theorem SpecialPeriods.CuspGlobalOverlap.puncturedBiholomorph_preserves_base
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspUniformization.PuncturedQuotient C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (puncturedBiholomorph C D hrcap hperiod x) =
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (CuspQuotient.projection C.correction C.radius x) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [← puncturedBiholomorph_coordinate C D hrcap hperiod x]
  exact
    ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).left_inv
        (puncturedBiholomorph_base_mem_chart C D hrcap hperiod x)).symm

theorem SpecialPeriods.CuspGlobalOverlap.logBase_nonempty (r : ℝ) (hr : 0 < r) :
    Nonempty (SpecialPeriods.CuspFamily.LogBase r) := by
  have hhalf : 0 < r / 2 := half_pos hr
  have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
    linarith
  let t : SpecialPeriods.CuspFamily.puncturedDisc r :=
    ⟨((r / 2 : ℝ) : ℂ),
      (SpecialPeriods.CuspFamily.mem_puncturedDisc r _).mpr
        ⟨hnorm, Complex.ofReal_ne_zero.mpr hhalf.ne'⟩⟩
  obtain ⟨s, _⟩ := SpecialPeriods.CuspFamily.baseExponential_surjective r t
  exact ⟨s⟩

theorem SpecialPeriods.CuspGlobalOverlap.cyclicSpace_nonempty
    (C : SpecialPeriods.CuspFamily.Data) : Nonempty C.Space := by
  obtain ⟨s⟩ := logBase_nonempty C.radius C.radius_pos
  exact ⟨C.quotient (s, 0)⟩

theorem SpecialPeriods.CuspGlobalOverlap.puncturedSpace_nonempty
    (C : SpecialPeriods.CuspFamily.Data) :
    Nonempty (CuspUniformization.PuncturedQuotient C.correction C.radius) := by
  obtain ⟨s⟩ := logBase_nonempty C.radius C.radius_pos
  exact ⟨CuspUniformization.puncturedCuspCover C.correction C.radius ⟨((s : ℂ), 0), s.property⟩⟩

theorem SpecialPeriods.CuspGlobalOverlap.familyPatch_nonempty (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Nonempty (familyPatch C D hrcap) :=
  (cyclicSpace_nonempty C).map (familyMapInto C D hrcap)

def SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    PartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspQuotient.QuotientSpace C.correction C.radius) D.Space ω := by
  letI :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  letI := D.chartedSpace (familyCovering D)
  exact
    (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
          (CuspUniformization.puncturedQuotientOpen C.correction C.radius)
          (puncturedSpace_nonempty C)).symm.trans
      ((puncturedBiholomorph C D hrcap hperiod).toPartialDiffeomorph.trans
        (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
          (familyPatch C D hrcap) (familyPatch_nonempty C D hrcap)))

@[simp]
theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_source
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).source =
      (CuspUniformization.puncturedQuotientOpen C.correction C.radius : Set _) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  simp [cuspToRegularPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp]
theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_target
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).target = (familyPatch C D hrcap : Set D.Space) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  simp [cuspToRegularPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_source_iff
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspQuotient.QuotientSpace C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    x ∈ (cuspToRegularPartial C D hrcap hperiod).source ↔
      CuspQuotient.projection C.correction C.radius x ≠ 0 := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_source]
  rfl

theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_target_iff
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (y : D.Space) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    y ∈ (cuspToRegularPartial C D hrcap hperiod).target ↔
      compactProjection D y ∈
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source ∧
        ‖SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (compactProjection D y)‖ <
          C.radius := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_target]
  exact mem_basePatch_iff C.radius hrcap (D.projection y)

theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_apply
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : x ∈ CuspUniformization.puncturedQuotientOpen C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod x =
      (puncturedBiholomorph C D hrcap hperiod ⟨x, hx⟩ : D.Space) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  let e :=
    (CuspUniformization.puncturedQuotientOpen C.correction
          C.radius).openPartialHomeomorphSubtypeCoe
      (puncturedSpace_nonempty C)
  have he : e.symm x = ⟨x, hx⟩ :=
    e.left_inv (Set.mem_univ (⟨x, hx⟩ : CuspUniformization.PuncturedQuotient _ _))
  change (puncturedBiholomorph C D hrcap hperiod (e.symm x) : D.Space) = _
  rw [he]

theorem SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_preserves_base
    (C : SpecialPeriods.CuspFamily.Data)
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (hrcap : C.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (hperiod :
      ∀ s : SpecialPeriods.CuspFamily.LogBase C.radius,
        D.periods.point (SpecialPeriods.CuspFamily.logBaseToRegular C.radius hrcap s) =
          C.periods.point s)
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : x ∈ CuspUniformization.puncturedQuotientOpen C.correction C.radius) :
    letI :=
      CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
        C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (cuspToRegularPartial C D hrcap hperiod x) =
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (CuspQuotient.projection C.correction C.radius x) := by
  let :=
    CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one C.holomorphic
      C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_apply C D hrcap hperiod x hx]
  exact puncturedBiholomorph_preserves_base C D hrcap hperiod ⟨x, hx⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    PartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspQuotient.QuotientSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius)
      ((sphereRegularData π hπ h₀ h₁)).Space ω :=
  cuspToRegularPartial (sphereCuspData π hπ h₀ h₁ r hr hrD) (sphereRegularData π hπ h₀ h₁) hrcap
    (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_source_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x :
      CuspQuotient.QuotientSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    x ∈ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).source ↔
      CuspQuotient.projection ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
          ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius x ≠
        0 :=
  cuspToRegularPartial_source_iff (sphereCuspData π hπ h₀ h₁ r hr hrD)
    (sphereRegularData π hπ h₀ h₁) hrcap (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap) x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_target_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (y : ((sphereRegularData π hπ h₀ h₁)).Space) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    y ∈ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).target ↔
      compactProjection (sphereRegularData π hπ h₀ h₁) y ∈
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source ∧
        ‖SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (compactProjection (sphereRegularData π hπ h₀ h₁) y)‖ <
          r :=
  cuspToRegularPartial_target_iff (sphereCuspData π hπ h₀ h₁ r hr hrD)
    (sphereRegularData π hπ h₀ h₁) hrcap (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap) y

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_preserves_base
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (r : ℝ) (hr : 0 < r)
    (hrD : r ≤ (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (x :
      CuspQuotient.QuotientSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius)
    (hx :
      x ∈
        CuspUniformization.puncturedQuotientOpen ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
          ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius) :
    letI :=
      CuspQuotient.chartedSpace ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_pos
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius_lt_one
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).holomorphic
        ((sphereCuspData π hπ h₀ h₁ r hr hrD)).smallDrift
    letI :=
      ((sphereRegularData π hπ h₀ h₁)).chartedSpace
        (familyCovering (sphereRegularData π hπ h₀ h₁))
    compactProjection (sphereRegularData π hπ h₀ h₁)
        (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap x) =
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (CuspQuotient.projection ((sphereCuspData π hπ h₀ h₁ r hr hrD)).correction
          ((sphereCuspData π hπ h₀ h₁ r hr hrD)).radius x) :=
  cuspToRegularPartial_preserves_base (sphereCuspData π hπ h₀ h₁ r hr hrD)
    (sphereRegularData π hπ h₀ h₁) hrcap (spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap) x hx

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.instChartedSpace1 :
    ChartedSpace (ToricCharts.CoordinateSpace 3) SpecialCuspPiece :=
  CuspPiece.nativeChartedSpace SpecialPeriods.specialCuspData specialBaseCover
    specialCuspRadius_le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
def SpecialPeriods.Threefold.specialCuspNativeOverlap :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) SpecialCuspPiece SpecialRegularFamily ω :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
theorem SpecialPeriods.Threefold.specialCuspNativeOverlap_source_iff (x : SpecialCuspPiece) :
    x ∈ specialCuspNativeOverlap.source ↔
      CuspQuotient.projection SpecialPeriods.specialCuspData.correction
          (specialBaseCover.radius Option.none) x ≠
        0 :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_source_iff
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
theorem SpecialPeriods.Threefold.specialCuspNativeOverlap_target_iff (y : SpecialRegularFamily) :
    y ∈ specialCuspNativeOverlap.target ↔
      specialRegularFamilyProjectionToBase y ∈ (punctureChart Option.none).source ∧
        ‖punctureChart Option.none (specialRegularFamilyProjectionToBase y)‖ <
          specialBaseCover.radius Option.none :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_target_iff
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le y

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
theorem SpecialPeriods.Threefold.specialCuspNativeOverlap_base (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspNativeOverlap.source) :
    specialRegularFamilyProjectionToBase (specialCuspNativeOverlap x) =
      specialCuspPieceProjectionToBase x :=
  SpecialPeriods.CuspGlobalOverlap.sphereCuspToRegularPartial_preserves_base
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
    specialCuspRadius_le specialBaseCover_cusp_radius_bounds.2.2.le x
    ((specialCuspNativeOverlap_source_iff x).mp hx)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
def SpecialPeriods.Threefold.specialCuspOverlap :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) SpecialCuspPiece SpecialRegularFamily ω :=
  (Diffeomorph.toPartialDiffeomorph
        (CuspPiece.nativeToCommon SpecialPeriods.specialCuspData specialBaseCover
            specialCuspRadius_le).symm).trans
    specialCuspNativeOverlap

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
theorem SpecialPeriods.Threefold.specialCuspOverlap_source :
    specialCuspOverlap.source =
      specialCuspPieceProjectionToBase ⁻¹'
        (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  ext x
  change (x ∈ (Set.univ : Set SpecialCuspPiece) ∧ x ∈ specialCuspNativeOverlap.source) ↔ _
  simp only [Set.mem_univ, true_and]
  exact
    (specialCuspNativeOverlap_source_iff x).trans
      (CuspPiece.projectionToBase_mem_regular_iff SpecialPeriods.specialCuspData specialBaseCover
          x).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
theorem SpecialPeriods.Threefold.specialCuspOverlap_target :
    specialCuspOverlap.target =
      specialRegularFamilyProjectionToBase ⁻¹'
        (specialBaseCover.fillingPatch Option.none :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  ext y
  change
    (y ∈ specialCuspNativeOverlap.target ∧
        specialCuspNativeOverlap.symm y ∈ (Set.univ : Set SpecialCuspPiece)) ↔
      _
  simp only [Set.mem_univ, and_true]
  exact
    (specialCuspNativeOverlap_target_iff y).trans
      (specialBaseCover.mem_fillingPatch Option.none
          (specialRegularFamilyProjectionToBase y)).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialCuspPieceChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace in
attribute [local instance] SpecialPeriods.Threefold.instChartedSpace1 in
theorem SpecialPeriods.Threefold.specialCuspOverlap_base (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspOverlap.source) :
    specialRegularFamilyProjectionToBase (specialCuspOverlap x) =
      specialCuspPieceProjectionToBase x :=
  specialCuspNativeOverlap_base x hx.2

def CuspUniformization.localLog (z0 z : ℂ) : ℂ :=
  logarithm z0 + logarithm (z / z0)

theorem CuspUniformization.localLog_contDiffAt_of_mem_slitPlane {z0 z : ℂ}
    (hz : z / z0 ∈ Complex.slitPlane) : ContDiffAt ℂ ω (localLog z0) z := by
  change
    ContDiffAt ℂ ω (fun w : ℂ => logarithm z0 + Complex.log (w / z0) / (2 * Real.pi * Complex.I))
      z
  exact
    contDiffAt_const.add
      (((Complex.contDiffAt_log hz).comp z (contDiffAt_id.div_const z0)).div_const _)

theorem CuspUniformization.localLog_contDiffAt {z0 : ℂ} (hz0 : z0 ≠ 0) :
    ContDiffAt ℂ ω (localLog z0) z0 :=
  localLog_contDiffAt_of_mem_slitPlane (by simp [hz0])

theorem CuspUniformization.exponential_localLog {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    exponential (localLog z0 z) = z := by
  rw [localLog, exponential_add, exponential_logarithm hz0,
    exponential_logarithm (div_ne_zero hz hz0), mul_div_cancel₀ _ hz0]

theorem CuspUniformization.logarithm_eq_localLog_add_int {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    ∃ n : ℤ, logarithm z = localLog z0 z + n := by
  apply (exponential_eq_iff (logarithm z) (localLog z0 z)).mp
  rw [exponential_logarithm hz, exponential_localLog hz0 hz]

def Elliptic.LogGauge.baseOpen : TopologicalSpace.Opens SpecialPeriods.Disc :=
  ⟨{z | (z : ℂ) ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

abbrev Elliptic.LogGauge.BaseStar :=
  baseOpen

def Elliptic.LogGauge.familyOpen : TopologicalSpace.Opens (SpecialPeriods.Disc × RealTorus₄) :=
  ⟨{x | (x.1 : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const⟩

abbrev Elliptic.LogGauge.FamilyStar (_P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :=
  familyOpen

def Elliptic.LogGauge.coverOpen : TopologicalSpace.Opens (SpecialPeriods.Disc × ComplexPlane₂) :=
  ⟨{x | (x.1 : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp continuous_fst) continuous_const⟩

abbrev Elliptic.LogGauge.CoverStar :=
  coverOpen

def Elliptic.LogGauge.project (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (x : CoverStar) :
    FamilyStar P :=
  ⟨P.quotientMap x, x.2⟩

theorem Elliptic.LogGauge.project_surjective (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :
    Function.Surjective (project P) := by
  intro x
  obtain ⟨y, hy⟩ := P.quotientMap_surjective x.1
  have hy0 : (y.1 : ℂ) ≠ 0 := by
    have hb : y.1 = x.1.1 := congrArg Prod.fst hy
    rw [hb]
    exact x.2
  exact ⟨⟨y, hy0⟩, Subtype.ext hy⟩

def Elliptic.LogGauge.periodVector (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice)
    (z : SpecialPeriods.Disc) : ComplexPlane₂ :=
  P.periodEquiv z (Elliptic.realCast v)

@[simp]
theorem Elliptic.LogGauge.periodVector_neg (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) (z : SpecialPeriods.Disc) : periodVector P (-v) z = -periodVector P v z := by
  change P.periodEquiv z (Elliptic.realCast (-v)) = -P.periodEquiv z (Elliptic.realCast v)
  rw [show Elliptic.realCast (-v) = -Elliptic.realCast v by ext i; simp [Elliptic.realCast],
    map_neg]

theorem Elliptic.LogGauge.periodVector_mem_lattice
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) (z : SpecialPeriods.Disc) :
    periodVector P v z ∈ (P.point z).lattice := by
  rw [← P.periodEquiv_map_lattice z]
  exact
    Submodule.mem_map.mpr
      ⟨Elliptic.realCast v, (Elliptic.standardLattice_mem_iff _).mpr ⟨v, rfl⟩, rfl⟩

theorem Elliptic.LogGauge.periodVector_holomorphic
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (periodVector P v) :=
  P.holomorphic_periodEquiv_const (Elliptic.realCast v)

theorem Elliptic.LogGauge.quotientMap_integer_period
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) (z : SpecialPeriods.Disc)
    (u : ComplexPlane₂) (a : ℂ) (n : ℤ) :
    P.quotientMap (z, u + (a + n) • periodVector P v z) =
      P.quotientMap (z, u + a • periodVector P v z) := by
  rw [← P.fibreInclusion_mkQ, ← P.fibreInclusion_mkQ]
  apply congrArg (P.fibreInclusion z)
  apply (Submodule.Quotient.eq _).mpr
  have hp := (P.point z).lattice.smul_mem n (periodVector_mem_lattice P v z)
  convert hp using 1
  rw [add_smul, Int.cast_smul_eq_zsmul]
  abel

theorem Elliptic.LogGauge.quotientMap_eq_of_scalar_int
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) (z : SpecialPeriods.Disc)
    (u : ComplexPlane₂) {a b : ℂ} (hab : ∃ n : ℤ, a = b + n) :
    P.quotientMap (z, u + a • periodVector P v z) =
      P.quotientMap (z, u + b • periodVector P v z) := by
  obtain ⟨n, rfl⟩ := hab
  exact quotientMap_integer_period P v z u b n

def Elliptic.LogGauge.sectionCoordinate (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) (z : SpecialPeriods.Disc) : RealTorus₄ :=
  standardLattice.mkQ
    ((P.periodEquiv z).symm (CuspUniformization.logarithm z • periodVector P v z))

@[simp]
theorem Elliptic.LogGauge.sectionCoordinate_neg (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) (z : SpecialPeriods.Disc) :
    sectionCoordinate P (-v) z = -sectionCoordinate P v z := by
  simp only [sectionCoordinate, periodVector_neg, smul_neg, map_neg]

def Elliptic.LogGauge.gaugeMap (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice)
    (x : FamilyStar P) : FamilyStar P :=
  ⟨(x.1.1, x.1.2 + sectionCoordinate P v x.1.1), x.2⟩

@[simp]
theorem Elliptic.LogGauge.gaugeMap_neg_gaugeMap (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) (x : FamilyStar P) : gaugeMap P (-v) (gaugeMap P v x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (x.1.2 + sectionCoordinate P v x.1.1) + sectionCoordinate P (-v) x.1.1 = x.1.2
    rw [sectionCoordinate_neg, add_neg_cancel_right]

def Elliptic.LogGauge.gaugeEquiv (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) :
    Equiv.Perm (FamilyStar P) where
  toFun := gaugeMap P v
  invFun := gaugeMap P (-v)
  left_inv := gaugeMap_neg_gaugeMap P v
  right_inv x := by simpa only [neg_neg] using gaugeMap_neg_gaugeMap P (-v) x

def Elliptic.LogGauge.gaugeLift (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice)
    (a : ℂ → ℂ) (x : CoverStar) : CoverStar :=
  ⟨(x.1.1, x.1.2 + a x.1.1 • periodVector P v x.1.1), x.2⟩

@[simp]
theorem Elliptic.LogGauge.gaugeMap_project (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) (x : CoverStar) :
    gaugeMap P v (project P x) = project P (gaugeLift P v CuspUniformization.logarithm x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change
    standardLattice.mkQ ((P.periodEquiv x.1.1).symm x.1.2) +
        standardLattice.mkQ
          ((P.periodEquiv x.1.1).symm
            (CuspUniformization.logarithm x.1.1 • periodVector P v x.1.1)) =
      standardLattice.mkQ
        ((P.periodEquiv x.1.1).symm
          (x.1.2 + CuspUniformization.logarithm x.1.1 • periodVector P v x.1.1))
  rw [map_add, map_add]

theorem Elliptic.LogGauge.gaugeMap_project_localLog
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (x : CoverStar) :
    gaugeMap P v (project P x) = project P (gaugeLift P v (CuspUniformization.localLog z₀) x) := by
  rw [gaugeMap_project]
  apply Subtype.ext
  exact
    quotientMap_eq_of_scalar_int P v x.1.1 x.1.2
      (CuspUniformization.logarithm_eq_localLog_add_int hz₀ x.2)

def Elliptic.LogGauge.zeroSection (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (z : BaseStar) : FamilyStar P :=
  ⟨(z.1, 0), z.2⟩

def Elliptic.LogGauge.sectionMap (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) :
    BaseStar → FamilyStar P :=
  gaugeMap P v ∘ zeroSection P

theorem Elliptic.LogGauge.sectionMap_formula (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) (z : BaseStar) :
    (sectionMap P v z : P.TotalSpace) =
      P.quotientMap (z.1, CuspUniformization.logarithm z.1 • periodVector P v z.1) := by
  apply Prod.ext
  · rfl
  · exact zero_add _

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.neighborhoodPoint (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : SpecialPeriods.Triangle.ellipticNeighborhood j :=
  (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.neighborhoodPoint_ne_center (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    neighborhoodPoint j z ≠ SpecialPeriods.Triangle.ellipticNeighborhoodCenter j := by
  intro he
  have hc := congrArg (SpecialPeriods.Triangle.ellipticNeighborhoodChart j) he
  have hz : z.val = SpecialPeriods.discZero := by
    simpa only [neighborhoodPoint, Diffeomorph.apply_symm_apply,
      SpecialPeriods.Triangle.ellipticNeighborhoodChart_center] using hc
  exact z.property (congrArg (fun u : SpecialPeriods.Disc => (u : ℂ)) hz)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_regular (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (neighborhoodPoint j z : ℍ) ∈ SpecialPeriods.triangleRegularLocus := by
  have hself :
    SpecialPeriods.triangleOrbitProjection (neighborhoodPoint j z) ≠
      SpecialPeriods.Triangle.ellipticOrbitCenter j :=
    fun he =>
    neighborhoodPoint_ne_center j z
      ((SpecialPeriods.Triangle.ellipticNeighborhood_projection_eq_center_iff j
            (neighborhoodPoint j z)).mp
        he)
  have hother :=
    SpecialPeriods.Triangle.ellipticNeighborhood_avoids_other j (neighborhoodPoint j z)
      (neighborhoodPoint j z).property
  apply (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff _).mp
  apply (SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mpr
  cases j
  · exact ⟨hself, hother⟩
  · exact ⟨hother, hself⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.localBase (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : SpecialPeriods.TriangleRegularPoint :=
  ⟨neighborhoodPoint j z, localBase_regular j z⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.EllipticFilling.localBase_val (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (localBase j z : ℍ) =
      ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val : ℍ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_mem_neighborhood (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (localBase j z : ℍ) ∈ SpecialPeriods.Triangle.ellipticNeighborhood j :=
  (neighborhoodPoint j z).property

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_injective (j : Elliptic.Kind) :
    Function.Injective (localBase j) := by
  intro z w he
  have hv : (localBase j z : ℍ) = (localBase j w : ℍ) :=
    congrArg (fun u : SpecialPeriods.TriangleRegularPoint => (u : ℍ)) he
  have hn :
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val =
      (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm w.val :=
    Subtype.ext hv
  exact Subtype.ext ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm.injective hn)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_isLocalDiffeomorph (j : Elliptic.Kind) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (localBase j) := by
  have hn : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (neighborhoodPoint j) := by
    intro z
    exact
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) Elliptic.LogGauge.baseOpen z).comp (K := 𝓘(ℂ)) (P :=
        SpecialPeriods.Triangle.ellipticNeighborhood j)
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm.isLocalDiffeomorph z.val)
  have hv :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : Elliptic.LogGauge.BaseStar => (neighborhoodPoint j z : ℍ)) := by
    intro z
    exact
      (hn z).comp (K := 𝓘(ℂ)) (P := ℍ)
        (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (SpecialPeriods.Triangle.ellipticNeighborhood j)
          (neighborhoodPoint j z))
  exact
    isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) hv SpecialPeriods.triangleRegularDomain
      (localBase_regular j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (localBase j) :=
  (localBase_isLocalDiffeomorph j).contMDiff

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_continuous (j : Elliptic.Kind) :
    Continuous (localBase j) :=
  (localBase_holomorphic j).continuous

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.ellipticCenter_not_regular (j : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticCenter j ∉ SpecialPeriods.triangleRegularLocus := by
  cases j
  · exact SpecialPeriods.triangle_centerOne_not_regular
  · exact SpecialPeriods.triangle_centerTwo_not_regular

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.neighborhoodChart_ne_zero_of_regular (j : Elliptic.Kind)
    (u : SpecialPeriods.Triangle.ellipticNeighborhood j)
    (hu : (u : ℍ) ∈ SpecialPeriods.triangleRegularLocus) :
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j u : ℂ) ≠ 0 := by
  intro he
  have hchart : SpecialPeriods.Triangle.ellipticNeighborhoodChart j u = SpecialPeriods.discZero :=
    Subtype.ext he
  have huc : u = SpecialPeriods.Triangle.ellipticNeighborhoodCenter j :=
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).injective
      (hchart.trans (SpecialPeriods.Triangle.ellipticNeighborhoodChart_center j).symm)
  have hc : (u : ℍ) = SpecialPeriods.Triangle.ellipticCenter j := congrArg Subtype.val huc
  exact ellipticCenter_not_regular j (hc ▸ hu)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_range (j : Elliptic.Kind) :
    Set.range (localBase j) =
      {u : SpecialPeriods.TriangleRegularPoint |
        (u : ℍ) ∈ SpecialPeriods.Triangle.ellipticNeighborhood j} := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    exact localBase_mem_neighborhood j z
  · intro hu
    let v : SpecialPeriods.Triangle.ellipticNeighborhood j := ⟨u.val, hu⟩
    let z : Elliptic.LogGauge.BaseStar :=
      ⟨SpecialPeriods.Triangle.ellipticNeighborhoodChart j v,
        neighborhoodChart_ne_zero_of_regular j v u.property⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change
      ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm
            (SpecialPeriods.Triangle.ellipticNeighborhoodChart j v) :
          ℍ) =
        (u : ℍ)
    exact
      congrArg (fun q : SpecialPeriods.Triangle.ellipticNeighborhood j => (q : ℍ))
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm_apply_apply v)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.puncturedRotation (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : Elliptic.LogGauge.BaseStar :=
  ⟨Elliptic.familyRotation j z.val, Elliptic.LogGauge.familyRotation_ne_zero j z.val z.property⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.EllipticFilling.puncturedRotation_val (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    (puncturedRotation j z).val = Elliptic.familyRotation j z.val :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_rotation (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    localBase j (puncturedRotation j z) =
      SpecialPeriods.Triangle.ellipticGenerator j • localBase j z := by
  let := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
  have he :
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z.val) =
      SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
        (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val := by
    apply (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).injective
    change
      SpecialPeriods.Triangle.ellipticNeighborhoodChart j
          ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm
            (Elliptic.familyRotation j z.val)) =
        SpecialPeriods.Triangle.ellipticNeighborhoodChart j
          (SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
            (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val)
    rw [Diffeomorph.apply_symm_apply, SpecialPeriods.Triangle.ellipticNeighborhoodChart_generator,
      Diffeomorph.apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun u : SpecialPeriods.Triangle.ellipticNeighborhood j => (u : ℍ)) he

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_rotation_iterate (j : Elliptic.Kind) (n : ℕ)
    (z : Elliptic.LogGauge.BaseStar) :
    localBase j ((puncturedRotation j)^[n] z) =
      SpecialPeriods.Triangle.ellipticGenerator j ^ n • localBase j z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', localBase_rotation, ih, pow_succ', SemigroupAction.mul_smul]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.baseQuotient (j : Elliptic.Kind) :
    Elliptic.LogGauge.BaseStar → SpecialPeriods.TriangleRegularQuotient :=
  SpecialPeriods.triangleRegularProject ∘ localBase j

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.EllipticFilling.baseQuotient_toOrbit (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    SpecialPeriods.triangleRegularToOrbit (baseQuotient j z) =
      SpecialPeriods.triangleOrbitProjection (localBase j z : ℍ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localBase_orbit_classification (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup) (z w : Elliptic.LogGauge.BaseStar)
    (h : g • localBase j z = localBase j w) :
    ∃ n : ℕ,
      n < j.order ∧
        g = SpecialPeriods.Triangle.ellipticGenerator j ^ n ∧ w = (puncturedRotation j)^[n] z := by
  have hambient : g • (localBase j z : ℍ) = (localBase j w : ℍ) := congrArg Subtype.val h
  have hg : g ∈ SpecialPeriods.Triangle.ellipticStabilizer j :=
    SpecialPeriods.Triangle.ellipticNeighborhood_return j g
      ⟨(localBase j w : ℍ), ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z, hambient⟩,
        localBase_mem_neighborhood j w⟩
  obtain ⟨n, hn, rfl⟩ := (SpecialPeriods.Triangle.mem_ellipticStabilizer_iff j g).mp hg
  refine ⟨n, hn, rfl, ?_⟩
  apply localBase_injective j
  exact ((localBase_rotation_iterate j n z).trans h).symm

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.ellipticFullChart_localBase (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleOrbitProjection (localBase j z : ℍ)) =
      (z.val : ℂ) ^ j.order := by
  rw [localBase_val, SpecialPeriods.Triangle.ellipticFullChart_projection]
  change
    ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j
              ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z.val) :
            SpecialPeriods.Disc) :
          ℂ) ^
        j.order =
      _
  rw [Diffeomorph.apply_symm_apply]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.ellipticFullChart_baseQuotient (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit (baseQuotient j z)) =
      (z.val : ℂ) ^ j.order :=
  ellipticFullChart_localBase j z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.regularBasePatch (j : Elliptic.Kind) :
    TopologicalSpace.Opens SpecialPeriods.TriangleRegularQuotient :=
  ⟨SpecialPeriods.triangleRegularToOrbit ⁻¹'
      (SpecialPeriods.Triangle.ellipticNeighborhoodImage j :
        Set SpecialPeriods.TriangleOrbitSpace),
    (SpecialPeriods.Triangle.ellipticNeighborhoodImage j).isOpen.preimage
      SpecialPeriods.triangleRegularToOrbit_continuous⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.baseQuotient_mem_regularBasePatch (j : Elliptic.Kind)
    (z : Elliptic.LogGauge.BaseStar) : baseQuotient j z ∈ regularBasePatch j :=
  ⟨(localBase j z : ℍ), localBase_mem_neighborhood j z, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.baseQuotient_range (j : Elliptic.Kind) :
    Set.range (baseQuotient j) =
      (regularBasePatch j : Set SpecialPeriods.TriangleRegularQuotient) := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact baseQuotient_mem_regularBasePatch j z
  · rintro ⟨u, hu, he⟩
    change
      SpecialPeriods.triangleOrbitProjection u = SpecialPeriods.triangleRegularToOrbit q at he
    have hreg : u ∈ SpecialPeriods.triangleRegularLocus := by
      apply (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff u).mp
      rw [he]
      exact ⟨q, rfl⟩
    have hin : (⟨u, hreg⟩ : SpecialPeriods.TriangleRegularPoint) ∈ Set.range (localBase j) := by
      rw [localBase_range]
      exact hu
    obtain ⟨z, hz⟩ := hin
    refine ⟨z, SpecialPeriods.triangleRegularToOrbit_injective ?_⟩
    rw [baseQuotient_toOrbit, hz]
    exact he

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.regularBasePatch_mem_iff_compactifiedChart
    (j : Elliptic.Kind) (q : SpecialPeriods.TriangleRegularQuotient) :
    q ∈ regularBasePatch j ↔
      SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleRegularToOrbit q) ∈
        (SpecialPeriods.Triangle.ellipticCompactifiedChart j).source := by
  rw [SpecialPeriods.Triangle.openInclusion_mem_ellipticCompactifiedChart_source,
    SpecialPeriods.Triangle.ellipticFullChart_source]
  rfl

def Elliptic.LogGauge.starPermutation {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) : Equiv.Perm (FamilyStar D.periods) :=
  (D.permutation v).subtypeEquiv
    (fun x => by
      change (x.1 : ℂ) ≠ 0 ↔ (Elliptic.familyRotation j x.1 : ℂ) ≠ 0
      rw [familyRotation_val_exponential, mul_ne_zero_iff]
      exact ⟨fun hx => ⟨CuspUniformization.exponential_ne_zero _, hx⟩, fun hx => hx.2⟩)

@[simp]
theorem Elliptic.LogGauge.starPermutation_coe {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (x : FamilyStar D.periods) :
    (starPermutation D v x : D.TotalSpace) = D.permutation v x :=
  rfl

def Elliptic.LogGauge.starLift {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) (v : PeriodLattice)
    (x : CoverStar) : CoverStar :=
  ⟨D.complexLift v x, familyRotation_ne_zero j x.1.1 x.2⟩

@[simp]
theorem Elliptic.LogGauge.starPermutation_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (x : CoverStar) :
    starPermutation D v (project D.periods x) = project D.periods (starLift D v x) := by
  apply Subtype.ext
  exact (D.complexLift_quotientMap v x).symm

theorem Elliptic.LogGauge.periodVector_covariance {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (z : SpecialPeriods.Disc) :
    Elliptic.linearMatrix j (D.periods.point z) *ᵥ periodVector D.periods v z =
      periodVector D.periods v (Elliptic.familyRotation j z) := by
  have h := D.periodEquiv_flatLinear z (Elliptic.realCast v)
  rw [Elliptic.flatLinear_fixes_realCast j v hv] at h
  exact h.symm

theorem Elliptic.LogGauge.complexLift_translation {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (z : SpecialPeriods.Disc) :
    D.periods.periodEquiv z ((1 / (j.order : ℝ)) • Elliptic.realCast v) =
      (1 / (j.order : ℂ)) • periodVector D.periods v z := by
  rw [map_smul]
  ext i
  simp only [periodVector, Pi.smul_apply, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, smul_eq_mul]

theorem Elliptic.LogGauge.complexLift_formula {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (z : SpecialPeriods.Disc)
    (u : ComplexPlane₂) :
    D.complexLift v (z, u) =
      (Elliptic.familyRotation j z,
        Elliptic.linearMatrix j (D.periods.point z) *ᵥ u +
          (1 / (j.order : ℂ)) • periodVector D.periods v (Elliptic.familyRotation j z)) := by
  unfold Elliptic.Equivariant.Data.complexLift
  rw [complexLift_translation]

theorem Elliptic.LogGauge.periodVector_zero {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (z : SpecialPeriods.Disc) : periodVector D.periods 0 z = 0 := by
  change D.periods.periodEquiv z (Elliptic.realCast 0) = 0
  rw [show Elliptic.realCast 0 = 0 by ext i; simp [Elliptic.realCast], map_zero]

theorem Elliptic.LogGauge.gaugeLift_starLift_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) (x : CoverStar) :
    project D.periods (gaugeLift D.periods v CuspUniformization.logarithm (starLift D v x)) =
      project D.periods (starLift D 0 (gaugeLift D.periods v CuspUniformization.logarithm x)) := by
  apply Subtype.ext
  change
    D.periods.quotientMap
        (Elliptic.familyRotation j x.1.1,
          (D.complexLift v x.1).2 +
            CuspUniformization.logarithm (Elliptic.familyRotation j x.1.1 : ℂ) •
              periodVector D.periods v (Elliptic.familyRotation j x.1.1)) =
      D.periods.quotientMap
        (D.complexLift 0
          (x.1.1,
            x.1.2 + CuspUniformization.logarithm (x.1.1 : ℂ) • periodVector D.periods v x.1.1))
  rw [show x.1 = (x.1.1, x.1.2) by rfl, complexLift_formula, complexLift_formula]
  simp only [periodVector_zero, smul_zero, add_zero, Matrix.mulVec_add, Matrix.mulVec_smul,
    periodVector_covariance D v hv]
  rw [add_assoc, ← add_smul]
  apply
    quotientMap_eq_of_scalar_int D.periods v (Elliptic.familyRotation j x.1.1)
      (Elliptic.linearMatrix j (D.periods.point x.1.1) *ᵥ x.1.2)
  obtain ⟨n, hn⟩ := logarithm_familyRotation j x.1.1 x.2
  exact ⟨n, by rw [hn]; ring⟩

theorem Elliptic.LogGauge.gaugeMap_intertwines {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    gaugeMap D.periods v (starPermutation D v x) = starPermutation D 0 (gaugeMap D.periods v x) :=
  by
  obtain ⟨y, rfl⟩ := project_surjective D.periods x
  rw [starPermutation_project, gaugeMap_project, gaugeMap_project, starPermutation_project]
  exact gaugeLift_starLift_project D v hv y

theorem Elliptic.LogGauge.starPermutation_iterate_coe {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (r : ℕ) (x : FamilyStar D.periods) :
    ((starPermutation D v)^[r] x : D.TotalSpace) = (D.permutation v)^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', starPermutation_coe, ih]

theorem Elliptic.LogGauge.starPermutation_pow_order {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    starPermutation D v ^ j.order = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change ((starPermutation D v ^ j.order) x : D.TotalSpace) = x
  rw [Equiv.Perm.coe_pow, starPermutation_iterate_coe, ← Equiv.Perm.coe_pow,
    D.permutation_pow_order v hv]
  rfl

@[instance_reducible]
def Elliptic.LogGauge.starAction {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (Elliptic.CyclicGroup j) (FamilyStar D.periods) :=
  Elliptic.CyclicAction.action (starPermutation D v) (starPermutation_pow_order D v hv)

theorem Elliptic.LogGauge.starAction_coe {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) (g : Elliptic.CyclicGroup j)
    (x : FamilyStar D.periods) :
    letI := D.action v hv
    letI := starAction D v hv
    ((g • x : FamilyStar D.periods) : D.TotalSpace) = g • (x : D.TotalSpace) := by
  let := D.action v hv
  let := starAction D v hv
  change
    ((starPermutation D v ^ g.toAdd.val) x : D.TotalSpace) =
      (D.permutation v ^ g.toAdd.val) (x : D.TotalSpace)
  rw [Equiv.Perm.coe_pow, starPermutation_iterate_coe, Equiv.Perm.coe_pow]

theorem Elliptic.LogGauge.gaugeMap_starAction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : FamilyStar D.periods) :
    gaugeMap D.periods v (@SMul.smul _ _ (starAction D v hv).toSMul g x) =
      @SMul.smul _ _ (starAction D 0 (by simp)).toSMul g (gaugeMap D.periods v x) := by
  have h : Function.Semiconj (gaugeMap D.periods v) (starPermutation D v) (starPermutation D 0) :=
    gaugeMap_intertwines D v hv
  change
    gaugeMap D.periods v ((starPermutation D v ^ g.toAdd.val) x) =
      (starPermutation D 0 ^ g.toAdd.val) (gaugeMap D.periods v x)
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact h.iterate_right g.toAdd.val x

theorem Elliptic.LogGauge.starAction_free {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    IsCancelSMul (Elliptic.CyclicGroup j) (FamilyStar D.periods) := by
  let := starAction D v hv
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  let := D.action v hv
  have hc : g • (x : D.TotalSpace) = (x : D.TotalSpace) :=
    (starAction_coe D v hv g x).symm.trans (congrArg Subtype.val hx)
  have hb : (Elliptic.familyRotation j)^[g.toAdd.val] x.1.1 = x.1.1 := by
    simpa only [D.action_apply v hv g] using congrArg Prod.fst hc
  have hg : g.toAdd.val = 0 := by
    by_contra hg
    have hz :=
      (Elliptic.familyRotation_iterate_fixed_iff j g.toAdd.val (Nat.pos_of_ne_zero hg)
            (ZMod.val_lt _) x.1.1).mp
        hb
    exact x.2 (congrArg Subtype.val hz)
  apply Multiplicative.ext
  exact (ZMod.val_eq_zero _).mp hg

theorem Elliptic.LogGauge.starAction_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    letI := starAction D v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fun x : FamilyStar D.periods => g • x) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  let := D.action v hv
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
        (fun y : FamilyStar D.periods => ((g • y : FamilyStar D.periods) : D.TotalSpace)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fun y : FamilyStar D.periods => g • y)
        x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  have h :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun y : FamilyStar D.periods => g • (y : D.TotalSpace)) :=
    (D.action_holomorphic v hv g).comp contMDiff_subtype_val
  simpa only [starAction_coe] using h x

theorem Elliptic.LogGauge.starAction_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    ContinuousConstSMul (Elliptic.CyclicGroup j) (FamilyStar D.periods) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  exact ⟨fun g => (starAction_holomorphic D v hv g).continuous⟩

@[instance_reducible]
def Elliptic.LogGauge.gaugeCoveringChartedSpace :
    ChartedSpace Elliptic.FamilyModel (SpecialPeriods.Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (SpecialPeriods.Disc × ComplexPlane₂))

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace in
theorem Elliptic.LogGauge.gaugeCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (SpecialPeriods.Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := (modelWithCornersSelf ℂ ℂ)) (I' :=
      (modelWithCornersSelf ℂ ComplexPlane₂)) SpecialPeriods.Disc ComplexPlane₂

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
theorem Elliptic.LogGauge.project_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :
    letI := P.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (project P) := by
  let := P.totalChartedSpace
  let := P.coveringAction
  have hq :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω P.quotientMap :=
    CoveringQuotient.project_isLocalDiffeomorph P.quotientCoveringMap P.coveringAction_holomorphic
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) hq coverOpen familyOpen (fun _ hx => hx)

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
theorem Elliptic.LogGauge.project_holomorphic (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (project P) := by
  let := P.totalChartedSpace
  exact (project_isLocalDiffeomorph P).contMDiff

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
theorem Elliptic.LogGauge.gaugeLift_holomorphicAt (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) {a : ℂ → ℂ} {x : CoverStar} (ha : ContDiffAt ℂ ω a (x.1.1 : ℂ)) :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeLift P v a) x := by
  have hb :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun y : CoverStar => y.1.1) := by
    have hfst :
      ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
        (Prod.fst : SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.Disc) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_fst
    exact hfst.comp contMDiff_subtype_val
  have hw :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun y : CoverStar => y.1.2) := by
    have hsnd :
      ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ ComplexPlane₂) ω
        (Prod.snd : SpecialPeriods.Disc × ComplexPlane₂ → ComplexPlane₂) := by
      rw [modelWithCornersSelf_prod]
      exact contMDiff_snd
    exact hsnd.comp contMDiff_subtype_val
  have hbc :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun y : CoverStar => (y.1.1 : ℂ)) :=
    contMDiff_subtype_val.comp hb
  have hscalar :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun y : CoverStar => a y.1.1) x :=
    ha.contMDiffAt.comp x hbc.contMDiffAt
  have hp :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun y : CoverStar => periodVector P v y.1.1) :=
    (periodVector_holomorphic P v).comp hb
  have hsum :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun y : CoverStar => y.1.2 + a y.1.1 • periodVector P v y.1.1) x :=
    hw.contMDiffAt.add (hscalar.smul hp.contMDiffAt)
  have hpair :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (fun y : CoverStar => (y.1.1, y.1.2 + a y.1.1 • periodVector P v y.1.1)) x := by
    simpa only [← modelWithCornersSelf_prod] using hb.contMDiffAt.prodMk hsum
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (Subtype.val ∘ gaugeLift P v a) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeLift P v a) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp hpair

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
theorem Elliptic.LogGauge.gaugeMap_comp_project_holomorphic
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeMap P v ∘ project P) := by
  let := P.totalChartedSpace
  intro x
  have hl := gaugeLift_holomorphicAt P v (x := x) (CuspUniformization.localLog_contDiffAt x.2)
  have h := (project_holomorphic P).contMDiffAt.comp x hl
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (gaugeMap_project_localLog P v x.2)

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
theorem Elliptic.LogGauge.gaugeMap_holomorphic (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (gaugeMap P v) := by
  let := P.totalChartedSpace
  exact
    contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (project_isLocalDiffeomorph P) (project_surjective P)
      (gaugeMap_comp_project_holomorphic P v)

attribute [local instance] Elliptic.LogGauge.gaugeCoveringChartedSpace
    Elliptic.LogGauge.gaugeCoveringManifold in
theorem Elliptic.LogGauge.gaugeMap_continuous (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc)
    (v : PeriodLattice) : Continuous (gaugeMap P v) := by
  let := P.totalChartedSpace
  exact (gaugeMap_holomorphic P v).continuous

def Elliptic.LogGauge.restrictedProject (G : Type*) [Group G] {M : Type*} [TopologicalSpace M]
    [MulAction G M] (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    (x : U) : V :=
  ⟨Elliptic.FiniteQuotient.project G M x,
    by
    change
      (x : M) ∈
        Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M))
    rw [hpre]
    exact x.2⟩

theorem Elliptic.LogGauge.restrictedProject_surjective (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M)) :
    Function.Surjective (restrictedProject G U V hpre) := by
  intro y
  obtain ⟨x, hx⟩ := Elliptic.FiniteQuotient.project_surjective G M y.1
  have hxU : x ∈ (U : Set M) := by
    rw [← hpre]
    change Elliptic.FiniteQuotient.project G M x ∈ (V : Set (Elliptic.FiniteQuotient.Space G M))
    rw [hx]
    exact y.2
  exact ⟨⟨x, hxU⟩, Subtype.ext hx⟩

def Elliptic.LogGauge.openQuotientEquiv (G : Type*) [Group G] {M : Type*} [TopologicalSpace M]
    [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M)) :
    Elliptic.FiniteQuotient.Space G U ≃ V :=
  (Equiv.subtypeQuotientEquivQuotientSubtype (fun x : M => x ∈ (U : Set M)) (s₁ :=
      MulAction.orbitRel G M) (s₂ := MulAction.orbitRel G U)
      (fun y => y ∈ (V : Set (Elliptic.FiniteQuotient.Space G M)))
      (by
        intro x
        change x ∈ (U : Set M) ↔ x ∈ Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set _)
        rw [hpre])
      (by
        intro x y
        change (x ∈ MulAction.orbit G y) ↔ ((x : M) ∈ MulAction.orbit G (y : M))
        constructor
        · rintro ⟨g, hg⟩
          exact ⟨g, (hcompat g y).symm.trans (congrArg Subtype.val hg)⟩
        · rintro ⟨g, hg⟩
          exact ⟨g, Subtype.ext ((hcompat g y).trans hg)⟩)).symm

@[simp]
theorem Elliptic.LogGauge.openQuotientEquiv_project (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    (x : U) :
    openQuotientEquiv G U V hcompat hpre (Elliptic.FiniteQuotient.project G U x) =
      restrictedProject G U V hpre x :=
  rfl

@[simp]
theorem Elliptic.LogGauge.openQuotientEquiv_symm_restrictedProject (G : Type*) [Group G]
    {M : Type*} [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M)
    [MulAction G U] (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    (x : U) :
    (openQuotientEquiv G U V hcompat hpre).symm (restrictedProject G U V hpre x) =
      Elliptic.FiniteQuotient.project G U x := by
  rw [← openQuotientEquiv_project G U V hcompat hpre x, Equiv.symm_apply_apply]

theorem Elliptic.LogGauge.subtypeAction_isCancelSMul (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) [IsCancelSMul G M] :
    IsCancelSMul G U where
  right_cancel' g h x
    he := by
    apply IsCancelSMul.right_cancel g h (x : M)
    simpa only [hcompat] using congrArg Subtype.val he

theorem Elliptic.LogGauge.subtypeAction_holomorphic (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    (g : G) :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : U => g • x) := by
  intro x
  have hi :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
        (fun y : U => ((g • y : U) : M)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun y : U => g • y)
        x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply hi.mp
  simpa only [hcompat, Function.comp_def] using
    ((hM g).comp contMDiff_subtype_val).contMDiffAt (x := x)

theorem Elliptic.LogGauge.subtypeAction_continuousConstSMul (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) :
    ContinuousConstSMul G U where
  continuous_const_smul g := (subtypeAction_holomorphic G U hcompat hM g).continuous

theorem Elliptic.LogGauge.restrictedProject_isLocalDiffeomorph (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M] :
    letI := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
    IsLocalDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (restrictedProject G U V hpre) := by
  let := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
  have hUV : Set.MapsTo (Elliptic.FiniteQuotient.project G M) (U : Set M) (V : Set _) := by
    intro x hx
    change x ∈ Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set _)
    rwa [hpre]
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (CoveringQuotient.project_isLocalDiffeomorph
        (Elliptic.FiniteQuotient.project_isQuotientCoveringMap G M) hM)
      U V hUV

def Elliptic.LogGauge.openQuotientBiholomorph (G : Type*) [Group G] {M : Type*}
    [TopologicalSpace M] [MulAction G M] (U : TopologicalSpace.Opens M) [MulAction G U]
    (V : TopologicalSpace.Opens (Elliptic.FiniteQuotient.Space G M))
    (hcompat : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hpre :
      Elliptic.FiniteQuotient.project G M ⁻¹' (V : Set (Elliptic.FiniteQuotient.Space G M)) =
        (U : Set M))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    (hM :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x))
    [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M] :
    letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    letI := subtypeAction_continuousConstSMul G U hcompat hM
    letI := subtypeAction_isCancelSMul G U hcompat
    letI := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
    letI := Elliptic.FiniteQuotient.chartedSpace (E := E) G U
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (Elliptic.FiniteQuotient.Space G U) V ω := by
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let := subtypeAction_continuousConstSMul G U hcompat hM
  let := subtypeAction_isCancelSMul G U hcompat
  let := Elliptic.FiniteQuotient.chartedSpace (E := E) G M
  let := Elliptic.FiniteQuotient.chartedSpace (E := E) G U
  have hr := restrictedProject_isLocalDiffeomorph G U V hpre hM
  refine
    { toEquiv := openQuotientEquiv G U V hcompat hpre
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply
      CoveringQuotient.contMDiff_of_comp
        (Elliptic.FiniteQuotient.project_isQuotientCoveringMap G U) (modelWithCornersSelf ℂ E) ω
    exact hr.contMDiff
  · apply
      contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        (modelWithCornersSelf ℂ E) hr (restrictedProject_surjective G U V hpre)
    have he :
      (openQuotientEquiv G U V hcompat hpre).symm ∘ restrictedProject G U V hpre =
        Elliptic.FiniteQuotient.project G U := by
      funext x
      exact openQuotientEquiv_symm_restrictedProject G U V hcompat hpre x
    rw [he]
    exact
      Elliptic.FiniteQuotient.project_holomorphic G U (subtypeAction_holomorphic G U hcompat hM)

theorem Elliptic.LogGauge.discLocallyCompact : LocallyCompactSpace SpecialPeriods.Disc :=
  SpecialPeriods.unitDisc.isOpen.locallyCompactSpace

attribute [local instance] Elliptic.LogGauge.discLocallyCompact in
theorem Elliptic.LogGauge.familyStarLocallyCompact : LocallyCompactSpace familyOpen :=
  familyOpen.isOpen.locallyCompactSpace

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.StarQuotient {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) : Type :=
  @Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) (FamilyStar D.periods) _
    (starAction D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
instance Elliptic.LogGauge.starTopology {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) : TopologicalSpace (StarQuotient D v hv) :=
  inferInstanceAs
    (TopologicalSpace
      (@Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) (FamilyStar D.periods) _
        (starAction D v hv)))

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.starProject {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) : FamilyStar D.periods → StarQuotient D v hv :=
  @Elliptic.FiniteQuotient.project (Elliptic.CyclicGroup j) (FamilyStar D.periods) _
    (starAction D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
theorem Elliptic.LogGauge.starProject_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    Function.Surjective (starProject D v hv) :=
  Quotient.mk_surjective

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
theorem Elliptic.LogGauge.starCoveringMap {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    IsQuotientCoveringMap (starProject D v hv) (Elliptic.CyclicGroup j) := by
  let := starAction D v hv
  let := starAction_continuous D v hv
  let := starAction_free D v hv
  exact
    Elliptic.FiniteQuotient.project_isQuotientCoveringMap (Elliptic.CyclicGroup j)
      (FamilyStar D.periods)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
@[instance_reducible]
def Elliptic.LogGauge.starChartedSpace {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    ChartedSpace Elliptic.FamilyModel (StarQuotient D v hv) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  exact CoveringQuotient.chartedSpace (E := Elliptic.FamilyModel) (starCoveringMap D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
theorem Elliptic.LogGauge.starProject_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.periods.totalChartedSpace
    letI := starChartedSpace D v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (starProject D v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starAction D v hv
  exact
    CoveringQuotient.contMDiff_project (starCoveringMap D v hv) ω (starAction_holomorphic D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
abbrev Elliptic.LogGauge.TautologicalStar {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j) :=
  StarQuotient D 0 (Matrix.mulVec_zero j.matrix)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.gaugeQuotientEquiv {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) : StarQuotient D v hv ≃ TautologicalStar D :=
  @quotientEquiv (Elliptic.CyclicGroup j) _ (FamilyStar D.periods) (FamilyStar D.periods)
    (starAction D v hv) (starAction D 0 (Matrix.mulVec_zero j.matrix)) (gaugeEquiv D.periods v)
    (gaugeMap_starAction D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.gaugeQuotientBiholomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    letI := starChartedSpace D v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (StarQuotient D v hv) (TautologicalStar D)
      ω := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := starChartedSpace D v hv
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  refine
    { toEquiv := gaugeQuotientEquiv D v hv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · let := starAction D v hv
    apply
      CoveringQuotient.contMDiff_of_comp (starCoveringMap D v hv)
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
    exact
      (starProject_holomorphic D 0 (Matrix.mulVec_zero j.matrix)).comp
        (gaugeMap_holomorphic D.periods v)
  · let := starAction D 0 (Matrix.mulVec_zero j.matrix)
    apply
      CoveringQuotient.contMDiff_of_comp (starCoveringMap D 0 (Matrix.mulVec_zero j.matrix))
        (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
    exact (starProject_holomorphic D v hv).comp (gaugeMap_holomorphic D.periods (-v))

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.starUpstairsProjection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (x : FamilyStar D.periods) : BaseStar :=
  ⟨Elliptic.discPower j.order j.order_pos x.1.1,
    by
    change (x.1.1 : ℂ) ^ j.order ≠ 0
    exact pow_ne_zero _ x.2⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
theorem Elliptic.LogGauge.starUpstairsProjection_invariant {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : FamilyStar D.periods) :
    letI := starAction D v hv
    starUpstairsProjection D (g • x) = starUpstairsProjection D x := by
  let := D.action v hv
  let := starAction D v hv
  apply Subtype.ext
  change
    Elliptic.discPower j.order j.order_pos ((g • x : FamilyStar D.periods) : D.TotalSpace).1 =
      Elliptic.discPower j.order j.order_pos (x : D.TotalSpace).1
  rw [starAction_coe D v hv]
  exact D.action_discPower v hv g x

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.starProjection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) : StarQuotient D v hv → BaseStar := by
  let := starAction D v hv
  exact
    Elliptic.FiniteQuotient.descend (starUpstairsProjection D)
      (starUpstairsProjection_invariant D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.fillingOpen {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) : TopologicalSpace.Opens (D.Space v hv) :=
  ⟨{x | (D.projection v hv x : ℂ) ≠ 0},
    isOpen_ne_fun (continuous_subtype_val.comp (D.projection_continuous v hv)) continuous_const⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
abbrev Elliptic.LogGauge.FillingStar {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :=
  fillingOpen D v hv

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
@[simp]
theorem Elliptic.LogGauge.quotient_preimage_fillingOpen {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    (D.quotient v hv) ⁻¹' (fillingOpen D v hv : Set (D.Space v hv)) =
      (familyOpen : Set D.TotalSpace) := by
  ext x
  change (D.projection v hv (D.quotient v hv x) : ℂ) ≠ 0 ↔ (x.1 : ℂ) ≠ 0
  simp only [D.projection_quotient, Elliptic.discPower_coe, ne_eq,
    pow_eq_zero_iff j.order_pos.ne']

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.fillingStarProject {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) (x : FamilyStar D.periods) :
    FillingStar D v hv :=
  ⟨D.quotient v hv x, by
    change (D.projection v hv (D.quotient v hv x) : ℂ) ≠ 0
    rw [D.projection_quotient, Elliptic.discPower_coe]
    exact pow_ne_zero _ x.2⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
theorem Elliptic.LogGauge.fillingStarProject_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Surjective (fillingStarProject D v hv) := by
  let := D.action v hv.1
  exact
    restrictedProject_surjective (Elliptic.CyclicGroup j) familyOpen (fillingOpen D v hv)
      (quotient_preimage_fillingOpen D v hv)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.fillingStarProjection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) (x : FillingStar D v hv) : BaseStar :=
  ⟨D.projection v hv x, x.2⟩

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.fillingOpenComparison {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := starChartedSpace D v hv.1
    letI := D.chartedSpace v hv
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (StarQuotient D v hv.1) (FillingStar D v hv)
      ω := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  let := starAction D v hv.1
  exact
    openQuotientBiholomorph (Elliptic.CyclicGroup j) familyOpen (fillingOpen D v hv)
      (starAction_coe D v hv.1) (quotient_preimage_fillingOpen D v hv)
      (D.action_holomorphic v hv.1)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
def Elliptic.LogGauge.fillingToTautologicalBiholomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (FillingStar D v hv) (TautologicalStar D) ω :=
  by
  let := D.chartedSpace v hv
  let := starChartedSpace D v hv.1
  let := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
  exact (fillingOpenComparison D v hv).symm.trans (gaugeQuotientBiholomorph D v hv.1)

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
@[simp]
theorem Elliptic.LogGauge.fillingToTautologicalBiholomorph_project {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : FamilyStar D.periods) :
    fillingToTautologicalBiholomorph D v hv (fillingStarProject D v hv x) =
      starProject D 0 (Matrix.mulVec_zero j.matrix) (gaugeMap D.periods v x) :=
  rfl

attribute [local instance] Elliptic.LogGauge.discLocallyCompact
    Elliptic.LogGauge.familyStarLocallyCompact in
theorem Elliptic.LogGauge.fillingToTautologicalBiholomorph_base {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : FillingStar D v hv) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (fillingToTautologicalBiholomorph D v hv x) =
      fillingStarProjection D v hv x := by
  obtain ⟨y, rfl⟩ := fillingStarProject_surjective D v hv x
  rfl

theorem SpecialPeriods.EllipticFilling.ellipticGenerator_dual_matrix (j : Elliptic.Kind) :
    (SpecialPeriods.triangleDualRepresentation (SpecialPeriods.Triangle.ellipticGenerator j) :
        LatticeMatrix) =
      j.matrix := by
  cases j
  · exact SpecialPeriods.triangleDualRepresentation_generator₁_matrix
  · exact SpecialPeriods.triangleDualRepresentation_generator₂_matrix

theorem SpecialPeriods.EllipticFilling.ellipticGenerator_torus_mkQ (j : Elliptic.Kind)
    (x : Elliptic.RealCoordinates) :
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j)
        (standardLattice.mkQ x) =
      standardLattice.mkQ (Elliptic.flatLinear j x) := by
  rw [SpecialPeriods.triangleTorusHomeomorph_mkQ, SpecialPeriods.triangleRealEquiv_apply,
    ellipticGenerator_dual_matrix]
  rfl

theorem SpecialPeriods.EllipticFilling.ellipticGenerator_torus_eq (j : Elliptic.Kind) :
    SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j) =
      Elliptic.flatTorusAffine j 0 := by
  apply Homeomorph.ext
  intro x
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [ellipticGenerator_torus_mkQ, Elliptic.flatTorusAffine_mkQ]
  have hz : Elliptic.realCast (0 : PeriodLattice) = 0 := by
    ext i
    simp [Elliptic.realCast]
  rw [Elliptic.flatAffine, hz, smul_zero, add_zero]

theorem SpecialPeriods.EllipticFilling.flatTorusAffine_zero_iterate (j : Elliptic.Kind) (n : ℕ)
    (x : RealTorus₄) :
    (Elliptic.flatTorusAffine j 0)^[n] x =
      SpecialPeriods.triangleTorusHomeomorph (SpecialPeriods.Triangle.ellipticGenerator j ^ n)
        x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ',
      SpecialPeriods.triangleTorusHomeomorph_mul_apply, ellipticGenerator_torus_eq]

theorem SpecialPeriods.EllipticFilling.zeroAction_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action 0 (Matrix.mulVec_zero j.matrix)
    g • x =
      ((Elliptic.familyRotation j)^[g.toAdd.val] x.1,
        SpecialPeriods.triangleTorusHomeomorph
          (SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val) x.2) := by
  let := D.action 0 (Matrix.mulVec_zero j.matrix)
  rw [D.action_apply, flatTorusAffine_zero_iterate]

theorem SpecialPeriods.EllipticFilling.zeroStarAction_coe {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j)
    (x : Elliptic.LogGauge.FamilyStar D.periods) :
    letI := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    ((g • x : Elliptic.LogGauge.FamilyStar D.periods) : D.TotalSpace) =
      ((Elliptic.familyRotation j)^[g.toAdd.val] x.1.1,
        SpecialPeriods.triangleTorusHomeomorph
          (SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val) x.1.2) := by
  let := D.action 0 (Matrix.mulVec_zero j.matrix)
  let := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  rw [Elliptic.LogGauge.starAction_coe, zeroAction_apply]

theorem SpecialPeriods.EllipticFilling.zeroStarAction_fst {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j)
    (x : Elliptic.LogGauge.FamilyStar D.periods) :
    letI := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    (g • x : Elliptic.LogGauge.FamilyStar D.periods).1.1 =
      (Elliptic.familyRotation j)^[g.toAdd.val] x.1.1 := by
  let := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  exact congrArg Prod.fst (zeroStarAction_coe D g x)

theorem SpecialPeriods.EllipticFilling.zeroStarAction_snd {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (g : Elliptic.CyclicGroup j)
    (x : Elliptic.LogGauge.FamilyStar D.periods) :
    letI := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
    (g • x : Elliptic.LogGauge.FamilyStar D.periods).1.2 =
      SpecialPeriods.triangleTorusHomeomorph
        (SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val) x.1.2 := by
  let := Elliptic.LogGauge.starAction D 0 (Matrix.mulVec_zero j.matrix)
  exact congrArg Prod.snd (zeroStarAction_coe D g x)

def SpecialPeriods.EllipticFilling.localTotalMap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) :
    Elliptic.LogGauge.FamilyStar (localPeriods P j) →
      (PeriodFamily.regularPeriods P).TotalSpace :=
  fun x => (localBase j ⟨x.1.1, x.2⟩, x.1.2)

theorem SpecialPeriods.EllipticFilling.localTotalMap_injective (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) : Function.Injective (localTotalMap P j) := by
  intro x y h
  have hb := localBase_injective j (congrArg Prod.fst h)
  apply Subtype.ext
  exact
    Prod.ext (congrArg Subtype.val hb)
      (congrArg (fun z : (PeriodFamily.regularPeriods P).TotalSpace => z.2) h)

theorem SpecialPeriods.EllipticFilling.localTotalMap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind) :
    letI := (localPeriods P j).totalChartedSpace
    letI := (PeriodFamily.regularPeriods P).totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (localTotalMap P j) := by
  let Q := restrictPeriods (localPeriods P j) Elliptic.LogGauge.baseOpen
  let := (localPeriods P j).totalChartedSpace
  let := (PeriodFamily.regularPeriods P).totalChartedSpace
  let := Q.totalChartedSpace
  let e := restrictFamilyBiholomorph (localPeriods P j) Elliptic.LogGauge.baseOpen
  have hm :=
    periodFamilyMap_isLocalDiffeomorph Q (PeriodFamily.regularPeriods P) (localBase j)
      (fun _ => rfl) (localBase_isLocalDiffeomorph j)
  intro x
  have h :=
    (e.symm.isLocalDiffeomorph x).comp (K := (modelWithCornersSelf ℂ Elliptic.FamilyModel)) (P :=
      (PeriodFamily.regularPeriods P).TotalSpace) (hm (e.symm x))
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq h
  apply Filter.Eventually.of_forall
  intro y
  change
    localTotalMap P j y =
      periodFamilyMap Q (PeriodFamily.regularPeriods P) (localBase j)
        ((restrictFamilyBiholomorph (localPeriods P j) Elliptic.LogGauge.baseOpen).symm y)
  rw [restrictFamilyBiholomorph_symm_apply]
  rfl

theorem SpecialPeriods.EllipticFilling.puncturedRotation_iterate_coe (j : Elliptic.Kind) (n : ℕ)
    (z : Elliptic.LogGauge.BaseStar) :
    ((puncturedRotation j)^[n] z).val = (Elliptic.familyRotation j)^[n] z.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', puncturedRotation_val, ih, Function.iterate_succ_apply']

theorem SpecialPeriods.EllipticFilling.localTotalMap_smul (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (g : Elliptic.CyclicGroup j) (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    letI := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (PeriodFamily.regularData P h₁ h₂).totalAction
    localTotalMap P j (g • x) =
      SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val • localTotalMap P j x := by
  let L := localData P h₁ h₂ j
  let D := PeriodFamily.regularData P h₁ h₂
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := D.totalAction
  have hb :
    (⟨(g • x : Elliptic.LogGauge.FamilyStar L.periods).1.1,
          (g • x : Elliptic.LogGauge.FamilyStar L.periods).2⟩ :
        Elliptic.LogGauge.BaseStar) =
      (puncturedRotation j)^[g.toAdd.val] ⟨x.1.1, x.2⟩ := by
    apply Subtype.ext
    exact
      (zeroStarAction_fst L g x).trans
        (puncturedRotation_iterate_coe j g.toAdd.val ⟨x.1.1, x.2⟩).symm
  apply Prod.ext
  · change
      localBase j
          ⟨(g • x : Elliptic.LogGauge.FamilyStar L.periods).1.1,
            (g • x : Elliptic.LogGauge.FamilyStar L.periods).2⟩ =
        SpecialPeriods.Triangle.ellipticGenerator j ^ g.toAdd.val • localBase j ⟨x.1.1, x.2⟩
    rw [hb, localBase_rotation_iterate]
  · exact zeroStarAction_snd L g x

def SpecialPeriods.EllipticFilling.regularMap (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Elliptic.LogGauge.FamilyStar (localPeriods P j) → (PeriodFamily.regularData P h₁ h₂).Space :=
  (PeriodFamily.regularData P h₁ h₂).quotient ∘ localTotalMap P j

@[simp]
theorem SpecialPeriods.EllipticFilling.regularMap_base (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    (PeriodFamily.regularData P h₁ h₂).projection (regularMap P j h₁ h₂ x) =
      baseQuotient j ⟨x.1.1, x.2⟩ :=
  rfl

theorem SpecialPeriods.EllipticFilling.regularMap_smul (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (g : Elliptic.CyclicGroup j) (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    letI := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    regularMap P j h₁ h₂ (g • x) = regularMap P j h₁ h₂ x := by
  let := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).totalAction
  change
    (PeriodFamily.regularData P h₁ h₂).quotient (localTotalMap P j (g • x)) =
      (PeriodFamily.regularData P h₁ h₂).quotient (localTotalMap P j x)
  rw [localTotalMap_smul, PeriodFamily.Data.quotient_smul]

theorem SpecialPeriods.EllipticFilling.regularMap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := (localPeriods P j).totalChartedSpace
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (regularMap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (PeriodFamily.regularPeriods P).totalChartedSpace
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  intro x
  exact
    (localTotalMap_isLocalDiffeomorph P j x).comp (K :=
      (modelWithCornersSelf ℂ Elliptic.FamilyModel)) (P :=
      (PeriodFamily.regularData P h₁ h₂).Space)
      ((PeriodFamily.regularData P h₁ h₂).quotient_isLocalDiffeomorph
        (PeriodFamily.regularCovering P h₁ h₂) (localTotalMap P j x))

def SpecialPeriods.EllipticFilling.regularOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    TopologicalSpace.Opens (PeriodFamily.regularData P h₁ h₂).Space :=
  ⟨(PeriodFamily.regularData P h₁ h₂).projection ⁻¹'
      (regularBasePatch j : Set SpecialPeriods.TriangleRegularQuotient),
    (regularBasePatch j).isOpen.preimage (PeriodFamily.regularData P h₁ h₂).projection_continuous⟩

@[simp]
theorem SpecialPeriods.EllipticFilling.regularOverlap_mem (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (y : (PeriodFamily.regularData P h₁ h₂).Space) :
    y ∈ regularOverlap P j h₁ h₂ ↔
      (PeriodFamily.regularData P h₁ h₂).projection y ∈ regularBasePatch j :=
  Iff.rfl

theorem SpecialPeriods.EllipticFilling.regularMap_mem_overlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    regularMap P j h₁ h₂ x ∈ regularOverlap P j h₁ h₂ := by
  rw [regularOverlap_mem, regularMap_base]
  exact baseQuotient_mem_regularBasePatch j ⟨x.1.1, x.2⟩

theorem SpecialPeriods.EllipticFilling.regularMap_range (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Set.range (regularMap P j h₁ h₂) =
      (regularOverlap P j h₁ h₂ : Set (PeriodFamily.regularData P h₁ h₂).Space) := by
  let D := PeriodFamily.regularData P h₁ h₂
  let := D.totalAction
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact regularMap_mem_overlap P j h₁ h₂ x
  · intro hy
    obtain ⟨u, rfl⟩ := D.quotient_surjective y
    have hb : D.baseQuotient u.1 ∈ regularBasePatch j := hy
    have hz' : D.baseQuotient u.1 ∈ Set.range (baseQuotient j) := by
      rw [baseQuotient_range]
      exact hb
    obtain ⟨z, hz⟩ := hz'
    have hbase : D.baseQuotient (localBase j z) = D.baseQuotient u.1 := hz
    obtain ⟨g, hg⟩ := (PeriodFamily.regularCovering P h₁ h₂).apply_eq_iff_mem_orbit.mp hbase
    let x : Elliptic.LogGauge.FamilyStar (localPeriods P j) :=
      ⟨(z.val, SpecialPeriods.triangleTorusHomeomorph g u.2), z.property⟩
    refine ⟨x, ?_⟩
    change D.quotient (localTotalMap P j x) = D.quotient u
    apply (D.quotient_eq_iff _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

theorem SpecialPeriods.EllipticFilling.regularMap_eq_iff (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x y : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    letI := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    regularMap P j h₁ h₂ x = regularMap P j h₁ h₂ y ↔ ∃ g : Elliptic.CyclicGroup j, g • y = x := by
  let L := localData P h₁ h₂ j
  let D := PeriodFamily.regularData P h₁ h₂
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := D.totalAction
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff (localTotalMap P j x) (localTotalMap P j y)).mp h
    have hb : g • localBase j ⟨y.1.1, y.2⟩ = localBase j ⟨x.1.1, x.2⟩ := congrArg Prod.fst hg
    obtain ⟨n, hn, hgn, _⟩ := localBase_orbit_classification j g ⟨y.1.1, y.2⟩ ⟨x.1.1, x.2⟩ hb
    let c : Elliptic.CyclicGroup j := Multiplicative.ofAdd (n : ZMod j.order)
    refine ⟨c, localTotalMap_injective P j ?_⟩
    calc
      localTotalMap P j (c • y) =
          SpecialPeriods.Triangle.ellipticGenerator j ^ n • localTotalMap P j y := by
        rw [localTotalMap_smul]
        simp only [c, toAdd_ofAdd, ZMod.val_natCast_of_lt hn]
      _ = localTotalMap P j x := hgn ▸ hg
  · rintro ⟨g, rfl⟩
    exact regularMap_smul P j h₁ h₂ g y

def SpecialPeriods.EllipticFilling.regularMapToOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) : regularOverlap P j h₁ h₂ :=
  ⟨regularMap P j h₁ h₂ x, regularMap_mem_overlap P j h₁ h₂ x⟩

theorem SpecialPeriods.EllipticFilling.regularMapToOverlap_surjective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Surjective (regularMapToOverlap P j h₁ h₂) := by
  intro y
  have hy : y.val ∈ Set.range (regularMap P j h₁ h₂) := by
    rw [regularMap_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

def SpecialPeriods.EllipticFilling.tautologicalToOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Elliptic.LogGauge.TautologicalStar (localData P h₁ h₂ j) → regularOverlap P j h₁ h₂ := by
  let := Elliptic.LogGauge.starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  exact
    Quotient.lift (regularMapToOverlap P j h₁ h₂)
      (by
        rintro x y ⟨g, hg⟩
        apply Subtype.ext
        exact (regularMap_eq_iff P j h₁ h₂ x y).mpr ⟨g, hg⟩)

theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_injective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Injective (tautologicalToOverlap P j h₁ h₂) := by
  let L := localData P h₁ h₂ j
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  intro a b h
  obtain ⟨x, rfl⟩ := Elliptic.LogGauge.starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) a
  obtain ⟨y, rfl⟩ := Elliptic.LogGauge.starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) b
  have hxy : regularMap P j h₁ h₂ x = regularMap P j h₁ h₂ y := congrArg Subtype.val h
  exact Quotient.sound ((regularMap_eq_iff P j h₁ h₂ x y).mp hxy)

theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_surjective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Surjective (tautologicalToOverlap P j h₁ h₂) := by
  intro y
  obtain ⟨x, rfl⟩ := regularMapToOverlap_surjective P j h₁ h₂ y
  exact
    ⟨Elliptic.LogGauge.starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x, rfl⟩

theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_bijective
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Function.Bijective (tautologicalToOverlap P j h₁ h₂) :=
  ⟨tautologicalToOverlap_injective P j h₁ h₂, tautologicalToOverlap_surjective P j h₁ h₂⟩

theorem Elliptic.LogGauge.sectionMap_formula_of_exponential
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) (z : BaseStar) (s : ℂ)
    (hs : CuspUniformization.exponential s = (z.1 : ℂ)) :
    (sectionMap P v z : P.TotalSpace) = P.quotientMap (z.1, s • periodVector P v z.1) := by
  rw [sectionMap_formula]
  have hlogs : ∃ n : ℤ, CuspUniformization.logarithm (z.1 : ℂ) = s + n :=
    (CuspUniformization.exponential_eq_iff _ _).mp
      ((CuspUniformization.exponential_logarithm z.2).trans hs.symm)
  simpa only [zero_add] using quotientMap_eq_of_scalar_int P v z.1 0 hlogs

theorem Elliptic.LogGauge.gaugeMap_project_of_exponential
    (P : HolomorphicPeriodMap ℂ SpecialPeriods.Disc) (v : PeriodLattice) (x : CoverStar) (s : ℂ)
    (hs : CuspUniformization.exponential s = (x.1.1 : ℂ)) :
    (gaugeMap P v (project P x) : P.TotalSpace) =
      P.quotientMap (x.1.1, x.1.2 + s • periodVector P v x.1.1) := by
  rw [gaugeMap_project]
  exact
    quotientMap_eq_of_scalar_int P v x.1.1 x.1.2
      ((CuspUniformization.exponential_eq_iff _ _).mp
        ((CuspUniformization.exponential_logarithm x.2).trans hs.symm))

def Elliptic.LogGauge.mainFillingToTautologicalBiholomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :
    letI := D.chartedSpace j.twist (Elliptic.mainTwist_admissible j)
    letI := starChartedSpace D 0 (Matrix.mulVec_zero j.matrix)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (FillingStar D j.twist (Elliptic.mainTwist_admissible j)) (TautologicalStar D) ω :=
  fillingToTautologicalBiholomorph D j.twist (Elliptic.mainTwist_admissible j)

theorem Elliptic.LogGauge.mainFillingToTautologicalBiholomorph_base {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j)
    (x : FillingStar D j.twist (Elliptic.mainTwist_admissible j)) :
    starProjection D 0 (Matrix.mulVec_zero j.matrix) (mainFillingToTautologicalBiholomorph D x) =
      fillingStarProjection D j.twist (Elliptic.mainTwist_admissible j) x :=
  fillingToTautologicalBiholomorph_base D j.twist (Elliptic.mainTwist_admissible j) x

theorem SpecialPeriods.EllipticFilling.regularMapToOverlap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := (localPeriods P j).totalChartedSpace
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (regularMapToOverlap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (regularMap_isLocalDiffeomorph P j h₁ h₂)
      (regularOverlap P j h₁ h₂) (regularMap_mem_overlap P j h₁ h₂)

theorem SpecialPeriods.EllipticFilling.tautologicalToOverlap_isLocalDiffeomorph
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI :=
      Elliptic.LogGauge.starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (tautologicalToOverlap P j h₁ h₂) := by
  let L := localData P h₁ h₂ j
  let := L.periods.totalChartedSpace
  let := L.periods.totalSpace_isManifold
  let := Elliptic.LogGauge.starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := Elliptic.LogGauge.starChartedSpace L 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have hq :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (Elliptic.LogGauge.starProject L 0 (Matrix.mulVec_zero j.matrix)) :=
    CoveringQuotient.project_isLocalDiffeomorph
      (Elliptic.LogGauge.starCoveringMap L 0 (Matrix.mulVec_zero j.matrix))
      (Elliptic.LogGauge.starAction_holomorphic L 0 (Matrix.mulVec_zero j.matrix))
  intro y
  obtain ⟨x, rfl⟩ := Elliptic.LogGauge.starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) y
  exact localDiffeomorphAt_of_comp (hq x) (regularMapToOverlap_isLocalDiffeomorph P j h₁ h₂ x)

def SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI :=
      Elliptic.LogGauge.starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (Elliptic.LogGauge.TautologicalStar (localData P h₁ h₂ j)) (regularOverlap P j h₁ h₂) ω := by
  let := Elliptic.LogGauge.starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (tautologicalToOverlap_isLocalDiffeomorph P j h₁ h₂).diffeomorphOfBijective
      (tautologicalToOverlap_bijective P j h₁ h₂)

@[simp]
theorem SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_project
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.FamilyStar (localPeriods P j)) :
    tautologicalOverlapBiholomorph P j h₁ h₂
        (Elliptic.LogGauge.starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x) =
      regularMapToOverlap P j h₁ h₂ x :=
  rfl

theorem SpecialPeriods.EllipticFilling.tautologicalOverlapBiholomorph_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : Elliptic.LogGauge.TautologicalStar (localData P h₁ h₂ j)) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit
          ((PeriodFamily.regularData P h₁ h₂).projection
            (tautologicalOverlapBiholomorph P j h₁ h₂ x).val)) =
      ((Elliptic.LogGauge.starProjection (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x :
          SpecialPeriods.Disc) :
        ℂ) := by
  obtain ⟨y, rfl⟩ :=
    Elliptic.LogGauge.starProject_surjective (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
      x
  change
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit (baseQuotient j ⟨y.1.1, y.2⟩)) =
      (y.1.1 : ℂ) ^ j.order
  exact ellipticFullChart_baseQuotient j ⟨y.1.1, y.2⟩

abbrev SpecialPeriods.EllipticFilling.MainFillingStar (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :=
  Elliptic.LogGauge.FillingStar (localData P h₁ h₂ j) j.twist (Elliptic.mainTwist_admissible j)

def SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    Diffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (MainFillingStar P j h₁ h₂)
      (regularOverlap P j h₁ h₂) ω := by
  let L := localData P h₁ h₂ j
  let := fillingChartedSpace P h₁ h₂ j
  let := Elliptic.LogGauge.starChartedSpace L 0 (Matrix.mulVec_zero j.matrix)
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (Elliptic.LogGauge.mainFillingToTautologicalBiholomorph L).trans
      (tautologicalOverlapBiholomorph P j h₁ h₂)

theorem SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : MainFillingStar P j h₁ h₂) :
    SpecialPeriods.Triangle.ellipticFullChart j
        (SpecialPeriods.triangleRegularToOrbit
          ((PeriodFamily.regularData P h₁ h₂).projection
            (puncturedFillingBiholomorph P j h₁ h₂ x).val)) =
      (fillingProjection P h₁ h₂ j x.val : ℂ) := by
  let L := localData P h₁ h₂ j
  have h :=
    tautologicalOverlapBiholomorph_coordinate P j h₁ h₂
      (Elliptic.LogGauge.mainFillingToTautologicalBiholomorph L x)
  have hb :=
    congrArg (fun z : Elliptic.LogGauge.BaseStar => ((z : SpecialPeriods.Disc) : ℂ))
      (Elliptic.LogGauge.mainFillingToTautologicalBiholomorph_base L x)
  exact h.trans hb

def SpecialPeriods.EllipticFilling.regularCompactProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    (PeriodFamily.regularData P h₁ h₂).Space → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  fun x =>
  SpecialPeriods.triangleOpenInclusion
    (SpecialPeriods.triangleRegularToOrbit ((PeriodFamily.regularData P h₁ h₂).projection x))

theorem SpecialPeriods.EllipticFilling.puncturedFillingBiholomorph_base
    (P : HolomorphicPeriodMap ℂ ℍ) (j : Elliptic.Kind)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (x : MainFillingStar P j h₁ h₂) :
    regularCompactProjection P h₁ h₂ (puncturedFillingBiholomorph P j h₁ h₂ x).val =
      (SpecialPeriods.Triangle.ellipticCompactifiedChart j).symm
        (fillingProjection P h₁ h₂ j x.val : ℂ) := by
  let y := puncturedFillingBiholomorph P j h₁ h₂ x
  have hs :
    regularCompactProjection P h₁ h₂ y.val ∈
      (SpecialPeriods.Triangle.ellipticCompactifiedChart j).source :=
    (regularBasePatch_mem_iff_compactifiedChart j _).mp y.property
  have hc :
    SpecialPeriods.Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y.val) =
      (fillingProjection P h₁ h₂ j x.val : ℂ) := by
    rw [regularCompactProjection, SpecialPeriods.Triangle.ellipticCompactifiedChart_openInclusion]
    exact puncturedFillingBiholomorph_coordinate P j h₁ h₂ x
  exact
    ((SpecialPeriods.Triangle.ellipticCompactifiedChart j).left_inv hs).symm.trans
      (congrArg (SpecialPeriods.Triangle.ellipticCompactifiedChart j).symm hc)

theorem SpecialPeriods.EllipticFilling.mainFillingStar_nonempty (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Nonempty (MainFillingStar P j h₁ h₂) := by
  let z : SpecialPeriods.Disc := ⟨(1 / 2 : ℂ), by norm_num [SpecialPeriods.unitDisc]⟩
  obtain ⟨y, hy⟩ := fillingProjection_surjective P h₁ h₂ j z
  refine ⟨⟨y, ?_⟩⟩
  change (fillingProjection P h₁ h₂ j y : ℂ) ≠ 0
  rw [hy]
  norm_num [z]

theorem SpecialPeriods.EllipticFilling.regularOverlap_nonempty (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Nonempty (regularOverlap P j h₁ h₂) := by
  obtain ⟨x⟩ := mainFillingStar_nonempty P h₁ h₂ j
  exact ⟨puncturedFillingBiholomorph P j h₁ h₂ x⟩

theorem SpecialPeriods.EllipticFilling.piece_nonempty (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) : Nonempty (Piece P h₁ h₂ C j) :=
  by
  obtain ⟨x, _⟩ :=
    pieceProjection_surjective P h₁ h₂ C j
      ⟨SpecialPeriods.Threefold.puncturePoint (Option.some j),
        C.point_mem_fillingPatch (Option.some j)⟩
  exact ⟨x⟩

theorem SpecialPeriods.EllipticFilling.regularOverlap_mem_iff_compactifiedChart
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (y : (PeriodFamily.regularData P h₁ h₂).Space) :
    y ∈ regularOverlap P j h₁ h₂ ↔
      regularCompactProjection P h₁ h₂ y ∈
        (SpecialPeriods.Triangle.ellipticCompactifiedChart j).source :=
  regularBasePatch_mem_iff_compactifiedChart j ((PeriodFamily.regularData P h₁ h₂).projection y)

def SpecialPeriods.EllipticFilling.puncturedFillingPartial (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    PartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (fillingSpace P h₁ h₂ j)
      (PeriodFamily.regularData P h₁ h₂).Space ω := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
          (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
            (Elliptic.mainTwist_admissible j))
          (mainFillingStar_nonempty P h₁ h₂ j)).symm.trans
      ((puncturedFillingBiholomorph P j h₁ h₂).toPartialDiffeomorph.trans
        (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
          (regularOverlap P j h₁ h₂) (regularOverlap_nonempty P h₁ h₂ j)))

@[simp]
theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_source
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).source =
      (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j) :
        Set _) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  simp [puncturedFillingPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp]
theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_target
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).target =
      (regularOverlap P j h₁ h₂ : Set (PeriodFamily.regularData P h₁ h₂).Space) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  simp [puncturedFillingPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp]
theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_apply
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : MainFillingStar P j h₁ h₂) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    puncturedFillingPartial P h₁ h₂ j x.val = (puncturedFillingBiholomorph P j h₁ h₂ x).val := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  let e :=
    (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j)).openPartialHomeomorphSubtypeCoe
      (mainFillingStar_nonempty P h₁ h₂ j)
  have he : e.symm x.val = x := e.left_inv (Set.mem_univ x)
  change
    (puncturedFillingBiholomorph P j h₁ h₂ (e.symm x.val) :
        (PeriodFamily.regularData P h₁ h₂).Space) =
      _
  rw [he]

theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_base (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : fillingSpace P h₁ h₂ j)
    (hx : x ∈ (puncturedFillingPartial P h₁ h₂ j).source) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    regularCompactProjection P h₁ h₂ (puncturedFillingPartial P h₁ h₂ j x) =
      (SpecialPeriods.Triangle.ellipticCompactifiedChart j).symm
        (fillingProjection P h₁ h₂ j x : ℂ) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have hx' :
    x ∈
      (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j) :
        Set (fillingSpace P h₁ h₂ j)) := by simpa only [puncturedFillingPartial_source] using hx
  rw [puncturedFillingPartial_apply P h₁ h₂ j ⟨x, hx'⟩]
  exact puncturedFillingBiholomorph_base P j h₁ h₂ ⟨x, hx'⟩

theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (x : fillingSpace P h₁ h₂ j)
    (hx : x ∈ (puncturedFillingPartial P h₁ h₂ j).source) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    SpecialPeriods.Triangle.ellipticCompactifiedChart j
        (regularCompactProjection P h₁ h₂ (puncturedFillingPartial P h₁ h₂ j x)) =
      (fillingProjection P h₁ h₂ j x : ℂ) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have hx' :
    x ∈
      (Elliptic.LogGauge.fillingOpen (localData P h₁ h₂ j) j.twist
          (Elliptic.mainTwist_admissible j) :
        Set (fillingSpace P h₁ h₂ j)) := by simpa only [puncturedFillingPartial_source] using hx
  rw [puncturedFillingPartial_apply P h₁ h₂ j ⟨x, hx'⟩, regularCompactProjection,
    SpecialPeriods.Triangle.ellipticCompactifiedChart_openInclusion]
  exact puncturedFillingBiholomorph_coordinate P j h₁ h₂ ⟨x, hx'⟩

theorem SpecialPeriods.EllipticFilling.puncturedFillingPartial_symm_coordinate
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (y : (PeriodFamily.regularData P h₁ h₂).Space)
    (hy : y ∈ (puncturedFillingPartial P h₁ h₂ j).target) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    (fillingProjection P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) : ℂ) =
      SpecialPeriods.Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  have h :=
    puncturedFillingPartial_coordinate P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y)
      ((puncturedFillingPartial P h₁ h₂ j).map_target hy)
  have he : puncturedFillingPartial P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) = y :=
    (puncturedFillingPartial P h₁ h₂ j).right_inv hy
  exact
    h.symm.trans
      (congrArg
        (fun z : (PeriodFamily.regularData P h₁ h₂).Space =>
          SpecialPeriods.Triangle.ellipticCompactifiedChart j
            (regularCompactProjection P h₁ h₂ z))
        he)

def SpecialPeriods.EllipticFilling.smallOverlap (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    letI := pieceChartedSpace P h₁ h₂ C j
    letI := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
    PartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) (Piece P h₁ h₂ C j)
      (PeriodFamily.regularData P h₁ h₂).Space ω := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  exact
    (opensInclusionPartialDiffeomorph (modelWithCornersSelf ℂ Elliptic.FamilyModel)
          (pieceDomain P h₁ h₂ C j) (piece_nonempty P h₁ h₂ C j)).trans
      (puncturedFillingPartial P h₁ h₂ j)

@[simp]
theorem SpecialPeriods.EllipticFilling.smallOverlap_apply (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j) :
    smallOverlap P h₁ h₂ C j x = puncturedFillingPartial P h₁ h₂ j x.val :=
  rfl

@[simp]
theorem SpecialPeriods.EllipticFilling.smallOverlap_source (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    (smallOverlap P h₁ h₂ C j).source =
      pieceProjectionToBase P h₁ h₂ C j ⁻¹'
        (SpecialPeriods.Threefold.regularPatch :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  change
    Set.univ ∩
        (Subtype.val : Piece P h₁ h₂ C j → fillingSpace P h₁ h₂ j) ⁻¹'
          (puncturedFillingPartial P h₁ h₂ j).source =
      _
  rw [Set.univ_inter, puncturedFillingPartial_source]
  ext x
  exact (pieceProjectionToBase_mem_regular_iff P h₁ h₂ C j x).symm

theorem SpecialPeriods.EllipticFilling.smallOverlap_mem_source (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j) :
    x ∈ (smallOverlap P h₁ h₂ C j).source ↔ (fillingProjection P h₁ h₂ j x.val : ℂ) ≠ 0 := by
  rw [smallOverlap_source]
  exact pieceProjectionToBase_mem_regular_iff P h₁ h₂ C j x

theorem SpecialPeriods.EllipticFilling.smallOverlap_apply_mainStar (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j)
    (hx : (fillingProjection P h₁ h₂ j x.val : ℂ) ≠ 0) :
    smallOverlap P h₁ h₂ C j x =
      (puncturedFillingBiholomorph P j h₁ h₂ (⟨x.val, hx⟩ : MainFillingStar P j h₁ h₂)).val :=
  puncturedFillingPartial_apply P h₁ h₂ j ⟨x.val, hx⟩

@[simp]
theorem SpecialPeriods.EllipticFilling.smallOverlap_target (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    (smallOverlap P h₁ h₂ C j).target =
      regularCompactProjection P h₁ h₂ ⁻¹'
        (C.fillingPatch (Option.some j) : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (PeriodFamily.regularData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)
  change
    (puncturedFillingPartial P h₁ h₂ j).target ∩
        (puncturedFillingPartial P h₁ h₂ j).symm ⁻¹'
          ((pieceDomain P h₁ h₂ C j).openPartialHomeomorphSubtypeCoe
              (piece_nonempty P h₁ h₂ C j)).target =
      _
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  ext y
  constructor
  · rintro ⟨hy, hyV⟩
    have hyOverlap : y ∈ regularOverlap P j h₁ h₂ := by
      change y ∈ (regularOverlap P j h₁ h₂ : Set (PeriodFamily.regularData P h₁ h₂).Space)
      rw [← puncturedFillingPartial_target P h₁ h₂ j]
      exact hy
    refine
      (C.mem_fillingPatch (Option.some j) (regularCompactProjection P h₁ h₂ y)).mpr
        ⟨(regularOverlap_mem_iff_compactifiedChart P h₁ h₂ j y).mp hyOverlap, ?_⟩
    change
      ‖SpecialPeriods.Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y)‖ <
        C.radius (Option.some j)
    rw [← puncturedFillingPartial_symm_coordinate P h₁ h₂ j y hy]
    exact hyV
  · intro hy
    have hy' := (C.mem_fillingPatch (Option.some j) (regularCompactProjection P h₁ h₂ y)).mp hy
    have hyFull : y ∈ (puncturedFillingPartial P h₁ h₂ j).target := by
      rw [puncturedFillingPartial_target]
      exact (regularOverlap_mem_iff_compactifiedChart P h₁ h₂ j y).mpr hy'.1
    refine ⟨hyFull, ?_⟩
    change
      ‖(fillingProjection P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) : ℂ)‖ <
        C.radius (Option.some j)
    rw [puncturedFillingPartial_symm_coordinate P h₁ h₂ j y hyFull]
    exact hy'.2

theorem SpecialPeriods.EllipticFilling.smallOverlap_base (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (x : Piece P h₁ h₂ C j)
    (hx : x ∈ (smallOverlap P h₁ h₂ C j).source) :
    regularCompactProjection P h₁ h₂ (smallOverlap P h₁ h₂ C j x) =
      pieceProjectionToBase P h₁ h₂ C j x := by
  rw [smallOverlap_apply]
  exact
    puncturedFillingPartial_base P h₁ h₂ j x.val
      (by
        rw [puncturedFillingPartial_source]
        exact (smallOverlap_mem_source P h₁ h₂ C j x).mp hx)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
def SpecialPeriods.Threefold.specialEllipticOverlap (j : Elliptic.Kind) :
    PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (SpecialEllipticPiece j) SpecialRegularFamily
      ω :=
  SpecialPeriods.EllipticFilling.smallOverlap SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticOverlap_source (j : Elliptic.Kind) :
    (specialEllipticOverlap j).source =
      specialEllipticPieceProjectionToBase j ⁻¹'
        (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  SpecialPeriods.EllipticFilling.smallOverlap_source SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticOverlap_target (j : Elliptic.Kind) :
    (specialEllipticOverlap j).target =
      specialRegularFamilyProjectionToBase ⁻¹'
        (specialBaseCover.fillingPatch (Option.some j) :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  SpecialPeriods.EllipticFilling.smallOverlap_target SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.specialRegularFamilyChartedSpace
    SpecialPeriods.Threefold.specialEllipticPieceChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticOverlap_base (j : Elliptic.Kind)
    (x : SpecialEllipticPiece j) (hx : x ∈ (specialEllipticOverlap j).source) :
    specialRegularFamilyProjectionToBase (specialEllipticOverlap j x) =
      specialEllipticPieceProjectionToBase j x :=
  SpecialPeriods.EllipticFilling.smallOverlap_base SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j x hx

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
def SpecialPeriods.Threefold.localOverlap :
    (i : Puncture) →
      PartialDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (localPiece (Option.some i))
        (localPiece Option.none) ω
  | none => specialCuspOverlap
  | some j => specialEllipticOverlap j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localOverlap_source (i : Puncture) :
    (localOverlap i).source =
      localBaseMap (Option.some i) ⁻¹'
        (specialBaseCover.patch Option.none :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact specialCuspOverlap_source
  | some j => exact specialEllipticOverlap_source j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localOverlap_target (i : Puncture) :
    (localOverlap i).target =
      localBaseMap Option.none ⁻¹'
        (specialBaseCover.patch (Option.some i) :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact specialCuspOverlap_target
  | some j => exact specialEllipticOverlap_target j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.localOverlap_base (i : Puncture) (x : localPiece (Option.some i))
    (hx : x ∈ (localOverlap i).source) :
    localBaseMap Option.none (localOverlap i x) = localBaseMap (Option.some i) x := by
  cases i with
  | none => exact specialCuspOverlap_base x hx
  | some j => exact specialEllipticOverlap_base j x hx

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
abbrev SpecialPeriods.Threefold.gluingStar :
    Star.Input SpecialPeriods.TriangleCompactifiedOrbitSpace Puncture
    where
  patch := specialBaseCover.patch
  cover := specialBaseCover.isOpenCover
  disjoint := specialBaseCover.pairwise_disjoint
  piece := localPiece
  toBase := localBaseMap
  toBase_mem := localProjectionToBase_mem
  overlap i := (localOverlap i).toOpenPartialHomeomorph
  source_eq := localOverlap_source
  target_eq := localOverlap_target
  preserves_base := localOverlap_base

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
abbrev SpecialPeriods.Threefold.gluingData :
    ThreefoldGluing.Data SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  gluingStar.toData

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.gluingData_transition_holomorphic (i j : Index) :
    ContMDiffOn (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (gluingData.transition i j)
      (gluingData.transition i j).source :=
  gluingStar.toData_transition_holomorphic (fun i => (localOverlap i).contMDiffOn)
    (fun i => (localOverlap i).symm.contMDiffOn) i j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace in
theorem SpecialPeriods.Threefold.gluingData_localProjection_proper (i : Index) :
    IsProperMap (gluingData.localProjection i) :=
  localProjection_proper i

theorem ThreefoldGluing.Data.restrictedProjection_eq {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) :
    (D.patch i : Set B).restrictPreimage D.projection =
      D.localProjection i ∘ (D.patchHomeomorph i).symm := by
  funext x
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using
    D.patchHomeomorph_projection i ((D.patchHomeomorph i).symm x)

theorem ThreefoldGluing.Data.restrictedProjection_proper {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (hi : IsProperMap (D.localProjection i)) :
    IsProperMap ((D.patch i : Set B).restrictPreimage D.projection) := by
  rw [D.restrictedProjection_eq]
  exact hi.comp (D.patchHomeomorph i).symm.isProperMap

theorem ThreefoldGluing.Data.projection_fibre_eq_localImage {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) (b : D.patch i) :
    D.projection ⁻¹' {(b : B)} = D.inclusion i '' (D.localProjection i ⁻¹' { b }) := by
  ext x
  constructor
  · intro hx
    change D.projection x = (b : B) at hx
    have hi : x ∈ Set.range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection x ∈ D.patch i
      rw [hx]
      exact b.property
    obtain ⟨z, rfl⟩ := hi
    refine ⟨z, ?_, rfl⟩
    change D.localProjection i z = b
    apply Subtype.ext
    exact (D.projection_inclusion i z).symm.trans hx
  · rintro ⟨z, hz, rfl⟩
    change D.localProjection i z = b at hz
    change D.projection (D.inclusion i z) = (b : B)
    exact (D.projection_inclusion i z).trans (congrArg Subtype.val hz)

theorem ThreefoldGluing.Data.projection_fibre_compact {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (hproper : ∀ i : D.J, IsProperMap (D.localProjection i))
    (b : B) : IsCompact (D.projection ⁻¹' { b }) := by
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  rw [D.projection_fibre_eq_localImage i ⟨b, hi⟩]
  exact
    ((hproper i).isCompact_preimage isCompact_singleton).image
      (D.inclusion_openEmbedding i).continuous

theorem ThreefoldGluing.Data.projection_proper {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) :
    IsProperMap D.projection := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨D.projection_continuous, ?_, D.projection_fibre_compact hproper⟩
  apply D.cover.isClosedMap_iff_restrictPreimage.mpr
  intro i
  exact (D.restrictedProjection_proper i (hproper i)).isClosedMap

theorem ThreefoldGluing.Data.compactSpace {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [CompactSpace B]
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) : CompactSpace D.Space := by
  constructor
  simpa only [Set.preimage_univ] using
    (D.projection_proper hproper).isCompact_preimage
      (isCompact_univ : IsCompact (Set.univ : Set B))

theorem ThreefoldGluing.Data.secondCountableSpace_of_compactBase {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [CompactSpace B] [∀ i, SecondCountableTopology (D.piece i)] :
    SecondCountableTopology D.Space := by
  classical
  obtain ⟨s, hs⟩ := D.cover.exists_finite_of_compactSpace
  let : ∀ i : s, SecondCountableTopology (Set.range (D.inclusion i.val)) := fun i =>
    (D.inclusion_openEmbedding i.val).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply
    TopologicalSpace.secondCountableTopology_of_countable_cover (U := fun i : s =>
      Set.range (D.inclusion i.val)) (fun i => (D.inclusion_openEmbedding i.val).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := hs.exists_mem (D.projection x)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [D.inclusion_range]
  exact hi

def ThreefoldGluing.Data.Compatible {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    {Y : Type*} (f : ∀ i, D.piece i → Y) : Prop :=
  ∀ i j x, x ∈ (D.transition i j).source → f j (D.transition i j x) = f i x

def ThreefoldGluing.Data.descend {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    {Y : Type*} (f : ∀ i, D.piece i → Y) (_hf : D.Compatible f) (x : D.Space) : Y :=
  f (D.representative x).1 (D.representative x).2

@[simp]
theorem ThreefoldGluing.Data.descend_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) {Y : Type*} (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (i : D.J) (x : D.piece i) : D.descend f hf (D.inclusion i x) = f i x := by
  let r := D.representative (D.inclusion i x)
  have h := (D.inclusion_eq_iff r.1 i r.2 x).mp (D.inclusion_representative _)
  change f r.1 r.2 = f i x
  rw [← h.2]
  exact (hf r.1 i r.2 h.1).symm

def ThreefoldGluing.Data.liftedPatch {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) (i : D.J) : TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (D.patch i : Set B), (D.patch i).isOpen.preimage D.projection_continuous⟩

theorem ThreefoldGluing.Data.patchHomeomorph_symm_eq_parametrization {B : Type u}
    [TopologicalSpace B] (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J)
    (x : D.liftedPatch i) : (D.patchHomeomorph i).symm x = (D.parametrization i).symm x.val := by
  have hx : D.inclusion i ((D.patchHomeomorph i).symm x) = x.val :=
    congrArg Subtype.val ((D.patchHomeomorph i).apply_symm_apply x)
  rw [← hx, D.parametrization_symm_inclusion]

def ThreefoldGluing.Data.patchBiholomorph {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [∀ i, ChartedSpace E (D.piece i)]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]
    (hhol :
      ∀ i j,
        ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (D.transition i j)
          (D.transition i j).source)
    (i : D.J) :
    letI := D.chartedSpace (E := E)
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) (D.piece i)
      (D.liftedPatch i) ω := by
  letI := D.chartedSpace (E := E)
  let e : D.piece i ≃ₜ D.liftedPatch i := D.patchHomeomorph i
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · intro x
    have he :
      ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
          (fun z : D.piece i => ((e z).val : D.Space)) x ↔
        ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω e x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp ((D.inclusion_holomorphic hhol i) x)
  · intro x
    have hx : x.val ∈ (D.parametrization i).target := by
      rw [D.parametrization_target, D.inclusion_range]
      exact x.property
    have h :=
      ((D.parametrization_symm_holomorphic hhol i).contMDiffAt
            ((D.parametrization i).open_target.mem_nhds hx)).comp
        x contMDiff_subtype_val.contMDiffAt
    convert h using 1
    funext y
    exact D.patchHomeomorph_symm_eq_parametrization i y

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
abbrev SpecialPeriods.Threefold.Space :=
  gluingData.Space

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
@[instance_reducible]
def SpecialPeriods.Threefold.chartedSpace : ChartedSpace (ℂ × ComplexPlane₂) Space :=
  gluingData.chartedSpace

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
abbrev SpecialPeriods.Threefold.projection :
    Space → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  gluingData.projection

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.projection_proper : IsProperMap projection :=
  gluingData.projection_proper gluingData_localProjection_proper

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.space_compact : CompactSpace Space :=
  gluingData.compactSpace gluingData_localProjection_proper

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.space_t2Space : T2Space Space :=
  gluingData.spaceT2

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.space_secondCountable : SecondCountableTopology Space :=
  gluingData.secondCountableSpace_of_compactBase

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.space_isManifold :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω Space :=
  gluingData.isManifold gluingData_transition_holomorphic

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.space_nonempty : Nonempty Space :=
  ⟨gluingData.inclusion Option.none specialRegularFamilyPoint⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
def SpecialPeriods.Threefold.projectionSphere : Space → RiemannSphere :=
  SpecialPeriods.Triangle.triangleSphereUniformization ∘ projection

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
abbrev SpecialPeriods.Threefold.inclusion (i : Index) : localPiece i → Space :=
  gluingData.inclusion i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.inclusion_openEmbedding (i : Index) :
    Topology.IsOpenEmbedding (SpecialPeriods.Threefold.inclusion i) :=
  gluingData.inclusion_openEmbedding i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.inclusion_holomorphic (i : Index) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (SpecialPeriods.Threefold.inclusion i) :=
  gluingData.inclusion_holomorphic gluingData_transition_holomorphic i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.projection_inclusion (i : Index) (x : localPiece i) :
    projection (SpecialPeriods.Threefold.inclusion i x) = localProjectionToBase i x :=
  gluingData.projection_inclusion i x

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.inclusion_range (i : Index) :
    Set.range (SpecialPeriods.Threefold.inclusion i) =
      projection ⁻¹'
        (specialBaseCover.patch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  gluingData.inclusion_range i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
abbrev SpecialPeriods.Threefold.liftedPatch (i : Index) : TopologicalSpace.Opens Space :=
  gluingData.liftedPatch i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.localPieceChartedSpace SpecialPeriods.Threefold.localPiece_nonempty
    SpecialPeriods.Threefold.localPiece_t2Space
    SpecialPeriods.Threefold.localPiece_secondCountable
    SpecialPeriods.Threefold.localPiece_isManifold in
attribute [local instance] SpecialPeriods.Threefold.chartedSpace in
def SpecialPeriods.Threefold.patchBiholomorph (i : Index) :
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (localPiece i) (liftedPatch i) ω :=
  gluingData.patchBiholomorph gluingData_transition_holomorphic i

theorem retraction_leftInverse {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (i : C(A, X)) (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A) :
    Function.LeftInverse r i := fun a => congrArg (fun f : C(A, A) => f a) hir

def retractionHomotopyEquiv {A X : Type*} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X))
    (r : C(X, A)) (hir : r.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).HomotopyRel (i.comp r) (Set.range i)) :
    ContinuousMap.HomotopyEquiv A X where
  toFun := i
  invFun := r
  left_inv := by rw [hir]
  right_inv := ⟨H.toHomotopy.symm⟩

def Elliptic.discRadial (t : unitInterval) (z : SpecialPeriods.Disc) : SpecialPeriods.Disc :=
  ⟨(1 - (t : ℝ)) • (z : ℂ),
    by
    have ha : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
    have ha1 : 1 - (t : ℝ) ≤ 1 := by linarith [t.property.1]
    have hn : ‖(1 - (t : ℝ)) • (z : ℂ)‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact
        (mul_le_of_le_one_left (norm_nonneg _) ha1).trans_lt (SpecialPeriods.disc_norm_lt_one z)
    simpa [SpecialPeriods.unitDisc] using hn⟩

theorem Elliptic.discRadial_continuous :
    Continuous (fun p : unitInterval × SpecialPeriods.Disc => discRadial p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk
    _

@[simp]
theorem Elliptic.discRadial_zero (z : SpecialPeriods.Disc) : discRadial 0 z = z := by
  apply Subtype.ext
  simp [discRadial]

@[simp]
theorem Elliptic.discRadial_one (z : SpecialPeriods.Disc) : discRadial 1 z = discZero := by
  apply Subtype.ext
  simp [discRadial, discZero]

@[simp]
theorem Elliptic.discRadial_discZero (t : unitInterval) : discRadial t discZero = discZero := by
  apply Subtype.ext
  simp [discRadial, discZero]

theorem Elliptic.discRadial_familyRotation (j : Kind) (t : unitInterval)
    (z : SpecialPeriods.Disc) :
    discRadial t (familyRotation j z) = familyRotation j (discRadial t z) := by
  cases j <;> apply Subtype.ext
  · change
      (1 - (t : ℝ)) • (-SpecialPeriods.rho * (z : ℂ)) =
        -SpecialPeriods.rho * ((1 - (t : ℝ)) • (z : ℂ))
    simp only [Complex.real_smul]
    ring
  · change (1 - (t : ℝ)) • (-Complex.I * (z : ℂ)) = -Complex.I * ((1 - (t : ℝ)) • (z : ℂ))
    simp only [Complex.real_smul]
    ring

theorem Elliptic.discRadial_familyRotation_iterate (j : Kind) (t : unitInterval) (n : ℕ)
    (z : SpecialPeriods.Disc) :
    discRadial t ((familyRotation j)^[n] z) = (familyRotation j)^[n] (discRadial t z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', discRadial_familyRotation, ih]

def Elliptic.familyRadial (j : Kind) (t : unitInterval) (x : Family j) : Family j :=
  (discRadial t x.1, x.2)

theorem Elliptic.familyRadial_continuous (j : Kind) :
    Continuous (fun p : unitInterval × Family j => familyRadial j p.1 p.2) :=
  (discRadial_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
    (continuous_snd.comp continuous_snd)

@[simp]
theorem Elliptic.familyRadial_zero (j : Kind) (x : Family j) : familyRadial j 0 x = x := by
  exact Prod.ext (discRadial_zero x.1) rfl

@[simp]
theorem Elliptic.familyRadial_one (j : Kind) (x : Family j) :
    familyRadial j 1 x = (discZero, x.2) := by exact Prod.ext (discRadial_one x.1) rfl

theorem Elliptic.familyRadial_fixed (j : Kind) (t : unitInterval) (x : Family j)
    (hx : x.1 = discZero) : familyRadial j t x = x := by
  exact Prod.ext (by change discRadial t x.1 = x.1; rw [hx, discRadial_discZero]) rfl

theorem Elliptic.familyRadial_equivariant (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (t : unitInterval) (x : Family j) :
    letI := familyAction j v hv
    familyRadial j t (g • x) = g • familyRadial j t x := by
  let := familyAction j v hv
  rw [familyAction_apply, familyAction_apply]
  exact Prod.ext (discRadial_familyRotation_iterate j t g.toAdd.val x.1) rfl

def Elliptic.fillingRadial (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) : Filling j v hv → Filling j v hv := by
  letI := familyAction j v hv.1
  exact
    FiniteQuotient.descend (fun x => fillingQuotient j v hv (familyRadial j t x))
      (fun g x => by
        rw [familyRadial_equivariant]
        exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g _)

@[simp]
theorem Elliptic.fillingRadial_fillingQuotient (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : Family j) :
    fillingRadial j v hv t (fillingQuotient j v hv x) =
      fillingQuotient j v hv (familyRadial j t x) :=
  rfl

theorem Elliptic.fillingRadial_continuous (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v) :
    Continuous (fun p : unitInterval × Filling j v hv => fillingRadial j v hv p.1 p.2) := by
  have hq : Topology.IsQuotientMap (fillingQuotient j v hv) := isQuotientMap_quotient_mk'
  apply hq.continuous_lift_prod_right
  exact (fillingQuotient_continuous j v hv).comp (familyRadial_continuous j)

@[simp]
theorem Elliptic.fillingRadial_zero (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (x : Filling j v hv) : fillingRadial j v hv 0 x = x := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient, familyRadial_zero]

theorem Elliptic.fillingRadial_one_mem_central (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (x : Filling j v hv) : fillingRadial j v hv 1 x ∈ fillingProjection j v hv ⁻¹' { discZero } :=
  by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient, familyRadial_one]
  exact (discPower_eq_zero_iff j.order j.order_pos discZero).mpr rfl

theorem Elliptic.fillingRadial_fixed (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : Filling j v hv) (hx : fillingProjection j v hv x = discZero) :
    fillingRadial j v hv t x = x := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  change discPower j.order j.order_pos y.1 = discZero at hx
  rw [fillingRadial_fillingQuotient,
    familyRadial_fixed j t y ((discPower_eq_zero_iff j.order j.order_pos y.1).mp hx)]

def Elliptic.fillingCentralSubtypeInclusion (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (fillingProjection j v hv ⁻¹' { discZero }) (Filling j v hv) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def Elliptic.fillingCentralRetraction (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (Filling j v hv) (fillingProjection j v hv ⁻¹' { discZero }) :=
  ⟨fun x => ⟨fillingRadial j v hv 1 x, fillingRadial_one_mem_central j v hv x⟩,
    ((fillingRadial_continuous j v hv).comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩

def Elliptic.torusFibreMap (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) : ((familyPeriods j).point z).Torus → Filling j v hv :=
  fillingQuotient j v hv ∘ (familyPeriods j).fibreInclusion z

theorem Elliptic.torusFibreMap_holomorphic (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      ω (torusFibreMap j v hv z) := by
  let := (familyPeriods j).totalChartedSpace
  exact (fillingQuotient_holomorphic j v hv).comp ((familyPeriods j).fibreInclusion_holomorphic z)

theorem Elliptic.torusFibreMap_continuous (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) : Continuous (torusFibreMap j v hv z) :=
  (torusFibreMap_holomorphic j v hv z).continuous

@[simp]
theorem Elliptic.fillingProjection_torusFibreMap (j : Kind) (v : PeriodLattice)
    (hv : AdmissibleTwist j v) (z : SpecialPeriods.Disc) (x : ((familyPeriods j).point z).Torus) :
    fillingProjection j v hv (torusFibreMap j v hv z x) = discPower j.order j.order_pos z :=
  rfl

theorem Elliptic.range_torusFibreMap (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (z : SpecialPeriods.Disc) :
    Set.range (torusFibreMap j v hv z) =
      fillingProjection j v hv ⁻¹' {discPower j.order j.order_pos z} := by
  let := familyAction j v hv.1
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact fillingProjection_torusFibreMap j v hv z x
  · intro hq
    obtain ⟨x, rfl⟩ := fillingQuotient_surjective j v hv q
    have hp : discPower j.order j.order_pos x.1 = discPower j.order j.order_pos z := hq
    obtain ⟨r, hr, hrot⟩ := (discPower_eq_iff_familyRotation j z x.1).mp hp.symm
    let g : CyclicGroup j := Multiplicative.ofAdd (r : ZMod j.order)
    have hg : g.toAdd.val = r := ZMod.val_natCast_of_lt hr
    have hbase : (g • x).1 = z := by
      rw [familyAction_apply, hg]
      exact hrot
    have hx : g • x ∈ Set.range ((familyPeriods j).fibreInclusion z) := by
      rw [(familyPeriods j).range_fibreInclusion]
      exact hbase
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    change fillingQuotient j v hv ((familyPeriods j).fibreInclusion z y) = _
    rw [hy]
    exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g x

theorem Elliptic.fillingProjection_fibre_connected (j : Kind) (v : PeriodLattice)
    (hv : AdmissibleTwist j v) (b : SpecialPeriods.Disc) :
    IsConnected (fillingProjection j v hv ⁻¹' { b }) := by
  obtain ⟨z, rfl⟩ := discPower_surjective j.order j.order_pos b
  rw [← range_torusFibreMap j v hv z]
  exact isConnected_range (torusFibreMap_continuous j v hv z)

def Elliptic.Equivariant.Data.fillingHomeomorph {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    D.Space v hv ≃ₜ Elliptic.Filling j v hv :=
  Homeomorph.refl _

theorem Elliptic.Equivariant.Data.projection_fibre_isConnected {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v)
    (b : SpecialPeriods.Disc) : IsConnected (D.projection v hv ⁻¹' { b }) :=
  Elliptic.fillingProjection_fibre_connected j v hv b

def Elliptic.Equivariant.Data.fillingRadial {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) (t : unitInterval) :
    D.Space v hv → D.Space v hv :=
  Elliptic.fillingRadial j v hv t

@[simp]
theorem Elliptic.Equivariant.Data.fillingRadial_quotient {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v)
    (t : unitInterval) (x : D.TotalSpace) :
    D.fillingRadial v hv t (D.quotient v hv x) =
      D.quotient v hv (Elliptic.discRadial t x.1, x.2) :=
  rfl

theorem Elliptic.Equivariant.Data.fillingRadial_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (fun p : unitInterval × D.Space v hv => D.fillingRadial v hv p.1 p.2) :=
  Elliptic.fillingRadial_continuous j v hv

@[simp]
theorem Elliptic.Equivariant.Data.fillingRadial_zero {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.Space v hv) : D.fillingRadial v hv 0 x = x :=
  Elliptic.fillingRadial_zero j v hv x

theorem Elliptic.Equivariant.Data.fillingRadial_fixed {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v)
    (t : unitInterval) (x : D.Space v hv) (hx : D.projection v hv x = Elliptic.discZero) :
    D.fillingRadial v hv t x = x :=
  Elliptic.fillingRadial_fixed j v hv t x hx

def Elliptic.Equivariant.Data.fillingCentralSubtypeInclusion {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    ContinuousMap (D.projection v hv ⁻¹' { Elliptic.discZero }) (D.Space v hv) :=
  Elliptic.fillingCentralSubtypeInclusion j v hv

def Elliptic.Equivariant.Data.fillingCentralRetraction {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : PeriodLattice) (hv : Elliptic.AdmissibleTwist j v) :
    ContinuousMap (D.Space v hv) (D.projection v hv ⁻¹' { Elliptic.discZero }) :=
  Elliptic.fillingCentralRetraction j v hv

def FibreTopology.restrictPreimageFibreHomeomorph {X Y : Type*} [TopologicalSpace X] (f : X → Y)
    (S : Set Y) (b : S) : (S.restrictPreimage f ⁻¹' { b }) ≃ₜ (f ⁻¹' {(b : Y)}) := by
  let forward : (S.restrictPreimage f ⁻¹' { b }) → (f ⁻¹' {(b : Y)}) := fun x =>
    ⟨x.val.val, congrArg (fun y : S => (y : Y)) x.property⟩
  let backward : (f ⁻¹' {(b : Y)}) → (S.restrictPreimage f ⁻¹' { b }) := fun x =>
    ⟨⟨x.val, by
        change f x.val ∈ S
        rw [show f x.val = b.val from x.property]
        exact b.property⟩,
      Subtype.ext x.property⟩
  refine
    { toFun := forward
      invFun := backward
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

theorem FibreTopology.restrictPreimage_fibre_isConnected {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set Y) (b : S) (h : IsConnected (f ⁻¹' {(b : Y)})) :
    IsConnected (S.restrictPreimage f ⁻¹' { b }) :=
  isConnected_iff_connectedSpace.mpr
    ((restrictPreimageFibreHomeomorph f S b).connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp h))

theorem FibreTopology.preimage_singleton_comp_injective {X Y Z : Type*} (f : X → Y) (g : Y → Z)
    (hg : Function.Injective g) (b : Y) : (g ∘ f) ⁻¹' {g b} = f ⁻¹' { b } := by
  ext x
  exact hg.eq_iff

theorem FibreTopology.fibre_isConnected_comp_injective {X Y Z : Type*} [TopologicalSpace X]
    (f : X → Y) (g : Y → Z) (hg : Function.Injective g) (b : Y) (h : IsConnected (f ⁻¹' { b })) :
    IsConnected ((g ∘ f) ⁻¹' {g b}) := by
  rw [preimage_singleton_comp_injective f g hg b]
  exact h

theorem FibreTopology.fibre_isConnected_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (e : Y ≃ₜ Z) (b : Z)
    (h : IsConnected (f ⁻¹' {e.symm b})) : IsConnected ((e ∘ f) ⁻¹' { b }) := by
  have he := fibre_isConnected_comp_injective f e e.injective (e.symm b) h
  simpa only [e.apply_symm_apply] using he

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialRegularFamilyProjection_fibre_isConnected
    (b : regularPatch) : IsConnected (specialRegularFamilyProjection ⁻¹' { b }) := by
  let D :=
    regularFamilyData SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
      SpecialPeriods.specialPeriodMap_generator₂
  have hf (q : SpecialPeriods.TriangleRegularQuotient) : IsConnected (D.projection ⁻¹' { q }) := by
    obtain ⟨z, rfl⟩ :=
      (PeriodFamily.regularCovering SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁
            SpecialPeriods.specialPeriodMap_generator₂).surjective
        q
    apply isConnected_iff_connectedSpace.mpr
    exact
      (D.fibreHomeomorph
            (PeriodFamily.regularCovering SpecialPeriods.specialPeriodMap
              SpecialPeriods.specialPeriodMap_generator₁
              SpecialPeriods.specialPeriodMap_generator₂)
            z).connectedSpace_iff.mp
        inferInstance
  change IsConnected ((regularBiholomorph.toHomeomorph ∘ D.projection) ⁻¹' { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph D.projection regularBiholomorph.toHomeomorph b
      (hf (regularBiholomorph.symm b))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPieceCoordinate_fibre_isConnected
    (b : coordinateBall (specialBaseCover.radius Option.none)) :
    IsConnected
      (CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover ⁻¹' { b }) := by
  let D :=
    CuspPiece.restrictedData SpecialPeriods.specialCuspData specialBaseCover specialCuspRadius_le
  have he :
    CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover ⁻¹' { b } =
      CuspQuotient.projection SpecialPeriods.specialCuspData.correction
          (specialBaseCover.radius Option.none) ⁻¹'
        {(b : ℂ)} := by
    ext x
    exact Subtype.ext_iff
  rw [he]
  exact
    CuspUniformization.fibre_connected SpecialPeriods.specialCuspData.correction
      (specialBaseCover.radius Option.none) (specialBaseCover.radius_pos Option.none)
      D.radius_lt_one D.holomorphic D.smallDrift b

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialCuspPieceProjection_fibre_isConnected
    (b : specialBaseCover.fillingPatch Option.none) :
    IsConnected (specialCuspPieceProjection ⁻¹' { b }) := by
  change
    IsConnected
      ((((specialBaseCover.fillingChart Option.none).symm.toHomeomorph) ∘
          CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover) ⁻¹'
        { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph
      (CuspPiece.coordinate SpecialPeriods.specialCuspData specialBaseCover)
      (specialBaseCover.fillingChart Option.none).symm.toHomeomorph b
      (specialCuspPieceCoordinate_fibre_isConnected (specialBaseCover.fillingChart Option.none b))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPieceCoordinate_fibre_isConnected
    (j : Elliptic.Kind) (b : coordinateBall (specialBaseCover.radius (Option.some j))) :
    IsConnected
      (SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          specialBaseCover j ⁻¹'
        { b }) := by
  let f :=
    SpecialPeriods.EllipticFilling.fillingProjection SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂ j
  let S : Set SpecialPeriods.Disc :=
    SpecialPeriods.EllipticFilling.smallDisc (specialBaseCover.radius (Option.some j))
  let e :=
    SpecialPeriods.EllipticFilling.smallDiscHomeomorph (specialBaseCover.radius (Option.some j))
      (specialBaseCover.radius_lt_chart (Option.some j))
  have hf (q : SpecialPeriods.Disc) : IsConnected (f ⁻¹' { q }) :=
    (SpecialPeriods.EllipticFilling.localData SpecialPeriods.specialPeriodMap
          SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
          j).projection_fibre_isConnected
      j.twist (Elliptic.mainTwist_admissible j) q
  change IsConnected ((e ∘ S.restrictPreimage f) ⁻¹' { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph (S.restrictPreimage f) e b
      (FibreTopology.restrictPreimage_fibre_isConnected f S (e.symm b) (hf (e.symm b).val))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPieceProjection_fibre_isConnected
    (j : Elliptic.Kind) (b : specialBaseCover.fillingPatch (Option.some j)) :
    IsConnected (specialEllipticPieceProjection j ⁻¹' { b }) := by
  change
    IsConnected
      ((((specialBaseCover.fillingChart (Option.some j)).symm.toHomeomorph) ∘
          SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
            SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
            specialBaseCover j) ⁻¹'
        { b })
  exact
    FibreTopology.fibre_isConnected_comp_homeomorph
      (SpecialPeriods.EllipticFilling.pieceCoordinate SpecialPeriods.specialPeriodMap
        SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
        specialBaseCover j)
      (specialBaseCover.fillingChart (Option.some j)).symm.toHomeomorph b
      (specialEllipticPieceCoordinate_fibre_isConnected j
        (specialBaseCover.fillingChart (Option.some j) b))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.localProjection_fibre_isConnected (i : Index)
    (b : specialBaseCover.patch i) : IsConnected (localProjection i ⁻¹' { b }) := by
  cases i with
  | none => exact specialRegularFamilyProjection_fibre_isConnected b
  | some i =>
    cases i with
    | none => exact specialCuspPieceProjection_fibre_isConnected b
    | some j => exact specialEllipticPieceProjection_fibre_isConnected j b

theorem ThreefoldGluing.Data.projection_fibre_isConnected {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B)
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' { b })) (b : B) :
    IsConnected (D.projection ⁻¹' { b }) := by
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  rw [D.projection_fibre_eq_localImage i ⟨b, hi⟩]
  exact
    (hlocal i ⟨b, hi⟩).image (D.inclusion i) (D.inclusion_openEmbedding i).continuous.continuousOn

theorem ThreefoldGluing.Data.projection_surjective_of_connected_fibres {B : Type u}
    [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' { b })) :
    Function.Surjective D.projection := by
  intro b
  obtain ⟨x, hx⟩ := (D.projection_fibre_isConnected hlocal b).nonempty
  exact ⟨x, hx⟩

theorem ThreefoldGluing.Data.connectedSpace {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [ConnectedSpace B]
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i))
    (hlocal : ∀ i (b : D.patch i), IsConnected (D.localProjection i ⁻¹' { b })) :
    ConnectedSpace D.Space := by
  have hq : Topology.IsQuotientMap D.projection :=
    (D.projection_proper hproper).isClosedMap.isQuotientMap D.projection_continuous
      (D.projection_surjective_of_connected_fibres hlocal)
  apply connectedSpace_iff_univ.mpr
  simpa only [Set.preimage_univ] using
    hq.isCoinducing.isConnected_preimage_of_isClosed (D.projection_fibre_isConnected hlocal)
      isClosed_univ (isConnected_univ : IsConnected (Set.univ : Set B))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.gluingData_localProjection_fibre_isConnected (i : Index)
    (b : specialBaseCover.patch i) : IsConnected (gluingData.localProjection i ⁻¹' { b }) :=
  localProjection_fibre_isConnected i b

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.projection_fibre_isConnected
    (b : SpecialPeriods.TriangleCompactifiedOrbitSpace) : IsConnected (projection ⁻¹' { b }) :=
  gluingData.projection_fibre_isConnected gluingData_localProjection_fibre_isConnected b

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace
    SpecialPeriods.Threefold.chartedSpace in
theorem SpecialPeriods.Threefold.space_connected : ConnectedSpace Space :=
  gluingData.connectedSpace gluingData_localProjection_proper
    gluingData_localProjection_fibre_isConnected



end
