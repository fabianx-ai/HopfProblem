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
Original source lines 168789--182554; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.LCP.PeriodConstruction
import Lib.Geometry.Manifold.Instances.RiemannSphere
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

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
structure SpecialPeriods.Threefold.BaseCover where
  radius : Puncture → ℝ
  radius_pos : ∀ i, 0 < radius i
  radius_lt_chart : ∀ i, radius i < punctureChartRadius i
  pairwise_disjoint :
    Pairwise
      (fun i j =>
        Disjoint
          (coordinateDisc (punctureChart i) (radius i) :
            Set SpecialPeriods.TriangleCompactifiedOrbitSpace)
          (coordinateDisc (punctureChart j) (radius j) :
            Set SpecialPeriods.TriangleCompactifiedOrbitSpace))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.BaseCover.fillingPatch (C : SpecialPeriods.Threefold.BaseCover)
    (i : SpecialPeriods.Threefold.Puncture) :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.Threefold.coordinateDisc (SpecialPeriods.Threefold.punctureChart i) (C.radius i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.BaseCover.mem_fillingPatch
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∈ C.fillingPatch i ↔
      x ∈ (SpecialPeriods.Threefold.punctureChart i).source ∧
        ‖SpecialPeriods.Threefold.punctureChart i x‖ < C.radius i := by
  simp only [fillingPatch, SpecialPeriods.Threefold.mem_coordinateDisc, Metric.mem_ball,
    dist_zero_right]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_subset_chart
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ⊆
      (SpecialPeriods.Threefold.punctureChart i).source :=
  Set.inter_subset_left

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.coordinateBall_subset_target
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    Metric.ball (0 : ℂ) (C.radius i) ⊆ (SpecialPeriods.Threefold.punctureChart i).target := by
  rw [SpecialPeriods.Threefold.punctureChart_target]
  exact Metric.ball_subset_ball (C.radius_lt_chart i).le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_eq_inverse_image
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      (SpecialPeriods.Threefold.punctureChart i).symm '' Metric.ball 0 (C.radius i) :=
  SpecialPeriods.Threefold.coordinateDisc_eq_symm_image (SpecialPeriods.Threefold.punctureChart i)
    (C.coordinateBall_subset_target i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.point_mem_fillingPatch
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.puncturePoint i ∈ C.fillingPatch i :=
  SpecialPeriods.Threefold.center_mem_coordinateDisc (SpecialPeriods.Threefold.punctureChart i)
    (SpecialPeriods.Threefold.puncturePoint_mem_source i)
    (SpecialPeriods.Threefold.punctureChart_point i) (C.radius_pos i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_disjoint
    (C : SpecialPeriods.Threefold.BaseCover) {i j : SpecialPeriods.Threefold.Puncture}
    (hij : i ≠ j) :
    Disjoint (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)
      (C.fillingPatch j : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  C.pairwise_disjoint hij

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.point_mem_fillingPatch_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i j : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.puncturePoint i ∈ C.fillingPatch j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    exact Set.disjoint_left.mp (C.fillingPatch_disjoint hij) (C.point_mem_fillingPatch i) h
  · rintro rfl
    exact C.point_mem_fillingPatch i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.chart_eq_zero_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    SpecialPeriods.Threefold.punctureChart i x = 0 ↔
      x = SpecialPeriods.Threefold.puncturePoint i :=
  SpecialPeriods.Threefold.punctureChart_eq_zero_iff i (C.fillingPatch_subset_chart i hx)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.inverse_mem_fillingPatch
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (C.radius i)) :
    (SpecialPeriods.Threefold.punctureChart i).symm z ∈ C.fillingPatch i := by
  have ht := C.coordinateBall_subset_target i hz
  refine ⟨(SpecialPeriods.Threefold.punctureChart i).map_target ht, ?_⟩
  change
    SpecialPeriods.Threefold.punctureChart i ((SpecialPeriods.Threefold.punctureChart i).symm z) ∈
      Metric.ball 0 (C.radius i)
  rw [(SpecialPeriods.Threefold.punctureChart i).right_inv ht]
  exact hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.exists_baseCover_below (R : Puncture → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ C : BaseCover, ∀ i, C.radius i < R i := by
  obtain ⟨r, hr, _, _, hdisj⟩ :=
    exists_pairwise_disjoint_coordinateDiscs puncturePoint puncturePoint_injective punctureChart
      puncturePoint_mem_source punctureChart_point (fun _ => ⊤) (fun _ => trivial)
      (fun i => Min.min (R i) (punctureChartRadius i))
      (fun i => lt_min (hR i) (punctureChartRadius_pos i))
  exact
    ⟨{  radius := r
        radius_pos := fun i => (hr i).1
        radius_lt_chart := fun i => (hr i).2.trans_le (min_le_right _ _)
        pairwise_disjoint := hdisj }, fun i => (hr i).2.trans_le (min_le_left _ _)⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.sphereRadiusCap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    Puncture → ℝ
  | none => (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius
  | some _ => 1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.sphereRadiusCap_pos
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (i : Puncture) : 0 < sphereRadiusCap π hπ h₀ h₁ i := by
  cases i with
  | none => exact (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius_pos
  | some j => norm_num [sphereRadiusCap]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.baseCoverOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    BaseCover :=
  (exists_baseCover_below (sphereRadiusCap π hπ h₀ h₁) (sphereRadiusCap_pos π hπ h₀ h₁)).choose

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.baseCoverOfSphere_radius_lt_cap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (i : Puncture) : (baseCoverOfSphere π hπ h₀ h₁).radius i < sphereRadiusCap π hπ h₀ h₁ i :=
  (exists_baseCover_below (sphereRadiusCap π hπ h₀ h₁)
        (sphereRadiusCap_pos π hπ h₀ h₁)).choose_spec
    i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.baseCoverOfSphere_cusp_radius_bounds
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    0 < (baseCoverOfSphere π hπ h₀ h₁).radius Option.none ∧
      (baseCoverOfSphere π hπ h₀ h₁).radius Option.none <
          (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius ∧
        (baseCoverOfSphere π hπ h₀ h₁).radius Option.none <
          SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width :=
  ⟨(baseCoverOfSphere π hπ h₀ h₁).radius_pos Option.none,
    baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ Option.none,
    (baseCoverOfSphere π hπ h₀ h₁).radius_lt_chart Option.none⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularPatch :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  ⟨({ SpecialPeriods.triangleCuspPoint, SpecialPeriods.triangleCompactifiedCenterOne,
          SpecialPeriods.triangleCompactifiedCenterTwo } :
        Set SpecialPeriods.TriangleCompactifiedOrbitSpace)ᶜ,
    (((Set.finite_singleton SpecialPeriods.triangleCompactifiedCenterTwo).insert
            SpecialPeriods.triangleCompactifiedCenterOne).insert
        SpecialPeriods.triangleCuspPoint).isClosed.isOpen_compl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.mem_regularPatch
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∈ regularPatch ↔
      x ≠ SpecialPeriods.triangleCuspPoint ∧
        x ≠ SpecialPeriods.triangleCompactifiedCenterOne ∧
          x ≠ SpecialPeriods.triangleCompactifiedCenterTwo := by
  simp only [regularPatch, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.openInclusion_mem_regularPatch_iff
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ regularPatch ↔
      q ∈ SpecialPeriods.triangleOrbitRegularDomain := by
  rw [mem_regularPatch, SpecialPeriods.triangleOrbitRegularDomain_mem_iff]
  constructor
  · rintro ⟨_, h₁, h₂⟩
    exact
      ⟨fun h => h₁ (congrArg SpecialPeriods.triangleOpenInclusion h), fun h =>
        h₂ (congrArg SpecialPeriods.triangleOpenInclusion h)⟩
  · rintro ⟨h₁, h₂⟩
    exact
      ⟨SpecialPeriods.triangleOpenInclusion_ne_cusp q, fun h => h₁ (OnePoint.coe_injective h),
        fun h => h₂ (OnePoint.coe_injective h)⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularInclusion :
    SpecialPeriods.TriangleRegularQuotient → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleOpenInclusion ∘ SpecialPeriods.triangleRegularToOrbit

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding regularInclusion :=
  SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.comp
    SpecialPeriods.triangleRegularToOrbit_isOpenEmbedding

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularInclusion_mem
    (q : SpecialPeriods.TriangleRegularQuotient) : regularInclusion q ∈ regularPatch := by
  apply (openInclusion_mem_regularPatch_iff (SpecialPeriods.triangleRegularToOrbit q)).mpr
  exact Set.mem_range_self q

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularInclusion_range :
    Set.range regularInclusion =
      (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact regularInclusion_mem q
  · intro hx
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp ((mem_regularPatch x).mp hx).1
    have hq' : SpecialPeriods.triangleOpenInclusion q = x := hq
    have hreg : q ∈ SpecialPeriods.triangleOrbitRegularDomain :=
      (openInclusion_mem_regularPatch_iff q).mp (hq' ▸ hx)
    obtain ⟨r, hr⟩ := hreg
    exact ⟨r, (congrArg SpecialPeriods.triangleOpenInclusion hr).trans hq'⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularInclusion := by
  intro q
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω SpecialPeriods.triangleRegularToOrbit q :=
    (SpecialPeriods.triangleRegularOrbitBiholomorph.isLocalDiffeomorph q).comp (K := 𝓘(ℂ)) (P :=
      SpecialPeriods.TriangleOrbitSpace)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) SpecialPeriods.triangleOrbitRegularDomain
        (SpecialPeriods.triangleRegularOrbitBiholomorph q))
  exact
    hreg.comp (K := 𝓘(ℂ)) (P := SpecialPeriods.TriangleCompactifiedOrbitSpace)
      (SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph
        (SpecialPeriods.triangleRegularToOrbit q))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularInclusionToPatch
    (q : SpecialPeriods.TriangleRegularQuotient) : regularPatch :=
  ⟨regularInclusion q, regularInclusion_mem q⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularInclusionToPatch_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularInclusionToPatch :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) regularInclusion_isLocalDiffeomorph regularPatch
    regularInclusion_mem

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularInclusionToPatch_bijective :
    Function.Bijective regularInclusionToPatch := by
  constructor
  · intro q r h
    exact regularInclusion_isOpenEmbedding.injective (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ Set.range regularInclusion := by
      rw [regularInclusion_range]
      exact x.property
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, Subtype.ext hq⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleRegularQuotient regularPatch ω :=
  regularInclusionToPatch_isLocalDiffeomorph.diffeomorphOfBijective
    regularInclusionToPatch_bijective

abbrev SpecialPeriods.Threefold.Index :=
  Option Puncture

theorem SpecialPeriods.Threefold.mem_regularPatch_iff_ne_puncture
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∈ regularPatch ↔ ∀ i : Puncture, x ≠ puncturePoint i := by
  rw [mem_regularPatch]
  constructor
  · rintro ⟨hc, h₁, h₂⟩ i
    cases i with
    | none => exact hc
    | some j => cases j <;> assumption
  · intro h
    exact ⟨h Option.none, h (Option.some .three), h (Option.some .four)⟩

theorem SpecialPeriods.Threefold.not_mem_regularPatch_iff
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∉ regularPatch ↔ ∃ i : Puncture, x = puncturePoint i := by
  classical
  rw [mem_regularPatch_iff_ne_puncture]
  simp only [Classical.not_forall, ne_eq, Classical.not_not]

def SpecialPeriods.Threefold.BaseCover.patch (C : SpecialPeriods.Threefold.BaseCover) :
    SpecialPeriods.Threefold.Index →
      TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace
  | none => SpecialPeriods.Threefold.regularPatch
  | some i => C.fillingPatch i

theorem SpecialPeriods.Threefold.BaseCover.exists_patch (C : SpecialPeriods.Threefold.BaseCover)
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    ∃ i : SpecialPeriods.Threefold.Index, x ∈ C.patch i := by
  classical
  by_cases hx : x ∈ SpecialPeriods.Threefold.regularPatch
  · exact ⟨Option.none, hx⟩
  · obtain ⟨i, rfl⟩ := (SpecialPeriods.Threefold.not_mem_regularPatch_iff x).mp hx
    exact ⟨Option.some i, C.point_mem_fillingPatch i⟩

theorem SpecialPeriods.Threefold.BaseCover.isOpenCover (C : SpecialPeriods.Threefold.BaseCover) :
    TopologicalSpace.IsOpenCover C.patch := by
  change (⨆ i, C.patch i) = ⊤
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := C.exists_patch x
  exact (le_iSup C.patch i) hi

theorem SpecialPeriods.Threefold.BaseCover.patch_iUnion (C : SpecialPeriods.Threefold.BaseCover) :
    ⋃ i : SpecialPeriods.Threefold.Index,
        (C.patch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      Set.univ :=
  C.isOpenCover.iSup_set_eq_univ

theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_regular_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    x ∈ SpecialPeriods.Threefold.regularPatch ↔ x ≠ SpecialPeriods.Threefold.puncturePoint i := by
  constructor
  · intro h
    exact (SpecialPeriods.Threefold.mem_regularPatch_iff_ne_puncture x).mp h i
  · intro hne
    apply (SpecialPeriods.Threefold.mem_regularPatch_iff_ne_puncture x).mpr
    intro j hxj
    have hji : j = i := (C.point_mem_fillingPatch_iff j i).mp (hxj ▸ hx)
    exact hne (hxj.trans (congrArg SpecialPeriods.Threefold.puncturePoint hji))

theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_regular_iff_coordinate_ne_zero
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    x ∈ SpecialPeriods.Threefold.regularPatch ↔ SpecialPeriods.Threefold.punctureChart i x ≠ 0 :=
  (C.fillingPatch_regular_iff i hx).trans (not_congr (C.chart_eq_zero_iff i hx)).symm

theorem SpecialPeriods.Threefold.BaseCover.inverse_mem_regular_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (C.radius i)) :
    (SpecialPeriods.Threefold.punctureChart i).symm z ∈ SpecialPeriods.Threefold.regularPatch ↔
      z ≠ 0 := by
  rw [C.fillingPatch_regular_iff_coordinate_ne_zero i (C.inverse_mem_fillingPatch i hz),
    (SpecialPeriods.Threefold.punctureChart i).right_inv (C.coordinateBall_subset_target i hz)]

def SpecialPeriods.Threefold.coordinateBall (r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩

@[simp]
theorem SpecialPeriods.Threefold.mem_coordinateBall (r : ℝ) (z : ℂ) :
    z ∈ coordinateBall r ↔ z ∈ Metric.ball 0 r :=
  Iff.rfl

def SpecialPeriods.Threefold.coordinateDiscForward {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ) :
    coordinateDisc e.toOpenPartialHomeomorph r → coordinateBall r := fun x => ⟨e x, x.property.2⟩

def SpecialPeriods.Threefold.coordinateDiscInverse {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)
    (hball : Metric.ball 0 r ⊆ e.target) :
    coordinateBall r → coordinateDisc e.toOpenPartialHomeomorph r := fun z =>
  ⟨e.symm z, e.map_target (hball z.property),
    by
    change e (e.symm (z : ℂ)) ∈ Metric.ball 0 r
    have he : e (e.symm (z : ℂ)) = (z : ℂ) := e.right_inv (hball z.property)
    exact he.symm ▸ z.property⟩

theorem SpecialPeriods.Threefold.coordinateDiscForward_holomorphic {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscForward e r) := by
  have hf :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : coordinateDisc e.toOpenPartialHomeomorph r => e (x : X)) :=
    e.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun x => x.property.1)
  intro x
  have h :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun y => (coordinateDiscForward e r y : ℂ)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscForward e r) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hf x)

theorem SpecialPeriods.Threefold.coordinateDiscInverse_holomorphic {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)
    (hball : Metric.ball 0 r ⊆ e.target) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscInverse e r hball) := by
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : coordinateBall r => e.symm (z : ℂ)) :=
    e.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => hball z.property)
  intro z
  have h :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => (coordinateDiscInverse e r hball w : X)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscInverse e r hball) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hf z)

def SpecialPeriods.Threefold.coordinateDiscBiholomorph {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)
    (hball : Metric.ball 0 r ⊆ e.target) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (coordinateDisc e.toOpenPartialHomeomorph r) (coordinateBall r) ω
    where
  toFun := coordinateDiscForward e r
  invFun := coordinateDiscInverse e r hball
  left_inv x := Subtype.ext (e.left_inv x.property.1)
  right_inv z := Subtype.ext (e.right_inv (hball z.property))
  contMDiff_toFun := coordinateDiscForward_holomorphic e r
  contMDiff_invFun := coordinateDiscInverse_holomorphic e r hball

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.BaseCover.fillingChart (C : SpecialPeriods.Threefold.BaseCover)
    (i : SpecialPeriods.Threefold.Puncture) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (C.fillingPatch i)
      (SpecialPeriods.Threefold.coordinateBall (C.radius i)) ω :=
  SpecialPeriods.Threefold.coordinateDiscBiholomorph (SpecialPeriods.Threefold.puncturePartial i)
    (C.radius i) (C.coordinateBall_subset_target i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.BaseCover.fillingEmbedding (C : SpecialPeriods.Threefold.BaseCover)
    (i : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.coordinateBall (C.radius i) →
      SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  fun z => ((C.fillingChart i).symm z : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.BaseCover.punctureChart_fillingEmbedding
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (z : SpecialPeriods.Threefold.coordinateBall (C.radius i)) :
    SpecialPeriods.Threefold.punctureChart i (C.fillingEmbedding i z) = (z : ℂ) :=
  (SpecialPeriods.Threefold.punctureChart i).right_inv
    (C.coordinateBall_subset_target i z.property)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.fillingEmbedding_mem_regular_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (z : SpecialPeriods.Threefold.coordinateBall (C.radius i)) :
    C.fillingEmbedding i z ∈ SpecialPeriods.Threefold.regularPatch ↔ (z : ℂ) ≠ 0 :=
  C.inverse_mem_regular_iff i z.property

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.BaseCover.fillingEmbedding_eq_point_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (z : SpecialPeriods.Threefold.coordinateBall (C.radius i)) :
    C.fillingEmbedding i z = SpecialPeriods.Threefold.puncturePoint i ↔ (z : ℂ) = 0 := by
  constructor
  · intro h
    have he := congrArg (SpecialPeriods.Threefold.punctureChart i) h
    simpa only [C.punctureChart_fillingEmbedding,
      SpecialPeriods.Threefold.punctureChart_point] using he
  · intro h
    change
      (SpecialPeriods.Threefold.punctureChart i).symm (z : ℂ) =
        SpecialPeriods.Threefold.puncturePoint i
    rw [h, SpecialPeriods.Threefold.punctureChart_symm_zero]

def PeriodFamily.dualComplexMatrix (g : SpecialPeriods.TriangleGroup) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℂ)

@[simp]
theorem PeriodFamily.dualComplexMatrix_one : dualComplexMatrix 1 = 1 := by
  simp [dualComplexMatrix]

theorem PeriodFamily.dualComplexMatrix_mul (g h : SpecialPeriods.TriangleGroup) :
    dualComplexMatrix (g * h) = dualComplexMatrix g * dualComplexMatrix h := by
  simp only [dualComplexMatrix, map_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact Matrix.map_mul

@[simp]
theorem PeriodFamily.dualComplexMatrix_generator₁ :
    dualComplexMatrix SpecialPeriods.triangleGenerator₁ = A₁.map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, SpecialPeriods.triangleDualRepresentation_generator₁_matrix]

@[simp]
theorem PeriodFamily.dualComplexMatrix_generator₂ :
    dualComplexMatrix SpecialPeriods.triangleGenerator₂ = A₂.map (Int.castRingHom ℂ) := by
  rw [dualComplexMatrix, SpecialPeriods.triangleDualRepresentation_generator₂_matrix]

def PeriodFamily.matrixRight (M : Matrix (Fin 2) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => M i (![2, 3] k)

theorem PeriodFamily.periodMatrix_right (p : PeriodPoint) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (fun i k => (R * p.matrix) i (![2, 3] k)) = R := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [PeriodPoint.matrix, Matrix.mul_apply, Fin.sum_univ_two]

structure PeriodFamily.Data (V B : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B] where
  periods : HolomorphicPeriodMap V B
  base_holomorphic :
    ∀ g : SpecialPeriods.TriangleGroup,
      ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) ω (fun b : B => g • b)
  covariance₁ :
    ∀ b, periods.point (SpecialPeriods.triangleGenerator₁ • b) = (periods.point b).step₁
  covariance₂ :
    ∀ b, periods.point (SpecialPeriods.triangleGenerator₂ • b) = (periods.point b).step₂

def PeriodFamily.Data.rightBlock {V : Type*} {B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (g : SpecialPeriods.TriangleGroup) (b : B) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i k =>
  ((D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g) i (![2, 3] k)

private def PeriodFamily.Data.HasCovariance_mo1973_18367 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) : Prop :=
  ∀ b : B,
    ∃ R : Matrix (Fin 2) (Fin 2) ℂ,
      (D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g =
        R * (D.periods.point b).val.matrix

private theorem PeriodFamily.Data.hasCovariance_one_mo1973_18368 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    D.HasCovariance_mo1973_18367 1 := by
  intro b
  exact ⟨1, by simp⟩

private theorem PeriodFamily.Data.hasCovariance_mul_mo1973_18369 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    {g h : SpecialPeriods.TriangleGroup} (hg : D.HasCovariance_mo1973_18367 g)
    (hh : D.HasCovariance_mo1973_18367 h) : D.HasCovariance_mo1973_18367 (g * h) := by
  intro b
  obtain ⟨Rg, hg⟩ := hg (h • b)
  obtain ⟨Rh, hh⟩ := hh b
  refine ⟨Rg * Rh, ?_⟩
  rw [SemigroupAction.mul_smul, PeriodFamily.dualComplexMatrix_mul, ← Matrix.mul_assoc, hg,
    Matrix.mul_assoc, hh, Matrix.mul_assoc]

private theorem PeriodFamily.Data.hasCovariance_generator₁_mo1973_18370 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    D.HasCovariance_mo1973_18367 SpecialPeriods.triangleGenerator₁ := by
  intro b
  refine ⟨(D.periods.point b).val.R₁, ?_⟩
  rw [D.covariance₁, PeriodFamily.dualComplexMatrix_generator₁]
  change (D.periods.point b).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₁_matrix _
      ((D.periods.point b).val.τ_ne_zero (D.periods.point b).property.1),
    Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

private theorem PeriodFamily.Data.hasCovariance_generator₂_mo1973_18371 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    D.HasCovariance_mo1973_18367 SpecialPeriods.triangleGenerator₂ := by
  intro b
  refine ⟨(D.periods.point b).val.R₂, ?_⟩
  rw [D.covariance₂, PeriodFamily.dualComplexMatrix_generator₂]
  change (D.periods.point b).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) = _
  rw [PeriodPoint.step₂_matrix _
      ((D.periods.point b).val.τ_ne_zero (D.periods.point b).property.1),
    Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

private theorem PeriodFamily.Data.hasCovariance_pow_mo1973_18372 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    {g : SpecialPeriods.TriangleGroup} (hg : D.HasCovariance_mo1973_18367 g) (n : ℕ) :
    D.HasCovariance_mo1973_18367 (g ^ n) := by
  induction n with
  | zero => simpa using D.hasCovariance_one_mo1973_18368
  | succ n ih => simpa only [pow_succ] using D.hasCovariance_mul_mo1973_18369 ih hg

private theorem PeriodFamily.Data.cyclic_eq_generator_pow_mo1973_18373 {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) : x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simpa only [nsmul_eq_mul, mul_one] using (ZMod.natCast_zmod_val x.toAdd).symm

private theorem PeriodFamily.Data.hasCovariance_mo1973_18374 {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) : D.HasCovariance_mo1973_18367 g := by
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    rw [cyclic_eq_generator_pow_mo1973_18373 x, map_pow]
    exact D.hasCovariance_pow_mo1973_18372 D.hasCovariance_generator₁_mo1973_18370 _
  | inr x =>
    rw [cyclic_eq_generator_pow_mo1973_18373 x, map_pow]
    exact D.hasCovariance_pow_mo1973_18372 D.hasCovariance_generator₂_mo1973_18371 _
  | mul g h hg hh => exact D.hasCovariance_mul_mo1973_18369 hg hh

theorem PeriodFamily.Data.rightBlock_eq_of_covariance {V : Type*} {B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (R : Matrix (Fin 2) (Fin 2) ℂ)
    (hR :
      (D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g =
        R * (D.periods.point b).val.matrix) :
    D.rightBlock g b = R := by
  unfold rightBlock
  rw [hR, PeriodFamily.periodMatrix_right]

theorem PeriodFamily.Data.matrix_covariance {V : Type*} {B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) :
    (D.periods.point (g • b)).val.matrix * PeriodFamily.dualComplexMatrix g =
      D.rightBlock g b * (D.periods.point b).val.matrix := by
  obtain ⟨R, hR⟩ := D.hasCovariance_mo1973_18374 g b
  rw [D.rightBlock_eq_of_covariance g b R hR]
  exact hR

def SpecialPeriods.triangleRealRepresentation : TriangleGroup →* (RealPlane₄ ≃ₗ[ℝ] RealPlane₄) :=
  Matrix.SpecialLinearGroup.toLin'.comp
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).comp triangleDualRepresentation)

def SpecialPeriods.triangleRealEquiv (g : TriangleGroup) : RealPlane₄ ≃ₗ[ℝ] RealPlane₄ :=
  triangleRealRepresentation g

theorem SpecialPeriods.triangleRealEquiv_apply (g : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv g x =
      (triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℝ) *ᵥ x :=
  rfl

@[simp]
theorem SpecialPeriods.triangleRealEquiv_one :
    triangleRealEquiv 1 = LinearEquiv.refl ℝ RealPlane₄ :=
  triangleRealRepresentation.map_one

theorem SpecialPeriods.triangleRealEquiv_mul (g h : TriangleGroup) :
    triangleRealEquiv (g * h) = triangleRealEquiv g * triangleRealEquiv h :=
  triangleRealRepresentation.map_mul g h

theorem SpecialPeriods.triangleRealEquiv_mul_apply (g h : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv (g * h) x = triangleRealEquiv g (triangleRealEquiv h x) := by
  rw [triangleRealEquiv_mul]
  rfl

@[simp]
theorem SpecialPeriods.triangleRealEquiv_inv (g : TriangleGroup) :
    triangleRealEquiv g⁻¹ = (triangleRealEquiv g).symm :=
  triangleRealRepresentation.map_inv g

theorem SpecialPeriods.triangleRealEquiv_realCast (g : TriangleGroup) (v : Lattice) :
    triangleRealEquiv g (Elliptic.realCast v) =
      Elliptic.realCast ((triangleDualRepresentation g : LatticeMatrix) *ᵥ v) := by
  rw [triangleRealEquiv_apply]
  ext i
  exact
    (RingHom.map_mulVec (Int.castRingHom ℝ) (triangleDualRepresentation g : LatticeMatrix) v
        i).symm

theorem SpecialPeriods.triangleRealEquiv_mem_standardLattice (g : TriangleGroup) {x : RealPlane₄}
    (hx : x ∈ standardLattice) : triangleRealEquiv g x ∈ standardLattice := by
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact
    (Elliptic.standardLattice_mem_iff _).mpr
      ⟨(triangleDualRepresentation g : LatticeMatrix) *ᵥ v, triangleRealEquiv_realCast g v⟩

theorem SpecialPeriods.triangleRealEquiv_map_standardLattice (g : TriangleGroup) :
    standardLattice.map ((triangleRealEquiv g).restrictScalars ℤ).toLinearMap = standardLattice :=
  by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact triangleRealEquiv_mem_standardLattice g hy
  · intro hx
    refine ⟨triangleRealEquiv g⁻¹ x, triangleRealEquiv_mem_standardLattice g⁻¹ hx, ?_⟩
    change triangleRealEquiv g (triangleRealEquiv g⁻¹ x) = x
    rw [triangleRealEquiv_inv, LinearEquiv.apply_symm_apply]

def SpecialPeriods.triangleTorusLinearEquiv (g : TriangleGroup) : RealTorus₄ ≃ₗ[ℤ] RealTorus₄ :=
  Submodule.Quotient.equiv standardLattice standardLattice
    ((triangleRealEquiv g).restrictScalars ℤ) (triangleRealEquiv_map_standardLattice g)

def SpecialPeriods.triangleTorusHomeomorph (g : TriangleGroup) : RealTorus₄ ≃ₜ RealTorus₄
    where
  toEquiv := (triangleTorusLinearEquiv g).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp (triangleRealEquiv g).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp
        (triangleRealEquiv g).symm.toContinuousLinearEquiv.continuous

@[simp]
theorem SpecialPeriods.triangleTorusHomeomorph_mkQ (g : TriangleGroup) (x : RealPlane₄) :
    triangleTorusHomeomorph g (standardLattice.mkQ x) =
      standardLattice.mkQ (triangleRealEquiv g x) :=
  rfl

@[simp]
theorem SpecialPeriods.triangleTorusHomeomorph_zero (g : TriangleGroup) :
    triangleTorusHomeomorph g 0 = 0 :=
  (triangleTorusLinearEquiv g).map_zero

theorem SpecialPeriods.triangleTorusHomeomorph_add (g : TriangleGroup) (x y : RealTorus₄) :
    triangleTorusHomeomorph g (x + y) =
      triangleTorusHomeomorph g x + triangleTorusHomeomorph g y :=
  (triangleTorusLinearEquiv g).map_add x y

@[simp]
theorem SpecialPeriods.triangleTorusHomeomorph_one_apply (x : RealTorus₄) :
    triangleTorusHomeomorph 1 x = x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_one]
  rfl

@[simp]
theorem SpecialPeriods.triangleTorusHomeomorph_one :
    triangleTorusHomeomorph 1 = Homeomorph.refl RealTorus₄ := by
  apply Homeomorph.ext
  exact triangleTorusHomeomorph_one_apply

theorem SpecialPeriods.triangleTorusHomeomorph_mul_apply (g h : TriangleGroup) (x : RealTorus₄) :
    triangleTorusHomeomorph (g * h) x = triangleTorusHomeomorph g (triangleTorusHomeomorph h x) :=
  by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, triangleTorusHomeomorph_mkQ, triangleTorusHomeomorph_mkQ,
    triangleRealEquiv_mul_apply]

theorem SpecialPeriods.triangleTorusHomeomorph_mul (g h : TriangleGroup) :
    triangleTorusHomeomorph (g * h) =
      (triangleTorusHomeomorph h).trans (triangleTorusHomeomorph g) := by
  apply Homeomorph.ext
  exact triangleTorusHomeomorph_mul_apply g h

@[simp]
theorem SpecialPeriods.triangleTorusHomeomorph_inv (g : TriangleGroup) :
    triangleTorusHomeomorph g⁻¹ = (triangleTorusHomeomorph g).symm := by
  apply Homeomorph.ext
  intro x
  apply (triangleTorusHomeomorph g).injective
  rw [← triangleTorusHomeomorph_mul_apply, mul_inv_cancel, triangleTorusHomeomorph_one_apply,
    Homeomorph.apply_symm_apply]

@[instance_reducible]
def SpecialPeriods.triangleTorusAction : MulAction TriangleGroup RealTorus₄
    where
  smul g x := triangleTorusHomeomorph g x
  one_smul := triangleTorusHomeomorph_one_apply
  mul_smul := triangleTorusHomeomorph_mul_apply

theorem SpecialPeriods.triangleTorusAction_mkQ (g : TriangleGroup) (x : RealPlane₄) :
    letI := triangleTorusAction
    g • standardLattice.mkQ x =
      standardLattice.mkQ
        ((triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℝ) *ᵥ x) := by
  change triangleTorusHomeomorph g (standardLattice.mkQ x) = _
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_apply]

@[simp]
theorem SpecialPeriods.triangleTorusAction_zero (g : TriangleGroup) :
    letI := triangleTorusAction
    g • (0 : RealTorus₄) = 0 :=
  triangleTorusHomeomorph_zero g

theorem SpecialPeriods.triangleTorusAction_continuous :
    letI := triangleTorusAction
    ContinuousConstSMul TriangleGroup RealTorus₄ := by
  let := triangleTorusAction
  exact ⟨fun g => (triangleTorusHomeomorph g).continuous⟩

theorem SpecialPeriods.triangleTorusAction_generator₁_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleGenerator₁ • standardLattice.mkQ x =
      standardLattice.mkQ (Elliptic.flatLinear .three x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_generator₁_matrix]
  rfl

theorem SpecialPeriods.triangleTorusAction_generator₂_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleGenerator₂ • standardLattice.mkQ x =
      standardLattice.mkQ (Elliptic.flatLinear .four x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_generator₂_matrix]
  rfl

abbrev PeriodFamily.Data.TotalSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) :=
  D.periods.TotalSpace

@[instance_reducible]
def PeriodFamily.Data.totalAction {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : MulAction SpecialPeriods.TriangleGroup D.TotalSpace := by
  let := SpecialPeriods.triangleTorusAction
  exact inferInstanceAs (MulAction SpecialPeriods.TriangleGroup (B × RealTorus₄))

theorem PeriodFamily.Data.totalAction_zeroSection {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) :
    letI := D.totalAction
    g • D.periods.zeroSection b = D.periods.zeroSection (g • b) := by
  let := D.totalAction
  change (g • b, SpecialPeriods.triangleTorusHomeomorph g 0) = (g • b, 0)
  rw [SpecialPeriods.triangleTorusHomeomorph_zero]

theorem PeriodFamily.Data.periodEquiv_matrix {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B)
    (x : RealPlane₄) :
    D.periods.periodEquiv b x = (D.periods.point b).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem PeriodFamily.Data.realEquiv_complexCast (g : SpecialPeriods.TriangleGroup)
    (x : RealPlane₄) :
    (fun i => ((SpecialPeriods.triangleRealEquiv g x) i : ℂ)) =
      PeriodFamily.dualComplexMatrix g *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [SpecialPeriods.triangleRealEquiv_apply, PeriodFamily.dualComplexMatrix, Matrix.mulVec,
    dotProduct]

theorem PeriodFamily.Data.periodEquiv_monodromy {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (x : RealPlane₄) :
    D.periods.periodEquiv (g • b) (SpecialPeriods.triangleRealEquiv g x) =
      D.rightBlock g b *ᵥ D.periods.periodEquiv b x := by
  rw [D.periodEquiv_matrix, realEquiv_complexCast, Matrix.mulVec_mulVec, D.periodEquiv_matrix,
    Matrix.mulVec_mulVec, D.matrix_covariance]

theorem PeriodFamily.Data.periodEquiv_symm_monodromy {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (b : B) (w : ComplexPlane₂) :
    (D.periods.periodEquiv (g • b)).symm (D.rightBlock g b *ᵥ w) =
      SpecialPeriods.triangleRealEquiv g ((D.periods.periodEquiv b).symm w) := by
  apply (D.periods.periodEquiv (g • b)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_monodromy, LinearEquiv.apply_symm_apply]

def PeriodFamily.Data.complexLift {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (g : SpecialPeriods.TriangleGroup) (x : B × ComplexPlane₂) :
    B × ComplexPlane₂ :=
  (g • x.1, D.rightBlock g x.1 *ᵥ x.2)

theorem PeriodFamily.Data.complexLift_quotientMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (x : B × ComplexPlane₂) :
    letI := D.totalAction
    D.periods.quotientMap (D.complexLift g x) = g • D.periods.quotientMap x := by
  let := D.totalAction
  change
    (g • x.1,
        standardLattice.mkQ
          ((D.periods.periodEquiv (g • x.1)).symm (D.rightBlock g x.1 *ᵥ x.2))) =
      (g • x.1,
        SpecialPeriods.triangleTorusHomeomorph g
          (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [D.periodEquiv_symm_monodromy, SpecialPeriods.triangleTorusHomeomorph_mkQ]

@[instance_reducible]
def PeriodFamily.Data.coveringChartedSpace {V B : Type*} [NormedAddCommGroup V]
    [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] PeriodFamily.Data.coveringChartedSpace in
theorem PeriodFamily.Data.coveringManifold {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ V) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B
      ComplexPlane₂

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
theorem PeriodFamily.Data.periodMatrix_entry_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (i : Fin 2)
    (k : Fin 4) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : B => (D.periods.point b).val.matrix i k) := by
  fin_cases i
  · fin_cases k
    · exact contMDiff_const.mul D.periods.holomorphic_mu
    · exact D.periods.holomorphic_tau
    · exact contMDiff_const
    · exact contMDiff_const
  · fin_cases k
    · exact D.periods.holomorphic_beta
    · exact D.periods.holomorphic_mu
    · exact contMDiff_const
    · exact contMDiff_const

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
theorem PeriodFamily.Data.rightBlock_entry_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) (i k : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b : B => D.rightBlock g b i k) := by
  have h₀ :=
    ((D.periodMatrix_entry_holomorphic i 0).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 0 (![2, 3] k)))
  have h₁ :=
    ((D.periodMatrix_entry_holomorphic i 1).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 1 (![2, 3] k)))
  have h₂ :=
    ((D.periodMatrix_entry_holomorphic i 2).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 2 (![2, 3] k)))
  have h₃ :=
    ((D.periodMatrix_entry_holomorphic i 3).comp (D.base_holomorphic g)).mul
      (contMDiff_const (c := PeriodFamily.dualComplexMatrix g 3 (![2, 3] k)))
  convert ((h₀.add h₁).add h₂).add h₃ using 1
  funext b
  simp [rightBlock, Matrix.mul_apply, Fin.sum_univ_four, add_assoc, Function.comp_def]

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
theorem PeriodFamily.Data.linearLift_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun x : B × ComplexPlane₂ => D.rightBlock g x.1 *ᵥ x.2) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      (Prod.fst : B × ComplexPlane₂ → B) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (Prod.snd : B × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  apply contMDiff_pi_space.mpr
  intro i
  have h₀ := ((D.rightBlock_entry_holomorphic g i 0).comp hf).mul ((contMDiff_pi_space.mp hs) 0)
  have h₁ := ((D.rightBlock_entry_holomorphic g i 1).comp hf).mul ((contMDiff_pi_space.mp hs) 1)
  convert h₀.add h₁ using 1
  funext x
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Function.comp_def]

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
theorem PeriodFamily.Data.complexLift_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (g : SpecialPeriods.TriangleGroup) :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.complexLift g) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (modelWithCornersSelf ℂ V) ω
      (fun x : B × ComplexPlane₂ => g • x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (D.base_holomorphic g).comp contMDiff_fst
  have hs := D.linearLift_holomorphic g
  rw [modelWithCornersSelf_prod] at hf hs ⊢
  exact hf.prodMk hs

attribute [local instance] PeriodFamily.Data.coveringChartedSpace
    PeriodFamily.Data.coveringManifold in
theorem PeriodFamily.Data.totalAction_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] (g : SpecialPeriods.TriangleGroup) :
    letI := D.periods.totalChartedSpace
    letI := D.totalAction
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : D.TotalSpace => g • x) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  let := D.periods.coveringAction
  apply
    CoveringQuotient.contMDiff_of_comp (E := V × ComplexPlane₂) D.periods.quotientCoveringMap
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
  have h := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic g)
  convert h using 1
  funext x
  exact (D.complexLift_quotientMap g x).symm

def PeriodFamily.Data.BaseSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (_D : PeriodFamily.Data V B) : Type _ :=
  DiagonalQuotient.BaseSpace SpecialPeriods.TriangleGroup B

def PeriodFamily.Data.Space {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : Type _ :=
  @MulAction.orbitRel.Quotient SpecialPeriods.TriangleGroup D.TotalSpace _ D.totalAction

instance PeriodFamily.Data.baseSpaceTopology {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    TopologicalSpace D.BaseSpace :=
  inferInstanceAs (TopologicalSpace (DiagonalQuotient.BaseSpace SpecialPeriods.TriangleGroup B))

instance PeriodFamily.Data.spaceTopology {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : TopologicalSpace D.Space :=
  inferInstanceAs
    (TopologicalSpace
      (@MulAction.orbitRel.Quotient SpecialPeriods.TriangleGroup D.TotalSpace _ D.totalAction))

def PeriodFamily.Data.baseQuotient {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : B → D.BaseSpace :=
  DiagonalQuotient.baseQuotient SpecialPeriods.TriangleGroup B

def PeriodFamily.Data.quotient {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : D.TotalSpace → D.Space := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient SpecialPeriods.TriangleGroup B RealTorus₄

def PeriodFamily.Data.projection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : D.Space → D.BaseSpace := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.projection SpecialPeriods.TriangleGroup B RealTorus₄

@[simp]
theorem PeriodFamily.Data.projection_quotient {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (x : D.TotalSpace) :
    D.projection (D.quotient x) = D.baseQuotient (D.periods.projection x) :=
  rfl

theorem PeriodFamily.Data.quotient_surjective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Function.Surjective D.quotient := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_surjective SpecialPeriods.TriangleGroup B RealTorus₄

theorem PeriodFamily.Data.quotient_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Continuous D.quotient := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_continuous SpecialPeriods.TriangleGroup B RealTorus₄

theorem PeriodFamily.Data.projection_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Continuous D.projection := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.projection_continuous SpecialPeriods.TriangleGroup B RealTorus₄

theorem PeriodFamily.Data.quotient_isQuotientMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Topology.IsQuotientMap D.quotient := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_isQuotientMap SpecialPeriods.TriangleGroup B RealTorus₄

theorem PeriodFamily.Data.quotient_eq_iff {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (x y : D.TotalSpace) :
    letI := D.totalAction
    D.quotient x = D.quotient y ↔ ∃ g : SpecialPeriods.TriangleGroup, g • y = x := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_eq_iff SpecialPeriods.TriangleGroup B RealTorus₄ x y

@[simp]
theorem PeriodFamily.Data.quotient_smul {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) (g : SpecialPeriods.TriangleGroup) (x : D.TotalSpace) :
    letI := D.totalAction
    D.quotient (g • x) = D.quotient x := by
  let := SpecialPeriods.triangleTorusAction
  exact DiagonalQuotient.quotient_smul SpecialPeriods.TriangleGroup B RealTorus₄ g x

theorem PeriodFamily.Data.quotientCoveringMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) :
    letI := D.totalAction
    IsQuotientCoveringMap D.quotient SpecialPeriods.TriangleGroup := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact DiagonalQuotient.quotientCoveringMap (F := RealTorus₄) hq

theorem PeriodFamily.Data.projection_proper {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) :
    IsProperMap D.projection := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact DiagonalQuotient.projection_proper (F := RealTorus₄) hq

theorem PeriodFamily.Data.baseT2Space {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) [T2Space B]
    [LocallyCompactSpace B] [ProperlyDiscontinuousSMul SpecialPeriods.TriangleGroup B] :
    T2Space D.BaseSpace :=
  DiagonalQuotient.baseT2Space hq

theorem PeriodFamily.Data.spaceT2Space {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [T2Space D.BaseSpace] : T2Space D.Space := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  let : T2Space (DiagonalQuotient.BaseSpace SpecialPeriods.TriangleGroup B) :=
    ‹T2Space D.BaseSpace›
  exact DiagonalQuotient.spaceT2Space (F := RealTorus₄) hq

theorem PeriodFamily.Data.spaceT2Space_of_properlyDiscontinuous {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) [T2Space B]
    [LocallyCompactSpace B] [ProperlyDiscontinuousSMul SpecialPeriods.TriangleGroup B] :
    T2Space D.Space := by
  let := D.baseT2Space hq
  exact D.spaceT2Space hq

theorem PeriodFamily.Data.spaceSecondCountable {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [SecondCountableTopology B] : SecondCountableTopology D.Space := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact DiagonalQuotient.spaceSecondCountable (F := RealTorus₄) hq

@[instance_reducible]
def PeriodFamily.Data.chartedSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) :
    ChartedSpace (V × ComplexPlane₂) D.Space := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact CoveringQuotient.chartedSpace (E := V × ComplexPlane₂) (D.quotientCoveringMap hq)

theorem PeriodFamily.Data.isManifold {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.chartedSpace hq
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.Space := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.isManifold (D.quotientCoveringMap hq) ω D.totalAction_holomorphic

theorem PeriodFamily.Data.quotient_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.contMDiff_project (D.quotientCoveringMap hq) ω D.totalAction_holomorphic

def PeriodFamily.Data.fibreHomeomorph {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    (D.periods.point b).Torus ≃ₜ (D.projection ⁻¹' {D.baseQuotient b}) := by
  let := SpecialPeriods.triangleTorusAction
  let := SpecialPeriods.triangleTorusAction_continuous
  exact
    (D.periods.torusHomeomorph b).symm.trans
      (DiagonalQuotient.fibreHomeomorphOver (F := RealTorus₄) hq b).symm

def PeriodFamily.Data.zeroSection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B) : D.BaseSpace → D.Space := by
  let := D.totalAction
  refine Quotient.lift (fun b : B => D.quotient (D.periods.zeroSection b)) ?_
  rintro b b' ⟨g, hg⟩
  rw [← hg, ← D.totalAction_zeroSection, D.quotient_smul]

@[simp]
theorem PeriodFamily.Data.zeroSection_baseQuotient {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    D.zeroSection (D.baseQuotient b) = D.quotient (D.periods.zeroSection b) :=
  rfl

@[simp]
theorem PeriodFamily.Data.projection_zeroSection {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : D.BaseSpace) :
    D.projection (D.zeroSection b) = b := by
  induction b using Quotient.inductionOn with
  | h b => rfl

theorem PeriodFamily.Data.zeroSection_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) :
    Continuous D.zeroSection := by
  exact
    isQuotientMap_quotient_mk'.continuous_iff.mpr
      (D.quotient_continuous.comp (continuous_id.prodMk continuous_const))

theorem PeriodFamily.Data.quotient_isLocalDiffeomorph {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact
    CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap hq)
      D.totalAction_holomorphic

def PeriodFamily.regularPeriods (P : HolomorphicPeriodMap ℂ ℍ) :
    HolomorphicPeriodMap ℂ SpecialPeriods.TriangleRegularPoint
    where
  point z := P.point z.val
  holomorphic_tau :=
    P.holomorphic_tau.comp (contMDiff_subtype_val (U := SpecialPeriods.triangleRegularDomain))
  holomorphic_mu :=
    P.holomorphic_mu.comp (contMDiff_subtype_val (U := SpecialPeriods.triangleRegularDomain))
  holomorphic_beta :=
    P.holomorphic_beta.comp (contMDiff_subtype_val (U := SpecialPeriods.triangleRegularDomain))

def PeriodFamily.regularData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Data ℂ SpecialPeriods.TriangleRegularPoint
    where
  periods := regularPeriods P
  base_holomorphic := SpecialPeriods.triangleRegularAction_holomorphic
  covariance₁
    z := by
    change
      P.point
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁
            z.val) =
        _
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply]
    exact h₁ z.val
  covariance₂
    z := by
    change
      P.point
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂
            z.val) =
        _
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply]
    exact h₂ z.val

theorem PeriodFamily.regularCovering (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    IsQuotientCoveringMap (regularData P h₁ h₂).baseQuotient SpecialPeriods.TriangleGroup :=
  SpecialPeriods.triangleRegularProject_covering

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.regularFamilyData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData P h₁ h₂

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.RegularFamily (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Type :=
  (regularFamilyData P h₁ h₂).Space

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.regularFamilyChartedSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    ChartedSpace (ℂ × ComplexPlane₂) (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularFamily_t2Space (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    T2Space (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).spaceT2Space_of_properlyDiscontinuous
    (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularFamily_secondCountable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    SecondCountableTopology (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).spaceSecondCountable (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularFamily_isManifold (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := regularFamilyChartedSpace P h₁ h₂
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).isManifold (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularFamilyProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    RegularFamily P h₁ h₂ → regularPatch :=
  regularBiholomorph ∘ (regularFamilyData P h₁ h₂).projection

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularFamilyProjection_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    IsProperMap (regularFamilyProjection P h₁ h₂) :=
  regularBiholomorph.toHomeomorph.isProperMap.comp
    ((regularFamilyData P h₁ h₂).projection_proper (PeriodFamily.regularCovering P h₁ h₂))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularFamilyProjectionToBase (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    RegularFamily P h₁ h₂ → SpecialPeriods.TriangleCompactifiedOrbitSpace := fun x =>
  (regularFamilyProjection P h₁ h₂ x : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularFamilyZeroSection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    regularPatch → RegularFamily P h₁ h₂ :=
  (regularFamilyData P h₁ h₂).zeroSection ∘ regularBiholomorph.symm

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.regularFamilyZeroSection_continuous
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Continuous (regularFamilyZeroSection P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).zeroSection_continuous.comp regularBiholomorph.symm.continuous

def SpecialPeriods.Triangle.firstSector : Set ℍ :=
  {z | z.re < -(1 / 2) ∧ 1 < ‖(z : ℂ)‖}

def SpecialPeriods.Triangle.secondSector : Set ℍ :=
  {z | stripLeft < z.re ∧ stripRight < ‖(z : ℂ) - (stripLeft : ℂ)‖}

def SpecialPeriods.Triangle.firstExcluded : Set ℍ :=
  {z | -(1 / 2) < z.re ∨ ‖(z : ℂ)‖ < 1}

def SpecialPeriods.Triangle.secondExcluded : Set ℍ :=
  {z | z.re < stripLeft ∨ ‖(z : ℂ) - (stripLeft : ℂ)‖ < stripRight}

def SpecialPeriods.Triangle.circularDoubleInterior : Set ℍ :=
  firstSector ∩ secondSector

theorem SpecialPeriods.Triangle.stripLeft_add_stripRight : stripLeft + stripRight = -1 := by
  unfold stripLeft stripRight
  ring

theorem SpecialPeriods.Triangle.stripLeft_lt_neg_one : stripLeft < -1 := by
  linarith [stripLeft_add_stripRight, stripRight_pos]

theorem SpecialPeriods.Triangle.firstExcluded_subset_pingPongOne : firstExcluded ⊆ pingPongOne := by
  intro z hz
  rcases hz with hx | hn
  · change -1 < z.re
    linarith
  · have hr := Complex.re_le_norm (-(z : ℂ))
    simp only [Complex.neg_re, UpperHalfPlane.coe_re, norm_neg] at hr
    change -1 < z.re
    linarith

theorem SpecialPeriods.Triangle.secondExcluded_subset_pingPongTwo :
    secondExcluded ⊆ pingPongTwo := by
  intro z hz
  rcases hz with hx | hn
  · exact hx.trans stripLeft_lt_neg_one
  · have hr := Complex.re_le_norm ((z : ℂ) - (stripLeft : ℂ))
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at hr
    change z.re < -1
    linarith [stripLeft_add_stripRight]

theorem SpecialPeriods.Triangle.pingPongTwo_subset_firstSector : pingPongTwo ⊆ firstSector := by
  intro z hz
  change z.re < -1 at hz
  refine ⟨by linarith, ?_⟩
  have hr := Complex.re_le_norm (-(z : ℂ))
  simp only [Complex.neg_re, UpperHalfPlane.coe_re, norm_neg] at hr
  linarith

theorem SpecialPeriods.Triangle.pingPongOne_subset_secondSector : pingPongOne ⊆ secondSector := by
  intro z hz
  change -1 < z.re at hz
  refine ⟨stripLeft_lt_neg_one.trans hz, ?_⟩
  have hr := Complex.re_le_norm ((z : ℂ) - (stripLeft : ℂ))
  simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at hr
  linarith [stripLeft_add_stripRight]

theorem SpecialPeriods.Triangle.secondExcluded_subset_firstSector :
    secondExcluded ⊆ firstSector :=
  secondExcluded_subset_pingPongTwo.trans pingPongTwo_subset_firstSector

theorem SpecialPeriods.Triangle.firstExcluded_subset_secondSector :
    firstExcluded ⊆ secondSector :=
  firstExcluded_subset_pingPongOne.trans pingPongOne_subset_secondSector

theorem SpecialPeriods.Triangle.circularDoubleInterior_disjoint_firstExcluded :
    Disjoint circularDoubleInterior firstExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact lt_asymm hz.1.1 hx
  · exact lt_asymm hz.1.2 hn

theorem SpecialPeriods.Triangle.circularDoubleInterior_disjoint_secondExcluded :
    Disjoint circularDoubleInterior secondExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact lt_asymm hz.2.1 hx
  · exact lt_asymm hz.2.2 hn

theorem SpecialPeriods.Triangle.generatorOne_firstSector :
    Set.MapsTo (fun z : ℍ => generatorOneSL • z) firstSector firstExcluded := by
  intro z hz
  left
  change -(1 / 2) < (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hn : 1 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2]
  simp only [← neg_div]
  apply (lt_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
  nlinarith

theorem SpecialPeriods.Triangle.norm_add_one_lt_norm_of_re_lt_half (z : ℍ)
    (hz : z.re < -(1 / 2)) : ‖(z : ℂ) + 1‖ < ‖(z : ℂ)‖ := by
  have hsq : ‖(z : ℂ) + 1‖ ^ 2 < ‖(z : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

theorem SpecialPeriods.Triangle.generatorOne_sq_firstSector :
    Set.MapsTo (fun z : ℍ => (generatorOneSL ^ 2) • z) firstSector firstExcluded := by
  intro z hz
  right
  change ‖(((generatorOneSL ^ 2) • z : ℍ) : ℂ)‖ < 1
  rw [generatorOneSL_sq_smul_coe]
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr z.ne_zero)).mpr (norm_add_one_lt_norm_of_re_lt_half z hz.1)

private def SpecialPeriods.Triangle.secondShift_mo1973_18636 (z : ℍ) : ℂ :=
  (z : ℂ) - (stripLeft : ℂ)

private theorem SpecialPeriods.Triangle.secondShift_re_mo1973_18637 (z : ℍ) :
    (secondShift_mo1973_18636 z).re = z.re - stripLeft := by simp [secondShift_mo1973_18636]

private theorem SpecialPeriods.Triangle.secondShift_add_real_ne_zero_mo1973_18638 (z : ℍ)
    (a : ℝ) : secondShift_mo1973_18636 z + (a : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [secondShift_mo1973_18636, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    sub_zero, add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.stripLeft_eq_neg_stripRight_sub_one_mo1973_18639 :
    stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]

private theorem SpecialPeriods.Triangle.width_eq_two_stripRight_add_one_mo1973_18640 :
    width = 2 * stripRight + 1 := by
  unfold stripRight
  ring

private theorem SpecialPeriods.Triangle.stripRight_sq_complex_mo1973_18641 :
    (stripRight : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, stripRight_sq]
  norm_num

private theorem SpecialPeriods.Triangle.generatorTwo_secondShift_mo1973_18642 (z : ℍ) :
    secondShift_mo1973_18636 (generatorTwoSL • z) =
      (stripRight : ℂ) * (secondShift_mo1973_18636 z - stripRight) /
        (secondShift_mo1973_18636 z + stripRight) := by
  have hd := secondShift_add_real_ne_zero_mo1973_18638 z stripRight
  have hs := stripRight_sq_complex_mo1973_18641
  unfold secondShift_mo1973_18636 at *
  rw [generatorTwoSL_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_18639,
    width_eq_two_stripRight_add_one_mo1973_18640] at *
  push_cast at *
  have he :
    (z : ℂ) + (2 * (stripRight : ℂ) + 1) = (z : ℂ) - (-(stripRight : ℂ) - 1) + stripRight := by
    ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.generatorTwo_sq_secondShift_mo1973_18643 (z : ℍ) :
    secondShift_mo1973_18636 ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) ^ 2 / secondShift_mo1973_18636 z := by
  have hz : secondShift_mo1973_18636 z ≠ 0 := by
    simpa using secondShift_add_real_ne_zero_mo1973_18638 z 0
  have hd := secondShift_add_real_ne_zero_mo1973_18638 z stripRight
  have hR : (stripRight : ℂ) ≠ 0 := by exact_mod_cast stripRight_pos.ne'
  rw [pow_two, SemigroupAction.mul_smul, generatorTwo_secondShift_mo1973_18642,
    generatorTwo_secondShift_mo1973_18642]
  field_simp [hz, hd, hR]
  ring

private theorem SpecialPeriods.Triangle.generatorTwo_cube_secondShift_mo1973_18644 (z : ℍ) :
    secondShift_mo1973_18636 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) * (secondShift_mo1973_18636 z + stripRight) /
        (secondShift_mo1973_18636 z - stripRight) := by
  have hd : secondShift_mo1973_18636 z - (stripRight : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_eq_add_neg] using
      secondShift_add_real_ne_zero_mo1973_18638 z (-stripRight)
  have hs := stripRight_sq_complex_mo1973_18641
  unfold secondShift_mo1973_18636 at *
  rw [generatorTwoSL_cube_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_18639,
    width_eq_two_stripRight_add_one_mo1973_18640] at *
  push_cast at *
  have he : (z : ℂ) + 1 = (z : ℂ) - (-(stripRight : ℂ) - 1) - stripRight := by ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.norm_sub_div_add_lt_one_mo1973_18645 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ < 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 < ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero]
    nlinarith [mul_pos hr hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem SpecialPeriods.Triangle.re_add_div_sub_pos_mo1973_18646 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : r < ‖u‖) : 0 < ((u + (r : ℂ)) / (u - (r : ℂ))).re := by
  have hd : u - (r : ℂ) ≠ 0 := by
    intro h
    have he : u = (r : ℂ) := sub_eq_zero.mp h
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hu
    exact lt_irrefl r hu
  have hsq : r ^ 2 < Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.div_re, ← add_div]
  apply div_pos ?_ (Complex.normSq_pos.mpr hd)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
    Complex.ofReal_im, add_zero, sub_zero]
  rw [Complex.normSq_apply] at hsq
  nlinarith

private theorem SpecialPeriods.Triangle.re_neg_sq_div_neg_mo1973_18647 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : (-(r : ℂ) ^ 2 / u).re < 0 := by
  have hd : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hnum : -(r ^ 2) * u.re < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_neg_of_neg_of_pos hnum (Complex.normSq_pos.mpr hd)

theorem SpecialPeriods.Triangle.generatorTwo_secondSector :
    Set.MapsTo (fun z : ℍ => generatorTwoSL • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inr ?_
  change ‖secondShift_mo1973_18636 (generatorTwoSL • z)‖ < stripRight
  rw [generatorTwo_secondShift_mo1973_18642, mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 < (secondShift_mo1973_18636 z).re := by
    rw [secondShift_re_mo1973_18637]
    exact sub_pos.mpr hz.1
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (norm_sub_div_add_lt_one_mo1973_18645 stripRight_pos hrez)
      stripRight_pos

theorem SpecialPeriods.Triangle.generatorTwo_sq_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inl ?_
  have hrez : 0 < (secondShift_mo1973_18636 z).re := by
    rw [secondShift_re_mo1973_18637]
    exact sub_pos.mpr hz.1
  have h := re_neg_sq_div_neg_mo1973_18647 stripRight_pos hrez
  rw [← generatorTwo_sq_secondShift_mo1973_18643 z, secondShift_re_mo1973_18637] at h
  exact sub_neg.mp h

theorem SpecialPeriods.Triangle.generatorTwo_cube_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) secondSector secondExcluded := by
  intro z hz
  refine Or.inl ?_
  have hnorm : stripRight < ‖secondShift_mo1973_18636 z‖ := hz.2
  have h : (secondShift_mo1973_18636 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re < 0 := by
    rw [generatorTwo_cube_secondShift_mo1973_18644, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, MulZeroClass.zero_mul, sub_zero]
    exact
      mul_neg_of_neg_of_pos (neg_neg_of_pos stripRight_pos)
        (re_add_div_sub_pos_mo1973_18646 stripRight_pos hnorm)
  rw [secondShift_re_mo1973_18637] at h
  exact sub_neg.mp h

private theorem SpecialPeriods.lift_neWord_domain_subset_mo1973_18651 {ι G α : Type*} [Group G]
    [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (X : ι → Set α)
    (D : Set α) (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ X i) {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f w.prod • D ⊆ X i := by
  induction w with
  | singleton x hx => simpa using hD _ x hx
  | @append i j k l w₁ hne w₂ _ih₁ ih₂ =>
    calc
      Monoid.CoprodI.lift f (Monoid.CoprodI.NeWord.append w₁ hne w₂).prod • D =
          Monoid.CoprodI.lift f w₁.prod • Monoid.CoprodI.lift f w₂.prod • D := by
        simp [SemigroupAction.mul_smul]
      _ ⊆ Monoid.CoprodI.lift f w₁.prod • X k := (Set.smul_set_subset_smul_set_iff.mpr ih₂)
      _ ⊆ X i := Monoid.CoprodI.lift_word_ping_pong f X hpp w₁ hne

private theorem SpecialPeriods.tiling_cyclicPowerHom_two_mo1973_18652 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem SpecialPeriods.tiling_cyclicPowerHom_three_mo1973_18653 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem SpecialPeriods.cyclicThree_domain_subset_mo1973_18654 {G α : Type*} [Group G]
    [MulAction G α] (a : G) (ha : a ^ 3 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => a • z) S T)
    (h₂ : Set.MapsTo (fun z => a ^ 2 • z) S T) (g : Multiplicative (ZMod 3)) (hg : g ≠ 1) :
    cyclicPowerHom 3 a ha g • S ⊆ T := by
  have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 3),
          x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
      g hg
  rcases hc with rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [tiling_cyclicPowerHom_two_mo1973_18652]
    exact Set.smul_set_subset_iff.mpr h₂

private theorem SpecialPeriods.cyclicFour_domain_subset_mo1973_18655 {G α : Type*} [Group G]
    [MulAction G α] (b : G) (hb : b ^ 4 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => b • z) S T)
    (h₂ : Set.MapsTo (fun z => b ^ 2 • z) S T) (h₃ : Set.MapsTo (fun z => b ^ 3 • z) S T)
    (g : Multiplicative (ZMod 4)) (hg : g ≠ 1) : cyclicPowerHom 4 b hb g • S ⊆ T := by
  have hc :
    g = Multiplicative.ofAdd (1 : ZMod 4) ∨
      g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 4),
          x ≠ 1 →
            x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
      g hg
  rcases hc with rfl | rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [tiling_cyclicPowerHom_two_mo1973_18652]
    exact Set.smul_set_subset_iff.mpr h₂
  · rw [tiling_cyclicPowerHom_three_mo1973_18653]
    exact Set.smul_set_subset_iff.mpr h₃

theorem SpecialPeriods.triangleLift_mapsTo_pingPongUnion {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (hDa₁ : Set.MapsTo (fun z => a • z) D X)
    (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D X) (hDb₁ : Set.MapsTo (fun z => b • z) D Y)
    (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D Y) (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D Y)
    (g : TriangleGroup) (hg : g ≠ 1) :
    Set.MapsTo (fun z => triangleLift a b ha hb g • z) D (X ∪ Y) := by
  classical
  let H : Bool → Type := fun i => cond i (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i =>
    match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i =>
      match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have hto_ne : toI g ≠ 1 := by
    intro h
    apply hg
    calc
      g = fromI (toI g) := (DFunLike.congr_fun hleft g).symm
      _ = 1 := by rw [h, map_one]
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i := by
    intro i j hij h hh
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact cyclicThree_domain_subset_mo1973_18654 a ha Y X ha₁ ha₂ h hh
    · exact cyclicFour_domain_subset_mo1973_18655 b hb X Y hb₁ hb₂ hb₃ h hh
    · exact (hij rfl).elim
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ U i := by
    intro i h hh
    cases i
    · exact cyclicThree_domain_subset_mo1973_18654 a ha D X hDa₁ hDa₂ h hh
    · exact cyclicFour_domain_subset_mo1973_18655 b hb D Y hDb₁ hDb₂ hDb₃ h hh
  let : (i : Bool) → DecidableEq (H i) := fun _ => Classical.decEq _
  let r := Monoid.CoprodI.Word.equiv (M := H) (toI g)
  have hr : r.prod = toI g := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply (toI g)
  have hr_ne : r ≠ Monoid.CoprodI.Word.empty := by
    intro h
    apply hto_ne
    rw [← hr, h, Monoid.CoprodI.Word.prod_empty]
  obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word r hr_ne
  have hwprod : w.prod = toI g := by
    change w.toWord.prod = toI g
    rw [hw]
    exact hr
  have himage := lift_neWord_domain_subset_mo1973_18651 f U D hpp hstart w
  have hUi : U i ⊆ X ∪ Y := by
    cases i
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have heval : triangleLift a b ha hb g = Monoid.CoprodI.lift f (toI g) :=
    DFunLike.congr_fun hrepresentation g
  intro z hz
  rw [heval, ← hwprod]
  exact hUi (Set.smul_set_subset_iff.mp himage hz)

theorem SpecialPeriods.triangleLift_disjoint_domain_translate {G α : Type*} [Group G]
    [MulAction G α] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (hDa₁ : Set.MapsTo (fun z => a • z) D X)
    (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D X) (hDb₁ : Set.MapsTo (fun z => b • z) D Y)
    (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D Y) (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D Y)
    (hDX : Disjoint D X) (hDY : Disjoint D Y) (g : TriangleGroup) (hg : g ≠ 1) :
    Disjoint D (triangleLift a b ha hb g • D) := by
  apply (hDX.sup_right hDY).mono_right
  exact
    Set.smul_set_subset_iff.mpr
      (triangleLift_mapsTo_pingPongUnion a b ha hb X Y D ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂
        hDb₃ g hg)

theorem SpecialPeriods.triangleLift_eq_one_of_domain_mem {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y D : Set α)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (hDa₁ : Set.MapsTo (fun z => a • z) D X)
    (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D X) (hDb₁ : Set.MapsTo (fun z => b • z) D Y)
    (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D Y) (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D Y)
    (hDX : Disjoint D X) (hDY : Disjoint D Y) (g : TriangleGroup) {z : α} (hz : z ∈ D)
    (hgz : triangleLift a b ha hb g • z ∈ D) : g = 1 := by
  by_contra hg
  have hd :=
    triangleLift_disjoint_domain_translate a b ha hb X Y D ha₁ ha₂ hb₁ hb₂ hb₃ hDa₁ hDa₂ hDb₁ hDb₂
      hDb₃ hDX hDY g hg
  exact hd.le_bot ⟨hgz, ⟨z, hz, rfl⟩⟩

theorem SpecialPeriods.Triangle.generatorOnePerm_firstSector :
    Set.MapsTo (fun z : ℍ => generatorOnePerm z) firstSector firstExcluded :=
  generatorOne_firstSector

theorem SpecialPeriods.Triangle.generatorOnePerm_sq_firstSector :
    Set.MapsTo (fun z : ℍ => (generatorOnePerm ^ 2) z) firstSector firstExcluded := by
  intro z hz
  change (generatorOnePerm ^ 2) z ∈ firstExcluded
  rw [generatorOnePerm_pow_apply]
  exact generatorOne_sq_firstSector hz

theorem SpecialPeriods.Triangle.generatorTwoPerm_secondSector :
    Set.MapsTo (fun z : ℍ => generatorTwoPerm z) secondSector secondExcluded :=
  generatorTwo_secondSector

theorem SpecialPeriods.Triangle.generatorTwoPerm_sq_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoPerm ^ 2) z) secondSector secondExcluded := by
  intro z hz
  change (generatorTwoPerm ^ 2) z ∈ secondExcluded
  rw [generatorTwoPerm_pow_apply]
  exact generatorTwo_sq_secondSector hz

theorem SpecialPeriods.Triangle.generatorTwoPerm_cube_secondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoPerm ^ 3) z) secondSector secondExcluded := by
  intro z hz
  change (generatorTwoPerm ^ 3) z ∈ secondExcluded
  rw [generatorTwoPerm_pow_apply]
  exact generatorTwo_cube_secondSector hz

theorem SpecialPeriods.Triangle.eq_one_of_circularDoubleInterior_mem
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ circularDoubleInterior)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ circularDoubleInterior) : g = 1 :=
  by
  exact
    SpecialPeriods.triangleLift_eq_one_of_domain_mem generatorOnePerm generatorTwoPerm
      generatorOnePerm_cube generatorTwoPerm_fourth firstExcluded secondExcluded
      circularDoubleInterior
      (fun _ hw => generatorOnePerm_firstSector (secondExcluded_subset_firstSector hw))
      (fun _ hw => generatorOnePerm_sq_firstSector (secondExcluded_subset_firstSector hw))
      (fun _ hw => generatorTwoPerm_secondSector (firstExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_sq_secondSector (firstExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_cube_secondSector (firstExcluded_subset_secondSector hw))
      (fun _ hw => generatorOnePerm_firstSector hw.1)
      (fun _ hw => generatorOnePerm_sq_firstSector hw.1)
      (fun _ hw => generatorTwoPerm_secondSector hw.2)
      (fun _ hw => generatorTwoPerm_sq_secondSector hw.2)
      (fun _ hw => generatorTwoPerm_cube_secondSector hw.2)
      circularDoubleInterior_disjoint_firstExcluded circularDoubleInterior_disjoint_secondExcluded
      g hz hgz

def SpecialPeriods.Triangle.fordInterior : Set ℍ :=
  {z | stripLeft < z.re ∧ z.re < stripRight ∧ 1 < ‖(z : ℂ) + 1‖ ∧ 1 < ‖(z : ℂ)‖}

theorem SpecialPeriods.Triangle.fordInterior_isOpen : IsOpen fordInterior :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
    ((isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const
            ((UpperHalfPlane.continuous_coe.add continuous_const).norm)).inter
        (isOpen_lt continuous_const UpperHalfPlane.continuous_coe.norm)))

theorem SpecialPeriods.Triangle.fordInterior_subset_fordRegion : fordInterior ⊆ fordRegion := by
  intro z hz
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

theorem SpecialPeriods.Triangle.fordInterior_subset_secondSector : fordInterior ⊆ secondSector := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hn : 1 < Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hprod : 0 < stripRight * (z.re - stripLeft) := mul_pos stripRight_pos (sub_pos.mpr hz.1)
  have hs : stripRight ^ 2 < ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
    have hleft : stripLeft = -1 - stripRight := by linarith [stripLeft_add_stripRight]
    rw [hleft] at hprod ⊢
    nlinarith [stripRight_sq]
  nlinarith [norm_nonneg ((z : ℂ) - (stripLeft : ℂ)), stripRight_pos]

theorem SpecialPeriods.Triangle.fordInterior_left_mem_circularDoubleInterior (z : ℍ)
    (hz : z ∈ fordInterior) (hx : z.re < -(1 / 2)) : z ∈ circularDoubleInterior :=
  ⟨⟨hx, hz.2.2.2⟩, fordInterior_subset_secondSector hz⟩

theorem SpecialPeriods.Triangle.exists_mem_open_ne_re_and_image_re (e : ℍ ≃ₜ ℍ) (c : ℝ)
    (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) : ∃ z ∈ U, z.re ≠ c ∧ (e z).re ≠ c := by
  have hd : Dense {z : ℍ | z.re ≠ c} :=
    (dense_compl_singleton c).preimage UpperHalfPlane.isOpenMap_re
  have he : Dense {z : ℍ | (e z).re ≠ c} :=
    (dense_compl_singleton c).preimage (UpperHalfPlane.isOpenMap_re.comp e.isOpenMap)
  have ho : IsOpen {z : ℍ | z.re ≠ c} :=
    isOpen_compl_singleton.preimage UpperHalfPlane.continuous_re
  obtain ⟨z, hz⟩ :=
    he.inter_open_nonempty (U ∩ {z : ℍ | z.re ≠ c}) (hU.inter ho)
      (hd.inter_open_nonempty U hU hne)
  exact ⟨z, hz.1.1, hz.1.2, hz.2⟩

private theorem SpecialPeriods.Triangle.norm_lt_norm_add_one_of_re_gt_half_mo1973_18679 (z : ℍ)
    (hx : -(1 / 2) < z.re) : ‖(z : ℂ)‖ < ‖(z : ℂ) + 1‖ := by
  have hsq : ‖(z : ℂ)‖ ^ 2 < ‖(z : ℂ) + 1‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

private theorem SpecialPeriods.Triangle.norm_real_sub_inv_gt_mo1973_18680 {r : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 = 1 / 2) {u : ℂ} (hu : u ≠ 0) (hx : u.re < r) : r < ‖(r : ℂ) - u⁻¹‖ := by
  have he : (r : ℂ) - u⁻¹ = ((r : ℂ) * u - 1) / u := by field_simp
  have hnum : r ^ 2 * Complex.normSq u < Complex.normSq ((r : ℂ) * u - 1) := by
    simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal, map_one, mul_one,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul, sub_zero]
    nlinarith [mul_lt_mul_of_pos_left hx hr]
  have hsq : r ^ 2 < ‖(r : ℂ) - u⁻¹‖ ^ 2 := by
    rw [he, Complex.sq_norm, Complex.normSq_div]
    exact (lt_div_iff₀ (Complex.normSq_pos.mpr hu)).mpr hnum
  nlinarith [norm_nonneg ((r : ℂ) - u⁻¹)]

theorem SpecialPeriods.Triangle.fordInterior_right_mem_circularDoubleInterior (z : ℍ)
    (hz : z ∈ fordInterior) (hx : -(1 / 2) < z.re) :
    (generatorOneSL ^ 2 : SL(2, ℝ)) • z ∈ circularDoubleInterior := by
  have hd : 1 < Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.2]
  have hp : 0 < Complex.normSq (z : ℂ) := zero_lt_one.trans hd
  have hc : 1 < Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hshift : 0 < Complex.normSq (z : ℂ) + 2 * z.re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hc ⊢
    nlinarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ)).re < -(1 / 2)
    rw [generatorOneSL_sq_smul_coe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
      UpperHalfPlane.coe_re]
    have hfrac : -(1 / 2 : ℝ) < z.re / Complex.normSq (z : ℂ) :=
      (lt_div_iff₀ hp).mpr (by linarith)
    linarith
  · rw [generatorOneSL_sq_smul_coe]
    have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
      field_simp [z.ne_zero]
      ring
    rw [he, norm_neg, norm_div]
    exact
      (one_lt_div (norm_pos_iff.mpr z.ne_zero)).mpr
        (norm_lt_norm_add_one_of_re_gt_half_mo1973_18679 z hx)
  · change stripLeft < ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ)).re
    rw [generatorOneSL_sq_smul_coe]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
      UpperHalfPlane.coe_re]
    have hfrac : z.re / Complex.normSq (z : ℂ) < stripRight := by
      apply (div_lt_iff₀ hp).mpr
      exact hz.2.1.trans (by simpa only [mul_one] using mul_lt_mul_of_pos_left hd stripRight_pos)
    linarith [stripLeft_add_stripRight]
  · rw [generatorOneSL_sq_smul_coe]
    have hL : stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]
    rw [hL]
    push_cast
    have he : (-1 : ℂ) - (z : ℂ)⁻¹ - (-(stripRight : ℂ) - 1) = (stripRight : ℂ) - (z : ℂ)⁻¹ := by
      ring
    rw [he]
    exact norm_real_sub_inv_gt_mo1973_18680 stripRight_pos stripRight_sq z.ne_zero hz.2.1

theorem SpecialPeriods.Triangle.generatorOne_not_mem_fordInterior (z : ℍ)
    (hz : z ∈ fordInterior) : generatorOneSL • z ∉ fordInterior := by
  intro hw
  have hn := hw.2.2.2
  rw [generatorOneSL_smul_coe, norm_neg, norm_inv] at hn
  exact lt_asymm hn (inv_lt_one_of_one_lt₀ hz.2.2.1)

theorem SpecialPeriods.Triangle.generatorOne_sq_not_mem_fordInterior (z : ℍ)
    (hz : z ∈ fordInterior) : (generatorOneSL ^ 2 : SL(2, ℝ)) • z ∉ fordInterior := by
  intro hw
  have hn := hw.2.2.1
  have he : ((((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) + 1) = -(z : ℂ)⁻¹ := by
    rw [generatorOneSL_sq_smul_coe]
    ring
  rw [he, norm_neg, norm_inv] at hn
  exact lt_asymm hn (inv_lt_one_of_one_lt₀ hz.2.2.2)

@[instance_reducible]
def SpecialPeriods.Triangle.instMulAction1 : MulAction SpecialPeriods.TriangleGroup ℍ :=
  SpecialPeriods.triangleGeometricAction

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.first_generator_inv_eq_sq_mo1973_18685 :
    SpecialPeriods.triangleGenerator₁⁻¹ = SpecialPeriods.triangleGenerator₁ ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using SpecialPeriods.triangleGenerator₁_cube

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.first_generator_inv_apply_mo1973_18686 (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z =
      (generatorOneSL ^ 2) • z := by
  rw [first_generator_inv_eq_sq_mo1973_18685, map_pow,
    SpecialPeriods.triangleGeometricRepresentation_generator₁, generatorOnePerm_pow_apply]

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.right_mem_circularDouble_mo1973_18687 (z : ℍ)
    (hz : z ∈ fordInterior) (hx : -(1 / 2) < z.re) :
    SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z ∈
      circularDoubleInterior := by
  rw [first_generator_inv_apply_mo1973_18686]
  exact fordInterior_right_mem_circularDoubleInterior z hz hx

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
private theorem SpecialPeriods.Triangle.eq_one_of_fordInterior_mem_off_axis_mo1973_18688
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ fordInterior)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ fordInterior)
    (hx : z.re ≠ -(1 / 2))
    (hgx : (SpecialPeriods.triangleGeometricRepresentation g z).re ≠ -(1 / 2)) : g = 1 := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hgx with hgx | hgx
  · exact
      eq_one_of_circularDoubleInterior_mem g
        (fordInterior_left_mem_circularDoubleInterior z hz hx)
        (fordInterior_left_mem_circularDoubleInterior _ hgz hgx)
  · have hm :
      SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleGenerator₁⁻¹ * g) z ∈
        circularDoubleInterior := by
      change (SpecialPeriods.triangleGenerator₁⁻¹ * g) • z ∈ circularDoubleInterior
      simpa only [SemigroupAction.mul_smul, SpecialPeriods.triangleGeometricAction_smul] using
        right_mem_circularDouble_mo1973_18687 _ hgz hgx
    have he :=
      eq_one_of_circularDoubleInterior_mem (SpecialPeriods.triangleGenerator₁⁻¹ * g)
        (fordInterior_left_mem_circularDoubleInterior z hz hx) hm
    have hg : g = SpecialPeriods.triangleGenerator₁ := (inv_mul_eq_one.mp he).symm
    rw [hg, SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] at hgz
    exact False.elim (generatorOne_not_mem_fordInterior z hz hgz)
  · have hm :
      SpecialPeriods.triangleGeometricRepresentation (g * SpecialPeriods.triangleGenerator₁)
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z) ∈
        circularDoubleInterior := by
      change
        (g * SpecialPeriods.triangleGenerator₁) • (SpecialPeriods.triangleGenerator₁⁻¹ • z) ∈
          circularDoubleInterior
      rw [SemigroupAction.mul_smul, smul_inv_smul, SpecialPeriods.triangleGeometricAction_smul]
      exact fordInterior_left_mem_circularDoubleInterior _ hgz hgx
    have he :=
      eq_one_of_circularDoubleInterior_mem (g * SpecialPeriods.triangleGenerator₁)
        (right_mem_circularDouble_mo1973_18687 z hz hx) hm
    have hg : g = SpecialPeriods.triangleGenerator₁⁻¹ := eq_inv_of_mul_eq_one_left he
    apply False.elim
    apply generatorOne_sq_not_mem_fordInterior z hz
    rw [hg, first_generator_inv_apply_mo1973_18686] at hgz
    exact hgz
  · have hm :
      SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.triangleGenerator₁⁻¹ * g * SpecialPeriods.triangleGenerator₁)
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z) ∈
        circularDoubleInterior := by
      change
        (SpecialPeriods.triangleGenerator₁⁻¹ * g * SpecialPeriods.triangleGenerator₁) •
            (SpecialPeriods.triangleGenerator₁⁻¹ • z) ∈
          circularDoubleInterior
      rw [SemigroupAction.mul_smul, smul_inv_smul, SemigroupAction.mul_smul]
      simpa only [SpecialPeriods.triangleGeometricAction_smul] using
        right_mem_circularDouble_mo1973_18687 _ hgz hgx
    have he :=
      eq_one_of_circularDoubleInterior_mem
        (SpecialPeriods.triangleGenerator₁⁻¹ * g * SpecialPeriods.triangleGenerator₁)
        (right_mem_circularDouble_mo1973_18687 z hz hx) hm
    have he' :=
      congrArg
        (fun h : SpecialPeriods.TriangleGroup =>
          SpecialPeriods.triangleGenerator₁ * h * SpecialPeriods.triangleGenerator₁⁻¹)
        he
    simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, one_mul, mul_one,
      mul_inv_cancel_left] using he'

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
theorem SpecialPeriods.Triangle.eq_one_of_fordInterior_mem (g : SpecialPeriods.TriangleGroup)
    {z : ℍ} (hz : z ∈ fordInterior)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ fordInterior) : g = 1 := by
  let U : Set ℍ :=
    fordInterior ∩ (SpecialPeriods.triangleGeometricRepresentation g) ⁻¹' fordInterior
  have hU : IsOpen U :=
    fordInterior_isOpen.inter
      (fordInterior_isOpen.preimage (SpecialPeriods.triangleGeometricBiholomorph g).continuous)
  have hne : U.Nonempty := ⟨z, hz, hgz⟩
  obtain ⟨w, hw, hx, hgx⟩ :=
    exists_mem_open_ne_re_and_image_re
      (SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph (-(1 / 2)) U hU hne
  exact eq_one_of_fordInterior_mem_off_axis_mo1973_18688 g hw.1 hw.2 hx hgx

attribute [local instance] SpecialPeriods.Triangle.instMulAction1 in
theorem SpecialPeriods.Triangle.eq_one_of_fordInterior_eq (g : SpecialPeriods.TriangleGroup)
    {z w : ℍ} (hz : z ∈ fordInterior) (hw : w ∈ fordInterior)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) : g = 1 :=
  eq_one_of_fordInterior_mem g hz (hzw ▸ hw)

def SpecialPeriods.Triangle.verticalReflection (a : ℝ) : ℍ ≃ₜ ℍ
    where
  toFun z := ⟨(a : ℂ) - conj (z : ℂ), by simpa using z.im_pos⟩
  invFun z := ⟨(a : ℂ) - conj (z : ℂ), by simpa using z.im_pos⟩
  left_inv z := by apply UpperHalfPlane.ext; simp
  right_inv z := by apply UpperHalfPlane.ext; simp
  continuous_toFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (a : ℂ) - conj (z : ℂ))
    fun_prop
  continuous_invFun := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (a : ℂ) - conj (z : ℂ))
    fun_prop

@[simp]
theorem SpecialPeriods.Triangle.verticalReflection_re (a : ℝ) (z : ℍ) :
    (verticalReflection a z).re = a - z.re := by
  change ((a : ℂ) - conj (z : ℂ)).re = a - z.re
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re, UpperHalfPlane.coe_re]

@[simp]
theorem SpecialPeriods.Triangle.verticalReflection_im (a : ℝ) (z : ℍ) :
    (verticalReflection a z).im = z.im := by
  change ((a : ℂ) - conj (z : ℂ)).im = z.im
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.conj_im, zero_sub, neg_neg,
    UpperHalfPlane.coe_im]

theorem SpecialPeriods.Triangle.verticalReflection_involutive (a : ℝ) :
    Function.Involutive (verticalReflection a) :=
  (verticalReflection a).left_inv

theorem SpecialPeriods.Triangle.verticalReflection_fixed_iff (a : ℝ) (z : ℍ) :
    verticalReflection a z = z ↔ z.re = a / 2 := by
  constructor
  · intro h
    have hr := congrArg UpperHalfPlane.re h
    rw [verticalReflection_re] at hr
    linarith
  · intro h
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (verticalReflection a z).re = z.re
      rw [verticalReflection_re]
      linarith
    · exact verticalReflection_im a z

def SpecialPeriods.Triangle.rightReflection : ℍ ≃ₜ ℍ :=
  verticalReflection (-1)

def SpecialPeriods.Triangle.leftReflection : ℍ ≃ₜ ℍ :=
  verticalReflection (-(width + 1))

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_coe (z : ℍ) :
    (rightReflection z : ℂ) = -1 - conj (z : ℂ) := by simp [verticalReflection, rightReflection]

@[simp]
theorem SpecialPeriods.Triangle.leftReflection_coe (z : ℍ) :
    (leftReflection z : ℂ) = -((width : ℂ) + 1) - conj (z : ℂ) := by
  simp [verticalReflection, leftReflection]

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_re (z : ℍ) : (rightReflection z).re = -1 - z.re :=
  by simp [rightReflection]

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_norm (z : ℍ) :
    ‖(rightReflection z : ℂ)‖ = ‖(z : ℂ) + 1‖ := by
  rw [rightReflection_coe]
  calc
    _ = ‖-conj ((z : ℂ) + 1)‖ := by congr 1; simp; ring
    _ = _ := by rw [norm_neg, Complex.norm_conj]

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_add_one_norm (z : ℍ) :
    ‖(rightReflection z : ℂ) + 1‖ = ‖(z : ℂ)‖ := by
  rw [rightReflection_coe]
  calc
    _ = ‖-conj (z : ℂ)‖ := by congr 1; ring
    _ = _ := by rw [norm_neg, Complex.norm_conj]

theorem SpecialPeriods.Triangle.rightReflection_involutive :
    Function.Involutive rightReflection :=
  verticalReflection_involutive _

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_fixed_iff (z : ℍ) :
    rightReflection z = z ↔ z.re = -(1 / 2) := by
  simpa only [rightReflection, neg_div] using verticalReflection_fixed_iff (-1) z

@[simp]
theorem SpecialPeriods.Triangle.leftReflection_fixed_iff (z : ℍ) :
    leftReflection z = z ↔ z.re = stripLeft :=
  verticalReflection_fixed_iff _ _

theorem SpecialPeriods.Triangle.conjugate_denominatorOne_ne_zero (z : ℍ) : conj (z : ℂ) + 1 ≠ 0 :=
  by
  simpa only [map_add, map_one, map_ne_zero] using
    (map_ne_zero (starRingEnd ℂ)).mpr (denominatorOne_ne_zero z)

private def SpecialPeriods.Triangle.circleReflectionMap_mo1973_18716 (z : ℍ) : ℍ :=
  ⟨-1 + 1 / (conj (z : ℂ) + 1),
    by
    simp only [one_div, Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero, zero_add,
      Complex.inv_im, Complex.conj_im, add_zero, neg_neg, UpperHalfPlane.coe_im]
    exact div_pos z.im_pos (Complex.normSq_pos.mpr (conjugate_denominatorOne_ne_zero z))⟩

private theorem SpecialPeriods.Triangle.circleReflectionMap_involutive_mo1973_18717 :
    Function.Involutive circleReflectionMap_mo1973_18716 := by
  intro z
  apply UpperHalfPlane.ext
  change -1 + 1 / (conj (-1 + 1 / (conj (z : ℂ) + 1)) + 1) = (z : ℂ)
  simp

private theorem SpecialPeriods.Triangle.circleReflectionMap_continuous_mo1973_18718 :
    Continuous circleReflectionMap_mo1973_18716 := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : ℍ => -1 + 1 / (conj (z : ℂ) + 1))
  exact
    continuous_const.add
      (continuous_const.div
        ((Complex.continuous_conj.comp UpperHalfPlane.continuous_coe).add continuous_const)
        conjugate_denominatorOne_ne_zero)

def SpecialPeriods.Triangle.circleReflection : ℍ ≃ₜ ℍ
    where
  toFun := circleReflectionMap_mo1973_18716
  invFun := circleReflectionMap_mo1973_18716
  left_inv := circleReflectionMap_involutive_mo1973_18717
  right_inv := circleReflectionMap_involutive_mo1973_18717
  continuous_toFun := circleReflectionMap_continuous_mo1973_18718
  continuous_invFun := circleReflectionMap_continuous_mo1973_18718

@[simp]
theorem SpecialPeriods.Triangle.circleReflection_coe (z : ℍ) :
    (circleReflection z : ℂ) = -1 + 1 / (conj (z : ℂ) + 1) :=
  rfl

theorem SpecialPeriods.Triangle.circleReflection_involutive :
    Function.Involutive circleReflection :=
  circleReflectionMap_involutive_mo1973_18717

theorem SpecialPeriods.Triangle.circleReflection_im (z : ℍ) :
    (circleReflection z).im = z.im / Complex.normSq ((z : ℂ) + 1) := by
  change (-1 + 1 / (conj (z : ℂ) + 1)).im = _
  rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp]
  simp only [one_div, Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero, zero_add,
    Complex.inv_im, Complex.normSq_conj, Complex.conj_im, add_zero, neg_neg,
    UpperHalfPlane.coe_im]

@[simp]
theorem SpecialPeriods.Triangle.circleReflection_fixed_iff (z : ℍ) :
    circleReflection z = z ↔ ‖(z : ℂ) + 1‖ = 1 := by
  constructor
  · intro h
    have hi := congrArg UpperHalfPlane.im h
    rw [circleReflection_im] at hi
    have hd : Complex.normSq ((z : ℂ) + 1) ≠ 0 :=
      (Complex.normSq_pos.mpr (denominatorOne_ne_zero z)).ne'
    have hs : Complex.normSq ((z : ℂ) + 1) = 1 := by
      apply mul_left_cancel₀ z.im_ne_zero
      simpa only [mul_one] using ((div_eq_iff hd).mp hi).symm
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  · intro h
    apply UpperHalfPlane.ext
    rw [circleReflection_coe]
    have hs : Complex.normSq (conj (z : ℂ) + 1) = 1 := by
      rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp, Complex.normSq_conj,
        Complex.normSq_eq_norm_sq, h]
      norm_num
    simp [one_div, Complex.inv_def, hs]

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_mem_fordRegion_iff (z : ℍ) :
    rightReflection z ∈ fordRegion ↔ z ∈ fordRegion := by
  simp only [fordRegion, Set.mem_ofPred_eq, rightReflection_re, rightReflection_add_one_norm,
    rightReflection_norm]
  unfold stripLeft stripRight
  constructor
  · rintro ⟨hl, hr, hnorm, hadd⟩
    refine ⟨?_, ?_, hadd, hnorm⟩ <;> linarith
  · rintro ⟨hl, hr, hadd, hnorm⟩
    refine ⟨?_, ?_, hnorm, hadd⟩ <;> linarith

theorem SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion :
    Set.MapsTo rightReflection fordRegion fordRegion := fun z hz =>
  (rightReflection_mem_fordRegion_iff z).mpr hz

theorem SpecialPeriods.Triangle.generatorOne_reflections (z : ℍ) :
    generatorOneSL • z = rightReflection (circleReflection z) := by
  apply UpperHalfPlane.ext
  simp [generatorOne_coe, neg_div, one_div]

theorem SpecialPeriods.Triangle.generatorTwo_reflections (z : ℍ) :
    generatorTwoSL • z = circleReflection (leftReflection z) := by
  apply UpperHalfPlane.ext
  rw [generatorTwo_coe, circleReflection_coe, leftReflection_coe]
  simp only [map_sub, map_neg, map_add, Complex.conj_ofReal, map_one, Complex.conj_conj]
  rw [show -((width : ℂ) + 1) - (z : ℂ) + 1 = -(z : ℂ) - width by ring]
  have hd := denominatorTwo_ne_zero z
  field_simp [hd]
  ring

theorem SpecialPeriods.Triangle.cusp_reflections (z : ℍ) :
    cuspSL • z = leftReflection (rightReflection z) := by
  apply UpperHalfPlane.ext
  rw [cuspSL_apply]
  simp [UpperHalfPlane.coe_vadd]

theorem SpecialPeriods.Triangle.generatorOne_eq_rightReflection_of_norm_add_one (z : ℍ)
    (hz : ‖(z : ℂ) + 1‖ = 1) : generatorOneSL • z = rightReflection z := by
  rw [generatorOne_reflections, (circleReflection_fixed_iff z).mpr hz]

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_re_eq_stripRight_iff (z : ℍ) :
    (rightReflection z).re = stripRight ↔ z.re = stripLeft := by
  rw [rightReflection_re]
  unfold stripLeft stripRight
  constructor <;> intro h <;> linarith

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_re_eq_stripLeft_iff (z : ℍ) :
    (rightReflection z).re = stripLeft ↔ z.re = stripRight := by
  rw [rightReflection_re]
  unfold stripLeft stripRight
  constructor <;> intro h <;> linarith

theorem SpecialPeriods.Triangle.cusp_eq_rightReflection_of_re_eq_stripRight (z : ℍ)
    (hz : z.re = stripRight) : cuspSL • z = rightReflection z := by
  rw [cusp_reflections]
  exact
    (leftReflection_fixed_iff (rightReflection z)).mpr
      ((rightReflection_re_eq_stripLeft_iff z).mpr hz)

theorem SpecialPeriods.Triangle.generatorOne_inv_eq_rightReflection_of_norm (z : ℍ)
    (hz : ‖(z : ℂ)‖ = 1) : generatorOneSL⁻¹ • z = rightReflection z := by
  have h :=
    generatorOne_eq_rightReflection_of_norm_add_one (rightReflection z)
      (by simpa only [rightReflection_add_one_norm] using hz)
  rw [rightReflection_involutive z] at h
  simpa only [inv_smul_smul] using congrArg (fun w : ℍ => generatorOneSL⁻¹ • w) h.symm

def SpecialPeriods.Triangle.triangleInterior : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

def SpecialPeriods.Triangle.boundaryHeight (x : ℝ) : ℝ :=
  Real.sqrt (1 - (x + 1) ^ 2)

@[fun_prop]
theorem SpecialPeriods.Triangle.continuous_boundaryHeight : Continuous boundaryHeight := by
  unfold boundaryHeight
  fun_prop

theorem SpecialPeriods.Triangle.boundaryHeight_le_one (x : ℝ) : boundaryHeight x ≤ 1 := by
  have h : 1 - (x + 1) ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg (x + 1)]
  simpa only [boundaryHeight, Real.sqrt_one] using Real.sqrt_le_sqrt h

theorem SpecialPeriods.Triangle.neg_two_lt_stripLeft : -2 < stripLeft := by
  have h : width < 3 := by nlinarith [width_sq, width_pos]
  unfold stripLeft
  linarith

theorem SpecialPeriods.Triangle.circle_epigraph_iff (z : ℂ) :
    (0 < z.im ∧ 1 < ‖z + 1‖) ↔ boundaryHeight z.re < z.im := by
  have hnorm : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  constructor
  · rintro ⟨hy, hn⟩
    apply (Real.sqrt_lt' hy).mpr
    have hs := (sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mpr hn
    nlinarith
  · intro h
    have hy : 0 < z.im := lt_of_le_of_lt (Real.sqrt_nonneg _) h
    refine ⟨hy, ?_⟩
    apply (sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mp
    have hs := (Real.sqrt_lt' hy).mp h
    nlinarith

theorem SpecialPeriods.Triangle.mem_triangleInterior_iff_epigraph (z : ℂ) :
    z ∈ triangleInterior ↔ stripLeft < z.re ∧ z.re < -1 / 2 ∧ boundaryHeight z.re < z.im := by
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ (0 < z.im ∧ 1 < ‖z + 1‖)) ↔ _
  rw [circle_epigraph_iff]

def SpecialPeriods.Triangle.triangleBasepoint : ℂ :=
  -1 + 2 * Complex.I

theorem SpecialPeriods.Triangle.triangleBasepoint_mem : triangleBasepoint ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph]
  norm_num [triangleBasepoint, boundaryHeight, stripLeft_lt_neg_one]

theorem SpecialPeriods.Triangle.triangleInterior_isOpen : IsOpen triangleInterior :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm))))

theorem SpecialPeriods.Triangle.zero_not_mem_triangleInterior : (0 : ℂ) ∉ triangleInterior := by
  simp [triangleInterior]

theorem SpecialPeriods.Triangle.triangleInterior_ne_univ : triangleInterior ≠ Set.univ := by
  intro h
  exact zero_not_mem_triangleInterior (h.symm ▸ Set.mem_univ (0 : ℂ))

def SpecialPeriods.Triangle.triangleOpenStrip : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im}

theorem SpecialPeriods.Triangle.triangleOpenStrip_convex : Convex ℝ triangleOpenStrip :=
  (convex_halfSpace_re_gt stripLeft).inter
    ((convex_halfSpace_re_lt (-1 / 2)).inter (convex_halfSpace_im_gt 0))

theorem SpecialPeriods.Triangle.triangleOpenStrip_nonempty : triangleOpenStrip.Nonempty := by
  refine ⟨(-1 : ℂ) + Complex.I, ?_⟩
  norm_num [triangleOpenStrip, stripLeft_lt_neg_one]

def SpecialPeriods.Triangle.triangleHeightShift : ℂ ≃ₜ ℂ
    where
  toFun z := ⟨z.re, z.im - boundaryHeight z.re⟩
  invFun z := ⟨z.re, z.im + boundaryHeight z.re⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp
  continuous_toFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun z : ℂ => (z.re, z.im - boundaryHeight z.re)) from by fun_prop)
  continuous_invFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun z : ℂ => (z.re, z.im + boundaryHeight z.re)) from by fun_prop)

@[simp]
theorem SpecialPeriods.Triangle.triangleHeightShift_re (z : ℂ) :
    (triangleHeightShift z).re = z.re :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.triangleHeightShift_im (z : ℂ) :
    (triangleHeightShift z).im = z.im - boundaryHeight z.re :=
  rfl

theorem SpecialPeriods.Triangle.triangleInterior_eq_preimage_strip :
    triangleInterior = triangleHeightShift ⁻¹' triangleOpenStrip := by
  ext z
  rw [mem_triangleInterior_iff_epigraph]
  simp only [Set.mem_preimage, triangleOpenStrip, Set.mem_ofPred_eq, triangleHeightShift_re,
    triangleHeightShift_im, sub_pos]

def SpecialPeriods.Triangle.triangleInteriorHomeomorphStrip :
    triangleInterior ≃ₜ triangleOpenStrip :=
  triangleHeightShift.sets triangleInterior_eq_preimage_strip

instance SpecialPeriods.Triangle.triangleInterior_contractible :
    ContractibleSpace triangleInterior := by
  have : ContractibleSpace triangleOpenStrip :=
    triangleOpenStrip_convex.contractibleSpace triangleOpenStrip_nonempty
  exact triangleInteriorHomeomorphStrip.contractibleSpace

instance SpecialPeriods.Triangle.triangleInterior_simplyConnectedSpace :
    SimplyConnectedSpace triangleInterior :=
  inferInstance

theorem SpecialPeriods.Triangle.triangleInterior_isSimplyConnected :
    IsSimplyConnected triangleInterior := by
  change SimplyConnectedSpace triangleInterior
  infer_instance

def SpecialPeriods.Triangle.halfFordRegion : Set ℍ :=
  fordRegion ∩ {z | z.re ≤ -(1 / 2)}

def SpecialPeriods.Triangle.halfFordInterior : Set ℍ :=
  fordInterior ∩ {z | z.re < -(1 / 2)}

theorem SpecialPeriods.Triangle.halfFordRegion_isClosed : IsClosed halfFordRegion :=
  fordRegion_closed.inter (isClosed_le UpperHalfPlane.continuous_re continuous_const)

theorem SpecialPeriods.Triangle.halfFordInterior_isOpen : IsOpen halfFordInterior :=
  fordInterior_isOpen.inter (isOpen_lt UpperHalfPlane.continuous_re continuous_const)

theorem SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion :
    halfFordInterior ⊆ halfFordRegion := by
  intro z hz
  exact ⟨fordInterior_subset_fordRegion hz.1, (show z.re < -(1 / 2) from hz.2).le⟩

theorem SpecialPeriods.Triangle.norm_add_one_lt_norm_of_re_lt_neg_half (z : ℍ)
    (hzre : z.re < -(1 / 2)) : ‖(z : ℂ) + 1‖ < ‖(z : ℂ)‖ := by
  apply (sq_lt_sq₀ (norm_nonneg ((z : ℂ) + 1)) (norm_nonneg (z : ℂ))).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith

theorem SpecialPeriods.Triangle.one_lt_norm_of_re_lt_neg_half (z : ℍ) (hzre : z.re < -(1 / 2))
    (hn : 1 < ‖(z : ℂ) + 1‖) : 1 < ‖(z : ℂ)‖ :=
  hn.trans (norm_add_one_lt_norm_of_re_lt_neg_half z hzre)

theorem SpecialPeriods.Triangle.strict_ford_left_half_iff_triangleInterior (z : ℍ) :
    ((stripLeft < z.re ∧ z.re < stripRight ∧ 1 < ‖(z : ℂ) + 1‖ ∧ 1 < ‖(z : ℂ)‖) ∧
        z.re < -(1 / 2)) ↔
      (z : ℂ) ∈ triangleInterior := by
  change _ ↔ stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖(z : ℂ) + 1‖
  constructor
  · rintro ⟨⟨hl, _, hn, _⟩, hm⟩
    exact ⟨hl, by linarith, z.im_pos, hn⟩
  · rintro ⟨hl, hm, _, hn⟩
    have hm' : z.re < -(1 / 2) := by linarith
    refine ⟨⟨hl, ?_, hn, one_lt_norm_of_re_lt_neg_half z hm' hn⟩, hm'⟩
    linarith [stripRight_pos]

theorem SpecialPeriods.Triangle.halfFordInterior_eq_preimage_triangleInterior :
    halfFordInterior = ((↑) : ℍ → ℂ) ⁻¹' triangleInterior :=
  Set.ext strict_ford_left_half_iff_triangleInterior

@[simp]
theorem SpecialPeriods.Triangle.rightReflection_mem_fordInterior_iff (z : ℍ) :
    rightReflection z ∈ fordInterior ↔ z ∈ fordInterior := by
  simp only [fordInterior, Set.mem_ofPred_eq, rightReflection_re, rightReflection_add_one_norm,
    rightReflection_norm]
  unfold stripLeft stripRight
  constructor
  · rintro ⟨hl, hr, hnorm, hadd⟩
    refine ⟨?_, ?_, hadd, hnorm⟩ <;> linarith
  · rintro ⟨hl, hr, hadd, hnorm⟩
    refine ⟨?_, ?_, hnorm, hadd⟩ <;> linarith

theorem SpecialPeriods.Triangle.rightReflection_mapsTo_fordInterior :
    Set.MapsTo rightReflection fordInterior fordInterior := fun z hz =>
  (rightReflection_mem_fordInterior_iff z).mpr hz

def SpecialPeriods.Triangle.halfFold (b : Bool) : ℍ ≃ₜ ℍ :=
  if b then rightReflection else Homeomorph.refl ℍ

theorem SpecialPeriods.Triangle.halfFold_mapsTo_region (b : Bool) :
    Set.MapsTo (halfFold b) halfFordRegion fordRegion := by
  cases b
  · intro z hz
    exact hz.1
  · intro z hz
    exact rightReflection_mapsTo_fordRegion hz.1

theorem SpecialPeriods.Triangle.halfFold_image_region_subset (b : Bool) :
    halfFold b '' halfFordRegion ⊆ fordRegion :=
  (halfFold_mapsTo_region b).image_subset

theorem SpecialPeriods.Triangle.rightReflection_image_halfFordRegion :
    rightReflection '' halfFordRegion = fordRegion ∩ {z | -(1 / 2) ≤ z.re} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨rightReflection_mapsTo_fordRegion hw.1, ?_⟩
    change -(1 / 2) ≤ (rightReflection w).re
    rw [rightReflection_re]
    have hcut : w.re ≤ -(1 / 2) := hw.2
    linarith
  · rintro ⟨hz, hr⟩
    refine
      ⟨rightReflection z, ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩,
        rightReflection_involutive z⟩
    change (rightReflection z).re ≤ -(1 / 2)
    rw [rightReflection_re]
    change -(1 / 2) ≤ z.re at hr
    linarith

theorem SpecialPeriods.Triangle.halfFordRegion_union_reflection :
    halfFordRegion ∪ rightReflection '' halfFordRegion = fordRegion := by
  rw [rightReflection_image_halfFordRegion]
  ext z
  change
    ((z ∈ fordRegion ∧ z.re ≤ -(1 / 2)) ∨ (z ∈ fordRegion ∧ -(1 / 2) ≤ z.re)) ↔ z ∈ fordRegion
  constructor
  · rintro (hz | hz) <;> exact hz.1
  · intro hz
    rcases le_total z.re (-(1 / 2)) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩

theorem SpecialPeriods.Triangle.halfFold_closed_cover :
    (⋃ b : Bool, halfFold b '' halfFordRegion) = fordRegion := by
  ext z
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨b, hb⟩
    exact halfFold_image_region_subset b hb
  · intro hz
    rw [← halfFordRegion_union_reflection] at hz
    rcases hz with hz | hz
    · exact ⟨Bool.false, z, hz, rfl⟩
    · exact ⟨Bool.true, hz⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous in
theorem SpecialPeriods.Triangle.compact_return_height_bound {K : Set ℍ} (hK : IsCompact K) :
    ∃ hi : ℝ,
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        SpecialPeriods.triangleGeometricRepresentation g z ∈ K → z.im ≤ hi := by
  obtain ⟨hi, hhi⟩ := hK.bddAbove_image orbitHeightBound_continuous.continuousOn
  refine ⟨hi, fun g z hz => ?_⟩
  have hb :=
    triangle_im_le_orbitHeightBound g⁻¹ (SpecialPeriods.triangleGeometricRepresentation g z)
  have he :
    SpecialPeriods.triangleGeometricRepresentation g⁻¹
        (SpecialPeriods.triangleGeometricRepresentation g z) =
      z := by
    rw [map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply z
  rw [he] at hb
  exact hb.trans (hhi ⟨_, hz, rfl⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous in
theorem SpecialPeriods.Triangle.fordRegion_translates_finite_inter_compact {K : Set ℍ}
    (hK : IsCompact K) :
    {g : SpecialPeriods.TriangleGroup |
        (SpecialPeriods.triangleGeometricRepresentation g '' fordRegion ∩ K).Nonempty}.Finite := by
  obtain ⟨hi, hhi⟩ := compact_return_height_bound hK
  have hf :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := SpecialPeriods.TriangleGroup)
      (truncatedFordRegion_compact hi) hK
  apply hf.subset
  rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
  exact ⟨SpecialPeriods.triangleGeometricRepresentation g w, ⟨w, ⟨hw, hhi g w hz⟩, rfl⟩, hz⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous in
theorem SpecialPeriods.Triangle.fordRegion_translates_locallyFinite :
    LocallyFinite
      (fun g : SpecialPeriods.TriangleGroup =>
        SpecialPeriods.triangleGeometricRepresentation g '' fordRegion) := by
  intro z
  obtain ⟨K, hK, hKz⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds z
  exact ⟨K, hKz, fordRegion_translates_finite_inter_compact hK⟩

def SpecialPeriods.Triangle.halfTriangleMap (i : SpecialPeriods.TriangleGroup × Bool) : ℍ ≃ₜ ℍ :=
  (halfFold i.2).trans (SpecialPeriods.triangleGeometricBiholomorph i.1).toHomeomorph

@[simp]
theorem SpecialPeriods.Triangle.halfTriangleMap_apply (i : SpecialPeriods.TriangleGroup × Bool)
    (z : ℍ) :
    halfTriangleMap i z = SpecialPeriods.triangleGeometricRepresentation i.1 (halfFold i.2 z) :=
  rfl

def SpecialPeriods.Triangle.halfTriangleTile (i : SpecialPeriods.TriangleGroup × Bool) : Set ℍ :=
  halfTriangleMap i '' halfFordRegion

def SpecialPeriods.Triangle.halfTriangleOpenTile (i : SpecialPeriods.TriangleGroup × Bool) :
    Set ℍ :=
  halfTriangleMap i '' halfFordInterior

theorem SpecialPeriods.Triangle.halfTriangleTile_eq (i : SpecialPeriods.TriangleGroup × Bool) :
    halfTriangleTile i =
      SpecialPeriods.triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordRegion) := by
  rw [Set.image_image]
  rfl

theorem SpecialPeriods.Triangle.halfTriangleOpenTile_eq
    (i : SpecialPeriods.TriangleGroup × Bool) :
    halfTriangleOpenTile i =
      SpecialPeriods.triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordInterior) := by
  rw [Set.image_image]
  rfl

theorem SpecialPeriods.Triangle.halfTriangleOpenTile_isOpen
    (i : SpecialPeriods.TriangleGroup × Bool) : IsOpen (halfTriangleOpenTile i) :=
  (halfTriangleMap i).isOpenMap halfFordInterior halfFordInterior_isOpen

theorem SpecialPeriods.Triangle.halfTriangleTile_subset_fordRegion_translate
    (i : SpecialPeriods.TriangleGroup × Bool) :
    halfTriangleTile i ⊆ SpecialPeriods.triangleGeometricRepresentation i.1 '' fordRegion := by
  rw [halfTriangleTile_eq]
  exact Set.image_mono (halfFold_image_region_subset i.2)

theorem SpecialPeriods.Triangle.halfTriangleTiles_cover :
    (⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleTile i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨w, hw, g, hgz⟩ := SpecialPeriods.triangle_exists_fordRegion_preimage z
  have hfold : w ∈ ⋃ b : Bool, halfFold b '' halfFordRegion := by
    rw [halfFold_closed_cover]
    exact hw
  obtain ⟨b, u, hu, hwu⟩ := Set.mem_iUnion.mp hfold
  refine Set.mem_iUnion.mpr ⟨(g, b), u, hu, ?_⟩
  rw [halfTriangleMap_apply, hwu, hgz]

theorem SpecialPeriods.Triangle.halfTriangleTiles_finite_inter_compact {K : Set ℍ}
    (hK : IsCompact K) :
    {i : SpecialPeriods.TriangleGroup × Bool | (halfTriangleTile i ∩ K).Nonempty}.Finite := by
  apply
    ((fordRegion_translates_finite_inter_compact hK).prod
        (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
  rintro i ⟨z, hz, hKz⟩
  exact ⟨⟨z, halfTriangleTile_subset_fordRegion_translate i hz, hKz⟩, Set.mem_univ _⟩

theorem SpecialPeriods.Triangle.halfTriangleTiles_locallyFinite :
    LocallyFinite halfTriangleTile := by
  intro z
  obtain ⟨K, hK, hKz⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds z
  exact ⟨K, hKz, halfTriangleTiles_finite_inter_compact hK⟩

structure TriangleUniformizationGluing.BoundaryMap where
  toFun : ℍ → ℂ
  continuousOn : ContinuousOn toFun SpecialPeriods.Triangle.halfFordRegion
  boundary_real :
    ∀ z ∈ SpecialPeriods.Triangle.halfFordRegion,
      z ∉ SpecialPeriods.Triangle.halfFordInterior → (toFun z).im = 0

instance TriangleUniformizationGluing.instCoeFun1 : CoeFun BoundaryMap (fun _ => ℍ → ℂ) :=
  ⟨BoundaryMap.toFun⟩

def TriangleUniformizationGluing.BoundaryMap.foldedFordMap
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ) : ℂ := by
  classical
    exact if z.re ≤ -(1 / 2) then D z else conj (D (SpecialPeriods.Triangle.rightReflection z))

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_of_left
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    D.foldedFordMap z = D z := by simp only [foldedFordMap, if_pos hz]

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_of_right
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ} (hz : -(1 / 2) < z.re) :
    D.foldedFordMap z = conj (D (SpecialPeriods.Triangle.rightReflection z)) := by
  simp only [foldedFordMap, if_neg hz.not_ge]

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_eqOn_left
    (D : TriangleUniformizationGluing.BoundaryMap) :
    Set.EqOn D.foldedFordMap D SpecialPeriods.Triangle.halfFordRegion := fun _ hz =>
  D.foldedFordMap_of_left hz.2

theorem TriangleUniformizationGluing.BoundaryMap.real_at_axis
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hx : z.re = -(1 / 2)) : (D z).im = 0 := by
  apply D.boundary_real z ⟨hz, hx.le⟩
  intro hi
  have hh : z.re < -(1 / 2) := hi.2
  linarith

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_reflected
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = conj (D z) := by
  by_cases hx : (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2)
  · have hcut : z.re = -(1 / 2) := by
      rw [SpecialPeriods.Triangle.rightReflection_re] at hx
      have hleft : z.re ≤ -(1 / 2) := hz.2
      linarith
    have hfix : SpecialPeriods.Triangle.rightReflection z = z :=
      (SpecialPeriods.Triangle.rightReflection_fixed_iff z).mpr hcut
    rw [hfix, D.foldedFordMap_of_left hz.2]
    exact (Complex.conj_eq_iff_im.mpr (D.real_at_axis hz.1 hcut)).symm
  · simp only [foldedFordMap, if_neg hx]
    rw [SpecialPeriods.Triangle.rightReflection_involutive z]

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_eqOn_right
    (D : TriangleUniformizationGluing.BoundaryMap) :
    Set.EqOn D.foldedFordMap (fun z => conj (D (SpecialPeriods.Triangle.rightReflection z)))
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordRegion) := by
  rintro z ⟨w, hw, rfl⟩
  change
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection w) =
      conj
        (D (SpecialPeriods.Triangle.rightReflection (SpecialPeriods.Triangle.rightReflection w)))
  rw [D.foldedFordMap_reflected w hw, SpecialPeriods.Triangle.rightReflection_involutive w]

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_continuousOn
    (D : TriangleUniformizationGluing.BoundaryMap) :
    ContinuousOn D.foldedFordMap SpecialPeriods.Triangle.fordRegion := by
  have hl : ContinuousOn D.foldedFordMap SpecialPeriods.Triangle.halfFordRegion :=
    D.continuousOn.congr D.foldedFordMap_eqOn_left
  have hm :
    Set.MapsTo SpecialPeriods.Triangle.rightReflection
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordRegion)
      SpecialPeriods.Triangle.halfFordRegion := by
    rintro z ⟨w, hw, rfl⟩
    rw [SpecialPeriods.Triangle.rightReflection_involutive w]
    exact hw
  have hr :
    ContinuousOn D.foldedFordMap
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordRegion) := by
    apply
      (Complex.continuous_conj.continuousOn.comp
          (D.continuousOn.comp SpecialPeriods.Triangle.rightReflection.continuous.continuousOn hm)
          (Set.mapsTo_univ _ _)).congr
    exact D.foldedFordMap_eqOn_right
  rw [← SpecialPeriods.Triangle.halfFordRegion_union_reflection]
  exact
    hl.union_of_isClosed hr SpecialPeriods.Triangle.halfFordRegion_isClosed
      (SpecialPeriods.Triangle.rightReflection.isClosedMap _
        SpecialPeriods.Triangle.halfFordRegion_isClosed)

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_rightReflection
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) :
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = conj (D.foldedFordMap z) := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [D.foldedFordMap_of_left hx]
    exact D.foldedFordMap_reflected z ⟨hz, hx⟩
  · have hright : -(1 / 2) < z.re := lt_of_not_ge hx
    have hleft : (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2) := by
      rw [SpecialPeriods.Triangle.rightReflection_re]
      linarith
    rw [D.foldedFordMap_of_left hleft, D.foldedFordMap_of_right hright, Complex.conj_conj]

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_real_of_not_mem_interior
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion)
    (hi : z ∉ SpecialPeriods.Triangle.fordInterior) : (D.foldedFordMap z).im = 0 := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [D.foldedFordMap_of_left hx]
    exact D.boundary_real z ⟨hz, hx⟩ (fun hh => hi hh.1)
  · have hright : -(1 / 2) < z.re := lt_of_not_ge hx
    have hleft : (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2) := by
      rw [SpecialPeriods.Triangle.rightReflection_re]
      linarith
    have hr :
      SpecialPeriods.Triangle.rightReflection z ∈ SpecialPeriods.Triangle.halfFordRegion :=
      ⟨SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz, hleft⟩
    have hn :
      SpecialPeriods.Triangle.rightReflection z ∉ SpecialPeriods.Triangle.halfFordInterior := by
      intro hh
      exact hi ((SpecialPeriods.Triangle.rightReflection_mem_fordInterior_iff z).mp hh.1)
    rw [D.foldedFordMap_of_right hright, Complex.conj_im, D.boundary_real _ hr hn, neg_zero]

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_rightReflection_boundary
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion)
    (hi : z ∉ SpecialPeriods.Triangle.fordInterior) :
    D.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = D.foldedFordMap z := by
  rw [D.foldedFordMap_rightReflection hz]
  exact Complex.conj_eq_iff_im.mpr (D.foldedFordMap_real_of_not_mem_interior hz hi)

structure TriangleUniformizationGluing.HalfPlaneMap extends BoundaryMap where
  injOn : Set.InjOn toFun SpecialPeriods.Triangle.halfFordRegion
  image_eq : toFun '' SpecialPeriods.Triangle.halfFordRegion = {w : ℂ | 0 ≤ w.im}
  interior_positive : ∀ z ∈ SpecialPeriods.Triangle.halfFordInterior, 0 < (toFun z).im

instance TriangleUniformizationGluing.instCoeFun2 : CoeFun HalfPlaneMap (fun _ => ℍ → ℂ) :=
  ⟨fun D => D.toFun⟩

abbrev TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap
    (D : TriangleUniformizationGluing.HalfPlaneMap) : ℍ → ℂ :=
  D.toBoundaryMap.foldedFordMap

theorem TriangleUniformizationGluing.HalfPlaneMap.im_nonneg
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) : 0 ≤ (D z).im := by
  have h : D.toFun z ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion :=
    Set.mem_image_of_mem D.toFun hz
  rw [D.image_eq] at h
  exact h

theorem TriangleUniformizationGluing.HalfPlaneMap.im_eq_zero_iff_not_mem_halfFordInterior
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    (D z).im = 0 ↔ z ∉ SpecialPeriods.Triangle.halfFordInterior := by
  constructor
  · intro him hi
    exact (D.interior_positive z hi).ne' him
  · exact D.boundary_real z hz

theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_of_left
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    D.foldedFordMap z = D z :=
  D.toBoundaryMap.foldedFordMap_of_left hz

theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_of_right
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z : ℍ} (hz : -(1 / 2) < z.re) :
    D.foldedFordMap z = conj (D (SpecialPeriods.Triangle.rightReflection z)) :=
  D.toBoundaryMap.foldedFordMap_of_right hz

theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_surjOn
    (D : TriangleUniformizationGluing.HalfPlaneMap) :
    Set.SurjOn D.foldedFordMap SpecialPeriods.Triangle.fordRegion Set.univ := by
  intro w _
  by_cases hw : 0 ≤ w.im
  · have hmem : w ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion := by
      rw [D.image_eq]
      exact hw
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz.1, ?_⟩
    change D.toBoundaryMap.foldedFordMap z = w
    rw [D.toBoundaryMap.foldedFordMap_of_left hz.2]
    exact he
  · have hmem : conj w ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion := by
      rw [D.image_eq]
      change 0 ≤ (conj w).im
      rw [Complex.conj_im]
      exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hw))
    obtain ⟨z, hz, he⟩ := hmem
    refine
      ⟨SpecialPeriods.Triangle.rightReflection z,
        SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz.1, ?_⟩
    change D.toBoundaryMap.foldedFordMap (SpecialPeriods.Triangle.rightReflection z) = w
    rw [D.toBoundaryMap.foldedFordMap_reflected z hz, he, Complex.conj_conj]

private theorem
  TriangleUniformizationGluing.HalfPlaneMap.rightReflection_mem_halfFordRegion_mo1973_18870
    {z : ℍ} (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hx : -(1 / 2) < z.re) :
    SpecialPeriods.Triangle.rightReflection z ∈ SpecialPeriods.Triangle.halfFordRegion := by
  refine ⟨SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz, ?_⟩
  change (SpecialPeriods.Triangle.rightReflection z).re ≤ -(1 / 2)
  rw [SpecialPeriods.Triangle.rightReflection_re]
  linarith

private theorem TriangleUniformizationGluing.HalfPlaneMap.cross_fibre_mo1973_18871
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion)
    (hw : w ∈ SpecialPeriods.Triangle.fordRegion) (hwr : -(1 / 2) < w.re)
    (heq : D.foldedFordMap z = D.foldedFordMap w) :
    w = SpecialPeriods.Triangle.rightReflection z ∧ z ∉ SpecialPeriods.Triangle.fordInterior := by
  have hrw : SpecialPeriods.Triangle.rightReflection w ∈ SpecialPeriods.Triangle.halfFordRegion :=
    rightReflection_mem_halfFordRegion_mo1973_18870 hw hwr
  rw [D.foldedFordMap_of_left hz.2, D.foldedFordMap_of_right hwr] at heq
  have him := congrArg Complex.im heq
  rw [Complex.conj_im] at him
  have hzpos := D.im_nonneg hz
  have hwpos := D.im_nonneg hrw
  have hzreal : (D z).im = 0 := by linarith
  have hwreal : (D (SpecialPeriods.Triangle.rightReflection w)).im = 0 := by linarith
  have hf : D z = D (SpecialPeriods.Triangle.rightReflection w) :=
    heq.trans (Complex.conj_eq_iff_im.mpr hwreal)
  have hzw : z = SpecialPeriods.Triangle.rightReflection w := D.injOn hz hrw hf
  have hwz : w = SpecialPeriods.Triangle.rightReflection z := by
    rw [hzw, SpecialPeriods.Triangle.rightReflection_involutive]
  refine ⟨hwz, ?_⟩
  have hnot : z ∉ SpecialPeriods.Triangle.halfFordInterior :=
    (D.im_eq_zero_iff_not_mem_halfFordInterior hz).mp hzreal
  intro hi
  apply hnot
  refine ⟨hi, ?_⟩
  change z.re < -(1 / 2)
  rw [hzw, SpecialPeriods.Triangle.rightReflection_re]
  linarith

theorem TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap_eq_iff
    (D : TriangleUniformizationGluing.HalfPlaneMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hw : w ∈ SpecialPeriods.Triangle.fordRegion) :
    D.foldedFordMap z = D.foldedFordMap w ↔
      z = w ∨
        (w = SpecialPeriods.Triangle.rightReflection z ∧
          z ∉ SpecialPeriods.Triangle.fordInterior) := by
  constructor
  · intro heq
    by_cases hzl : z.re ≤ -(1 / 2)
    · by_cases hwl : w.re ≤ -(1 / 2)
      · left
        rw [D.foldedFordMap_of_left hzl, D.foldedFordMap_of_left hwl] at heq
        exact D.injOn ⟨hz, hzl⟩ ⟨hw, hwl⟩ heq
      · exact Or.inr (D.cross_fibre_mo1973_18871 ⟨hz, hzl⟩ hw (lt_of_not_ge hwl) heq)
    · have hzr : -(1 / 2) < z.re := lt_of_not_ge hzl
      by_cases hwl : w.re ≤ -(1 / 2)
      · obtain ⟨hzw, hwnot⟩ := D.cross_fibre_mo1973_18871 ⟨hw, hwl⟩ hz hzr heq.symm
        right
        constructor
        · rw [hzw, SpecialPeriods.Triangle.rightReflection_involutive]
        · rw [hzw, SpecialPeriods.Triangle.rightReflection_mem_fordInterior_iff]
          exact hwnot
      · have hwr : -(1 / 2) < w.re := lt_of_not_ge hwl
        left
        rw [D.foldedFordMap_of_right hzr, D.foldedFordMap_of_right hwr] at heq
        have hf :
          D (SpecialPeriods.Triangle.rightReflection z) =
            D (SpecialPeriods.Triangle.rightReflection w) := by
          simpa only [Complex.conj_conj] using congrArg (fun u : ℂ => conj u) heq
        exact
          SpecialPeriods.Triangle.rightReflection.injective
            (D.injOn (rightReflection_mem_halfFordRegion_mo1973_18870 hz hzr)
              (rightReflection_mem_halfFordRegion_mo1973_18870 hw hwr) hf)
  · rintro (rfl | ⟨rfl, hi⟩)
    · rfl
    · exact (D.toBoundaryMap.foldedFordMap_rightReflection_boundary hz hi).symm

structure TriangleUniformizationGluing.SignedHalfPlaneMap extends BoundaryMap where
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  injOn : Set.InjOn toFun SpecialPeriods.Triangle.halfFordRegion
  image_eq : toFun '' SpecialPeriods.Triangle.halfFordRegion = {w : ℂ | 0 ≤ orientation * w.im}
  interior_positive :
    ∀ z ∈ SpecialPeriods.Triangle.halfFordInterior, 0 < orientation * (toFun z).im

instance TriangleUniformizationGluing.instCoeFun3 : CoeFun SignedHalfPlaneMap (fun _ => ℍ → ℂ) :=
  ⟨fun D => D.toFun⟩

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_ne_zero
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : D.orientation ≠ 0 := by
  intro h
  have hs := D.orientation_sq
  rw [h] at hs
  norm_num at hs

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_coe_ne_zero
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : (D.orientation : ℂ) ≠ 0 := by
  exact_mod_cast D.orientation_ne_zero

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_mul_self
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : D.orientation * D.orientation = 1 := by
  simpa only [pow_two] using D.orientation_sq

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientation_coe_mul_self
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    (D.orientation : ℂ) * (D.orientation : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, D.orientation_mul_self, Complex.ofReal_one]

def TriangleUniformizationGluing.SignedHalfPlaneMap.orientationScale
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) (w : ℂ) : ℂ :=
  (D.orientation : ℂ) * w

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientationScale_involutive
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    Function.Involutive D.orientationScale := by
  intro w
  change (D.orientation : ℂ) * ((D.orientation : ℂ) * w) = w
  rw [← mul_assoc, D.orientation_coe_mul_self, one_mul]

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.orientationScale_injective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    Function.Injective D.orientationScale :=
  D.orientationScale_involutive.injective

abbrev TriangleUniformizationGluing.SignedHalfPlaneMap.foldedFordMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : ℍ → ℂ :=
  D.toBoundaryMap.foldedFordMap

def TriangleUniformizationGluing.SignedHalfPlaneMap.normalized
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    TriangleUniformizationGluing.HalfPlaneMap
    where
  toFun := fun z => (D.orientation : ℂ) * D z
  continuousOn := continuousOn_const.mul D.continuousOn
  boundary_real := by
    intro z hz hi
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul,
      add_zero, D.boundary_real z hz hi, MulZeroClass.mul_zero]
  injOn := by
    intro z hz w hw he
    exact D.injOn hz hw ((mul_right_inj' D.orientation_coe_ne_zero).mp he)
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h : D.toFun z ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion :=
        Set.mem_image_of_mem D.toFun hz
      rw [D.image_eq] at h
      simpa only [Set.mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        MulZeroClass.zero_mul, add_zero] using h
    · intro hw
      have h : (D.orientation : ℂ) * w ∈ D.toFun '' SpecialPeriods.Triangle.halfFordRegion := by
        rw [D.image_eq]
        simp only [Set.mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          MulZeroClass.zero_mul, add_zero]
        rw [← mul_assoc, D.orientation_mul_self, one_mul]
        exact hw
      obtain ⟨z, hz, he⟩ := h
      refine ⟨z, hz, ?_⟩
      change (D.orientation : ℂ) * D.toFun z = w
      rw [he, ← mul_assoc, D.orientation_coe_mul_self, one_mul]
  interior_positive := by
    intro z hz
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul,
      add_zero] using D.interior_positive z hz

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.normalized_foldedFordMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) (z : ℍ) :
    D.normalized.foldedFordMap z = (D.orientation : ℂ) * D.foldedFordMap z := by
  simp only [TriangleUniformizationGluing.HalfPlaneMap.foldedFordMap, foldedFordMap,
    TriangleUniformizationGluing.BoundaryMap.foldedFordMap]
  split_ifs
  · rfl
  · change
      conj ((D.orientation : ℂ) * D (SpecialPeriods.Triangle.rightReflection z)) =
        (D.orientation : ℂ) * conj (D (SpecialPeriods.Triangle.rightReflection z))
    rw [map_mul, Complex.conj_ofReal]

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.foldedFordMap_surjOn
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    Set.SurjOn D.foldedFordMap SpecialPeriods.Triangle.fordRegion Set.univ := by
  intro w _
  obtain ⟨z, hz, he⟩ := D.normalized.foldedFordMap_surjOn (Set.mem_univ ((D.orientation : ℂ) * w))
  refine ⟨z, hz, ?_⟩
  apply D.orientationScale_injective
  change (D.orientation : ℂ) * D.foldedFordMap z = (D.orientation : ℂ) * w
  rw [← D.normalized_foldedFordMap z]
  exact he

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.foldedFordMap_eq_iff
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hw : w ∈ SpecialPeriods.Triangle.fordRegion) :
    D.foldedFordMap z = D.foldedFordMap w ↔
      z = w ∨
        (w = SpecialPeriods.Triangle.rightReflection z ∧
          z ∉ SpecialPeriods.Triangle.fordInterior) := by
  have heq :
    D.normalized.foldedFordMap z = D.normalized.foldedFordMap w ↔
      D.foldedFordMap z = D.foldedFordMap w := by
    rw [D.normalized_foldedFordMap z, D.normalized_foldedFordMap w]
    constructor
    · intro h
      exact D.orientationScale_injective h
    · intro h
      exact congrArg D.orientationScale h
  exact heq.symm.trans (D.normalized.foldedFordMap_eq_iff hz hw)

def TriangleUniformizationGluing.halfPlaneOrientationSign (k : ℝ) : ℝ :=
  if 0 < k then 1 else -1

theorem TriangleUniformizationGluing.halfPlaneOrientationSign_sq (k : ℝ) :
    halfPlaneOrientationSign k ^ 2 = 1 := by
  unfold halfPlaneOrientationSign
  split_ifs <;> norm_num

theorem TriangleUniformizationGluing.halfPlaneOrientationSign_nonneg_iff {k : ℝ} (hk : k ≠ 0)
    (t : ℝ) : 0 ≤ halfPlaneOrientationSign k * t ↔ 0 ≤ k * t := by
  unfold halfPlaneOrientationSign
  split_ifs with hp
  · simpa only [one_mul] using (mul_nonneg_iff_of_pos_left hp).symm
  · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simp only [neg_one_mul, neg_nonneg]
    constructor
    · exact fun ht => mul_nonneg_of_nonpos_of_nonpos hn.le ht
    · intro ht
      by_contra h
      exact (not_le_of_gt (mul_neg_of_neg_of_pos hn (lt_of_not_ge h))) ht

theorem TriangleUniformizationGluing.halfPlaneOrientationSign_pos_iff {k : ℝ} (hk : k ≠ 0)
    (t : ℝ) : 0 < halfPlaneOrientationSign k * t ↔ 0 < k * t := by
  unfold halfPlaneOrientationSign
  split_ifs with hp
  · simpa only [one_mul] using (mul_pos_iff_of_pos_left hp).symm
  · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
    simp only [neg_one_mul, neg_pos]
    constructor
    · exact fun ht => mul_pos_of_neg_of_neg hn ht
    · intro ht
      by_contra h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hn.le (le_of_not_gt h))) ht

def TriangleUniformizationGluing.halfFordHomeomorphExtension {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (z : ℍ) : ℂ := by
  classical exact if hz : z ∈ SpecialPeriods.Triangle.halfFordRegion then (e ⟨z, hz⟩ : ℂ) else 0

@[simp]
theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_coe {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (z : SpecialPeriods.Triangle.halfFordRegion) : halfFordHomeomorphExtension e z = (e z : ℂ) := by
  simp only [halfFordHomeomorphExtension, dif_pos z.property]

theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_of_mem {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    {z : ℍ} (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    halfFordHomeomorphExtension e z = (e ⟨z, hz⟩ : ℂ) :=
  halfFordHomeomorphExtension_coe e ⟨z, hz⟩

theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_continuousOn {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k) :
    ContinuousOn (halfFordHomeomorphExtension e) SpecialPeriods.Triangle.halfFordRegion := by
  rw [continuousOn_iff_continuous_domRestrict]
  change
    Continuous (fun z : SpecialPeriods.Triangle.halfFordRegion => halfFordHomeomorphExtension e z)
  simp only [halfFordHomeomorphExtension_coe]
  exact continuous_subtype_val.comp e.continuous

theorem TriangleUniformizationGluing.halfFordHomeomorphExtension_isProperMap {k : ℝ}
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k) :
    IsProperMap
      (fun z : SpecialPeriods.Triangle.halfFordRegion => halfFordHomeomorphExtension e z) := by
  have hc : IsClosed (RiemannSphere.closedOrientedHalfPlane k) :=
    isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)
  simpa only [Function.comp_def, halfFordHomeomorphExtension_coe] using
    hc.isProperMap_subtypeVal.comp e.isProperMap

def TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph {k : ℝ} (hk : k ≠ 0)
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (hinterior :
      ∀ z : SpecialPeriods.Triangle.halfFordRegion,
        0 < k * (e z : ℂ).im ↔ (z : ℍ) ∈ SpecialPeriods.Triangle.halfFordInterior) :
    SignedHalfPlaneMap where
  toFun := halfFordHomeomorphExtension e
  continuousOn := halfFordHomeomorphExtension_continuousOn e
  boundary_real := by
    intro z hz hi
    rw [halfFordHomeomorphExtension_of_mem e hz]
    have hn : ¬0 < k * (e ⟨z, hz⟩ : ℂ).im := fun h => hi ((hinterior ⟨z, hz⟩).mp h)
    have he : k * (e ⟨z, hz⟩ : ℂ).im = 0 := le_antisymm (le_of_not_gt hn) (e ⟨z, hz⟩).property
    exact (mul_eq_zero.mp he).resolve_left hk
  orientation := halfPlaneOrientationSign k
  orientation_sq := halfPlaneOrientationSign_sq k
  injOn := by
    intro z hz w hw he
    rw [halfFordHomeomorphExtension_of_mem e hz, halfFordHomeomorphExtension_of_mem e hw] at he
    exact congrArg Subtype.val (e.injective (Subtype.ext he))
  image_eq := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_ofPred_eq, halfFordHomeomorphExtension_of_mem e hz,
        halfPlaneOrientationSign_nonneg_iff hk]
      exact (e ⟨z, hz⟩).property
    · intro hw
      have hwk : w ∈ RiemannSphere.closedOrientedHalfPlane k :=
        (halfPlaneOrientationSign_nonneg_iff hk w.im).mp hw
      obtain ⟨z, hz⟩ := e.surjective ⟨w, hwk⟩
      refine ⟨z, z.property, ?_⟩
      rw [halfFordHomeomorphExtension_coe]
      exact congrArg Subtype.val hz
  interior_positive := by
    intro z hz
    have hzR : z ∈ SpecialPeriods.Triangle.halfFordRegion :=
      SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz
    rw [halfFordHomeomorphExtension_of_mem e hzR, halfPlaneOrientationSign_pos_iff hk]
    exact (hinterior ⟨z, hzR⟩).mpr hz

@[simp]
theorem TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph_apply {k : ℝ} (hk : k ≠ 0)
    (e : SpecialPeriods.Triangle.halfFordRegion ≃ₜ RiemannSphere.closedOrientedHalfPlane k)
    (hinterior :
      ∀ z : SpecialPeriods.Triangle.halfFordRegion,
        0 < k * (e z : ℂ).im ↔ (z : ℍ) ∈ SpecialPeriods.Triangle.halfFordInterior)
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    signedHalfPlaneMapOfHomeomorph hk e hinterior z = (e z : ℂ) :=
  halfFordHomeomorphExtension_coe e z

def SpecialPeriods.Triangle.triangleClosedRegion : Set ℂ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖z + 1‖}

theorem SpecialPeriods.Triangle.boundaryHeight_pos_of_closed_bounds {x : ℝ} (hl : stripLeft ≤ x)
    (hr : x ≤ -1 / 2) : 0 < boundaryHeight x := by
  have hlo : 0 < x + 2 := by linarith [neg_two_lt_stripLeft]
  have hhi : 0 < -x := by linarith
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos hlo hhi]

theorem SpecialPeriods.Triangle.circle_closed_epigraph_iff {z : ℂ} (hl : stripLeft ≤ z.re)
    (hr : z.re ≤ -1 / 2) : (0 < z.im ∧ 1 ≤ ‖z + 1‖) ↔ boundaryHeight z.re ≤ z.im := by
  have hnorm : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  constructor
  · rintro ⟨hy, hn⟩
    apply (Real.sqrt_le_left hy.le).mpr
    have hs := (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mpr hn
    nlinarith
  · intro hh
    have hy : 0 < z.im := (boundaryHeight_pos_of_closed_bounds hl hr).trans_le hh
    refine ⟨hy, ?_⟩
    apply (sq_le_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg (z + 1))).mp
    have hs := (Real.sqrt_le_left hy.le).mp hh
    nlinarith

theorem SpecialPeriods.Triangle.mem_triangleClosedRegion_iff_epigraph (z : ℂ) :
    z ∈ triangleClosedRegion ↔ stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ boundaryHeight z.re ≤ z.im := by
  constructor
  · rintro ⟨hl, hr, hi, hn⟩
    exact ⟨hl, hr, (circle_closed_epigraph_iff hl hr).mp ⟨hi, hn⟩⟩
  · rintro ⟨hl, hr, hh⟩
    exact ⟨hl, hr, (circle_closed_epigraph_iff hl hr).mpr hh⟩

def SpecialPeriods.Triangle.triangleClosedStrip : Set ℂ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 ≤ z.im}

theorem SpecialPeriods.Triangle.triangleOpenStrip_eq_reProdIm :
    triangleOpenStrip = (Set.Ioo stripLeft (-1 / 2)) ×ℂ (Set.Ioi 0) := by
  ext z
  change
    (stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im) ↔
      ((stripLeft < z.re ∧ z.re < -1 / 2) ∧ 0 < z.im)
  exact and_assoc.symm

theorem SpecialPeriods.Triangle.triangleClosedStrip_eq_reProdIm :
    triangleClosedStrip = (Set.Icc stripLeft (-1 / 2)) ×ℂ (Set.Ici 0) := by
  ext z
  change
    (stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 ≤ z.im) ↔
      ((stripLeft ≤ z.re ∧ z.re ≤ -1 / 2) ∧ 0 ≤ z.im)
  exact and_assoc.symm

theorem SpecialPeriods.Triangle.closure_triangleOpenStrip :
    closure triangleOpenStrip = triangleClosedStrip := by
  rw [triangleOpenStrip_eq_reProdIm, Complex.closure_reProdIm,
    closure_Ioo (show stripLeft ≠ -1 / 2 by linarith [stripLeft_lt_neg_one]), closure_Ioi, ←
    triangleClosedStrip_eq_reProdIm]

theorem SpecialPeriods.Triangle.triangleClosedRegion_eq_preimage_strip :
    triangleClosedRegion = triangleHeightShift ⁻¹' triangleClosedStrip := by
  ext z
  rw [mem_triangleClosedRegion_iff_epigraph]
  simp only [Set.mem_preimage, triangleClosedStrip, Set.mem_ofPred_eq, triangleHeightShift_re,
    triangleHeightShift_im, sub_nonneg]

theorem SpecialPeriods.Triangle.closure_triangleInterior :
    closure triangleInterior = triangleClosedRegion := by
  rw [triangleInterior_eq_preimage_strip, ← triangleHeightShift.preimage_closure,
    closure_triangleOpenStrip, ← triangleClosedRegion_eq_preimage_strip]

theorem SpecialPeriods.Triangle.triangle_norm_add_one_le_norm {z : ℂ} (hz : z.re ≤ -1 / 2) :
    ‖z + 1‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg (z + 1)) (norm_nonneg z)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero]
  nlinarith

theorem SpecialPeriods.Triangle.coe_mem_triangleClosedRegion_iff_halfFordRegion (z : ℍ) :
    (z : ℂ) ∈ triangleClosedRegion ↔ z ∈ halfFordRegion := by
  change
    (stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖(z : ℂ) + 1‖) ↔
      ((stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ 1 ≤ ‖(z : ℂ) + 1‖ ∧ 1 ≤ ‖(z : ℂ)‖) ∧
        z.re ≤ -(1 / 2))
  constructor
  · rintro ⟨hl, hr, _, hn⟩
    refine ⟨⟨hl, ?_, hn, hn.trans (triangle_norm_add_one_le_norm hr)⟩, by linarith⟩
    linarith [stripRight_pos]
  · rintro ⟨hz, hr⟩
    exact ⟨hz.1, by linarith, z.im_pos, hz.2.2.1⟩

def SpecialPeriods.Triangle.triangleVerticalRay (t : ℝ) : ℂ :=
  -1 + ((t : ℂ) + 2) * Complex.I

@[simp]
theorem SpecialPeriods.Triangle.triangleVerticalRay_re (t : ℝ) :
    (triangleVerticalRay t).re = -1 := by simp [triangleVerticalRay]

@[simp]
theorem SpecialPeriods.Triangle.triangleVerticalRay_im (t : ℝ) :
    (triangleVerticalRay t).im = t + 2 := by simp [triangleVerticalRay]

theorem SpecialPeriods.Triangle.triangleVerticalRay_mem {t : ℝ} (ht : 0 ≤ t) :
    triangleVerticalRay t ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph, triangleVerticalRay_re, triangleVerticalRay_im]
  refine ⟨stripLeft_lt_neg_one, by norm_num, ?_⟩
  linarith [boundaryHeight_le_one (-1)]

theorem SpecialPeriods.Triangle.triangleVerticalRay_eventually_mem :
    ∀ᶠ t : ℝ in Filter.atTop, triangleVerticalRay t ∈ triangleInterior :=
  (Filter.eventually_ge_atTop (0 : ℝ)).mono fun _ ht => triangleVerticalRay_mem ht

theorem SpecialPeriods.Triangle.triangleVerticalRay_im_tendsto :
    Filter.Tendsto (fun t : ℝ => (triangleVerticalRay t).im) Filter.atTop Filter.atTop := by
  simpa only [triangleVerticalRay_im, id_eq] using
    (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) Filter.tendsto_id)

theorem SpecialPeriods.Triangle.triangleVerticalRay_norm_tendsto :
    Filter.Tendsto (fun t : ℝ => ‖triangleVerticalRay t‖) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (fun t => Complex.im_le_norm (triangleVerticalRay t))
    triangleVerticalRay_im_tendsto

theorem SpecialPeriods.Triangle.triangleVerticalRay_tendsto_cocompact :
    Filter.Tendsto triangleVerticalRay Filter.atTop (Filter.cocompact ℂ) := by
  simpa only [Metric.cobounded_eq_cocompact] using
    tendsto_norm_atTop_iff_cobounded.mp triangleVerticalRay_norm_tendsto

theorem SpecialPeriods.Triangle.triangle_infty_mem_frontier :
    ((OnePoint.infty) : OnePoint ℂ) ∈
      frontier (RiemannBoundary.onePointDomain triangleInterior) :=
  RiemannBoundary.infty_mem_frontier_onePointDomain_of_cocompact
    triangleVerticalRay_tendsto_cocompact triangleVerticalRay_eventually_mem

theorem SpecialPeriods.Triangle.triangle_infty_mem_closure :
    ((OnePoint.infty) : OnePoint ℂ) ∈ closure (RiemannBoundary.onePointDomain triangleInterior) :=
  frontier_subset_closure triangle_infty_mem_frontier

theorem RiemannMapping.restrict_isLocalDiffeomorph (U V : TopologicalSpace.Opens ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hUV : Set.MapsTo f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun z : U => (⟨f z, hUV z.property⟩ : V)) := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (isLocalDiffeomorphAt_of_deriv_ne_zero U hf hderiv z.property) U V hUV z.property

def RiemannMapping.biholomorphOfBijOn (U V : TopologicalSpace.Opens ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U : Set ℂ)) (hbij : Set.BijOn f (U : Set ℂ) (V : Set ℂ))
    (hderiv : ∀ z ∈ U, deriv f z ≠ 0) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U V ω := by
  apply (restrict_isLocalDiffeomorph U V hf hbij.mapsTo hderiv).diffeomorphOfBijective
  constructor
  · intro z w hzw
    apply Subtype.ext
    exact hbij.injOn z.property w.property (congrArg Subtype.val hzw)
  · intro w
    obtain ⟨z, hz, hzw⟩ := hbij.surjOn w.property
    exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩

def RiemannMapping.biholomorphUnitDisc (U : TopologicalSpace.Opens ℂ)
    (hUc : IsSimplyConnected (U : Set ℂ)) (hU : (U : Set ℂ) ≠ Set.univ) (x₀ : U) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U unitDisc ω :=
  biholomorphOfBijOn U unitDisc (riemannMap U hUc hU x₀) (riemannMap_spec U hUc hU x₀).1
    (riemannMap_spec U hUc hU x₀).2.1 (riemannMap_spec U hUc hU x₀).2.2.1

def RiemannMapping.triangleDomain : TopologicalSpace.Opens ℂ :=
  ⟨SpecialPeriods.Triangle.triangleInterior, SpecialPeriods.Triangle.triangleInterior_isOpen⟩

def RiemannMapping.trianglePoint : triangleDomain :=
  ⟨SpecialPeriods.Triangle.triangleBasepoint, SpecialPeriods.Triangle.triangleBasepoint_mem⟩

def RiemannMapping.triangleBiholomorph :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) triangleDomain unitDisc ω :=
  biholomorphUnitDisc triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
    SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint

def SpecialPeriods.Triangle.triangleClosedSet : Set (OnePoint ℂ) :=
  closure (RiemannBoundary.onePointDomain triangleInterior)

abbrev SpecialPeriods.Triangle.TriangleClosedDomain :=
  triangleClosedSet

theorem SpecialPeriods.Triangle.triangleClosedSet_isClosed : IsClosed triangleClosedSet :=
  isClosed_closure

theorem SpecialPeriods.Triangle.triangleClosedSet_isCompact : IsCompact triangleClosedSet :=
  triangleClosedSet_isClosed.isCompact

instance SpecialPeriods.Triangle.triangleClosedDomain_compactSpace :
    CompactSpace TriangleClosedDomain :=
  isCompact_iff_compactSpace.mp triangleClosedSet_isCompact

instance SpecialPeriods.Triangle.triangleClosedDomain_t2Space : T2Space TriangleClosedDomain :=
  inferInstance

theorem SpecialPeriods.Triangle.coe_mem_triangleClosedSet_iff_closure (z : ℂ) :
    (z : OnePoint ℂ) ∈ triangleClosedSet ↔ z ∈ closure triangleInterior := by
  change z ∈ ((↑) : ℂ → OnePoint ℂ) ⁻¹' closure (((↑) : ℂ → OnePoint ℂ) '' triangleInterior) ↔ _
  rw [← OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]

theorem SpecialPeriods.Triangle.coe_mem_triangleClosedSet_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ triangleClosedSet ↔
      stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖z + 1‖ := by
  rw [coe_mem_triangleClosedSet_iff_closure, closure_triangleInterior]
  rfl

theorem SpecialPeriods.Triangle.infty_mem_triangleClosedSet :
    ((OnePoint.infty) : OnePoint ℂ) ∈ triangleClosedSet :=
  triangle_infty_mem_closure

def SpecialPeriods.Triangle.triangleClosedInfinity : TriangleClosedDomain :=
  ⟨(OnePoint.infty), infty_mem_triangleClosedSet⟩

def SpecialPeriods.Triangle.triangleClosedInterior :
    TopologicalSpace.Opens TriangleClosedDomain :=
  ⟨{x | x.val ∈ RiemannBoundary.onePointDomain triangleInterior},
    (RiemannBoundary.isOpen_onePointDomain triangleInterior_isOpen).preimage
      continuous_subtype_val⟩

theorem SpecialPeriods.Triangle.triangleClosedInterior_dense :
    Dense (triangleClosedInterior : Set TriangleClosedDomain) := by
  have hi :
    ((↑) : TriangleClosedDomain → OnePoint ℂ) ''
        (triangleClosedInterior : Set TriangleClosedDomain) =
      RiemannBoundary.onePointDomain triangleInterior := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
  apply Subtype.dense_iff.mpr
  rw [hi]
  exact Set.Subset.refl _

def SpecialPeriods.Triangle.triangleClosedInclusion (z : RiemannMapping.triangleDomain) :
    TriangleClosedDomain :=
  ⟨(z : ℂ), subset_closure (RiemannBoundary.coe_mem_onePointDomain.mpr z.property)⟩

theorem SpecialPeriods.Triangle.triangleClosedInclusion_continuous :
    Continuous triangleClosedInclusion :=
  (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _

theorem SpecialPeriods.Triangle.triangleClosedInclusion_mem_interior
    (z : RiemannMapping.triangleDomain) : triangleClosedInclusion z ∈ triangleClosedInterior :=
  RiemannBoundary.coe_mem_onePointDomain.mpr z.property

def SpecialPeriods.Triangle.triangleClosedInteriorHomeomorph :
    RiemannMapping.triangleDomain ≃ₜ triangleClosedInterior
    where
  toFun z := ⟨triangleClosedInclusion z, triangleClosedInclusion_mem_interior z⟩
  invFun
    x := (RiemannBoundary.onePointDomainHomeomorph triangleInterior).symm ⟨x.val.val, x.property⟩
  left_inv
    z := by exact (RiemannBoundary.onePointDomainHomeomorph triangleInterior).symm_apply_apply z
  right_inv
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      congrArg (fun y : RiemannBoundary.onePointDomain triangleInterior => (y : OnePoint ℂ))
        ((RiemannBoundary.onePointDomainHomeomorph triangleInterior).apply_symm_apply
          ⟨x.val.val, x.property⟩)
  continuous_toFun := triangleClosedInclusion_continuous.subtype_mk _
  continuous_invFun :=
    (RiemannBoundary.onePointDomainHomeomorph triangleInterior).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

def SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph :
    triangleClosedInterior ≃ₜ Metric.ball (0 : ℂ) 1 :=
  triangleClosedInteriorHomeomorph.symm.trans RiemannMapping.triangleBiholomorph.toHomeomorph

@[simp]
theorem SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph_apply
    (z : RiemannMapping.triangleDomain) :
    triangleClosedInteriorDiscHomeomorph (triangleClosedInteriorHomeomorph z) =
      RiemannMapping.triangleBiholomorph z := by
  change
    RiemannMapping.triangleBiholomorph
        (triangleClosedInteriorHomeomorph.symm (triangleClosedInteriorHomeomorph z)) =
      _
  rw [triangleClosedInteriorHomeomorph.symm_apply_apply]

theorem SpecialPeriods.Triangle.coe_mem_triangleOnePoint_frontier_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) ↔
      z ∈ frontier triangleInterior := by
  change
    ((z : OnePoint ℂ) ∈ closure (RiemannBoundary.onePointDomain triangleInterior) ∧
        (z : OnePoint ℂ) ∉ interior (RiemannBoundary.onePointDomain triangleInterior)) ↔
      (z ∈ closure triangleInterior ∧ z ∉ interior triangleInterior)
  rw [(RiemannBoundary.isOpen_onePointDomain triangleInterior_isOpen).interior_eq,
    triangleInterior_isOpen.interior_eq]
  exact
    and_congr (coe_mem_triangleClosedSet_iff_closure z)
      (not_congr RiemannBoundary.coe_mem_onePointDomain)

theorem SpecialPeriods.Triangle.triangleClosedBoundary_iff_frontier (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔
      x.val ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) := by
  change
    x.val ∉ RiemannBoundary.onePointDomain triangleInterior ↔
      x.val ∈ closure (RiemannBoundary.onePointDomain triangleInterior) ∧
        x.val ∉ interior (RiemannBoundary.onePointDomain triangleInterior)
  rw [(RiemannBoundary.isOpen_onePointDomain triangleInterior_isOpen).interior_eq]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

def SpecialPeriods.Triangle.circleStraighten (z : ℂ) : ℂ :=
  Complex.I * z / (z + 2)

def SpecialPeriods.Triangle.circleUnstraighten (w : ℂ) : ℂ :=
  2 * w / (Complex.I - w)

theorem SpecialPeriods.Triangle.circleStraighten_sub_I {z : ℂ} (hz : z + 2 ≠ 0) :
    Complex.I - circleStraighten z = 2 * Complex.I / (z + 2) := by
  unfold circleStraighten
  field_simp
  ring

theorem SpecialPeriods.Triangle.circleStraighten_ne_I {z : ℂ} (hz : z + 2 ≠ 0) :
    circleStraighten z ≠ Complex.I := by
  have h : Complex.I - circleStraighten z ≠ 0 := by
    rw [circleStraighten_sub_I hz]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hz
  exact fun he => h (by rw [he, sub_self])

theorem SpecialPeriods.Triangle.circleUnstraighten_add_two {w : ℂ} (hw : Complex.I - w ≠ 0) :
    circleUnstraighten w + 2 = 2 * Complex.I / (Complex.I - w) := by
  unfold circleUnstraighten
  field_simp
  ring

theorem SpecialPeriods.Triangle.circleUnstraighten_add_two_ne_zero {w : ℂ}
    (hw : Complex.I - w ≠ 0) : circleUnstraighten w + 2 ≠ 0 := by
  rw [circleUnstraighten_add_two hw]
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hw

theorem SpecialPeriods.Triangle.circleUnstraighten_straighten {z : ℂ} (hz : z + 2 ≠ 0) :
    circleUnstraighten (circleStraighten z) = z := by
  rw [circleUnstraighten, circleStraighten_sub_I hz]
  unfold circleStraighten
  field_simp

theorem SpecialPeriods.Triangle.circleStraighten_unstraighten {w : ℂ} (hw : Complex.I - w ≠ 0) :
    circleStraighten (circleUnstraighten w) = w := by
  rw [circleStraighten, circleUnstraighten_add_two hw]
  unfold circleUnstraighten
  field_simp

def SpecialPeriods.Triangle.circleBoundaryChart : OpenPartialHomeomorph ℂ ℂ
    where
  toFun := circleStraighten
  invFun := circleUnstraighten
  source := {z | z + 2 ≠ 0}
  target := {w | Complex.I - w ≠ 0}
  map_source' z hz := sub_ne_zero.mpr (circleStraighten_ne_I hz).symm
  map_target' w hw := circleUnstraighten_add_two_ne_zero hw
  left_inv' z hz := circleUnstraighten_straighten hz
  right_inv' w hw := circleStraighten_unstraighten hw
  open_source := isOpen_ne_fun (continuous_id.add continuous_const) continuous_const
  open_target := isOpen_ne_fun (continuous_const.sub continuous_id) continuous_const
  continuousOn_toFun := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun z hz => hz
  continuousOn_invFun := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun z hz => hz

theorem SpecialPeriods.Triangle.circleStraighten_analyticOnNhd :
    AnalyticOnNhd ℂ circleStraighten {z | z + 2 ≠ 0} := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).div (analyticAt_id.add analyticAt_const) hz

theorem SpecialPeriods.Triangle.circleUnstraighten_analyticOnNhd :
    AnalyticOnNhd ℂ circleUnstraighten {w | Complex.I - w ≠ 0} := by
  intro z hz
  exact (analyticAt_const.mul analyticAt_id).div (analyticAt_const.sub analyticAt_id) hz

theorem SpecialPeriods.Triangle.circleStraighten_im (z : ℂ) :
    (circleStraighten z).im = (Complex.normSq (z + 1) - 1) / Complex.normSq (z + 2) := by
  simp only [circleStraighten, Complex.div_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    MulZeroClass.zero_mul, one_mul, zero_add, Complex.mul_re, zero_sub, Complex.add_re,
    Complex.re_ofNat, Complex.add_im, Complex.im_ofNat, add_zero]
  rw [← sub_div]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero]
  ring

theorem SpecialPeriods.Triangle.circleStraighten_im_pos_iff {z : ℂ} (hz : z + 2 ≠ 0) :
    0 < (circleStraighten z).im ↔ 1 < ‖z + 1‖ := by
  rw [circleStraighten_im, div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hz), sub_pos]
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (z + 1)]
  · intro h
    nlinarith

theorem SpecialPeriods.Triangle.circleStraighten_im_eq_zero_iff {z : ℂ} (hz : z + 2 ≠ 0) :
    (circleStraighten z).im = 0 ↔ ‖z + 1‖ = 1 := by
  rw [circleStraighten_im, div_eq_zero_iff, or_iff_left (Complex.normSq_pos.mpr hz).ne',
    sub_eq_zero, Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (z + 1)]
  · intro h
    rw [h]
    norm_num

theorem SpecialPeriods.Triangle.exists_circle_side_neighborhood {a : ℂ} (haL : stripLeft < a.re)
    (haR : a.re < -1 / 2) (hai : 0 < a.im) :
    ∃ r > 0,
      ∀ z ∈ Metric.ball a r,
        z ∈ circleBoundaryChart.source ∧
          (z ∈ triangleInterior ↔ 0 < (circleBoundaryChart z).im) := by
  let V : Set ℂ := {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a ⟨haL, haR, hai⟩
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  have hzden : z + 2 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.im_ofNat, add_zero, Complex.zero_im] at hi
    exact h.2.2.ne' hi
  refine ⟨hzden, ?_⟩
  change (stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖) ↔ 0 < (circleStraighten z).im
  rw [circleStraighten_im_pos_iff hzden]
  exact ⟨fun hz' => hz'.2.2.2, fun hnorm => ⟨h.1, h.2.1, h.2.2, hnorm⟩⟩

def SpecialPeriods.Triangle.leftBoundaryChart : ℂ ≃ₜ ℂ
    where
  toFun z := Complex.I * (z - stripLeft)
  invFun w := -Complex.I * w + stripLeft
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def SpecialPeriods.Triangle.rightBoundaryChart : ℂ ≃ₜ ℂ
    where
  toFun z := -Complex.I * (z + 1 / 2)
  invFun w := Complex.I * w - 1 / 2
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem SpecialPeriods.Triangle.leftBoundaryChart_im (z : ℂ) :
    (leftBoundaryChart z).im = z.re - stripLeft := by
  change (Complex.I * (z - (stripLeft : ℂ))).im = _
  simp

@[simp]
theorem SpecialPeriods.Triangle.rightBoundaryChart_im (z : ℂ) :
    (rightBoundaryChart z).im = -(z.re + 1 / 2) := by
  change (-Complex.I * (z + 1 / 2)).im = _
  simp

theorem SpecialPeriods.Triangle.leftBoundaryChart_symm_analyticAt (z : ℂ) :
    AnalyticAt ℂ leftBoundaryChart.symm z :=
  (analyticAt_const.mul analyticAt_id).add analyticAt_const

theorem SpecialPeriods.Triangle.rightBoundaryChart_symm_analyticAt (z : ℂ) :
    AnalyticAt ℂ rightBoundaryChart.symm z :=
  (analyticAt_const.mul analyticAt_id).sub analyticAt_const

theorem SpecialPeriods.Triangle.stripLeft_lt_right : stripLeft < -1 / 2 := by
  unfold stripLeft
  linarith [width_pos]

theorem SpecialPeriods.Triangle.exists_left_side_neighborhood {a : ℂ} (ha : a.re = stripLeft)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ triangleInterior ↔ 0 < (leftBoundaryChart z).im := by
  let V : Set ℂ := {z | z.re < -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}
  have hV : IsOpen V :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)))
  have haV : a ∈ V := ⟨ha ▸ stripLeft_lt_right, hai, haC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  rw [leftBoundaryChart_im, sub_pos]
  exact ⟨fun hz' => hz'.1, fun hz' => ⟨hz', h.1, h.2.1, h.2.2⟩⟩

theorem SpecialPeriods.Triangle.exists_right_side_neighborhood {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ triangleInterior ↔ 0 < (rightBoundaryChart z).im := by
  let V : Set ℂ := {z | stripLeft < z.re ∧ 0 < z.im ∧ 1 < ‖z + 1‖}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt continuous_const ((continuous_id.add continuous_const).norm)))
  have haV : a ∈ V := ⟨ha ▸ stripLeft_lt_right, hai, haC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV a haV
  refine ⟨r, hr, ?_⟩
  intro z hz
  have h := hball hz
  rw [rightBoundaryChart_im]
  have he : 0 < -(z.re + 1 / 2) ↔ z.re < -1 / 2 := by constructor <;> intro hi <;> linarith
  rw [he]
  exact ⟨fun hz' => hz'.2.1, fun hz' => ⟨h.1, hz', h.2.1, h.2.2⟩⟩

def SpecialPeriods.Triangle.triangleOpenLeftSide : Set ℂ :=
  {z | z.re = stripLeft ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

def SpecialPeriods.Triangle.triangleOpenRightSide : Set ℂ :=
  {z | z.re = -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

def SpecialPeriods.Triangle.triangleOpenCircleSide : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1}

theorem SpecialPeriods.Triangle.triangleOpenLeftSide_disjoint_interior :
    Disjoint triangleOpenLeftSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hL hI
  exact (ne_of_gt hI.1) hL.1

theorem SpecialPeriods.Triangle.triangleOpenRightSide_disjoint_interior :
    Disjoint triangleOpenRightSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hR hI
  exact (ne_of_lt hI.2.1) hR.1

theorem SpecialPeriods.Triangle.triangleOpenCircleSide_disjoint_interior :
    Disjoint triangleOpenCircleSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hC hI
  exact (ne_of_gt hI.2.2.2) hC.2.2.2

theorem SpecialPeriods.Triangle.centerOne_coe_re : (centerOne : ℂ).re = -1 / 2 := by
  simp only [centerOne_val, Complex.sub_re, SpecialPeriods.rho_re, Complex.one_re]
  norm_num

theorem SpecialPeriods.Triangle.centerTwo_coe_re : (centerTwo : ℂ).re = stripLeft :=
  centerTwo_re

theorem SpecialPeriods.Triangle.centerOne_norm_add_one : ‖(centerOne : ℂ) + 1‖ = 1 := by
  simpa only [centerOne_val, sub_add_cancel] using SpecialPeriods.norm_rho

theorem SpecialPeriods.Triangle.centerTwo_norm_add_one : ‖(centerTwo : ℂ) + 1‖ = 1 := by
  have hsq : Complex.normSq ((centerTwo : ℂ) + 1) = 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re,
      centerTwo_im]
    nlinarith [width_sq]
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((centerTwo : ℂ) + 1)]

theorem SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq {z w : ℂ} (hr : z.re = w.re)
    (hz : 0 < z.im) (hw : 0 < w.im) (hn : ‖z + 1‖ = ‖w + 1‖) : z = w := by
  apply Complex.ext hr
  apply (sq_eq_sq₀ hz.le hw.le).mp
  have hsq : Complex.normSq (z + 1) = Complex.normSq (w + 1) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, hr] at hsq
  nlinarith

theorem SpecialPeriods.Triangle.right_circle_endpoint_iff (z : ℂ) :
    (z.re = -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1) ↔ z = (centerOne : ℂ) := by
  constructor
  · rintro ⟨hr, hi, hn⟩
    exact
      complex_eq_of_re_eq_norm_add_one_eq (hr.trans centerOne_coe_re.symm) hi centerOne.im_pos
        (hn.trans centerOne_norm_add_one.symm)
  · rintro rfl
    exact ⟨centerOne_coe_re, centerOne.im_pos, centerOne_norm_add_one⟩

theorem SpecialPeriods.Triangle.left_circle_endpoint_iff (z : ℂ) :
    (z.re = stripLeft ∧ 0 < z.im ∧ ‖z + 1‖ = 1) ↔ z = (centerTwo : ℂ) := by
  constructor
  · rintro ⟨hr, hi, hn⟩
    exact
      complex_eq_of_re_eq_norm_add_one_eq (hr.trans centerTwo_coe_re.symm) hi centerTwo.im_pos
        (hn.trans centerTwo_norm_add_one.symm)
  · rintro rfl
    exact ⟨centerTwo_coe_re, centerTwo.im_pos, centerTwo_norm_add_one⟩

theorem SpecialPeriods.Triangle.mem_frontier_triangleInterior_iff_closedRegion {z : ℂ} :
    z ∈ frontier triangleInterior ↔ z ∈ triangleClosedRegion ∧ z ∉ triangleInterior := by
  rw [frontier, triangleInterior_isOpen.interior_eq, closure_triangleInterior]
  rfl

theorem SpecialPeriods.Triangle.triangleOpenLeftSide_subset_frontier :
    triangleOpenLeftSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  refine ⟨⟨hz.1.symm.le, ?_, hz.2.1, hz.2.2.le⟩, ?_⟩
  · simpa only [hz.1] using stripLeft_lt_right.le
  · exact fun h => Set.disjoint_left.mp triangleOpenLeftSide_disjoint_interior hz h

theorem SpecialPeriods.Triangle.triangleOpenRightSide_subset_frontier :
    triangleOpenRightSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  refine ⟨⟨?_, hz.1.le, hz.2.1, hz.2.2.le⟩, ?_⟩
  · simpa only [hz.1] using stripLeft_lt_right.le
  · exact fun h => Set.disjoint_left.mp triangleOpenRightSide_disjoint_interior hz h

theorem SpecialPeriods.Triangle.triangleOpenCircleSide_subset_frontier :
    triangleOpenCircleSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  exact
    ⟨⟨hz.1.le, hz.2.1.le, hz.2.2.1, hz.2.2.2.symm.le⟩, fun h =>
      Set.disjoint_left.mp triangleOpenCircleSide_disjoint_interior hz h⟩

theorem SpecialPeriods.Triangle.centerOne_mem_triangleClosedRegion :
    (centerOne : ℂ) ∈ triangleClosedRegion := by
  refine ⟨?_, ?_, centerOne.im_pos, ?_⟩
  · rw [centerOne_coe_re]
    exact stripLeft_lt_right.le
  · rw [centerOne_coe_re]
  · rw [centerOne_norm_add_one]

theorem SpecialPeriods.Triangle.centerTwo_mem_triangleClosedRegion :
    (centerTwo : ℂ) ∈ triangleClosedRegion := by
  refine ⟨?_, ?_, centerTwo.im_pos, ?_⟩
  · rw [centerTwo_coe_re]
  · rw [centerTwo_coe_re]
    exact stripLeft_lt_right.le
  · rw [centerTwo_norm_add_one]

theorem SpecialPeriods.Triangle.centerOne_not_mem_triangleInterior :
    (centerOne : ℂ) ∉ triangleInterior := by
  intro hz
  have h := hz.2.1
  rw [centerOne_coe_re] at h
  exact lt_irrefl _ h

theorem SpecialPeriods.Triangle.centerTwo_not_mem_triangleInterior :
    (centerTwo : ℂ) ∉ triangleInterior := by
  intro hz
  have h := hz.1
  rw [centerTwo_coe_re] at h
  exact lt_irrefl _ h

theorem SpecialPeriods.Triangle.centerOne_mem_frontier_triangleInterior :
    (centerOne : ℂ) ∈ frontier triangleInterior :=
  mem_frontier_triangleInterior_iff_closedRegion.mpr
    ⟨centerOne_mem_triangleClosedRegion, centerOne_not_mem_triangleInterior⟩

theorem SpecialPeriods.Triangle.centerTwo_mem_frontier_triangleInterior :
    (centerTwo : ℂ) ∈ frontier triangleInterior :=
  mem_frontier_triangleInterior_iff_closedRegion.mpr
    ⟨centerTwo_mem_triangleClosedRegion, centerTwo_not_mem_triangleInterior⟩

theorem SpecialPeriods.Triangle.centerOne_mem_closure_triangleInterior :
    (centerOne : ℂ) ∈ closure triangleInterior := by
  rw [closure_triangleInterior]
  exact centerOne_mem_triangleClosedRegion

theorem SpecialPeriods.Triangle.centerTwo_mem_closure_triangleInterior :
    (centerTwo : ℂ) ∈ closure triangleInterior := by
  rw [closure_triangleInterior]
  exact centerTwo_mem_triangleClosedRegion

theorem SpecialPeriods.Triangle.centerOne_coe_ne_centerTwo : (centerOne : ℂ) ≠ (centerTwo : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  rw [centerOne_coe_re, centerTwo_coe_re] at hr
  exact (ne_of_gt stripLeft_lt_right) hr

theorem SpecialPeriods.Triangle.mem_frontier_triangleInterior_iff {z : ℂ} :
    z ∈ frontier triangleInterior ↔
      z ∈ triangleOpenLeftSide ∨
        z ∈ triangleOpenRightSide ∨
          z ∈ triangleOpenCircleSide ∨ z = (centerOne : ℂ) ∨ z = (centerTwo : ℂ) := by
  constructor
  · intro hz
    obtain ⟨hR, hI⟩ := mem_frontier_triangleInterior_iff_closedRegion.mp hz
    rcases lt_or_eq_of_le hR.1 with hL | hL
    · rcases lt_or_eq_of_le hR.2.1 with hU | hU
      · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
        · exact (hI ⟨hL, hU, hR.2.2.1, hN⟩).elim
        · exact Or.inr (Or.inr (Or.inl ⟨hL, hU, hR.2.2.1, hN.symm⟩))
      · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
        · exact Or.inr (Or.inl ⟨hU, hR.2.2.1, hN⟩)
        · exact
            Or.inr
              (Or.inr
                (Or.inr (Or.inl ((right_circle_endpoint_iff z).mp ⟨hU, hR.2.2.1, hN.symm⟩))))
    · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
      · exact Or.inl ⟨hL.symm, hR.2.2.1, hN⟩
      · exact
          Or.inr
            (Or.inr
              (Or.inr (Or.inr ((left_circle_endpoint_iff z).mp ⟨hL.symm, hR.2.2.1, hN.symm⟩))))
  · rintro (h | h | h | rfl | rfl)
    · exact triangleOpenLeftSide_subset_frontier h
    · exact triangleOpenRightSide_subset_frontier h
    · exact triangleOpenCircleSide_subset_frontier h
    · exact centerOne_mem_frontier_triangleInterior
    · exact centerTwo_mem_frontier_triangleInterior

def SpecialPeriods.Triangle.triangleClosedCenterOne : TriangleClosedDomain :=
  ⟨((centerOne : ℂ) : OnePoint ℂ),
    (coe_mem_triangleClosedSet_iff_closure _).mpr centerOne_mem_closure_triangleInterior⟩

def SpecialPeriods.Triangle.triangleClosedCenterTwo : TriangleClosedDomain :=
  ⟨((centerTwo : ℂ) : OnePoint ℂ),
    (coe_mem_triangleClosedSet_iff_closure _).mpr centerTwo_mem_closure_triangleInterior⟩

@[simp]
theorem SpecialPeriods.Triangle.triangleClosedCenterOne_val :
    (triangleClosedCenterOne : OnePoint ℂ) = ((centerOne : ℂ) : OnePoint ℂ) :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.triangleClosedCenterTwo_val :
    (triangleClosedCenterTwo : OnePoint ℂ) = ((centerTwo : ℂ) : OnePoint ℂ) :=
  rfl

theorem SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo :
    triangleClosedCenterOne ≠ triangleClosedCenterTwo := by
  intro h
  exact centerOne_coe_ne_centerTwo (OnePoint.coe_injective (congrArg Subtype.val h))

@[simp]
theorem SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty :
    triangleClosedCenterOne ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty (centerOne : ℂ) (congrArg Subtype.val h)

@[simp]
theorem SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty :
    triangleClosedCenterTwo ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty (centerTwo : ℂ) (congrArg Subtype.val h)

theorem SpecialPeriods.Triangle.mem_triangleOnePoint_frontier_iff {x : OnePoint ℂ} :
    x ∈ frontier (RiemannBoundary.onePointDomain triangleInterior) ↔
      x = (OnePoint.infty) ∨
        x ∈ RiemannBoundary.onePointDomain triangleOpenLeftSide ∨
          x ∈ RiemannBoundary.onePointDomain triangleOpenRightSide ∨
            x ∈ RiemannBoundary.onePointDomain triangleOpenCircleSide ∨
              x = ((centerOne : ℂ) : OnePoint ℂ) ∨ x = ((centerTwo : ℂ) : OnePoint ℂ) := by
  induction x using OnePoint.rec with
  | infty => exact iff_of_true triangle_infty_mem_frontier (Or.inl rfl)
  | coe z =>
    simpa only [coe_mem_triangleOnePoint_frontier_iff, OnePoint.coe_ne_infty, false_or,
      RiemannBoundary.coe_mem_onePointDomain, OnePoint.coe_eq_coe] using
      (mem_frontier_triangleInterior_iff (z := z))

theorem SpecialPeriods.Triangle.triangleClosedBoundary_iff_cases (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔
      x = triangleClosedInfinity ∨
        x.val ∈ RiemannBoundary.onePointDomain triangleOpenLeftSide ∨
          x.val ∈ RiemannBoundary.onePointDomain triangleOpenRightSide ∨
            x.val ∈ RiemannBoundary.onePointDomain triangleOpenCircleSide ∨
              x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  rw [triangleClosedBoundary_iff_frontier]
  simpa only [Subtype.ext_iff, triangleClosedInfinity, triangleClosedCenterOne_val,
    triangleClosedCenterTwo_val] using (mem_triangleOnePoint_frontier_iff (x := x.val))

theorem SpecialPeriods.Triangle.triangleClosedBoundary_cases (x : TriangleClosedDomain)
    (hx : x ∉ triangleClosedInterior) :
    x = triangleClosedInfinity ∨
      (∃ z : ℂ, z ∈ triangleOpenLeftSide ∧ x.val = (z : OnePoint ℂ)) ∨
        (∃ z : ℂ, z ∈ triangleOpenRightSide ∧ x.val = (z : OnePoint ℂ)) ∨
          (∃ z : ℂ, z ∈ triangleOpenCircleSide ∧ x.val = (z : OnePoint ℂ)) ∨
            x = triangleClosedCenterOne ∨ x = triangleClosedCenterTwo := by
  rcases (triangleClosedBoundary_iff_cases x).mp hx with hi | hL | hR | hC | h₁ | h₂
  · exact Or.inl hi
  · obtain ⟨z, hz, he⟩ := hL
    exact Or.inr (Or.inl ⟨z, hz, he.symm⟩)
  · obtain ⟨z, hz, he⟩ := hR
    exact Or.inr (Or.inr (Or.inl ⟨z, hz, he.symm⟩))
  · obtain ⟨z, hz, he⟩ := hC
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨z, hz, he.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h₁))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h₂))))

def RiemannMapping.triangleMap : ℂ → ℂ :=
  riemannMap triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
    SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint

theorem RiemannMapping.triangleMap_differentiable :
    DifferentiableOn ℂ triangleMap SpecialPeriods.Triangle.triangleInterior :=
  (riemannMap_spec triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
      SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint).1

theorem RiemannMapping.triangleMap_bijOn :
    Set.BijOn triangleMap SpecialPeriods.Triangle.triangleInterior (Metric.ball (0 : ℂ) 1) :=
  (riemannMap_spec triangleDomain SpecialPeriods.Triangle.triangleInterior_isSimplyConnected
        SpecialPeriods.Triangle.triangleInterior_ne_univ trianglePoint).2.1

theorem RiemannMapping.triangleMap_biholomorph (z : triangleDomain) :
    triangleMap z = (triangleBiholomorph z : ℂ) :=
  rfl

theorem RiemannMapping.triangleMap_norm_lt_one {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) : ‖triangleMap z‖ < 1 := by
  simpa using triangleMap_bijOn.mapsTo hz

theorem SpecialPeriods.Triangle.cayley_re_sub (a z : ℂ) (hz : 1 - z ≠ 0) :
    (SpecialPeriods.cayley a z).re - a.re = -2 * a.im * z.im / Complex.normSq (1 - z) := by
  have hd : Complex.normSq (1 - z) ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  simp only [SpecialPeriods.cayley, Complex.div_re, Complex.sub_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.mul_im, Complex.one_re,
    Complex.one_im]
  field_simp [hd]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

theorem SpecialPeriods.Triangle.cayley_add_one (a z : ℂ) (hz : 1 - z ≠ 0) :
    SpecialPeriods.cayley a z + 1 = ((a + 1) - conj (a + 1) * z) / (1 - z) := by
  unfold SpecialPeriods.cayley
  simp only [map_add, map_one]
  field_simp
  ring

theorem SpecialPeriods.Triangle.cayley_circle_normSq (a z : ℂ) (hz : 1 - z ≠ 0)
    (ha : Complex.normSq (a + 1) = 1) :
    Complex.normSq (SpecialPeriods.cayley a z + 1) - 1 =
      (2 * z.re - 2 * ((a + 1) ^ 2 * conj z).re) / Complex.normSq (1 - z) := by
  have hd : Complex.normSq (1 - z) ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  rw [cayley_add_one a z hz, map_div₀]
  field_simp [hd]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, add_zero, pow_two] at ha ⊢
  linear_combination (1 + z.re ^ 2 + z.im ^ 2) * ha

theorem SpecialPeriods.Triangle.centerOne_re : centerOne.re = -1 / 2 := by
  simp only [UpperHalfPlane.re, centerOne_val, Complex.sub_re, SpecialPeriods.rho_re,
    Complex.one_re]
  norm_num

theorem SpecialPeriods.Triangle.centerOne_circle_normSq :
    Complex.normSq ((centerOne : ℂ) + 1) = 1 := by
  rw [centerOne_val, sub_add_cancel, Complex.normSq_eq_norm_sq, SpecialPeriods.norm_rho]
  norm_num

theorem SpecialPeriods.Triangle.centerTwo_circle_normSq :
    Complex.normSq ((centerTwo : ℂ) + 1) = 1 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re, centerTwo_im]
  nlinarith [width_sq]

theorem SpecialPeriods.Triangle.cayley_centerOne_circle_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.normSq (SpecialPeriods.cayley centerOne z + 1) - 1 =
      (3 * z.re - Real.sqrt 3 * z.im) / Complex.normSq (1 - z) := by
  rw [cayley_circle_normSq _ _ (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
      centerOne_circle_normSq]
  congr 1
  simp only [centerOne_val, sub_add_cancel, SpecialPeriods.rho_sq, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, sub_zero,
    SpecialPeriods.rho_re, SpecialPeriods.rho_im]
  ring

theorem SpecialPeriods.Triangle.cayley_centerTwo_circle_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.normSq (SpecialPeriods.cayley centerTwo z + 1) - 1 =
      2 * (z.re + z.im) / Complex.normSq (1 - z) := by
  rw [cayley_circle_normSq _ _ (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
      centerTwo_circle_normSq]
  congr 1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, add_zero, Complex.conj_re, Complex.conj_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, centerTwo_re, centerTwo_im]
  linear_combination z.im * width_sq

def SpecialPeriods.Triangle.cornerSectorThree : Set ℂ :=
  {z | 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re}

def SpecialPeriods.Triangle.cornerSectorFour : Set ℂ :=
  {z | z.im < 0 ∧ 0 < z.re + z.im}

theorem SpecialPeriods.Triangle.cayley_centerOne_right_iff {z : ℂ} (hz : ‖z‖ < 1) :
    (SpecialPeriods.cayley centerOne z).re < -1 / 2 ↔ 0 < z.im := by
  have h := cayley_re_sub centerOne z (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  rw [UpperHalfPlane.coe_re, centerOne_re] at h
  have hd := Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  have hc : 0 < (centerOne : ℂ).im := centerOne.im_pos
  have hsign : -2 * (centerOne : ℂ).im * z.im / Complex.normSq (1 - z) < 0 ↔ 0 < z.im := by
    rw [div_lt_iff₀ hd, MulZeroClass.zero_mul]
    constructor
    · intro hi
      by_contra hn
      have hle : z.im ≤ 0 := le_of_not_gt hn
      have hnonneg : 0 ≤ -2 * (centerOne : ℂ).im * z.im :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hle
      linarith
    · intro hi
      exact mul_neg_of_neg_of_pos (by linarith) hi
  rw [← h, sub_neg] at hsign
  exact hsign

theorem SpecialPeriods.Triangle.cayley_centerTwo_left_iff {z : ℂ} (hz : ‖z‖ < 1) :
    stripLeft < (SpecialPeriods.cayley centerTwo z).re ↔ z.im < 0 := by
  have h := cayley_re_sub centerTwo z (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  rw [UpperHalfPlane.coe_re, centerTwo_re] at h
  change (SpecialPeriods.cayley centerTwo z).re - stripLeft = _ at h
  have hd := Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)
  have hc : 0 < (centerTwo : ℂ).im := centerTwo.im_pos
  have hsign : 0 < -2 * (centerTwo : ℂ).im * z.im / Complex.normSq (1 - z) ↔ z.im < 0 := by
    rw [div_pos_iff_of_pos_right hd]
    constructor
    · intro hi
      by_contra hn
      have hle : 0 ≤ z.im := le_of_not_gt hn
      have hnonpos : -2 * (centerTwo : ℂ).im * z.im ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hle
      linarith
    · intro hi
      exact mul_pos_of_neg_of_neg (by linarith) hi
  rw [← h, sub_pos] at hsign
  exact hsign

theorem SpecialPeriods.Triangle.one_lt_norm_iff_normSq_sub_pos (u : ℂ) :
    1 < ‖u‖ ↔ 0 < Complex.normSq u - 1 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg u]

theorem SpecialPeriods.Triangle.cayley_centerOne_circle_iff {z : ℂ} (hz : ‖z‖ < 1) :
    1 < ‖SpecialPeriods.cayley centerOne z + 1‖ ↔ Real.sqrt 3 * z.im < 3 * z.re := by
  rw [one_lt_norm_iff_normSq_sub_pos, cayley_centerOne_circle_normSq hz,
    div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz)),
    sub_pos]

theorem SpecialPeriods.Triangle.cayley_centerTwo_circle_iff {z : ℂ} (hz : ‖z‖ < 1) :
    1 < ‖SpecialPeriods.cayley centerTwo z + 1‖ ↔ 0 < z.re + z.im := by
  rw [one_lt_norm_iff_normSq_sub_pos, cayley_centerTwo_circle_normSq hz,
    div_pos_iff_of_pos_right
      (Complex.normSq_pos.mpr (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one hz))]
  exact mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)

theorem SpecialPeriods.Triangle.cayley_analyticAt (a : ℂ) {z : ℂ} (hz : 1 - z ≠ 0) :
    AnalyticAt ℂ (SpecialPeriods.cayley a) z :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hz

theorem SpecialPeriods.Triangle.exists_cornerThree_radius :
    ∃ r : ℝ,
      0 < r ∧
        r ≤ 1 ∧
          ∀ z : ℂ,
            ‖z‖ < r →
              (SpecialPeriods.cayley centerOne z ∈ triangleInterior ↔ z ∈ cornerSectorThree) := by
  have hc : ContinuousAt (fun z : ℂ => (SpecialPeriods.cayley centerOne z).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (cayley_analyticAt centerOne (z := 0) (by simp)).continuousAt
  have hleft : ∀ᶠ z : ℂ in 𝓝 0, stripLeft < (SpecialPeriods.cayley centerOne z).re :=
    continuousAt_const.eventually_lt hc
      (by
        simp only [SpecialPeriods.cayley_zero, UpperHalfPlane.coe_re, centerOne_re]
        unfold stripLeft
        linarith [width_pos])
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hleft
  refine ⟨Min.min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_right _ _)
  have hzs : z ∈ Metric.ball 0 s := by simpa using hz.trans_le (min_le_left _ _)
  have hzi := SpecialPeriods.cayley_im_pos centerOne.im_pos hz1
  change
    (stripLeft < (SpecialPeriods.cayley centerOne z).re ∧
        (SpecialPeriods.cayley centerOne z).re < -1 / 2 ∧
          0 < (SpecialPeriods.cayley centerOne z).im ∧
            1 < ‖SpecialPeriods.cayley centerOne z + 1‖) ↔
      _
  rw [cayley_centerOne_right_iff hz1, cayley_centerOne_circle_iff hz1]
  exact ⟨fun h => ⟨h.2.1, h.2.2.2⟩, fun h => ⟨hball hzs, h.1, hzi, h.2⟩⟩

theorem SpecialPeriods.Triangle.exists_cornerFour_radius :
    ∃ r : ℝ,
      0 < r ∧
        r ≤ 1 ∧
          ∀ z : ℂ,
            ‖z‖ < r →
              (SpecialPeriods.cayley centerTwo z ∈ triangleInterior ↔ z ∈ cornerSectorFour) := by
  have hc : ContinuousAt (fun z : ℂ => (SpecialPeriods.cayley centerTwo z).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (cayley_analyticAt centerTwo (z := 0) (by simp)).continuousAt
  have hright : ∀ᶠ z : ℂ in 𝓝 0, (SpecialPeriods.cayley centerTwo z).re < -1 / 2 :=
    hc.eventually_lt continuousAt_const
      (by
        simp only [SpecialPeriods.cayley_zero, UpperHalfPlane.coe_re, centerTwo_re]
        linarith [width_pos])
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp hright
  refine ⟨Min.min s 1, lt_min hs zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_right _ _)
  have hzs : z ∈ Metric.ball 0 s := by simpa using hz.trans_le (min_le_left _ _)
  have hzi := SpecialPeriods.cayley_im_pos centerTwo.im_pos hz1
  change
    (stripLeft < (SpecialPeriods.cayley centerTwo z).re ∧
        (SpecialPeriods.cayley centerTwo z).re < -1 / 2 ∧
          0 < (SpecialPeriods.cayley centerTwo z).im ∧
            1 < ‖SpecialPeriods.cayley centerTwo z + 1‖) ↔
      _
  rw [cayley_centerTwo_left_iff hz1, cayley_centerTwo_circle_iff hz1]
  exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, hball hzs, hzi, h.2⟩⟩

def SpecialPeriods.Triangle.cornerParameterThree (w : ℂ) : ℂ :=
  SpecialPeriods.cayley centerOne (RiemannBoundary.principalRoot 3 w)

def SpecialPeriods.Triangle.cornerParameterFour (w : ℂ) : ℂ :=
  SpecialPeriods.cayley centerTwo (RiemannBoundary.rotatedPrincipalRootFour w)

@[simp]
theorem SpecialPeriods.Triangle.cornerParameterThree_zero : cornerParameterThree 0 = centerOne := by
  simp [cornerParameterThree, RiemannBoundary.principalRoot_zero (by norm_num : 0 < 3)]

@[simp]
theorem SpecialPeriods.Triangle.cornerParameterFour_zero : cornerParameterFour 0 = centerTwo := by
  simp [cornerParameterFour]

theorem SpecialPeriods.Triangle.continuousAt_cornerParameterThree_zero :
    ContinuousAt cornerParameterThree 0 := by
  have hc : ContinuousAt (SpecialPeriods.cayley (centerOne : ℂ)) 0 :=
    (cayley_analyticAt centerOne (by simp)).continuousAt
  have h0 : RiemannBoundary.principalRoot 3 (0 : ℂ) = 0 :=
    RiemannBoundary.principalRoot_zero (by norm_num)
  exact (h0 ▸ hc).comp (RiemannBoundary.continuousAt_principalRoot_zero (by norm_num : 0 < 3))

theorem SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero :
    ContinuousAt cornerParameterFour 0 := by
  have hc : ContinuousAt (SpecialPeriods.cayley (centerTwo : ℂ)) 0 :=
    (cayley_analyticAt centerTwo (by simp)).continuousAt
  exact
    (RiemannBoundary.rotatedPrincipalRootFour_zero ▸ hc).comp
      RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero

theorem SpecialPeriods.Triangle.cornerParameterThree_im_pos {w : ℂ}
    (hw : ‖RiemannBoundary.principalRoot 3 w‖ < 1) : 0 < (cornerParameterThree w).im :=
  SpecialPeriods.cayley_im_pos centerOne.im_pos hw

theorem SpecialPeriods.Triangle.cornerParameterFour_im_pos {w : ℂ}
    (hw : ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) : 0 < (cornerParameterFour w).im :=
  SpecialPeriods.cayley_im_pos centerTwo.im_pos hw

theorem SpecialPeriods.Triangle.cayley_coordinate_inverse (a : UpperHalfPlane) {z : ℂ}
    (hz : ‖z‖ < 1) :
    (SpecialPeriods.cayley a z - a) / (SpecialPeriods.cayley a z - conj (a : ℂ)) = z := by
  have he :=
    congrArg Subtype.val (toDisc_fromDisc a ⟨z, by simpa [SpecialPeriods.unitDisc] using hz⟩)
  simpa only [toDisc_val, cayleyCoordinate, fromDisc_val] using he

theorem SpecialPeriods.Triangle.cornerParameterThree_power {w : ℂ}
    (hw : ‖RiemannBoundary.principalRoot 3 w‖ < 1) :
    ((cornerParameterThree w - centerOne) / (cornerParameterThree w - conj (centerOne : ℂ))) ^ 3 =
      w := by
  rw [cornerParameterThree, cayley_coordinate_inverse centerOne hw,
    RiemannBoundary.principalRoot_pow (by norm_num : 0 < 3)]

theorem SpecialPeriods.Triangle.cornerParameterFour_power {w : ℂ}
    (hw : ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) :
    ((cornerParameterFour w - centerTwo) / (cornerParameterFour w - conj (centerTwo : ℂ))) ^ 4 =
      -w := by
  rw [cornerParameterFour, cayley_coordinate_inverse centerTwo hw,
    RiemannBoundary.rotatedPrincipalRootFour_pow]

private theorem SpecialPeriods.Triangle.exists_small_root_ball_mo1973_19462 {f : ℂ → ℂ}
    (hf : ContinuousAt f 0) (hf0 : f 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖f w‖ < r := by
  have hn : ∀ᶠ w in 𝓝 (0 : ℂ), ‖f w‖ < r :=
    hf.norm.eventually_lt continuousAt_const (by simpa only [hf0, norm_zero] using hr)
  exact Metric.mem_nhds_iff.mp hn

theorem SpecialPeriods.Triangle.cornerParameterThree_analyticOnNhd {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.principalRoot 3 w‖ < 1) :
    AnalyticOnNhd ℂ cornerParameterThree (U ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  exact
    (cayley_analyticAt centerOne (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (hU w hw.1))).comp
      (RiemannBoundary.analyticOnNhd_principalRoot_upper 3 w hw.2)

theorem SpecialPeriods.Triangle.cornerParameterFour_analyticOnNhd {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) :
    AnalyticOnNhd ℂ cornerParameterFour (U ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  exact
    (cayley_analyticAt centerTwo (SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (hU w hw.1))).comp
      (RiemannBoundary.analyticOnNhd_rotatedPrincipalRootFour_upper w hw.2)

theorem SpecialPeriods.Triangle.cornerParameterThree_continuousOn {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.principalRoot 3 w‖ < 1) :
    ContinuousOn cornerParameterThree (U ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hc := (SpecialPeriods.cayley_contDiffOn (centerOne : ℂ)).continuousOn
  exact
    hc.comp
      ((RiemannBoundary.continuousOn_principalRoot_closedUpper (by norm_num : 0 < 3)).mono
        (fun _ h => h.2))
      (fun w hw => by simpa using hU w hw.1)

theorem SpecialPeriods.Triangle.cornerParameterFour_continuousOn {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1) :
    ContinuousOn cornerParameterFour (U ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hc := (SpecialPeriods.cayley_contDiffOn (centerTwo : ℂ)).continuousOn
  exact
    hc.comp
      (RiemannBoundary.continuousOn_rotatedPrincipalRootFour_closedUpper.mono (fun _ h => h.2))
      (fun w hw => by simpa using hU w hw.1)

theorem SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood :
    ∃ δ : ℝ,
      0 < δ ∧
        AnalyticOnNhd ℂ cornerParameterThree (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im}) ∧
          ContinuousOn cornerParameterThree (Metric.ball 0 δ ∩ {w : ℂ | 0 ≤ w.im}) ∧
            Set.MapsTo cornerParameterThree (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im})
                triangleInterior ∧
              (∀ t : ℝ,
                  (t : ℂ) ∈ Metric.ball 0 δ → cornerParameterThree (t : ℂ) ∉ triangleInterior) ∧
                (∀ w ∈ Metric.ball 0 δ, 0 < (cornerParameterThree w).im) ∧
                  (∀ w ∈ Metric.ball 0 δ,
                    ((cornerParameterThree w - centerOne) /
                          (cornerParameterThree w - conj (centerOne : ℂ))) ^
                        3 =
                      w) := by
  obtain ⟨r, hr, hr1, hsector⟩ := exists_cornerThree_radius
  obtain ⟨δ, hδ, hδr⟩ :=
    exists_small_root_ball_mo1973_19462
      (RiemannBoundary.continuousAt_principalRoot_zero (by norm_num : 0 < 3))
      (RiemannBoundary.principalRoot_zero (by norm_num : 0 < 3)) hr
  have hδ1 : ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖RiemannBoundary.principalRoot 3 w‖ < 1 := fun w hw =>
    (hδr w hw).trans_le hr1
  refine
    ⟨δ, hδ, cornerParameterThree_analyticOnNhd hδ1, cornerParameterThree_continuousOn hδ1, ?_, ?_,
      ?_, ?_⟩
  · intro w hw
    exact (hsector _ (hδr w hw.1)).mpr (RiemannBoundary.principalRoot_three_upper hw.2)
  · intro t ht hmem
    have hs := (hsector _ (hδr (t : ℂ) ht)).mp hmem
    rcases RiemannBoundary.principalRoot_three_real_boundary (Complex.ofReal_im t) with h | h
    · exact hs.1.ne' h
    · exact hs.2.ne h
  · exact fun w hw => cornerParameterThree_im_pos (hδ1 w hw)
  · exact fun w hw => cornerParameterThree_power (hδ1 w hw)

theorem SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood :
    ∃ δ : ℝ,
      0 < δ ∧
        AnalyticOnNhd ℂ cornerParameterFour (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im}) ∧
          ContinuousOn cornerParameterFour (Metric.ball 0 δ ∩ {w : ℂ | 0 ≤ w.im}) ∧
            Set.MapsTo cornerParameterFour (Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im})
                triangleInterior ∧
              (∀ t : ℝ,
                  (t : ℂ) ∈ Metric.ball 0 δ → cornerParameterFour (t : ℂ) ∉ triangleInterior) ∧
                (∀ w ∈ Metric.ball 0 δ, 0 < (cornerParameterFour w).im) ∧
                  (∀ w ∈ Metric.ball 0 δ,
                    ((cornerParameterFour w - centerTwo) /
                          (cornerParameterFour w - conj (centerTwo : ℂ))) ^
                        4 =
                      -w) := by
  obtain ⟨r, hr, hr1, hsector⟩ := exists_cornerFour_radius
  obtain ⟨δ, hδ, hδr⟩ :=
    exists_small_root_ball_mo1973_19462 RiemannBoundary.continuousAt_rotatedPrincipalRootFour_zero
      RiemannBoundary.rotatedPrincipalRootFour_zero hr
  have hδ1 : ∀ w ∈ Metric.ball (0 : ℂ) δ, ‖RiemannBoundary.rotatedPrincipalRootFour w‖ < 1 :=
    fun w hw => (hδr w hw).trans_le hr1
  refine
    ⟨δ, hδ, cornerParameterFour_analyticOnNhd hδ1, cornerParameterFour_continuousOn hδ1, ?_, ?_,
      ?_, ?_⟩
  · intro w hw
    exact (hsector _ (hδr w hw.1)).mpr (RiemannBoundary.rotatedPrincipalRootFour_upper hw.2)
  · intro t ht hmem
    have hs := (hsector _ (hδr (t : ℂ) ht)).mp hmem
    rcases RiemannBoundary.rotatedPrincipalRootFour_real_boundary (Complex.ofReal_im t) with h | h
    · exact hs.1.ne h
    · exact hs.2.ne' h
  · exact fun w hw => cornerParameterFour_im_pos (hδ1 w hw)
  · exact fun w hw => cornerParameterFour_power (hδ1 w hw)

structure RiemannMapping.TriangleBoundaryGerm (φ : ℂ → ℂ) where
  function : ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  analytic : AnalyticOnNhd ℂ function (Metric.ball 0 radius)
  agrees : Set.EqOn function (triangleMap ∘ φ) (Metric.ball 0 radius ∩ {z | 0 < z.im})
  unit : ‖function 0‖ = 1
  strictDeriv : HasStrictDerivAt function (deriv function 0) 0
  deriv_ne_zero : deriv function 0 ≠ 0
  sourceCorrespondence :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖function z‖ < 1 →
        φ z ∈ SpecialPeriods.Triangle.triangleInterior ∧ triangleMap (φ z) = function z

theorem RiemannMapping.exists_triangleBoundaryGerm {φ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 δ ∩ {z | 0 < z.im}))
    (hφc : ContinuousOn φ (Metric.ball 0 δ ∩ {z | 0 ≤ z.im}))
    (hside :
      Set.MapsTo φ (Metric.ball 0 δ ∩ {z | 0 < z.im}) SpecialPeriods.Triangle.triangleInterior)
    (hout :
      ∀ t : ℝ, (t : ℂ) ∈ Metric.ball 0 δ → φ (t : ℂ) ∉ SpecialPeriods.Triangle.triangleInterior) :
    Nonempty (TriangleBoundaryGerm φ) := by
  obtain ⟨r, hr, H, hHa, hHe, _, hHc, hHd, hHn, hHside⟩ :=
    RiemannBoundary.exists_conformal_extension_discHomeomorph_in_half_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph Metric.isOpen_ball
      triangleMap_differentiable hφ.differentiableOn hφc hside hout
      (show ((0 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) δ from Metric.mem_ball_self hδ)
  refine
    ⟨{  function := H
        radius := r
        radius_pos := hr
        analytic := hHa
        agrees := hHe
        unit := hHc 0 (Metric.mem_ball_self hr)
        strictDeriv := hHd
        deriv_ne_zero := hHn
        sourceCorrespondence := ?_ }⟩
  filter_upwards [hHside, Metric.ball_mem_nhds (0 : ℂ) hr, Metric.ball_mem_nhds (0 : ℂ) hδ] with z
    hz hrz hδz hn
  have hi := hz.mp hn
  exact ⟨hside ⟨hδz, hi⟩, (hHe ⟨hrz, hi⟩).symm⟩

theorem RiemannMapping.exists_triangleCornerThreeGerm :
    Nonempty (TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterThree) := by
  obtain ⟨δ, hδ, hφ, hφc, hside, hout, _, _⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterThree_neighborhood
  exact exists_triangleBoundaryGerm hδ hφ hφc hside hout

theorem RiemannMapping.exists_triangleCornerFourGerm :
    Nonempty (TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterFour) := by
  obtain ⟨δ, hδ, hφ, hφc, hside, hout, _, _⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterFour_neighborhood
  exact exists_triangleBoundaryGerm hδ hφ hφc hside hout

def RiemannMapping.triangleCornerThreeGerm :
    TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterThree :=
  Classical.choice exists_triangleCornerThreeGerm

def RiemannMapping.triangleCornerFourGerm :
    TriangleBoundaryGerm SpecialPeriods.Triangle.cornerParameterFour :=
  Classical.choice exists_triangleCornerFourGerm

theorem RiemannMapping.triangleCornerThree_inverse_limit :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] (triangleCornerThreeGerm.function 0))
      (𝓝 (SpecialPeriods.Triangle.centerOne : ℂ)) := by
  simpa only [SpecialPeriods.Triangle.cornerParameterThree_zero] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph
      SpecialPeriods.Triangle.continuousAt_cornerParameterThree_zero
      triangleCornerThreeGerm.strictDeriv triangleCornerThreeGerm.deriv_ne_zero
      triangleCornerThreeGerm.sourceCorrespondence

theorem RiemannMapping.triangleCornerFour_inverse_limit :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] (triangleCornerFourGerm.function 0))
      (𝓝 (SpecialPeriods.Triangle.centerTwo : ℂ)) := by
  simpa only [SpecialPeriods.Triangle.cornerParameterFour_zero] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph
      SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero
      triangleCornerFourGerm.strictDeriv triangleCornerFourGerm.deriv_ne_zero
      triangleCornerFourGerm.sourceCorrespondence

theorem RiemannMapping.triangle_centers_complex_ne :
    (SpecialPeriods.Triangle.centerOne : ℂ) ≠ (SpecialPeriods.Triangle.centerTwo : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  change SpecialPeriods.Triangle.centerOne.re = SpecialPeriods.Triangle.centerTwo.re at hr
  rw [SpecialPeriods.Triangle.centerTwo_re] at hr
  have hleft : SpecialPeriods.Triangle.centerOne.re = -1 / 2 := by
    change (SpecialPeriods.rho - 1).re = -1 / 2
    simp only [Complex.sub_re, SpecialPeriods.rho_re, Complex.one_re]
    norm_num
  rw [hleft] at hr
  linarith [SpecialPeriods.Triangle.width_pos]

theorem RiemannMapping.triangleCorner_boundary_values_ne :
    triangleCornerThreeGerm.function 0 ≠ triangleCornerFourGerm.function 0 := by
  intro h
  have hp :=
    RiemannBoundary.boundary_points_eq_of_equal_disc_values triangleBiholomorph.toHomeomorph
      triangleMap_biholomorph SpecialPeriods.Triangle.continuousAt_cornerParameterThree_zero
      SpecialPeriods.Triangle.continuousAt_cornerParameterFour_zero
      triangleCornerThreeGerm.strictDeriv triangleCornerThreeGerm.deriv_ne_zero
      triangleCornerFourGerm.strictDeriv triangleCornerFourGerm.deriv_ne_zero
      triangleCornerThreeGerm.sourceCorrespondence triangleCornerFourGerm.sourceCorrespondence
      triangleCornerThreeGerm.unit h
  exact
    triangle_centers_complex_ne
      (by
        simpa only [SpecialPeriods.Triangle.cornerParameterThree_zero,
          SpecialPeriods.Triangle.cornerParameterFour_zero] using hp)

def RiemannMapping.triangleCuspScale : ℝ :=
  SpecialPeriods.Triangle.width / (2 * Real.pi)

theorem RiemannMapping.triangleCuspScale_pos : 0 < triangleCuspScale := by
  exact div_pos SpecialPeriods.Triangle.width_pos (mul_pos (by norm_num) Real.pi_pos)

theorem RiemannMapping.triangleCuspScale_endpoint :
    SpecialPeriods.Triangle.stripLeft + triangleCuspScale * Real.pi = -1 / 2 := by
  unfold SpecialPeriods.Triangle.stripLeft triangleCuspScale
  field_simp [Real.pi_ne_zero]
  ring

def RiemannMapping.triangleCuspLog : ℂ → ℂ :=
  RiemannBoundary.logHalfStrip SpecialPeriods.Triangle.stripLeft triangleCuspScale

theorem RiemannMapping.triangle_high_halfStrip_mem (z : ℂ)
    (hl : SpecialPeriods.Triangle.stripLeft < z.re)
    (hr : z.re < SpecialPeriods.Triangle.stripLeft + triangleCuspScale * Real.pi)
    (hi : 1 < z.im) : z ∈ SpecialPeriods.Triangle.triangleInterior := by
  rw [SpecialPeriods.Triangle.mem_triangleInterior_iff_epigraph]
  exact
    ⟨hl, by simpa only [triangleCuspScale_endpoint] using hr,
      (SpecialPeriods.Triangle.boundaryHeight_le_one z.re).trans_lt hi⟩

theorem RiemannMapping.triangle_high_halfStrip_edge_notMem (z : ℂ)
    (he :
      z.re = SpecialPeriods.Triangle.stripLeft ∨
        z.re = SpecialPeriods.Triangle.stripLeft + triangleCuspScale * Real.pi) :
    z ∉ SpecialPeriods.Triangle.triangleInterior := by
  intro hz
  rcases he with hl | hr
  · exact (lt_irrefl SpecialPeriods.Triangle.stripLeft) (hl ▸ hz.1)
  · rw [triangleCuspScale_endpoint] at hr
    exact (lt_irrefl (-1 / 2 : ℝ)) (hr ▸ hz.2.1)

theorem RiemannMapping.exists_triangleMap_extension_ideal_vertex :
    ∃ r > 0,
      ∃ H : ℂ → ℂ,
        AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
          Set.EqOn H (triangleMap ∘ triangleCuspLog)
              (Metric.ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn H (fun z => (conj (triangleMap (triangleCuspLog (conj z))))⁻¹)
                (Metric.ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
              (∀ t : ℝ, (t : ℂ) ∈ Metric.ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
                HasStrictDerivAt H (deriv H 0) 0 ∧
                  deriv H 0 ≠ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  exact
    RiemannBoundary.exists_conformal_extension_discHomeomorph_at_ideal_vertex
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph triangleMap_differentiable
      SpecialPeriods.Triangle.stripLeft 1 triangleCuspScale_pos triangle_high_halfStrip_mem
      (fun z _ he => triangle_high_halfStrip_edge_notMem z he)

theorem RiemannMapping.exists_triangleIdealGerm :
    Nonempty (TriangleBoundaryGerm triangleCuspLog) := by
  obtain ⟨r, hr, H, hHa, hHe, _, hHc, hHd, hHn, hHside⟩ :=
    exists_triangleMap_extension_ideal_vertex
  obtain ⟨R, hR, hheight⟩ :=
    RiemannBoundary.exists_logHalfStrip_height_radius SpecialPeriods.Triangle.stripLeft 1
      triangleCuspScale_pos
  refine
    ⟨{  function := H
        radius := r
        radius_pos := hr
        analytic := hHa
        agrees := hHe
        unit := hHc 0 (Metric.mem_ball_self hr)
        strictDeriv := hHd
        deriv_ne_zero := hHn
        sourceCorrespondence := ?_ }⟩
  filter_upwards [hHside, Metric.ball_mem_nhds (0 : ℂ) hr, Metric.ball_mem_nhds (0 : ℂ) hR] with q
    hq hrq hRq hn
  have hi : 0 < q.im := hq.mp hn
  have hq0 : q ≠ 0 := by
    intro heq
    rw [heq, Complex.zero_im] at hi
    exact (lt_irrefl 0) hi
  have hRe :=
    RiemannBoundary.logHalfStrip_re_mem_Ioo SpecialPeriods.Triangle.stripLeft
      triangleCuspScale_pos hi
  have hD : triangleCuspLog q ∈ SpecialPeriods.Triangle.triangleInterior :=
    triangle_high_halfStrip_mem _ hRe.1 hRe.2 (hheight q hRq hq0)
  exact ⟨hD, (hHe ⟨hrq, hi⟩).symm⟩

def RiemannMapping.triangleIdealGerm : TriangleBoundaryGerm triangleCuspLog :=
  Classical.choice exists_triangleIdealGerm

def RiemannMapping.triangleDiscOnOnePointDomain :
    RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior ≃ₜ
      Metric.ball (0 : ℂ) 1 :=
  RiemannBoundary.onePointDomainDiscHomeomorph triangleBiholomorph.toHomeomorph

def RiemannMapping.triangleOnePointRepresentative (z : OnePoint ℂ) : ℂ :=
  z.elim 0 triangleMap

@[simp]
theorem RiemannMapping.triangleOnePointRepresentative_coe (z : ℂ) :
    triangleOnePointRepresentative (z : OnePoint ℂ) = triangleMap z :=
  rfl

theorem RiemannMapping.triangleOnePointRepresentative_homeomorph
    (z : RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior) :
    triangleOnePointRepresentative z = (triangleDiscOnOnePointDomain z : ℂ) :=
  RiemannBoundary.onePointDomainDiscHomeomorph_representative triangleBiholomorph.toHomeomorph
    triangleMap_biholomorph 0 z

def RiemannMapping.triangleIdealParameter : ℂ → OnePoint ℂ :=
  RiemannBoundary.onePointLogHalfStrip SpecialPeriods.Triangle.stripLeft triangleCuspScale

@[simp]
theorem RiemannMapping.triangleIdealParameter_zero :
    triangleIdealParameter 0 = (OnePoint.infty) :=
  RiemannBoundary.onePointLogHalfStrip_zero _ _

theorem RiemannMapping.continuousAt_triangleIdealParameter_zero :
    ContinuousAt triangleIdealParameter 0 :=
  RiemannBoundary.continuousAt_onePointLogHalfStrip_zero SpecialPeriods.Triangle.stripLeft
    triangleCuspScale_pos

theorem RiemannMapping.triangleIdeal_onePoint_sourceCorrespondence :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖triangleIdealGerm.function z‖ < 1 →
        triangleIdealParameter z ∈
            RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior ∧
          triangleOnePointRepresentative (triangleIdealParameter z) =
            triangleIdealGerm.function z := by
  filter_upwards [triangleIdealGerm.sourceCorrespondence] with z hz hn
  have hzne : z ≠ 0 := by
    intro heq
    rw [heq, triangleIdealGerm.unit] at hn
    exact (lt_irrefl 1) hn
  have hparameter : triangleIdealParameter z = (triangleCuspLog z : OnePoint ℂ) :=
    RiemannBoundary.onePointLogHalfStrip_of_ne_zero SpecialPeriods.Triangle.stripLeft
      triangleCuspScale hzne
  rw [hparameter]
  obtain ⟨hmem, hvalue⟩ := hz hn
  exact ⟨RiemannBoundary.coe_mem_onePointDomain.mpr hmem, hvalue⟩

theorem RiemannMapping.triangleIdeal_inverse_limit :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleDiscOnOnePointDomain)
      (𝓝[Metric.ball (0 : ℂ) 1] (triangleIdealGerm.function 0))
      (𝓝 ((OnePoint.infty) : OnePoint ℂ)) := by
  simpa only [triangleIdealParameter_zero] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart triangleDiscOnOnePointDomain
      triangleOnePointRepresentative_homeomorph continuousAt_triangleIdealParameter_zero
      triangleIdealGerm.strictDeriv triangleIdealGerm.deriv_ne_zero
      triangleIdeal_onePoint_sourceCorrespondence

def SpecialPeriods.Triangle.triangleClosedInteriorToOnePoint :
    triangleClosedInterior ≃ₜ RiemannBoundary.onePointDomain triangleInterior
    where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, subset_closure x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem SpecialPeriods.Triangle.triangleClosedInterior_comap_onePoint_filter
    (x : TriangleClosedDomain) :
    Filter.comap triangleClosedInteriorToOnePoint
        (Filter.comap (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ)
          (𝓝 x.val)) =
      Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x) := by
  rw [nhds_subtype_eq_comap, Filter.comap_comap, Filter.comap_comap]
  rfl

theorem SpecialPeriods.Triangle.triangleClosedInterior_map_onePoint_filter
    (x : TriangleClosedDomain) :
    Filter.map triangleClosedInteriorToOnePoint
        (Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) =
      Filter.comap (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ)
        (𝓝 x.val) := by
  rw [← triangleClosedInterior_comap_onePoint_filter x,
    Filter.map_comap_of_surjective triangleClosedInteriorToOnePoint.surjective]

theorem SpecialPeriods.Triangle.triangleClosedInterior_forward_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Filter.Tendsto
        (fun z : triangleClosedInterior => (triangleClosedInteriorDiscHomeomorph z : ℂ))
        (Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) l ↔
      Filter.Tendsto
        (fun z : RiemannBoundary.onePointDomain triangleInterior =>
          (RiemannMapping.triangleDiscOnOnePointDomain z : ℂ))
        (Filter.comap (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ)
          (𝓝 x.val))
        l := by
  rw [← triangleClosedInterior_map_onePoint_filter x, Filter.tendsto_map'_iff]
  rfl

theorem SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Filter.Tendsto
        (fun z : triangleClosedInterior => (triangleClosedInteriorDiscHomeomorph z : ℂ))
        (Filter.comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) l ↔
      Filter.Tendsto RiemannMapping.triangleOnePointRepresentative
        (𝓝[RiemannBoundary.onePointDomain triangleInterior] x.val) l := by
  rw [triangleClosedInterior_forward_tendsto_iff]
  have he :
    (fun z : RiemannBoundary.onePointDomain triangleInterior =>
        (RiemannMapping.triangleDiscOnOnePointDomain z : ℂ)) =
      RiemannMapping.triangleOnePointRepresentative ∘
        (Subtype.val : RiemannBoundary.onePointDomain triangleInterior → OnePoint ℂ) := by
    funext z
    exact (RiemannMapping.triangleOnePointRepresentative_homeomorph z).symm
  rw [he, ← Filter.tendsto_map'_iff, Filter.map_comap_setCoe_val]
  rfl

theorem SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph_inverse_coe (z : ℂ) :
    ((RiemannBoundary.discHomeomorphInverse triangleClosedInteriorDiscHomeomorph z :
          TriangleClosedDomain) :
        OnePoint ℂ) =
      RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain z := by
  classical
  unfold RiemannBoundary.discHomeomorphInverse
  split_ifs <;> rfl

theorem SpecialPeriods.Triangle.triangleClosedInterior_inverse_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleClosedInteriorDiscHomeomorph) l
        (𝓝 x) ↔
      Filter.Tendsto
        (RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain) l
        (𝓝 x.val) := by
  rw [tendsto_subtype_rng]
  simp only [triangleClosedInteriorDiscHomeomorph_inverse_coe]

theorem SpecialPeriods.Triangle.triangleOnePointRepresentative_finite_tendsto_iff {a : ℂ}
    {l : Filter ℂ} :
    Filter.Tendsto RiemannMapping.triangleOnePointRepresentative
        (𝓝[RiemannBoundary.onePointDomain triangleInterior] (a : OnePoint ℂ)) l ↔
      Filter.Tendsto RiemannMapping.triangleMap (𝓝[triangleInterior] a) l := by
  change
    Filter.Tendsto RiemannMapping.triangleOnePointRepresentative
        (𝓝[((↑) : ℂ → OnePoint ℂ) '' triangleInterior] (a : OnePoint ℂ)) l ↔
      _
  rw [OnePoint.nhdsWithin_coe_image, Filter.tendsto_map'_iff]
  rfl

theorem SpecialPeriods.Triangle.triangleDiscOnOnePointDomain_inverse_coe (z : ℂ) :
    RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain z =
      ((RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleBiholomorph.toHomeomorph z :
          ℂ) :
        OnePoint ℂ) := by
  classical
  unfold RiemannBoundary.discHomeomorphInverse
  split_ifs <;> rfl

theorem SpecialPeriods.Triangle.triangleDiscOnOnePointDomain_finite_inverse_tendsto_iff {a : ℂ}
    {l : Filter ℂ} :
    Filter.Tendsto
        (RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleDiscOnOnePointDomain) l
        (𝓝 (a : OnePoint ℂ)) ↔
      Filter.Tendsto
        (RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleBiholomorph.toHomeomorph) l
        (𝓝 a) := by
  have h :=
    (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.tendsto_nhds_iff (f :=
      RiemannBoundary.discHomeomorphInverse RiemannMapping.triangleBiholomorph.toHomeomorph) (l :=
      l) (y := a)
  simpa only [Function.comp_def, ← triangleDiscOnOnePointDomain_inverse_coe] using h.symm

theorem RiemannMapping.exists_triangleSideBoundaryGerm (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0) {r : ℝ}
    (hr : 0 < r)
    (hside : ∀ z ∈ Metric.ball a r, z ∈ SpecialPeriods.Triangle.triangleInterior ↔ 0 < (e z).im) :
    Nonempty (TriangleBoundaryGerm (triangleSideParameter e a)) := by
  obtain ⟨δ, hδ, hδball⟩ := exists_boundary_chart_target_ball e ha hr
  have hadd : ∀ w ∈ Metric.ball (0 : ℂ) δ, w + e a ∈ Metric.ball (e a) δ := by
    intro w hw
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
  have hφ : AnalyticOnNhd ℂ (triangleSideParameter e a) (Metric.ball 0 δ) := by
    intro w hw
    exact
      (he (w + e a) (hδball _ (hadd w hw)).1).comp (f := fun z : ℂ => z + e a)
        (analyticAt_id.add analyticAt_const)
  apply
    exists_triangleBoundaryGerm hδ (hφ.mono Set.inter_subset_left)
      (hφ.continuousOn.mono Set.inter_subset_left)
  · intro w hw
    apply (hside _ (hδball _ (hadd w hw.1)).2).mpr
    rw [e.right_inv (hδball _ (hadd w hw.1)).1, Complex.add_im, hreal, add_zero]
    exact hw.2
  · intro t ht hin
    have hi := (hside _ (hδball _ (hadd t ht)).2).mp hin
    change 0 < (e (e.symm ((t : ℂ) + e a))).im at hi
    rw [e.right_inv (hδball _ (hadd t ht)).1, Complex.add_im, Complex.ofReal_im, hreal,
      add_zero] at hi
    exact lt_irrefl _ hi

theorem RiemannMapping.triangleSideBoundaryGerm_forward_limit (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (hreal : (e a).im = 0) {r : ℝ} (hr : 0 < r)
    (hside : ∀ z ∈ Metric.ball a r, z ∈ SpecialPeriods.Triangle.triangleInterior ↔ 0 < (e z).im)
    (g : TriangleBoundaryGerm (triangleSideParameter e a)) :
    Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a)
      (𝓝 (g.function 0)) := by
  have hec : ContinuousAt e a := e.continuousOn.continuousAt (e.open_source.mem_nhds ha)
  have ht : Filter.Tendsto (fun z => e z - e a) (𝓝 a) (𝓝 (0 : ℂ)) := by
    have hsub : Filter.Tendsto (fun z => e z - e a) (𝓝 a) (𝓝 (e a - e a)) :=
      hec.tendsto.sub_const (e a)
    simpa only [sub_self] using hsub
  have hlim :
    Filter.Tendsto (fun z => g.function (e z - e a))
      (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 (g.function 0)) :=
    ((g.analytic 0 (Metric.mem_ball_self g.radius_pos)).continuousAt.tendsto.comp ht).mono_left
      nhdsWithin_le_nhds
  have heq :
    triangleMap =ᶠ[𝓝[SpecialPeriods.Triangle.triangleInterior] a]
      (fun z => g.function (e z - e a)) := by
    have hs : ∀ᶠ z in 𝓝[SpecialPeriods.Triangle.triangleInterior] a, z ∈ e.source :=
      mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds ha)
    have hb : ∀ᶠ z in 𝓝[SpecialPeriods.Triangle.triangleInterior] a, z ∈ Metric.ball a r :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds a hr)
    have hp :
      ∀ᶠ z in 𝓝[SpecialPeriods.Triangle.triangleInterior] a,
        e z - e a ∈ Metric.ball (0 : ℂ) g.radius :=
      (ht.eventually (Metric.ball_mem_nhds (0 : ℂ) g.radius_pos)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs, hb, hp, self_mem_nhdsWithin] with z hz hbz hpz hzT
    have hi : 0 < (e z - e a).im := by
      rw [Complex.sub_im, hreal, sub_zero]
      exact (hside z hbz).mp hzT
    have hg := g.agrees ⟨hpz, hi⟩
    simpa only [Function.comp_apply, triangleSideParameter, sub_add_cancel, e.left_inv hz] using
      hg.symm
  exact hlim.congr' heq.symm

theorem RiemannMapping.triangleSideBoundaryGerm_inverse_limit (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (g : TriangleBoundaryGerm (triangleSideParameter e a)) :
    Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] (g.function 0)) (𝓝 a) := by
  simpa only [triangleSideParameter_zero e ha] using
    RiemannBoundary.tendsto_discHomeomorphInverse_of_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph
      (continuousAt_triangleSideParameter_zero e ha) g.strictDeriv g.deriv_ne_zero
      g.sourceCorrespondence

theorem RiemannMapping.exists_triangleMap_side_limits (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0) {r : ℝ}
    (hr : 0 < r)
    (hside : ∀ z ∈ Metric.ball a r, z ∈ SpecialPeriods.Triangle.triangleInterior ↔ 0 < (e z).im) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨g⟩ := exists_triangleSideBoundaryGerm e ha he hreal hr hside
  exact
    ⟨g.function 0, g.unit, triangleSideBoundaryGerm_forward_limit e ha hreal hr hside g,
      triangleSideBoundaryGerm_inverse_limit e ha g⟩

theorem RiemannMapping.exists_triangleMap_circle_side_limits {a : ℂ}
    (haL : SpecialPeriods.Triangle.stripLeft < a.re) (haR : a.re < -1 / 2) (hai : 0 < a.im)
    (haC : ‖a + 1‖ = 1) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := SpecialPeriods.Triangle.exists_circle_side_neighborhood haL haR hai
  have ha : a ∈ SpecialPeriods.Triangle.circleBoundaryChart.source :=
    (hside a (Metric.mem_ball_self hr)).1
  exact
    exists_triangleMap_side_limits SpecialPeriods.Triangle.circleBoundaryChart ha
      SpecialPeriods.Triangle.circleUnstraighten_analyticOnNhd
      ((SpecialPeriods.Triangle.circleStraighten_im_eq_zero_iff ha).mpr haC) hr
      (fun z hz => (hside z hz).2)

theorem RiemannMapping.exists_triangleMap_left_side_limits {a : ℂ}
    (ha : a.re = SpecialPeriods.Triangle.stripLeft) (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := SpecialPeriods.Triangle.exists_left_side_neighborhood ha hai haC
  apply
    exists_triangleMap_side_limits
      SpecialPeriods.Triangle.leftBoundaryChart.toOpenPartialHomeomorph (Set.mem_univ a)
      (fun z _ => SpecialPeriods.Triangle.leftBoundaryChart_symm_analyticAt z)
  · change (SpecialPeriods.Triangle.leftBoundaryChart a).im = 0
    simp [ha]
  · exact hr
  · exact hside

theorem RiemannMapping.exists_triangleMap_right_side_limits {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ w : ℂ,
      ‖w‖ = 1 ∧
        Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w) ∧
          Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
            (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := SpecialPeriods.Triangle.exists_right_side_neighborhood ha hai haC
  apply
    exists_triangleMap_side_limits
      SpecialPeriods.Triangle.rightBoundaryChart.toOpenPartialHomeomorph (Set.mem_univ a)
      (fun z _ => SpecialPeriods.Triangle.rightBoundaryChart_symm_analyticAt z)
  · change (SpecialPeriods.Triangle.rightBoundaryChart a).im = 0
    norm_num [SpecialPeriods.Triangle.rightBoundaryChart_im, ha]
  · exact hr
  · exact hside

def SpecialPeriods.Triangle.cornerCoordinate (a : UpperHalfPlane) (z : ℂ) : ℂ :=
  (z - a) / (z - conj (a : ℂ))

@[simp]
theorem SpecialPeriods.Triangle.cornerCoordinate_self (a : UpperHalfPlane) :
    cornerCoordinate a a = 0 := by simp [cornerCoordinate]

theorem SpecialPeriods.Triangle.cornerCoordinate_analyticAt (a : UpperHalfPlane) {z : ℂ}
    (hz : z - conj (a : ℂ) ≠ 0) : AnalyticAt ℂ (cornerCoordinate a) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hz

theorem SpecialPeriods.Triangle.cornerCoordinate_analyticAt_self (a : UpperHalfPlane) :
    AnalyticAt ℂ (cornerCoordinate a) (a : ℂ) :=
  cornerCoordinate_analyticAt a (sub_conj_ne_zero a a)

theorem SpecialPeriods.Triangle.cayley_cornerCoordinate (a : UpperHalfPlane) {z : ℂ}
    (hz : 0 < z.im) : SpecialPeriods.cayley a (cornerCoordinate a z) = z := by
  have he := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (fromDisc_toDisc a ⟨z, hz⟩)
  simpa only [fromDisc_val, toDisc_val, cornerCoordinate, cayleyCoordinate] using he

def SpecialPeriods.Triangle.cornerPowerThree (z : ℂ) : ℂ :=
  cornerCoordinate centerOne z ^ 3

def SpecialPeriods.Triangle.cornerPowerFour (z : ℂ) : ℂ :=
  -(cornerCoordinate centerTwo z ^ 4)

@[simp]
theorem SpecialPeriods.Triangle.cornerPowerThree_center : cornerPowerThree centerOne = 0 := by
  simp only [cornerPowerThree, cornerCoordinate_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true]

@[simp]
theorem SpecialPeriods.Triangle.cornerPowerFour_center : cornerPowerFour centerTwo = 0 := by
  simp only [cornerPowerFour, cornerCoordinate_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, neg_zero]

theorem SpecialPeriods.Triangle.cornerPowerThree_analyticAt_center :
    AnalyticAt ℂ cornerPowerThree (centerOne : ℂ) :=
  (cornerCoordinate_analyticAt_self centerOne).pow 3

theorem SpecialPeriods.Triangle.cornerPowerFour_analyticAt_center :
    AnalyticAt ℂ cornerPowerFour (centerTwo : ℂ) :=
  ((cornerCoordinate_analyticAt_self centerTwo).pow 4).neg

theorem SpecialPeriods.Triangle.exists_cornerCoordinate_neighborhood (a : UpperHalfPlane) {r : ℝ}
    (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball (a : ℂ) ε, 0 < z.im ∧ ‖cornerCoordinate a z‖ < r := by
  have him : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), 0 < z.im :=
    continuousAt_const.eventually_lt Complex.continuous_im.continuousAt a.im_pos
  have hnorm : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), ‖cornerCoordinate a z‖ < r :=
    (cornerCoordinate_analyticAt_self a).continuousAt.norm.eventually_lt continuousAt_const
      (by simpa only [cornerCoordinate_self, norm_zero] using hr)
  exact Metric.mem_nhds_iff.mp (him.and hnorm)

theorem SpecialPeriods.Triangle.exists_cornerThree_neighborhood :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerOne : ℂ) ε,
          0 < z.im ∧ (z ∈ triangleInterior ↔ cornerCoordinate centerOne z ∈ cornerSectorThree) := by
  obtain ⟨r, hr, _, hsector⟩ := exists_cornerThree_radius
  obtain ⟨ε, hε, hball⟩ := exists_cornerCoordinate_neighborhood centerOne hr
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have h := hball z hz
  refine ⟨h.1, ?_⟩
  have he := hsector _ h.2
  rwa [cayley_cornerCoordinate centerOne h.1] at he

theorem SpecialPeriods.Triangle.exists_cornerFour_neighborhood :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerTwo : ℂ) ε,
          0 < z.im ∧ (z ∈ triangleInterior ↔ cornerCoordinate centerTwo z ∈ cornerSectorFour) := by
  obtain ⟨r, hr, _, hsector⟩ := exists_cornerFour_radius
  obtain ⟨ε, hε, hball⟩ := exists_cornerCoordinate_neighborhood centerTwo hr
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have h := hball z hz
  refine ⟨h.1, ?_⟩
  have he := hsector _ h.2
  rwa [cayley_cornerCoordinate centerTwo h.1] at he

theorem SpecialPeriods.Triangle.cornerSectorThree_re_pos {z : ℂ} (hz : z ∈ cornerSectorThree) :
    0 < z.re := by
  change 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re at hz
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [mul_pos hsqrt hz.1]

theorem SpecialPeriods.Triangle.cornerSectorThree_arg {z : ℂ} (hz : z ∈ cornerSectorThree) :
    z.arg ∈ Set.Ioo 0 (Real.pi / 3) := by
  have hr := cornerSectorThree_re_pos hz
  change 0 < z.im ∧ Real.sqrt 3 * z.im < 3 * z.re at hz
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hm : Real.sqrt 3 * z.im < Real.sqrt 3 * (Real.sqrt 3 * z.re) := by
    rw [← mul_assoc, hsq]
    exact hz.2
  have him : z.im < Real.sqrt 3 * z.re := (mul_lt_mul_iff_right₀ hsqrt).mp hm
  have hargHalf : z.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hthird : Real.pi / 3 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan z.arg < Real.tan (Real.pi / 3) := by
    rw [Complex.tan_arg, Real.tan_pi_div_three]
    exact (div_lt_iff₀ hr).mpr him
  have harg0 : 0 < z.arg := by
    have hn : z.arg ≠ 0 := fun h => (ne_of_gt hz.1) (Complex.arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.1.le) hn.symm
  exact ⟨harg0, (Real.strictMonoOn_tan.lt_iff_lt hargHalf hthird).mp htan⟩

theorem SpecialPeriods.Triangle.cornerSectorThree_root_pow {z : ℂ} (hz : z ∈ cornerSectorThree) :
    RiemannBoundary.principalRoot 3 (z ^ 3) = z := by
  apply RiemannBoundary.principalRoot_pow_of_sector (by norm_num : 0 < 3)
  exact ⟨(cornerSectorThree_arg hz).1.le, (cornerSectorThree_arg hz).2.le⟩

private theorem SpecialPeriods.Triangle.im_pos_of_principalRoot_arg_mo1973_19574 {n : ℕ}
    (hn : 0 < n) {z : ℂ}
    (ha : (RiemannBoundary.principalRoot n z).arg ∈ Set.Ioo 0 (Real.pi / (n : ℝ))) : 0 < z.im := by
  rw [RiemannBoundary.arg_principalRoot hn] at ha
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have harg0 : 0 < z.arg := (div_pos_iff_of_pos_right hnR).mp ha.1
  have hargPi : z.arg < Real.pi := (div_lt_div_iff_of_pos_right hnR).mp ha.2
  have hz0 : z ≠ 0 := by
    intro hz
    simp only [hz, Complex.arg_zero, lt_self_iff_false] at harg0
  rw [← Complex.norm_mul_sin_arg]
  exact mul_pos (norm_pos_iff.mpr hz0) (Real.sin_pos_of_pos_of_lt_pi harg0 hargPi)

theorem SpecialPeriods.Triangle.cornerSectorThree_pow_im_pos {z : ℂ}
    (hz : z ∈ cornerSectorThree) : 0 < (z ^ 3).im := by
  apply im_pos_of_principalRoot_arg_mo1973_19574 (by norm_num : 0 < 3)
  rw [cornerSectorThree_root_pow hz]
  exact cornerSectorThree_arg hz

theorem SpecialPeriods.Triangle.cornerSectorFour_re_pos {z : ℂ} (hz : z ∈ cornerSectorFour) :
    0 < z.re := by
  change z.im < 0 ∧ 0 < z.re + z.im at hz
  linarith [hz.1, hz.2]

theorem SpecialPeriods.Triangle.cornerSectorFour_arg {z : ℂ} (hz : z ∈ cornerSectorFour) :
    z.arg ∈ Set.Ioo (-Real.pi / 4) 0 := by
  have hr := cornerSectorFour_re_pos hz
  change z.im < 0 ∧ 0 < z.re + z.im at hz
  have hargHalf : z.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hfourth : -Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan (-Real.pi / 4) < Real.tan z.arg := by
    rw [neg_div, Real.tan_neg, Real.tan_pi_div_four, Complex.tan_arg]
    apply (lt_div_iff₀ hr).mpr
    linarith [hz.2]
  exact ⟨(Real.strictMonoOn_tan.lt_iff_lt hfourth hargHalf).mp htan, Complex.arg_neg_iff.mpr hz.1⟩

theorem SpecialPeriods.Triangle.quarticRootRotation_arg :
    RiemannBoundary.quarticRootRotation.arg = -Real.pi / 4 := by
  rw [RiemannBoundary.quarticRootRotation, Complex.arg_exp_mul_I]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos]

theorem SpecialPeriods.Triangle.quarticRootRotation_inv_arg :
    (RiemannBoundary.quarticRootRotation⁻¹).arg = Real.pi / 4 := by
  rw [Complex.arg_inv, quarticRootRotation_arg]
  have hn : -Real.pi / 4 ≠ Real.pi := by linarith [Real.pi_pos]
  rw [if_neg hn]
  ring

theorem SpecialPeriods.Triangle.cornerSectorFour_unrotate_arg {z : ℂ}
    (hz : z ∈ cornerSectorFour) :
    (RiemannBoundary.quarticRootRotation⁻¹ * z).arg ∈ Set.Ioo 0 (Real.pi / 4) := by
  have ha := cornerSectorFour_arg hz
  have hz0 : z ≠ 0 := by
    intro h
    have hi := hz.1
    simp only [h, Complex.zero_im, lt_self_iff_false] at hi
  have hsum : (RiemannBoundary.quarticRootRotation⁻¹).arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [quarticRootRotation_inv_arg]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [Complex.arg_mul (inv_ne_zero RiemannBoundary.quarticRootRotation_ne_zero) hz0 hsum,
    quarticRootRotation_inv_arg]
  constructor <;> linarith [ha.1, ha.2]

theorem SpecialPeriods.Triangle.quarticRootRotation_inv_mul_pow_four (z : ℂ) :
    (RiemannBoundary.quarticRootRotation⁻¹ * z) ^ 4 = -(z ^ 4) := by
  rw [mul_pow, inv_pow, RiemannBoundary.quarticRootRotation_pow_four]
  norm_num

theorem SpecialPeriods.Triangle.cornerSectorFour_unrotate_root_pow {z : ℂ}
    (hz : z ∈ cornerSectorFour) :
    RiemannBoundary.principalRoot 4 (-(z ^ 4)) = RiemannBoundary.quarticRootRotation⁻¹ * z := by
  rw [← quarticRootRotation_inv_mul_pow_four]
  apply RiemannBoundary.principalRoot_pow_of_sector (by norm_num : 0 < 4)
  exact ⟨(cornerSectorFour_unrotate_arg hz).1.le, (cornerSectorFour_unrotate_arg hz).2.le⟩

theorem SpecialPeriods.Triangle.cornerSectorFour_root_pow {z : ℂ} (hz : z ∈ cornerSectorFour) :
    RiemannBoundary.rotatedPrincipalRootFour (-(z ^ 4)) = z := by
  rw [RiemannBoundary.rotatedPrincipalRootFour, cornerSectorFour_unrotate_root_pow hz, ←
    mul_assoc, mul_inv_cancel₀ RiemannBoundary.quarticRootRotation_ne_zero, one_mul]

theorem SpecialPeriods.Triangle.cornerSectorFour_pow_im_pos {z : ℂ} (hz : z ∈ cornerSectorFour) :
    0 < (-(z ^ 4)).im := by
  apply im_pos_of_principalRoot_arg_mo1973_19574 (by norm_num : 0 < 4)
  rw [cornerSectorFour_unrotate_root_pow hz]
  exact cornerSectorFour_unrotate_arg hz

theorem SpecialPeriods.Triangle.cornerParameterThree_cornerPower {z : ℂ} (hzi : 0 < z.im)
    (hz : cornerCoordinate centerOne z ∈ cornerSectorThree) :
    cornerParameterThree (cornerPowerThree z) = z := by
  change
    SpecialPeriods.cayley centerOne
        (RiemannBoundary.principalRoot 3 (cornerCoordinate centerOne z ^ 3)) =
      z
  rw [cornerSectorThree_root_pow hz, cayley_cornerCoordinate centerOne hzi]

theorem SpecialPeriods.Triangle.cornerParameterFour_cornerPower {z : ℂ} (hzi : 0 < z.im)
    (hz : cornerCoordinate centerTwo z ∈ cornerSectorFour) :
    cornerParameterFour (cornerPowerFour z) = z := by
  change
    SpecialPeriods.cayley centerTwo
        (RiemannBoundary.rotatedPrincipalRootFour (-(cornerCoordinate centerTwo z ^ 4))) =
      z
  rw [cornerSectorFour_root_pow hz, cayley_cornerCoordinate centerTwo hzi]

theorem SpecialPeriods.Triangle.exists_cornerParameterThree_coverage {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerOne : ℂ) ε,
          z ∈ triangleInterior →
            cornerPowerThree z ∈ Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im} ∧
              cornerParameterThree (cornerPowerThree z) = z := by
  obtain ⟨r, hr, hgeom⟩ := exists_cornerThree_neighborhood
  have hp : ∀ᶠ z : ℂ in 𝓝 (centerOne : ℂ), ‖cornerPowerThree z‖ < δ :=
    cornerPowerThree_analyticAt_center.continuousAt.norm.eventually_lt continuousAt_const
      (by simpa only [cornerPowerThree_center, norm_zero] using hδ)
  have hb : ∀ᶠ z : ℂ in 𝓝 (centerOne : ℂ), z ∈ Metric.ball (centerOne : ℂ) r :=
    Metric.ball_mem_nhds (centerOne : ℂ) hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.and hp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hT
  have hnear := hball hz
  have h := hgeom z hnear.1
  have hs := h.2.mp hT
  refine
    ⟨⟨by simpa only [Metric.mem_ball, dist_zero_right] using hnear.2, ?_⟩,
      cornerParameterThree_cornerPower h.1 hs⟩
  exact cornerSectorThree_pow_im_pos hs

theorem SpecialPeriods.Triangle.exists_cornerParameterFour_coverage {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z ∈ Metric.ball (centerTwo : ℂ) ε,
          z ∈ triangleInterior →
            cornerPowerFour z ∈ Metric.ball 0 δ ∩ {w : ℂ | 0 < w.im} ∧
              cornerParameterFour (cornerPowerFour z) = z := by
  obtain ⟨r, hr, hgeom⟩ := exists_cornerFour_neighborhood
  have hp : ∀ᶠ z : ℂ in 𝓝 (centerTwo : ℂ), ‖cornerPowerFour z‖ < δ :=
    cornerPowerFour_analyticAt_center.continuousAt.norm.eventually_lt continuousAt_const
      (by simpa only [cornerPowerFour_center, norm_zero] using hδ)
  have hb : ∀ᶠ z : ℂ in 𝓝 (centerTwo : ℂ), z ∈ Metric.ball (centerTwo : ℂ) r :=
    Metric.ball_mem_nhds (centerTwo : ℂ) hr
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.and hp)
  refine ⟨ε, hε, ?_⟩
  intro z hz hT
  have hnear := hball hz
  have h := hgeom z hnear.1
  have hs := h.2.mp hT
  refine
    ⟨⟨by simpa only [Metric.mem_ball, dist_zero_right] using hnear.2, ?_⟩,
      cornerParameterFour_cornerPower h.1 hs⟩
  exact cornerSectorFour_pow_im_pos hs

def RiemannMapping.triangleCornerThreePatch : ℂ → ℂ :=
  triangleCornerThreeGerm.function ∘ SpecialPeriods.Triangle.cornerPowerThree

def RiemannMapping.triangleCornerFourPatch : ℂ → ℂ :=
  triangleCornerFourGerm.function ∘ SpecialPeriods.Triangle.cornerPowerFour

@[simp]
theorem RiemannMapping.triangleCornerThreePatch_center :
    triangleCornerThreePatch SpecialPeriods.Triangle.centerOne =
      triangleCornerThreeGerm.function 0 := by
  simp only [triangleCornerThreePatch, Function.comp_apply,
    SpecialPeriods.Triangle.cornerPowerThree_center]

@[simp]
theorem RiemannMapping.triangleCornerFourPatch_center :
    triangleCornerFourPatch SpecialPeriods.Triangle.centerTwo =
      triangleCornerFourGerm.function 0 := by
  simp only [triangleCornerFourPatch, Function.comp_apply,
    SpecialPeriods.Triangle.cornerPowerFour_center]

theorem RiemannMapping.triangleCornerThreePatch_analyticAt :
    AnalyticAt ℂ triangleCornerThreePatch (SpecialPeriods.Triangle.centerOne : ℂ) := by
  have hH :
    AnalyticAt ℂ triangleCornerThreeGerm.function
      (SpecialPeriods.Triangle.cornerPowerThree SpecialPeriods.Triangle.centerOne) := by
    rw [SpecialPeriods.Triangle.cornerPowerThree_center]
    exact
      triangleCornerThreeGerm.analytic 0 (Metric.mem_ball_self triangleCornerThreeGerm.radius_pos)
  exact hH.comp SpecialPeriods.Triangle.cornerPowerThree_analyticAt_center

theorem RiemannMapping.triangleCornerFourPatch_analyticAt :
    AnalyticAt ℂ triangleCornerFourPatch (SpecialPeriods.Triangle.centerTwo : ℂ) := by
  have hH :
    AnalyticAt ℂ triangleCornerFourGerm.function
      (SpecialPeriods.Triangle.cornerPowerFour SpecialPeriods.Triangle.centerTwo) := by
    rw [SpecialPeriods.Triangle.cornerPowerFour_center]
    exact
      triangleCornerFourGerm.analytic 0 (Metric.mem_ball_self triangleCornerFourGerm.radius_pos)
  exact hH.comp SpecialPeriods.Triangle.cornerPowerFour_analyticAt_center

theorem RiemannMapping.exists_triangleCornerThreePatch_agrees :
    ∃ ε : ℝ,
      0 < ε ∧
        Set.EqOn triangleCornerThreePatch triangleMap
          (Metric.ball (SpecialPeriods.Triangle.centerOne : ℂ) ε ∩
            SpecialPeriods.Triangle.triangleInterior) := by
  obtain ⟨ε, hε, hcover⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterThree_coverage
      triangleCornerThreeGerm.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hc := hcover z hz.1 hz.2
  have he := triangleCornerThreeGerm.agrees hc.1
  change
    triangleCornerThreeGerm.function (SpecialPeriods.Triangle.cornerPowerThree z) = triangleMap z
  simpa only [Function.comp_apply, hc.2] using he

theorem RiemannMapping.exists_triangleCornerFourPatch_agrees :
    ∃ ε : ℝ,
      0 < ε ∧
        Set.EqOn triangleCornerFourPatch triangleMap
          (Metric.ball (SpecialPeriods.Triangle.centerTwo : ℂ) ε ∩
            SpecialPeriods.Triangle.triangleInterior) := by
  obtain ⟨ε, hε, hcover⟩ :=
    SpecialPeriods.Triangle.exists_cornerParameterFour_coverage triangleCornerFourGerm.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hc := hcover z hz.1 hz.2
  have he := triangleCornerFourGerm.agrees hc.1
  change
    triangleCornerFourGerm.function (SpecialPeriods.Triangle.cornerPowerFour z) = triangleMap z
  simpa only [Function.comp_apply, hc.2] using he

theorem RiemannMapping.triangleCornerThreePatch_eventuallyEq :
    triangleCornerThreePatch =ᶠ[𝓝[SpecialPeriods.Triangle.triangleInterior]
        (SpecialPeriods.Triangle.centerOne : ℂ)]
      triangleMap := by
  obtain ⟨ε, hε, he⟩ := exists_triangleCornerThreePatch_agrees
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (SpecialPeriods.Triangle.centerOne : ℂ) hε)] with
    z hz hb
  exact he ⟨hb, hz⟩

theorem RiemannMapping.triangleCornerFourPatch_eventuallyEq :
    triangleCornerFourPatch =ᶠ[𝓝[SpecialPeriods.Triangle.triangleInterior]
        (SpecialPeriods.Triangle.centerTwo : ℂ)]
      triangleMap := by
  obtain ⟨ε, hε, he⟩ := exists_triangleCornerFourPatch_agrees
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (SpecialPeriods.Triangle.centerTwo : ℂ) hε)] with
    z hz hb
  exact he ⟨hb, hz⟩

theorem RiemannMapping.triangleCornerThree_forward_limit :
    Filter.Tendsto triangleMap
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerOne : ℂ))
      (𝓝 (triangleCornerThreeGerm.function 0)) := by
  have h :
    Filter.Tendsto triangleCornerThreePatch
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerOne : ℂ))
      (𝓝 (triangleCornerThreePatch SpecialPeriods.Triangle.centerOne)) :=
    triangleCornerThreePatch_analyticAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [triangleCornerThreePatch_center] at h
  exact h.congr' triangleCornerThreePatch_eventuallyEq

theorem RiemannMapping.triangleCornerFour_forward_limit :
    Filter.Tendsto triangleMap
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerTwo : ℂ))
      (𝓝 (triangleCornerFourGerm.function 0)) := by
  have h :
    Filter.Tendsto triangleCornerFourPatch
      (𝓝[SpecialPeriods.Triangle.triangleInterior] (SpecialPeriods.Triangle.centerTwo : ℂ))
      (𝓝 (triangleCornerFourPatch SpecialPeriods.Triangle.centerTwo)) :=
    triangleCornerFourPatch_analyticAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [triangleCornerFourPatch_center] at h
  exact h.congr' triangleCornerFourPatch_eventuallyEq

def RiemannMapping.triangleCuspExp : ℂ → ℂ :=
  RiemannBoundary.halfStripExp SpecialPeriods.Triangle.stripLeft triangleCuspScale

@[simp]
theorem RiemannMapping.norm_triangleCuspExp (z : ℂ) :
    ‖triangleCuspExp z‖ = Real.exp (-z.im / triangleCuspScale) :=
  RiemannBoundary.norm_halfStripExp _ _ _

theorem RiemannMapping.triangleCuspExp_im_pos {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) : 0 < (triangleCuspExp z).im := by
  apply
    RiemannBoundary.halfStripExp_im_pos SpecialPeriods.Triangle.stripLeft triangleCuspScale_pos
  exact ⟨hz.1, by simpa only [triangleCuspScale_endpoint] using hz.2.1⟩

theorem RiemannMapping.triangleCuspLog_triangleCuspExp {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) :
    triangleCuspLog (triangleCuspExp z) = z := by
  apply
    RiemannBoundary.logHalfStrip_halfStripExp SpecialPeriods.Triangle.stripLeft
      triangleCuspScale_pos
  exact ⟨hz.1, by simpa only [triangleCuspScale_endpoint] using hz.2.1⟩

def RiemannMapping.triangleInfinityFilter : Filter ℂ :=
  Filter.cocompact ℂ ⊓ 𝓟 SpecialPeriods.Triangle.triangleInterior

theorem RiemannMapping.triangleInfinity_eventually_mem :
    ∀ᶠ z in triangleInfinityFilter, z ∈ SpecialPeriods.Triangle.triangleInterior :=
  (show
        ∀ᶠ z in 𝓟 SpecialPeriods.Triangle.triangleInterior,
          z ∈ SpecialPeriods.Triangle.triangleInterior
        by simp).filter_mono
    inf_le_right

theorem RiemannMapping.triangle_norm_add_stripLeft_le_im {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior) :
    ‖z‖ + SpecialPeriods.Triangle.stripLeft ≤ z.im := by
  have hre : z.re < 0 := hz.2.1.trans (by norm_num)
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_neg hre, abs_of_pos hz.2.2.1] at hnorm
  linarith [hz.1]

theorem RiemannMapping.tendsto_im_triangleInfinity :
    Filter.Tendsto (fun z : ℂ => z.im) triangleInfinityFilter Filter.atTop := by
  have hn : Filter.Tendsto (fun z : ℂ => ‖z‖) triangleInfinityFilter Filter.atTop :=
    tendsto_norm_cocompact_atTop.mono_left inf_le_left
  have hshift :
    Filter.Tendsto (fun z : ℂ => ‖z‖ + SpecialPeriods.Triangle.stripLeft) triangleInfinityFilter
      Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ SpecialPeriods.Triangle.stripLeft hn
  apply Filter.tendsto_atTop_mono' triangleInfinityFilter _ hshift
  filter_upwards [triangleInfinity_eventually_mem] with z hz
  exact triangle_norm_add_stripLeft_le_im hz

theorem RiemannMapping.tendsto_triangleCuspExp_triangleInfinity :
    Filter.Tendsto triangleCuspExp triangleInfinityFilter (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_triangleCuspExp]
  apply Real.tendsto_exp_atBot.comp
  have ht :=
    Filter.tendsto_neg_atTop_atBot.comp
      (tendsto_im_triangleInfinity.atTop_div_const triangleCuspScale_pos)
  simpa only [Function.comp_def, neg_div] using ht

theorem RiemannMapping.triangleMap_eq_ideal_cusp_of_param_mem {z : ℂ}
    (hz : z ∈ SpecialPeriods.Triangle.triangleInterior)
    (hq : triangleCuspExp z ∈ Metric.ball (0 : ℂ) triangleIdealGerm.radius) :
    triangleMap z = triangleIdealGerm.function (triangleCuspExp z) := by
  have he := triangleIdealGerm.agrees ⟨hq, triangleCuspExp_im_pos hz⟩
  simpa only [Function.comp_def, triangleCuspLog_triangleCuspExp hz] using he.symm

theorem RiemannMapping.triangleMap_eventually_eq_ideal_cusp :
    triangleMap =ᶠ[triangleInfinityFilter]
      (fun z => triangleIdealGerm.function (triangleCuspExp z)) := by
  have hsmall :=
    tendsto_triangleCuspExp_triangleInfinity.eventually
      (Metric.ball_mem_nhds (0 : ℂ) triangleIdealGerm.radius_pos)
  filter_upwards [triangleInfinity_eventually_mem, hsmall] with z hz hq
  exact triangleMap_eq_ideal_cusp_of_param_mem hz hq

theorem RiemannMapping.triangleIdeal_forward_limit :
    Filter.Tendsto triangleMap triangleInfinityFilter (𝓝 (triangleIdealGerm.function 0)) := by
  have hc :=
    (triangleIdealGerm.analytic 0
        (Metric.mem_ball_self triangleIdealGerm.radius_pos)).continuousAt
  exact
    (hc.tendsto.comp tendsto_triangleCuspExp_triangleInfinity).congr'
      triangleMap_eventually_eq_ideal_cusp.symm

theorem RiemannMapping.comap_coe_triangle_onePoint_nhds_infty :
    Filter.comap ((↑) : ℂ → OnePoint ℂ)
        (𝓝[RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior]
          ((OnePoint.infty) : OnePoint ℂ)) =
      triangleInfinityFilter := by
  have hp :
    ((↑) : ℂ → OnePoint ℂ) ⁻¹'
        RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior =
      SpecialPeriods.Triangle.triangleInterior :=
    Set.ext fun _ => RiemannBoundary.coe_mem_onePointDomain
  rw [nhdsWithin, Filter.comap_inf, OnePoint.comap_coe_nhds_infty,
    Filter.coclosedCompact_eq_cocompact, Filter.comap_principal, hp]
  rfl

theorem RiemannMapping.triangleIdeal_forward_limit_onePoint :
    Filter.Tendsto triangleOnePointRepresentative
      (𝓝[RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior]
        ((OnePoint.infty) : OnePoint ℂ))
      (𝓝 (triangleIdealGerm.function 0)) := by
  have hRange :
    Set.range ((↑) : ℂ → OnePoint ℂ) ∈
      𝓝[RiemannBoundary.onePointDomain SpecialPeriods.Triangle.triangleInterior]
        ((OnePoint.infty) : OnePoint ℂ) := by
    apply Filter.mem_of_superset self_mem_nhdsWithin
    rintro _ ⟨z, _, rfl⟩
    exact Set.mem_range_self z
  apply (Filter.tendsto_comap'_iff (i := ((↑) : ℂ → OnePoint ℂ)) hRange).mp
  simpa only [Function.comp_def, triangleOnePointRepresentative_coe,
    comap_coe_triangle_onePoint_nhds_infty] using triangleIdeal_forward_limit

theorem RiemannMapping.triangleClosed_finite_forward_limit
    (x : SpecialPeriods.Triangle.TriangleClosedDomain) {a w : ℂ} (hxa : x.val = (a : OnePoint ℂ))
    (hf : Filter.Tendsto triangleMap (𝓝[SpecialPeriods.Triangle.triangleInterior] a) (𝓝 w)) :
    Filter.Tendsto
      (fun z : SpecialPeriods.Triangle.triangleClosedInterior =>
        (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph z : ℂ))
      (Filter.comap
        (Subtype.val :
          SpecialPeriods.Triangle.triangleClosedInterior →
            SpecialPeriods.Triangle.TriangleClosedDomain)
        (𝓝 x))
      (𝓝 w) := by
  apply (SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff x).mpr
  rw [hxa]
  exact SpecialPeriods.Triangle.triangleOnePointRepresentative_finite_tendsto_iff.mpr hf

theorem RiemannMapping.triangleClosed_finite_inverse_limit
    (x : SpecialPeriods.Triangle.TriangleClosedDomain) {a w : ℂ} (hxa : x.val = (a : OnePoint ℂ))
    (hi :
      Filter.Tendsto (RiemannBoundary.discHomeomorphInverse triangleBiholomorph.toHomeomorph)
        (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 a)) :
    Filter.Tendsto
      (RiemannBoundary.discHomeomorphInverse
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph)
      (𝓝[Metric.ball (0 : ℂ) 1] w) (𝓝 x) := by
  apply (SpecialPeriods.Triangle.triangleClosedInterior_inverse_tendsto_iff x).mpr
  rw [hxa]
  exact SpecialPeriods.Triangle.triangleDiscOnOnePointDomain_finite_inverse_tendsto_iff.mpr hi

theorem RiemannMapping.triangleClosedDiscBoundaryLimits :
    RiemannBoundary.DiscBoundaryLimits
      SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph := by
  intro x hx
  rcases SpecialPeriods.Triangle.triangleClosedBoundary_cases x hx with rfl | ⟨a, ha, hxa⟩ |
    ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩ | rfl | rfl
  · exact
      ⟨triangleIdealGerm.function 0, triangleIdealGerm.unit,
        (SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff _).mpr
          triangleIdeal_forward_limit_onePoint,
        (SpecialPeriods.Triangle.triangleClosedInterior_inverse_tendsto_iff _).mpr
          triangleIdeal_inverse_limit⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_left_side_limits ha.1 ha.2.1 ha.2.2
    exact
      ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
        triangleClosed_finite_inverse_limit x hxa hi⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_right_side_limits ha.1 ha.2.1 ha.2.2
    exact
      ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
        triangleClosed_finite_inverse_limit x hxa hi⟩
  · obtain ⟨w, hw, hf, hi⟩ := exists_triangleMap_circle_side_limits ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
    exact
      ⟨w, hw, triangleClosed_finite_forward_limit x hxa hf,
        triangleClosed_finite_inverse_limit x hxa hi⟩
  · exact
      ⟨triangleCornerThreeGerm.function 0, triangleCornerThreeGerm.unit,
        triangleClosed_finite_forward_limit _ rfl triangleCornerThree_forward_limit,
        triangleClosed_finite_inverse_limit _ rfl triangleCornerThree_inverse_limit⟩
  · exact
      ⟨triangleCornerFourGerm.function 0, triangleCornerFourGerm.unit,
        triangleClosed_finite_forward_limit _ rfl triangleCornerFour_forward_limit,
        triangleClosed_finite_inverse_limit _ rfl triangleCornerFour_inverse_limit⟩

def RiemannMapping.triangleClosedDiscHomeomorph :
    SpecialPeriods.Triangle.TriangleClosedDomain ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
  RiemannBoundary.closedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInterior_dense
    SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits

theorem RiemannMapping.triangleClosedDiscHomeomorph_interior
    (z : SpecialPeriods.Triangle.triangleClosedInterior) :
    (triangleClosedDiscHomeomorph z : ℂ) =
      (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph z : ℂ) :=
  RiemannBoundary.closedDiscHomeomorph_coe SpecialPeriods.Triangle.triangleClosedInterior_dense
    SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph triangleClosedDiscBoundaryLimits
    z

theorem RiemannMapping.triangleClosedDiscHomeomorph_triangle (z : triangleDomain) :
    (triangleClosedDiscHomeomorph (SpecialPeriods.Triangle.triangleClosedInclusion z) : ℂ) =
      triangleMap z := by
  rw [triangleMap_biholomorph z]
  exact
    (triangleClosedDiscHomeomorph_interior
          (SpecialPeriods.Triangle.triangleClosedInteriorHomeomorph z)).trans
      (congrArg (fun w : Metric.ball (0 : ℂ) 1 => (w : ℂ))
        (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph_apply z))

theorem RiemannMapping.triangleClosedDiscHomeomorph_boundary
    {x : SpecialPeriods.Triangle.TriangleClosedDomain}
    (hx : x ∉ SpecialPeriods.Triangle.triangleClosedInterior) :
    ‖(triangleClosedDiscHomeomorph x : ℂ)‖ = 1 :=
  (RiemannBoundary.discCompactificationMap_boundary
      SpecialPeriods.Triangle.triangleClosedInterior_dense
      SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
      triangleClosedDiscBoundaryLimits hx).1

theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_lt_iff
    (x : SpecialPeriods.Triangle.TriangleClosedDomain) :
    ‖(triangleClosedDiscHomeomorph x : ℂ)‖ < 1 ↔
      x ∈ SpecialPeriods.Triangle.triangleClosedInterior := by
  constructor
  · intro h
    by_contra hx
    rw [triangleClosedDiscHomeomorph_boundary hx] at h
    exact lt_irrefl _ h
  · intro hx
    rw [triangleClosedDiscHomeomorph_interior
        (⟨x, hx⟩ : SpecialPeriods.Triangle.triangleClosedInterior)]
    simpa only [Metric.mem_ball, dist_zero_right] using
      (SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph ⟨x, hx⟩).property

@[simp]
theorem RiemannMapping.triangleClosedDiscHomeomorph_centerOne :
    (triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterOne : ℂ) =
      triangleCornerThreeGerm.function 0 := by
  change
    RiemannBoundary.discCompactificationMap SpecialPeriods.Triangle.triangleClosedInterior_dense
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
        SpecialPeriods.Triangle.triangleClosedCenterOne =
      _
  exact
    SpecialPeriods.Triangle.triangleClosedInterior_dense.extend_eq_of_tendsto
      (triangleClosed_finite_forward_limit _ rfl triangleCornerThree_forward_limit)

@[simp]
theorem RiemannMapping.triangleClosedDiscHomeomorph_centerTwo :
    (triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterTwo : ℂ) =
      triangleCornerFourGerm.function 0 := by
  change
    RiemannBoundary.discCompactificationMap SpecialPeriods.Triangle.triangleClosedInterior_dense
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
        SpecialPeriods.Triangle.triangleClosedCenterTwo =
      _
  exact
    SpecialPeriods.Triangle.triangleClosedInterior_dense.extend_eq_of_tendsto
      (triangleClosed_finite_forward_limit _ rfl triangleCornerFour_forward_limit)

@[simp]
theorem RiemannMapping.triangleClosedDiscHomeomorph_infty :
    (triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInfinity : ℂ) =
      triangleIdealGerm.function 0 := by
  change
    RiemannBoundary.discCompactificationMap SpecialPeriods.Triangle.triangleClosedInterior_dense
        SpecialPeriods.Triangle.triangleClosedInteriorDiscHomeomorph
        SpecialPeriods.Triangle.triangleClosedInfinity =
      _
  exact
    SpecialPeriods.Triangle.triangleClosedInterior_dense.extend_eq_of_tendsto
      ((SpecialPeriods.Triangle.triangleClosedInterior_forward_representative_tendsto_iff _).mpr
        triangleIdeal_forward_limit_onePoint)

theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_centerOne :
    ‖(triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterOne : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_centerOne]
  exact triangleCornerThreeGerm.unit

theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_centerTwo :
    ‖(triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterTwo : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_centerTwo]
  exact triangleCornerFourGerm.unit

theorem RiemannMapping.triangleClosedDiscHomeomorph_norm_infty :
    ‖(triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInfinity : ℂ)‖ = 1 := by
  rw [triangleClosedDiscHomeomorph_infty]
  exact triangleIdealGerm.unit

abbrev SpecialPeriods.Triangle.TriangleClosedFinite :=
  { x : TriangleClosedDomain // x ≠ triangleClosedInfinity }

theorem SpecialPeriods.Triangle.coe_mem_triangleClosedSet_iff_halfFordRegion (z : ℍ) :
    ((z : ℂ) : OnePoint ℂ) ∈ triangleClosedSet ↔ z ∈ halfFordRegion := by
  rw [coe_mem_triangleClosedSet_iff_closure, closure_triangleInterior]
  exact coe_mem_triangleClosedRegion_iff_halfFordRegion z

def SpecialPeriods.Triangle.halfFordToClosedDomain (z : halfFordRegion) : TriangleClosedDomain :=
  ⟨((z : ℍ) : ℂ), (coe_mem_triangleClosedSet_iff_halfFordRegion z).mpr z.property⟩

theorem SpecialPeriods.Triangle.halfFordToClosedDomain_ne_infinity (z : halfFordRegion) :
    halfFordToClosedDomain z ≠ triangleClosedInfinity := by
  intro h
  exact OnePoint.coe_ne_infty ((z : ℍ) : ℂ) (congrArg Subtype.val h)

def SpecialPeriods.Triangle.halfFordToClosedFinite (z : halfFordRegion) : TriangleClosedFinite :=
  ⟨halfFordToClosedDomain z, halfFordToClosedDomain_ne_infinity z⟩

theorem SpecialPeriods.Triangle.halfFordToClosedFinite_isEmbedding :
    Topology.IsEmbedding halfFordToClosedFinite := by
  have htarget : Topology.IsEmbedding (fun x : TriangleClosedFinite => x.val.val) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  apply htarget.of_comp_iff.mp
  exact
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      (UpperHalfPlane.isEmbedding_coe.comp Topology.IsEmbedding.subtypeVal)

theorem SpecialPeriods.Triangle.halfFordToClosedFinite_surjective :
    Function.Surjective halfFordToClosedFinite := by
  intro x
  have hx : x.val.val ≠ ((OnePoint.infty) : OnePoint ℂ) := by
    intro h
    exact x.property (Subtype.ext h)
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hx
  have hmem : (z : OnePoint ℂ) ∈ triangleClosedSet := by
    rw [hz]
    exact x.val.property
  have him : 0 < z.im := ((coe_mem_triangleClosedSet_iff z).mp hmem).2.2.1
  let w : ℍ := ⟨z, him⟩
  have hw : w ∈ halfFordRegion := (coe_mem_triangleClosedSet_iff_halfFordRegion w).mp hmem
  exact ⟨⟨w, hw⟩, Subtype.ext (Subtype.ext hz)⟩

def SpecialPeriods.Triangle.halfFordClosedHomeomorph : halfFordRegion ≃ₜ TriangleClosedFinite :=
  halfFordToClosedFinite_isEmbedding.toHomeomorphOfSurjective halfFordToClosedFinite_surjective

theorem SpecialPeriods.Triangle.halfFordClosedHomeomorph_mem_interior_iff (z : halfFordRegion) :
    (halfFordClosedHomeomorph z).val ∈ triangleClosedInterior ↔ (z : ℍ) ∈ halfFordInterior := by
  change (((z : ℍ) : ℂ) : OnePoint ℂ) ∈ RiemannBoundary.onePointDomain triangleInterior ↔ _
  rw [RiemannBoundary.coe_mem_onePointDomain, halfFordInterior_eq_preimage_triangleInterior]
  rfl

theorem SpecialPeriods.Triangle.halfFordClosedHomeomorph_of_interior (z : ℍ)
    (hz : z ∈ halfFordInterior) :
    (halfFordClosedHomeomorph ⟨z, halfFordInterior_subset_halfFordRegion hz⟩).val =
      triangleClosedInclusion
        (⟨(z : ℂ), by
            change (z : ℂ) ∈ triangleInterior
            simpa only [halfFordInterior_eq_preimage_triangleInterior, Set.mem_preimage] using
              hz⟩ :
          RiemannMapping.triangleDomain) :=
  rfl

theorem SpecialPeriods.Triangle.centerOne_mem_halfFordRegion : centerOne ∈ halfFordRegion :=
  (coe_mem_triangleClosedSet_iff_halfFordRegion centerOne).mp triangleClosedCenterOne.property

theorem SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion : centerTwo ∈ halfFordRegion :=
  (coe_mem_triangleClosedSet_iff_halfFordRegion centerTwo).mp triangleClosedCenterTwo.property

def RiemannMapping.normalizationZeroValue : ℂ :=
  triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterOne

def RiemannMapping.normalizationOneValue : ℂ :=
  triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedCenterTwo

def RiemannMapping.normalizationPoleValue : ℂ :=
  triangleClosedDiscHomeomorph SpecialPeriods.Triangle.triangleClosedInfinity

@[simp]
theorem RiemannMapping.normalizationZeroValue_eq :
    normalizationZeroValue = triangleCornerThreeGerm.function 0 :=
  triangleClosedDiscHomeomorph_centerOne

@[simp]
theorem RiemannMapping.normalizationOneValue_eq :
    normalizationOneValue = triangleCornerFourGerm.function 0 :=
  triangleClosedDiscHomeomorph_centerTwo

@[simp]
theorem RiemannMapping.normalizationPoleValue_eq :
    normalizationPoleValue = triangleIdealGerm.function 0 :=
  triangleClosedDiscHomeomorph_infty

def RiemannMapping.normalizationOrientation : ℝ :=
  RiemannSphere.MobiusCircle.orientation normalizationZeroValue normalizationOneValue
    normalizationPoleValue

theorem RiemannMapping.normalizationOrientation_ne_zero : normalizationOrientation ≠ 0 :=
  TriangleRiemannNormalization.normalization_orientation_ne_zero triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

def RiemannMapping.triangleFiniteNormalizationHomeomorph :
    SpecialPeriods.Triangle.TriangleClosedFinite ≃ₜ
      RiemannSphere.closedOrientedHalfPlane normalizationOrientation :=
  TriangleRiemannNormalization.normalizationHomeomorph triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

@[simp]
theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_apply
    (x : SpecialPeriods.Triangle.TriangleClosedFinite) :
    (triangleFiniteNormalizationHomeomorph x : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue
        (triangleClosedDiscHomeomorph (x : SpecialPeriods.Triangle.TriangleClosedDomain) : ℂ) :=
  TriangleRiemannNormalization.normalizationHomeomorph_apply triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty x

@[simp]
theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_centerOne :
    (triangleFiniteNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.triangleClosedCenterOne,
            SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty⟩ :
        ℂ) =
      0 :=
  TriangleRiemannNormalization.normalizationHomeomorph_first triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

@[simp]
theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_centerTwo :
    (triangleFiniteNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.triangleClosedCenterTwo,
            SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty⟩ :
        ℂ) =
      1 :=
  TriangleRiemannNormalization.normalizationHomeomorph_second triangleClosedDiscHomeomorph
    SpecialPeriods.Triangle.triangleClosedCenterOne
    SpecialPeriods.Triangle.triangleClosedCenterTwo SpecialPeriods.Triangle.triangleClosedInfinity
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
    SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
    SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty

theorem RiemannMapping.triangleFiniteNormalizationHomeomorph_strict_iff
    (x : SpecialPeriods.Triangle.TriangleClosedFinite) :
    0 < normalizationOrientation * (triangleFiniteNormalizationHomeomorph x : ℂ).im ↔
      (x : SpecialPeriods.Triangle.TriangleClosedDomain) ∈
        SpecialPeriods.Triangle.triangleClosedInterior := by
  have h :=
    TriangleRiemannNormalization.normalizationHomeomorph_strict_iff triangleClosedDiscHomeomorph
      SpecialPeriods.Triangle.triangleClosedCenterOne
      SpecialPeriods.Triangle.triangleClosedCenterTwo
      SpecialPeriods.Triangle.triangleClosedInfinity
      SpecialPeriods.Triangle.triangleClosedCenterOne_ne_centerTwo
      SpecialPeriods.Triangle.triangleClosedCenterOne_ne_infty
      SpecialPeriods.Triangle.triangleClosedCenterTwo_ne_infty
      triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
      triangleClosedDiscHomeomorph_norm_infty x
  exact h.trans (triangleClosedDiscHomeomorph_norm_lt_iff x)

def RiemannMapping.halfFordNormalizationHomeomorph :
    SpecialPeriods.Triangle.halfFordRegion ≃ₜ
      RiemannSphere.closedOrientedHalfPlane normalizationOrientation :=
  SpecialPeriods.Triangle.halfFordClosedHomeomorph.trans triangleFiniteNormalizationHomeomorph

@[simp]
theorem RiemannMapping.halfFordNormalizationHomeomorph_apply
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    (halfFordNormalizationHomeomorph z : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue
        (triangleClosedDiscHomeomorph (SpecialPeriods.Triangle.halfFordClosedHomeomorph z).val :
          ℂ) :=
  triangleFiniteNormalizationHomeomorph_apply (SpecialPeriods.Triangle.halfFordClosedHomeomorph z)

@[simp]
theorem RiemannMapping.halfFordNormalizationHomeomorph_centerOne :
    (halfFordNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.centerOne,
            SpecialPeriods.Triangle.centerOne_mem_halfFordRegion⟩ :
        ℂ) =
      0 :=
  triangleFiniteNormalizationHomeomorph_centerOne

@[simp]
theorem RiemannMapping.halfFordNormalizationHomeomorph_centerTwo :
    (halfFordNormalizationHomeomorph
          ⟨SpecialPeriods.Triangle.centerTwo,
            SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion⟩ :
        ℂ) =
      1 :=
  triangleFiniteNormalizationHomeomorph_centerTwo

theorem RiemannMapping.halfFordNormalizationHomeomorph_apply_of_interior (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.halfFordInterior) :
    (halfFordNormalizationHomeomorph
          ⟨z, SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz⟩ :
        ℂ) =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue (triangleMap (z : ℂ)) := by
  rw [halfFordNormalizationHomeomorph_apply,
    SpecialPeriods.Triangle.halfFordClosedHomeomorph_of_interior z hz,
    triangleClosedDiscHomeomorph_triangle]

theorem RiemannMapping.halfFordNormalizationHomeomorph_strict_iff
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    0 < normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im ↔
      (z : ℍ) ∈ SpecialPeriods.Triangle.halfFordInterior :=
  (triangleFiniteNormalizationHomeomorph_strict_iff
        (SpecialPeriods.Triangle.halfFordClosedHomeomorph z)).trans
    (SpecialPeriods.Triangle.halfFordClosedHomeomorph_mem_interior_iff z)

theorem RiemannMapping.halfFordNormalizationHomeomorph_boundary_iff
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    (halfFordNormalizationHomeomorph z : ℂ).im = 0 ↔
      (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior := by
  constructor
  · intro hz hin
    have h := (halfFordNormalizationHomeomorph_strict_iff z).mpr hin
    simp only [hz, MulZeroClass.mul_zero, lt_self_iff_false] at h
  · intro hz
    have hn : ¬0 < normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im :=
      fun h => hz ((halfFordNormalizationHomeomorph_strict_iff z).mp h)
    have he : normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im = 0 :=
      le_antisymm (le_of_not_gt hn) (halfFordNormalizationHomeomorph z).property
    exact (mul_eq_zero.mp he).resolve_left normalizationOrientation_ne_zero

def RiemannMapping.triangleSignedHalfPlaneMap : TriangleUniformizationGluing.SignedHalfPlaneMap :=
  TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph normalizationOrientation_ne_zero
    halfFordNormalizationHomeomorph halfFordNormalizationHomeomorph_strict_iff

@[simp]
theorem RiemannMapping.triangleSignedHalfPlaneMap_coe
    (z : SpecialPeriods.Triangle.halfFordRegion) :
    triangleSignedHalfPlaneMap z = (halfFordNormalizationHomeomorph z : ℂ) :=
  TriangleUniformizationGluing.signedHalfPlaneMapOfHomeomorph_apply
    normalizationOrientation_ne_zero halfFordNormalizationHomeomorph
    halfFordNormalizationHomeomorph_strict_iff z

theorem RiemannMapping.triangleSignedHalfPlaneMap_of_mem {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    triangleSignedHalfPlaneMap z = (halfFordNormalizationHomeomorph ⟨z, hz⟩ : ℂ) :=
  triangleSignedHalfPlaneMap_coe ⟨z, hz⟩

theorem RiemannMapping.triangleSignedHalfPlaneMap_of_interior (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.halfFordInterior) :
    triangleSignedHalfPlaneMap z =
      RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue (triangleMap (z : ℂ)) := by
  rw [triangleSignedHalfPlaneMap_of_mem
      (SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz)]
  exact halfFordNormalizationHomeomorph_apply_of_interior z hz

@[simp]
theorem RiemannMapping.triangleSignedHalfPlaneMap_centerOne :
    triangleSignedHalfPlaneMap SpecialPeriods.Triangle.centerOne = 0 := by
  rw [triangleSignedHalfPlaneMap_of_mem SpecialPeriods.Triangle.centerOne_mem_halfFordRegion]
  exact halfFordNormalizationHomeomorph_centerOne

@[simp]
theorem RiemannMapping.triangleSignedHalfPlaneMap_centerTwo :
    triangleSignedHalfPlaneMap SpecialPeriods.Triangle.centerTwo = 1 := by
  rw [triangleSignedHalfPlaneMap_of_mem SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion]
  exact halfFordNormalizationHomeomorph_centerTwo

theorem RiemannMapping.triangleSignedHalfPlaneMap_isProperMap :
    IsProperMap
      (fun z : SpecialPeriods.Triangle.halfFordRegion => triangleSignedHalfPlaneMap z) :=
  TriangleUniformizationGluing.halfFordHomeomorphExtension_isProperMap
    halfFordNormalizationHomeomorph

theorem RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω triangleSignedHalfPlaneMap SpecialPeriods.Triangle.halfFordInterior :=
  by
  have hab : normalizationZeroValue ≠ normalizationOneValue := by
    simpa only [normalizationZeroValue_eq, normalizationOneValue_eq] using
      triangleCorner_boundary_values_ne
  have hc : ‖normalizationPoleValue‖ = 1 := by
    simpa only [normalizationPoleValue_eq] using triangleIdealGerm.unit
  have hf : ContDiffOn ℂ ω triangleMap SpecialPeriods.Triangle.triangleInterior :=
    (triangleMap_differentiable.analyticOnNhd
          SpecialPeriods.Triangle.triangleInterior_isOpen).contDiffOn
      SpecialPeriods.Triangle.triangleInterior_isOpen.uniqueDiffOn
  have hcr :
    ContDiffOn ℂ ω
      (RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue)
      {z : ℂ | ‖z‖ < 1} :=
    RiemannSphere.crossRatio_holomorphicOn_disc hab hc
  have hcomp :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ =>
        RiemannSphere.MobiusCircle.crossRatio normalizationZeroValue normalizationOneValue
          normalizationPoleValue (triangleMap z))
      SpecialPeriods.Triangle.triangleInterior :=
    contMDiffOn_iff_contDiffOn.mpr (hcr.comp hf (fun _ hz => triangleMap_norm_lt_one hz))
  have hu :=
    hcomp.comp UpperHalfPlane.contMDiff_coe.contMDiffOn
      (show
        Set.MapsTo ((↑) : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior
          SpecialPeriods.Triangle.triangleInterior
        from by
        intro z hz
        simpa only [SpecialPeriods.Triangle.halfFordInterior_eq_preimage_triangleInterior,
          Set.mem_preimage] using hz)
  apply hu.congr
  intro z hz
  exact triangleSignedHalfPlaneMap_of_interior z hz

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_compact_preimage
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (K : Set ℂ) (hK : IsCompact K) :
    IsCompact (SpecialPeriods.Triangle.fordRegion ∩ D.foldedFordMap ⁻¹' K) := by
  have hhalf (L : Set ℂ) (hL : IsCompact L) :
    IsCompact (SpecialPeriods.Triangle.halfFordRegion ∩ D.toFun ⁻¹' L) := by
    have hs := (hlocal.isCompact_preimage hL).image continuous_subtype_val
    change
      IsCompact
        ((Subtype.val : SpecialPeriods.Triangle.halfFordRegion → ℍ) ''
          ((Subtype.val : SpecialPeriods.Triangle.halfFordRegion → ℍ) ⁻¹' (D.toFun ⁻¹' L))) at hs
    simpa only [Subtype.image_preimage_val] using hs
  have hconj : IsCompact ((conj : ℂ → ℂ) ⁻¹' K) :=
    Complex.conjCLE.toHomeomorph.isCompact_preimage.mpr hK
  have heq :
    SpecialPeriods.Triangle.fordRegion ∩ D.foldedFordMap ⁻¹' K =
      (SpecialPeriods.Triangle.halfFordRegion ∩ D.toFun ⁻¹' K) ∪
        SpecialPeriods.Triangle.rightReflection ''
          (SpecialPeriods.Triangle.halfFordRegion ∩ D.toFun ⁻¹' ((conj : ℂ → ℂ) ⁻¹' K)) := by
    ext z
    constructor
    · rintro ⟨hz, hKz⟩
      change D.foldedFordMap z ∈ K at hKz
      rw [← SpecialPeriods.Triangle.halfFordRegion_union_reflection] at hz
      rcases hz with hz | ⟨w, hw, rfl⟩
      · left
        refine ⟨hz, ?_⟩
        change D z ∈ K
        rwa [D.foldedFordMap_of_left hz.2] at hKz
      · right
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        change conj (D w) ∈ K
        rwa [D.foldedFordMap_reflected w hw] at hKz
    · rintro (⟨hz, hKz⟩ | ⟨w, ⟨hw, hKw⟩, rfl⟩)
      · refine ⟨hz.1, ?_⟩
        change D.foldedFordMap z ∈ K
        rwa [D.foldedFordMap_of_left hz.2]
      · refine ⟨SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hw.1, ?_⟩
        change D.foldedFordMap (SpecialPeriods.Triangle.rightReflection w) ∈ K
        rw [D.foldedFordMap_reflected w hw]
        exact hKw
  rw [heq]
  exact
    (hhalf K hK).union ((hhalf _ hconj).image SpecialPeriods.Triangle.rightReflection.continuous)

def SpecialPeriods.Triangle.closedFirstSector : Set ℍ :=
  {z | z.re ≤ -(1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖}

def SpecialPeriods.Triangle.closedSecondSector : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖}

def SpecialPeriods.Triangle.firstWeakExcluded : Set ℍ :=
  {z | -(1 / 2) ≤ z.re ∨ ‖(z : ℂ)‖ ≤ 1}

def SpecialPeriods.Triangle.secondWeakExcluded : Set ℍ :=
  {z | z.re ≤ stripLeft ∨ ‖(z : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight}

def SpecialPeriods.Triangle.circularDoubleRegion : Set ℍ :=
  closedFirstSector ∩ closedSecondSector

theorem SpecialPeriods.Triangle.firstExcluded_subset_firstWeakExcluded :
    firstExcluded ⊆ firstWeakExcluded := by
  intro z hz
  exact hz.imp le_of_lt le_of_lt

theorem SpecialPeriods.Triangle.secondExcluded_subset_secondWeakExcluded :
    secondExcluded ⊆ secondWeakExcluded := by
  intro z hz
  exact hz.imp le_of_lt le_of_lt

theorem SpecialPeriods.Triangle.firstWeakExcluded_subset_pingPongOne :
    firstWeakExcluded ⊆ pingPongOne := by
  intro z hz
  change -1 < z.re
  rcases hz with hx | hn
  · linarith
  · have habs : |z.re| < ‖(z : ℂ)‖ := Complex.abs_re_lt_norm.mpr z.im_ne_zero
    linarith [neg_le_abs z.re]

theorem SpecialPeriods.Triangle.secondWeakExcluded_subset_pingPongTwo :
    secondWeakExcluded ⊆ pingPongTwo := by
  intro z hz
  change z.re < -1
  rcases hz with hx | hn
  · exact hx.trans_lt stripLeft_lt_neg_one
  · have him : ((z : ℂ) - (stripLeft : ℂ)).im ≠ 0 := by simpa using z.im_ne_zero
    have habs := Complex.abs_re_lt_norm.mpr him
    have hr := le_abs_self (((z : ℂ) - (stripLeft : ℂ)).re)
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.ofReal_re] at habs hr
    linarith [stripLeft_add_stripRight]

theorem SpecialPeriods.Triangle.firstWeakExcluded_subset_secondSector :
    firstWeakExcluded ⊆ secondSector :=
  firstWeakExcluded_subset_pingPongOne.trans pingPongOne_subset_secondSector

theorem SpecialPeriods.Triangle.secondWeakExcluded_subset_firstSector :
    secondWeakExcluded ⊆ firstSector :=
  secondWeakExcluded_subset_pingPongTwo.trans pingPongTwo_subset_firstSector

theorem SpecialPeriods.Triangle.circularDoubleRegion_disjoint_firstExcluded :
    Disjoint circularDoubleRegion firstExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact (not_lt_of_ge hz.1.1) hx
  · exact (not_lt_of_ge hz.1.2) hn

theorem SpecialPeriods.Triangle.circularDoubleRegion_disjoint_secondExcluded :
    Disjoint circularDoubleRegion secondExcluded := by
  apply Set.disjoint_left.mpr
  intro z hz he
  rcases he with hx | hn
  · exact (not_lt_of_ge hz.2.1) hx
  · exact (not_lt_of_ge hz.2.2) hn

theorem SpecialPeriods.Triangle.generatorOne_closedFirstSector :
    Set.MapsTo (fun z : ℍ => generatorOneSL • z) closedFirstSector firstWeakExcluded := by
  intro z hz
  left
  change -(1 / 2) ≤ (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hn : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2]
  simp only [← neg_div]
  apply (le_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
  nlinarith

private theorem SpecialPeriods.Triangle.norm_add_one_le_norm_of_re_le_half_mo1973_19719 (z : ℍ)
    (hz : z.re ≤ -(1 / 2)) : ‖(z : ℂ) + 1‖ ≤ ‖(z : ℂ)‖ := by
  have hsq : ‖(z : ℂ) + 1‖ ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    linarith
  nlinarith [norm_nonneg ((z : ℂ) + 1), norm_nonneg (z : ℂ)]

theorem SpecialPeriods.Triangle.generatorOne_sq_closedFirstSector :
    Set.MapsTo (fun z : ℍ => (generatorOneSL ^ 2 : SL(2, ℝ)) • z) closedFirstSector
      firstWeakExcluded := by
  intro z hz
  right
  rw [generatorOneSL_sq_smul_coe]
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div]
  exact
    (div_le_one (norm_pos_iff.mpr z.ne_zero)).mpr
      (norm_add_one_le_norm_of_re_le_half_mo1973_19719 z hz.1)

private def SpecialPeriods.Triangle.secondShift_mo1973_19721 (z : ℍ) : ℂ :=
  (z : ℂ) - (stripLeft : ℂ)

private theorem SpecialPeriods.Triangle.secondShift_re_mo1973_19722 (z : ℍ) :
    (secondShift_mo1973_19721 z).re = z.re - stripLeft := by simp [secondShift_mo1973_19721]

private theorem SpecialPeriods.Triangle.secondShift_add_real_ne_zero_mo1973_19723 (z : ℍ)
    (a : ℝ) : secondShift_mo1973_19721 z + (a : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [secondShift_mo1973_19721, Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    sub_zero, add_zero, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

private theorem SpecialPeriods.Triangle.stripLeft_eq_neg_stripRight_sub_one_mo1973_19724 :
    stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]

private theorem SpecialPeriods.Triangle.width_eq_two_stripRight_add_one_mo1973_19725 :
    width = 2 * stripRight + 1 := by
  unfold stripRight
  ring

private theorem SpecialPeriods.Triangle.stripRight_sq_complex_mo1973_19726 :
    (stripRight : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, stripRight_sq]
  norm_num

private theorem SpecialPeriods.Triangle.generatorTwo_secondShift_mo1973_19727 (z : ℍ) :
    secondShift_mo1973_19721 (generatorTwoSL • z) =
      (stripRight : ℂ) * (secondShift_mo1973_19721 z - stripRight) /
        (secondShift_mo1973_19721 z + stripRight) := by
  have hd := secondShift_add_real_ne_zero_mo1973_19723 z stripRight
  have hs := stripRight_sq_complex_mo1973_19726
  unfold secondShift_mo1973_19721 at *
  rw [generatorTwoSL_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_19724,
    width_eq_two_stripRight_add_one_mo1973_19725] at *
  push_cast at *
  have he :
    (z : ℂ) + (2 * (stripRight : ℂ) + 1) = (z : ℂ) - (-(stripRight : ℂ) - 1) + stripRight := by
    ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.generatorTwo_sq_secondShift_mo1973_19728 (z : ℍ) :
    secondShift_mo1973_19721 ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) ^ 2 / secondShift_mo1973_19721 z := by
  have hz : secondShift_mo1973_19721 z ≠ 0 := by
    simpa using secondShift_add_real_ne_zero_mo1973_19723 z 0
  have hd := secondShift_add_real_ne_zero_mo1973_19723 z stripRight
  have hR : (stripRight : ℂ) ≠ 0 := by exact_mod_cast stripRight_pos.ne'
  rw [pow_two, SemigroupAction.mul_smul, generatorTwo_secondShift_mo1973_19727,
    generatorTwo_secondShift_mo1973_19727]
  field_simp [hz, hd, hR]
  ring

private theorem SpecialPeriods.Triangle.generatorTwo_cube_secondShift_mo1973_19729 (z : ℍ) :
    secondShift_mo1973_19721 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) =
      -(stripRight : ℂ) * (secondShift_mo1973_19721 z + stripRight) /
        (secondShift_mo1973_19721 z - stripRight) := by
  have hd : secondShift_mo1973_19721 z - (stripRight : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_neg, sub_eq_add_neg] using
      secondShift_add_real_ne_zero_mo1973_19723 z (-stripRight)
  have hs := stripRight_sq_complex_mo1973_19726
  unfold secondShift_mo1973_19721 at *
  rw [generatorTwoSL_cube_smul_coe]
  rw [stripLeft_eq_neg_stripRight_sub_one_mo1973_19724,
    width_eq_two_stripRight_add_one_mo1973_19725] at *
  push_cast at *
  have he : (z : ℂ) + 1 = (z : ℂ) - (-(stripRight : ℂ) - 1) - stripRight := by ring
  rw [he]
  field_simp [hd]
  linear_combination 2 * hs

private theorem SpecialPeriods.Triangle.norm_sub_div_add_le_one_mo1973_19730 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 ≤ u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ ≤ 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 ≤ ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero]
    nlinarith [mul_nonneg hr.le hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem SpecialPeriods.Triangle.re_add_div_sub_nonneg_mo1973_19731 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : r ≤ ‖u‖) : 0 ≤ ((u + (r : ℂ)) / (u - (r : ℂ))).re := by
  have hsq : r ^ 2 ≤ Complex.normSq u := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.div_re, ← add_div]
  apply div_nonneg ?_ (Complex.normSq_nonneg _)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
    Complex.ofReal_im, add_zero, sub_zero]
  rw [Complex.normSq_apply] at hsq
  nlinarith

private theorem SpecialPeriods.Triangle.re_neg_sq_div_nonpos_mo1973_19732 {r : ℝ} {u : ℂ}
    (hu : 0 ≤ u.re) : (-(r : ℂ) ^ 2 / u).re ≤ 0 := by
  have hnum : -(r ^ 2) * u.re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg r)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_nonpos_of_nonpos_of_nonneg hnum (Complex.normSq_nonneg u)

private theorem SpecialPeriods.Triangle.norm_sub_div_add_lt_one_mo1973_19733 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : ‖(u - (r : ℂ)) / (u + (r : ℂ))‖ < 1 := by
  have hd : u + (r : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  rw [norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hd)).mpr
  have hsq : ‖u - (r : ℂ)‖ ^ 2 < ‖u + (r : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero]
    nlinarith [mul_pos hr hu]
  nlinarith [norm_nonneg (u - (r : ℂ)), norm_nonneg (u + (r : ℂ))]

private theorem SpecialPeriods.Triangle.re_neg_sq_div_neg_mo1973_19735 {r : ℝ} (hr : 0 < r)
    {u : ℂ} (hu : 0 < u.re) : (-(r : ℂ) ^ 2 / u).re < 0 := by
  have hd : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hnum : -(r ^ 2) * u.re < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hr)) hu
  simpa [Complex.div_re, ← Complex.ofReal_pow] using
    div_neg_of_neg_of_pos hnum (Complex.normSq_pos.mpr hd)

theorem SpecialPeriods.Triangle.generatorTwo_sq_shift (z : ℍ) :
    (((generatorTwoSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) - (stripLeft : ℂ) =
      -(stripRight : ℂ) ^ 2 / ((z : ℂ) - (stripLeft : ℂ)) :=
  generatorTwo_sq_secondShift_mo1973_19728 z

theorem SpecialPeriods.Triangle.generatorTwo_shift_norm_le (z : ℍ) (hx : stripLeft ≤ z.re) :
    ‖((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight := by
  change ‖secondShift_mo1973_19721 (generatorTwoSL • z)‖ ≤ stripRight
  rw [generatorTwo_secondShift_mo1973_19727, mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 ≤ (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_nonneg.mpr hx
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (norm_sub_div_add_le_one_mo1973_19730 stripRight_pos hrez)
      stripRight_pos.le

theorem SpecialPeriods.Triangle.generatorTwo_shift_norm_lt (z : ℍ) (hx : stripLeft < z.re) :
    ‖((generatorTwoSL • z : ℍ) : ℂ) - (stripLeft : ℂ)‖ < stripRight := by
  change ‖secondShift_mo1973_19721 (generatorTwoSL • z)‖ < stripRight
  rw [generatorTwo_secondShift_mo1973_19727, mul_div_assoc, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos stripRight_pos]
  have hrez : 0 < (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_pos.mpr hx
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (norm_sub_div_add_lt_one_mo1973_19733 stripRight_pos hrez)
      stripRight_pos

theorem SpecialPeriods.Triangle.generatorTwo_sq_re_le_stripLeft (z : ℍ) (hx : stripLeft ≤ z.re) :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re ≤ stripLeft := by
  have hrez : 0 ≤ (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_nonneg.mpr hx
  have h := re_neg_sq_div_nonpos_mo1973_19732 (r := stripRight) hrez
  rw [← generatorTwo_sq_secondShift_mo1973_19728 z, secondShift_re_mo1973_19722] at h
  exact sub_nonpos.mp h

theorem SpecialPeriods.Triangle.generatorTwo_sq_re_lt_stripLeft (z : ℍ) (hx : stripLeft < z.re) :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re < stripLeft := by
  have hrez : 0 < (secondShift_mo1973_19721 z).re := by
    rw [secondShift_re_mo1973_19722]
    exact sub_pos.mpr hx
  have h := re_neg_sq_div_neg_mo1973_19735 stripRight_pos hrez
  rw [← generatorTwo_sq_secondShift_mo1973_19728 z, secondShift_re_mo1973_19722] at h
  exact sub_neg.mp h

theorem SpecialPeriods.Triangle.generatorTwo_cube_re_le_stripLeft (z : ℍ)
    (hn : stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖) :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re ≤ stripLeft := by
  have h : (secondShift_mo1973_19721 ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)).re ≤ 0 := by
    rw [generatorTwo_cube_secondShift_mo1973_19729, mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, MulZeroClass.zero_mul, sub_zero]
    exact
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr stripRight_pos.le)
        (re_add_div_sub_nonneg_mo1973_19731 stripRight_pos hn)
  rw [secondShift_re_mo1973_19722] at h
  exact sub_nonpos.mp h

theorem SpecialPeriods.Triangle.generatorTwo_closedSecondSector :
    Set.MapsTo (fun z : ℍ => generatorTwoSL • z) closedSecondSector secondWeakExcluded :=
  fun z hz => Or.inr (generatorTwo_shift_norm_le z hz.1)

theorem SpecialPeriods.Triangle.generatorTwo_sq_closedSecondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) closedSecondSector
      secondWeakExcluded :=
  fun z hz => Or.inl (generatorTwo_sq_re_le_stripLeft z hz.1)

theorem SpecialPeriods.Triangle.generatorTwo_cube_closedSecondSector :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) closedSecondSector
      secondWeakExcluded :=
  fun z hz => Or.inl (generatorTwo_cube_re_le_stripLeft z hz.2)

private theorem SpecialPeriods.Triangle.generatorOne_re_lower_of_one_le_norm_mo1973_19748 (z : ℍ)
    (hn : 1 ≤ ‖(z : ℂ)‖) : -(1 / 2) ≤ (generatorOneSL • z).re := by
  change -(1 / 2) ≤ (((generatorOneSL • z : ℍ) : ℂ)).re
  rw [generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, UpperHalfPlane.coe_re,
    Complex.one_re]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hsq : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  simp only [← neg_div]
  apply (le_div_iff₀ hd).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hsq ⊢
  nlinarith

private theorem SpecialPeriods.Triangle.re_lower_of_one_le_generatorOne_sq_norm_mo1973_19749
    (z : ℍ) (hn : 1 ≤ ‖(((generatorOneSL ^ 2) • z : ℍ) : ℂ)‖) : -(1 / 2) ≤ z.re := by
  rw [generatorOneSL_sq_smul_coe] at hn
  have he : (-1 : ℂ) - (z : ℂ)⁻¹ = -(((z : ℂ) + 1) / (z : ℂ)) := by
    field_simp [z.ne_zero]
    ring
  rw [he, norm_neg, norm_div] at hn
  have hnorm : ‖(z : ℂ)‖ ≤ ‖(z : ℂ) + 1‖ := (one_le_div (norm_pos_iff.mpr z.ne_zero)).mp hn
  have hsq := (sq_le_sq₀ (norm_nonneg (z : ℂ)) (norm_nonneg ((z : ℂ) + 1))).mpr hnorm
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hsq
  linarith

theorem SpecialPeriods.Triangle.generatorOne_sq_reflections (z : ℍ) :
    (generatorOneSL ^ 2) • z = circleReflection (rightReflection z) := by
  apply UpperHalfPlane.ext
  rw [generatorOneSL_sq_smul_coe, circleReflection_coe, rightReflection_coe]
  simp only [map_sub, map_neg, map_one, Complex.conj_conj]
  rw [show (-1 : ℂ) - (z : ℂ) + 1 = -(z : ℂ) by ring]
  simp [one_div, sub_eq_add_neg]

theorem SpecialPeriods.Triangle.generatorOne_closedFirst_return (z : ℍ)
    (hz : z ∈ closedFirstSector) (hw : generatorOneSL • z ∈ closedFirstSector) :
    generatorOneSL • z = circleReflection z := by
  have hx : (generatorOneSL • z).re = -(1 / 2) :=
    le_antisymm hw.1 (generatorOne_re_lower_of_one_le_norm_mo1973_19748 z hz.2)
  have hfix := (rightReflection_fixed_iff (generatorOneSL • z)).mpr hx
  calc
    generatorOneSL • z = rightReflection (generatorOneSL • z) := hfix.symm
    _ = circleReflection z := by rw [generatorOne_reflections, rightReflection_involutive]

theorem SpecialPeriods.Triangle.generatorOne_sq_closedFirst_return (z : ℍ)
    (hz : z ∈ closedFirstSector) (hw : (generatorOneSL ^ 2) • z ∈ closedFirstSector) :
    (generatorOneSL ^ 2) • z = circleReflection z := by
  have hx : z.re = -(1 / 2) :=
    le_antisymm hz.1 (re_lower_of_one_le_generatorOne_sq_norm_mo1973_19749 z hw.2)
  rw [generatorOne_sq_reflections, (rightReflection_fixed_iff z).mpr hx]

theorem SpecialPeriods.Triangle.generatorOne_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hw : generatorOneSL • z ∈ circularDoubleRegion) : generatorOneSL • z = circleReflection z :=
  generatorOne_closedFirst_return z hz.1 hw.1

theorem SpecialPeriods.Triangle.generatorOne_sq_closed_return (z : ℍ)
    (hz : z ∈ circularDoubleRegion) (hw : (generatorOneSL ^ 2) • z ∈ circularDoubleRegion) :
    (generatorOneSL ^ 2) • z = circleReflection z :=
  generatorOne_sq_closedFirst_return z hz.1 hw.1

private theorem SpecialPeriods.Triangle.eq_centerTwo_of_secondSector_boundaries_mo1973_19755
    (z : ℍ) (hr : z.re = stripLeft) (hn : ‖(z : ℂ) - (stripLeft : ℂ)‖ = stripRight) :
    z = centerTwo := by
  have hs := congrArg (fun r : ℝ => r ^ 2) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hr, sub_self, sub_zero, MulZeroClass.zero_mul,
    zero_add] at hs
  have hi : z.im = stripRight := by nlinarith [z.im_pos, stripRight_pos]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simpa only [UpperHalfPlane.coe_re, centerTwo_re, stripLeft] using hr
  · simpa only [UpperHalfPlane.coe_im, centerTwo_im, stripRight] using hi

private theorem SpecialPeriods.Triangle.generatorTwo_smul_cube_mo1973_19756 (z : ℍ) :
    generatorTwoSL • ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) = z := by
  rw [← SemigroupAction.mul_smul, ← pow_succ']
  change realSLPermutation (generatorTwoSL ^ 4) z = z
  rw [generatorTwoSL_fourth, realSLPermutation_neg_one]
  rfl

theorem SpecialPeriods.Triangle.generatorTwo_closedSecond_return (z : ℍ)
    (hz : z ∈ closedSecondSector) (hgz : generatorTwoSL • z ∈ closedSecondSector) :
    generatorTwoSL • z = circleReflection z := by
  have hr : z.re = stripLeft :=
    le_antisymm (le_of_not_gt fun h => (not_lt_of_ge hgz.2) (generatorTwo_shift_norm_lt z h)) hz.1
  rw [generatorTwo_reflections, (leftReflection_fixed_iff z).mpr hr]

theorem SpecialPeriods.Triangle.generatorTwo_sq_closedSecond_return_eq_centerTwo (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ closedSecondSector) : z = centerTwo := by
  have hr : z.re = stripLeft :=
    le_antisymm (le_of_not_gt fun h => (not_lt_of_ge hgz.1) (generatorTwo_sq_re_lt_stripLeft z h))
      hz.1
  have hn := hgz.2
  rw [generatorTwo_sq_shift, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos stripRight_pos] at hn
  have hp : 0 < ‖(z : ℂ) - (stripLeft : ℂ)‖ := stripRight_pos.trans_le hz.2
  have hle : ‖(z : ℂ) - (stripLeft : ℂ)‖ ≤ stripRight := by
    apply (mul_le_mul_iff_of_pos_left stripRight_pos).mp
    simpa only [pow_two] using (le_div_iff₀ hp).mp hn
  exact eq_centerTwo_of_secondSector_boundaries_mo1973_19755 z hr (le_antisymm hle hz.2)

theorem SpecialPeriods.Triangle.generatorTwo_sq_closedSecond_return (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    (generatorTwoSL ^ 2 : SL(2, ℝ)) • z = circleReflection z := by
  obtain rfl := generatorTwo_sq_closedSecond_return_eq_centerTwo z hz hgz
  have hl : leftReflection centerTwo = centerTwo :=
    (leftReflection_fixed_iff centerTwo).mpr centerTwo_re
  have hc : circleReflection centerTwo = centerTwo := by
    have h := generatorTwo_reflections centerTwo
    rw [generatorTwo_fix, hl] at h
    exact h.symm
  simp only [pow_two, SemigroupAction.mul_smul, generatorTwo_fix, hc]

theorem SpecialPeriods.Triangle.generatorTwo_cube_closedSecond_return (z : ℍ)
    (hz : z ∈ closedSecondSector)
    (hgz : (generatorTwoSL ^ 3 : SL(2, ℝ)) • z ∈ closedSecondSector) :
    (generatorTwoSL ^ 3 : SL(2, ℝ)) • z = circleReflection z := by
  have h :=
    generatorTwo_closedSecond_return ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z) hgz
      (by simpa only [generatorTwo_smul_cube_mo1973_19756] using hz)
  have hc := congrArg circleReflection h
  simpa only [generatorTwo_smul_cube_mo1973_19756,
    circleReflection_involutive ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z)] using hc.symm

theorem SpecialPeriods.Triangle.generatorTwo_closed_return (z : ℍ) (hz : z ∈ circularDoubleRegion)
    (hgz : generatorTwoSL • z ∈ circularDoubleRegion) : generatorTwoSL • z = circleReflection z :=
  generatorTwo_closedSecond_return z hz.2 hgz.2

theorem SpecialPeriods.Triangle.generatorTwo_sq_closed_return (z : ℍ)
    (hz : z ∈ circularDoubleRegion)
    (hgz : (generatorTwoSL ^ 2 : SL(2, ℝ)) • z ∈ circularDoubleRegion) :
    (generatorTwoSL ^ 2 : SL(2, ℝ)) • z = circleReflection z :=
  generatorTwo_sq_closedSecond_return z hz.2 hgz.2

theorem SpecialPeriods.Triangle.generatorTwo_cube_closed_return (z : ℍ)
    (hz : z ∈ circularDoubleRegion)
    (hgz : (generatorTwoSL ^ 3 : SL(2, ℝ)) • z ∈ circularDoubleRegion) :
    (generatorTwoSL ^ 3 : SL(2, ℝ)) • z = circleReflection z :=
  generatorTwo_cube_closedSecond_return z hz.2 hgz.2

theorem SpecialPeriods.Triangle.circleReflection_re (z : ℍ) :
    (circleReflection z).re = -1 + (z.re + 1) / Complex.normSq ((z : ℂ) + 1) := by
  change (-1 + 1 / (conj (z : ℂ) + 1)).re = _
  rw [show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp]
  simp only [one_div, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
    Complex.conj_re, Complex.normSq_conj, UpperHalfPlane.coe_re]

theorem SpecialPeriods.Triangle.circleReflection_re_le_neg_half_iff (z : ℍ) :
    (circleReflection z).re ≤ -(1 / 2) ↔ 1 ≤ ‖(z : ℂ)‖ := by
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  calc
    (circleReflection z).re ≤ -(1 / 2) ↔ (z.re + 1) / Complex.normSq ((z : ℂ) + 1) ≤ 1 / 2 := by
      rw [circleReflection_re]
      constructor <;> intro h <;> linarith
    _ ↔ z.re + 1 ≤ (1 / 2) * Complex.normSq ((z : ℂ) + 1) := (div_le_iff₀ hd)
    _ ↔ (1 : ℝ) ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.one_re,
        Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      constructor <;> intro h <;> nlinarith
    _ ↔ 1 ≤ ‖(z : ℂ)‖ := sq_le_sq₀ (by norm_num) (norm_nonneg _)

theorem SpecialPeriods.Triangle.one_le_circleReflection_norm_iff (z : ℍ) :
    1 ≤ ‖(circleReflection z : ℂ)‖ ↔ z.re ≤ -(1 / 2) := by
  simpa only [circleReflection_involutive z] using
    (circleReflection_re_le_neg_half_iff (circleReflection z)).symm

theorem SpecialPeriods.Triangle.circleReflection_re_ge_stripLeft_iff (z : ℍ) :
    stripLeft ≤ (circleReflection z).re ↔ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ := by
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hL : stripLeft = -stripRight - 1 := by linarith [stripLeft_add_stripRight]
  have he :
    stripRight * (‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2) =
      z.re + 1 + stripRight * Complex.normSq ((z : ℂ) + 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hL]
    linear_combination (2 * z.re + 2) * stripRight_sq
  calc
    stripLeft ≤ (circleReflection z).re ↔
        -stripRight ≤ (z.re + 1) / Complex.normSq ((z : ℂ) + 1) := by
      rw [circleReflection_re, hL]
      constructor <;> intro h <;> linarith
    _ ↔ -stripRight * Complex.normSq ((z : ℂ) + 1) ≤ z.re + 1 := (le_div_iff₀ hd)
    _ ↔ 0 ≤ z.re + 1 + stripRight * Complex.normSq ((z : ℂ) + 1) := by
      constructor <;> intro h <;> linarith
    _ ↔ 0 ≤ stripRight * (‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2) := by rw [he]
    _ ↔ 0 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 - stripRight ^ 2 :=
      (mul_nonneg_iff_of_pos_left stripRight_pos)
    _ ↔ stripRight ^ 2 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := sub_nonneg
    _ ↔ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ := sq_le_sq₀ stripRight_pos.le (norm_nonneg _)

theorem SpecialPeriods.Triangle.stripRight_le_circleReflection_sub_stripLeft_norm_iff (z : ℍ) :
    stripRight ≤ ‖(circleReflection z : ℂ) - (stripLeft : ℂ)‖ ↔ stripLeft ≤ z.re := by
  simpa only [circleReflection_involutive z] using
    (circleReflection_re_ge_stripLeft_iff (circleReflection z)).symm

@[simp]
theorem SpecialPeriods.Triangle.circleReflection_mem_closedFirstSector_iff (z : ℍ) :
    circleReflection z ∈ closedFirstSector ↔ z ∈ closedFirstSector := by
  change
    (circleReflection z).re ≤ -(1 / 2) ∧ 1 ≤ ‖(circleReflection z : ℂ)‖ ↔
      z.re ≤ -(1 / 2) ∧ 1 ≤ ‖(z : ℂ)‖
  rw [circleReflection_re_le_neg_half_iff, one_le_circleReflection_norm_iff, and_comm]

@[simp]
theorem SpecialPeriods.Triangle.circleReflection_mem_closedSecondSector_iff (z : ℍ) :
    circleReflection z ∈ closedSecondSector ↔ z ∈ closedSecondSector := by
  change
    stripLeft ≤ (circleReflection z).re ∧
        stripRight ≤ ‖(circleReflection z : ℂ) - (stripLeft : ℂ)‖ ↔
      stripLeft ≤ z.re ∧ stripRight ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖
  rw [circleReflection_re_ge_stripLeft_iff, stripRight_le_circleReflection_sub_stripLeft_norm_iff,
    and_comm]

@[simp]
theorem SpecialPeriods.Triangle.circleReflection_mem_circularDoubleRegion_iff (z : ℍ) :
    circleReflection z ∈ circularDoubleRegion ↔ z ∈ circularDoubleRegion := by
  simp only [circularDoubleRegion, Set.mem_inter_iff, circleReflection_mem_closedFirstSector_iff,
    circleReflection_mem_closedSecondSector_iff]

theorem SpecialPeriods.Triangle.circleReflection_mapsTo_circularDoubleRegion :
    Set.MapsTo circleReflection circularDoubleRegion circularDoubleRegion := fun z hz =>
  (circleReflection_mem_circularDoubleRegion_iff z).mpr hz

@[simp]
theorem SpecialPeriods.Triangle.circleReflection_add_one_norm (z : ℍ) :
    ‖(circleReflection z : ℂ) + 1‖ = 1 / ‖(z : ℂ) + 1‖ := by
  rw [circleReflection_coe]
  have he : (-1 : ℂ) + 1 / (conj (z : ℂ) + 1) + 1 = 1 / (conj (z : ℂ) + 1) := by ring
  rw [he, norm_div, NormOneClass.norm_one, show conj (z : ℂ) + 1 = conj ((z : ℂ) + 1) by simp,
    Complex.norm_conj]

theorem SpecialPeriods.Triangle.fordRegion_subset_closedSecondSector :
    fordRegion ⊆ closedSecondSector := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hn : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hprod : 0 ≤ stripRight * (z.re - stripLeft) :=
    mul_nonneg stripRight_pos.le (sub_nonneg.mpr hz.1)
  have hs : stripRight ^ 2 ≤ ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
    have hleft : stripLeft = -1 - stripRight := by linarith [stripLeft_add_stripRight]
    rw [hleft] at hprod ⊢
    nlinarith [stripRight_sq]
  exact (sq_le_sq₀ stripRight_pos.le (norm_nonneg _)).mp hs

theorem SpecialPeriods.Triangle.halfFordRegion_subset_circularDoubleRegion :
    halfFordRegion ⊆ circularDoubleRegion := by
  intro z hz
  exact ⟨⟨hz.2, hz.1.2.2.2⟩, fordRegion_subset_closedSecondSector hz.1⟩

theorem SpecialPeriods.Triangle.circularDoubleRegion_and_norm_add_one_iff_halfFordRegion (z : ℍ) :
    z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖ ↔ z ∈ halfFordRegion := by
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨⟨hz.2.1, ?_, hn, hz.1.2⟩, hz.1.1⟩
    linarith [hz.1.1, stripRight_pos]
  · intro hz
    exact ⟨halfFordRegion_subset_circularDoubleRegion hz, hz.1.2.2.1⟩

theorem SpecialPeriods.Triangle.halfFordRegion_eq_circularDoubleRegion_inter :
    halfFordRegion = circularDoubleRegion ∩ {z | 1 ≤ ‖(z : ℂ) + 1‖} := by
  ext z
  exact (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion z).symm

theorem SpecialPeriods.Triangle.fordRegion_left_mem_circularDoubleRegion (z : ℍ)
    (hz : z ∈ fordRegion) (hx : z.re ≤ -(1 / 2)) : z ∈ circularDoubleRegion :=
  halfFordRegion_subset_circularDoubleRegion ⟨hz, hx⟩

theorem SpecialPeriods.Triangle.circleReflection_image_halfFordRegion :
    circleReflection '' halfFordRegion = circularDoubleRegion ∩ {z | ‖(z : ℂ) + 1‖ ≤ 1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine
      ⟨circleReflection_mapsTo_circularDoubleRegion
          (halfFordRegion_subset_circularDoubleRegion hw),
        ?_⟩
    change ‖(circleReflection w : ℂ) + 1‖ ≤ 1
    rw [circleReflection_add_one_norm]
    exact (div_le_one (norm_pos_iff.mpr (denominatorOne_ne_zero w))).mpr hw.1.2.2.1
  · rintro ⟨hz, hn⟩
    refine ⟨circleReflection z, ?_, circleReflection_involutive z⟩
    apply (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion (circleReflection z)).mp
    refine ⟨circleReflection_mapsTo_circularDoubleRegion hz, ?_⟩
    rw [circleReflection_add_one_norm]
    exact (one_le_div (norm_pos_iff.mpr (denominatorOne_ne_zero z))).mpr hn

theorem SpecialPeriods.Triangle.circularDoubleRegion_eq_halfFordRegion_union_circle :
    circularDoubleRegion = halfFordRegion ∪ circleReflection '' halfFordRegion := by
  rw [circleReflection_image_halfFordRegion, halfFordRegion_eq_circularDoubleRegion_inter]
  ext z
  change
    z ∈ circularDoubleRegion ↔
      ((z ∈ circularDoubleRegion ∧ 1 ≤ ‖(z : ℂ) + 1‖) ∨
        (z ∈ circularDoubleRegion ∧ ‖(z : ℂ) + 1‖ ≤ 1))
  constructor
  · intro hz
    rcases le_total 1 ‖(z : ℂ) + 1‖ with hn | hn
    · exact Or.inl ⟨hz, hn⟩
    · exact Or.inr ⟨hz, hn⟩
  · rintro (hz | hz) <;> exact hz.1

theorem SpecialPeriods.Triangle.circleReflection_eq_self_of_halfFordRegion_mem (z : ℍ)
    (hz : z ∈ halfFordRegion) (hcz : circleReflection z ∈ halfFordRegion) :
    circleReflection z = z := by
  have hn : 1 ≤ ‖(circleReflection z : ℂ) + 1‖ := hcz.1.2.2.1
  rw [circleReflection_add_one_norm] at hn
  have hle := (one_le_div (norm_pos_iff.mpr (denominatorOne_ne_zero z))).mp hn
  exact (circleReflection_fixed_iff z).mpr (le_antisymm hle hz.1.2.2.1)

theorem SpecialPeriods.Triangle.generatorOne_inv_reflections (z : ℍ) :
    generatorOneSL⁻¹ • z = circleReflection (rightReflection z) := by
  have h : generatorOneSL • circleReflection (rightReflection z) = z := by
    rw [generatorOne_reflections, circleReflection_involutive, rightReflection_involutive]
  simpa only [inv_smul_smul] using congrArg (fun w : ℍ => generatorOneSL⁻¹ • w) h.symm

private theorem SpecialPeriods.lift_neWord_weak_to_strict_mo1973_19793 {ι G α : Type*} [Group G]
    [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (X W : ι → Set α)
    (hXW : ∀ i, X i ⊆ W i) (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    {i j k : ι} (w : Monoid.CoprodI.NeWord H i j) (hk : j ≠ k) :
    Monoid.CoprodI.lift f w.prod • W k ⊆ X i := by
  induction w generalizing k with
  | singleton x hx => simpa using hcross hk x hx
  | @append i j m l w₁ hne w₂ ih₁
    ih₂ =>
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, SemigroupAction.mul_smul]
    exact (Set.smul_set_subset_smul_set_iff.mpr ((ih₂ hk).trans (hXW m))).trans (ih₁ hne)

private theorem SpecialPeriods.lift_neWord_closed_domain_subset_mo1973_19794 {ι G α : Type*}
    [Group G] [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G)
    (X W : ι → Set α) (D : Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i) {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f w.prod • D ⊆ W i := by
  induction w with
  | singleton x hx => simpa using hD _ x hx
  | @append i j k l w₁ hne w₂ _ih₁
    ih₂ =>
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, SemigroupAction.mul_smul]
    exact
      (Set.smul_set_subset_smul_set_iff.mpr ih₂).trans
        ((lift_neWord_weak_to_strict_mo1973_19793 f X W hXW hcross w₁ hne).trans (hXW i))

private theorem SpecialPeriods.lift_neWord_factor_or_strict_mo1973_19795 {ι G α : Type*} [Group G]
    [MulAction G α] {H : ι → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (X W : ι → Set α)
    (D : Set α) (hXW : ∀ i, X i ⊆ W i)
    (hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ X i)
    (hD : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i) {i j : ι} (w : Monoid.CoprodI.NeWord H i j) :
    (∃ x : H i, w.prod = Monoid.CoprodI.of x) ∨ Monoid.CoprodI.lift f w.prod • D ⊆ X i := by
  cases w with
  | singleton x hx => exact Or.inl ⟨x, Monoid.CoprodI.NeWord.prod_singleton x hx⟩
  | @append i j k l w₁ hne w₂ =>
    right
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, SemigroupAction.mul_smul]
    exact
      (Set.smul_set_subset_smul_set_iff.mpr
            (lift_neWord_closed_domain_subset_mo1973_19794 f X W D hXW hcross hD w₂)).trans
        (lift_neWord_weak_to_strict_mo1973_19793 f X W hXW hcross w₁ hne)

private theorem SpecialPeriods.gluing_cyclicPowerHom_two_mo1973_19796 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem SpecialPeriods.gluing_cyclicPowerHom_three_mo1973_19797 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

private theorem SpecialPeriods.cyclicThree_closed_subset_mo1973_19798 {G α : Type*} [Group G]
    [MulAction G α] (a : G) (ha : a ^ 3 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => a • z) S T)
    (h₂ : Set.MapsTo (fun z => a ^ 2 • z) S T) (g : Multiplicative (ZMod 3)) (hg : g ≠ 1) :
    cyclicPowerHom 3 a ha g • S ⊆ T := by
  have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 3),
          x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
      g hg
  rcases hc with rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [gluing_cyclicPowerHom_two_mo1973_19796]
    exact Set.smul_set_subset_iff.mpr h₂

private theorem SpecialPeriods.cyclicFour_closed_subset_mo1973_19799 {G α : Type*} [Group G]
    [MulAction G α] (b : G) (hb : b ^ 4 = 1) (S T : Set α) (h₁ : Set.MapsTo (fun z => b • z) S T)
    (h₂ : Set.MapsTo (fun z => b ^ 2 • z) S T) (h₃ : Set.MapsTo (fun z => b ^ 3 • z) S T)
    (g : Multiplicative (ZMod 4)) (hg : g ≠ 1) : cyclicPowerHom 4 b hb g • S ⊆ T := by
  have hc :
    g = Multiplicative.ofAdd (1 : ZMod 4) ∨
      g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) :=
    (by decide :
        ∀ x : Multiplicative (ZMod 4),
          x ≠ 1 →
            x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
      g hg
  rcases hc with rfl | rfl | rfl
  · rw [cyclicPowerHom_one]
    exact Set.smul_set_subset_iff.mpr h₁
  · rw [gluing_cyclicPowerHom_two_mo1973_19796]
    exact Set.smul_set_subset_iff.mpr h₂
  · rw [gluing_cyclicPowerHom_three_mo1973_19797]
    exact Set.smul_set_subset_iff.mpr h₃

private theorem SpecialPeriods.cyclic_eq_generator_pow_val_mo1973_19800 {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) : x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem SpecialPeriods.triangleLift_eq_generator_pow_of_closed_domain_mem {G α : Type*} [Group G]
    [MulAction G α] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y XB YB D : Set α)
    (hXXB : X ⊆ XB) (hYYB : Y ⊆ YB) (ha₁ : Set.MapsTo (fun z => a • z) YB X)
    (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) YB X) (hb₁ : Set.MapsTo (fun z => b • z) XB Y)
    (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) XB Y) (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) XB Y)
    (hDa₁ : Set.MapsTo (fun z => a • z) D XB) (hDa₂ : Set.MapsTo (fun z => a ^ 2 • z) D XB)
    (hDb₁ : Set.MapsTo (fun z => b • z) D YB) (hDb₂ : Set.MapsTo (fun z => b ^ 2 • z) D YB)
    (hDb₃ : Set.MapsTo (fun z => b ^ 3 • z) D YB) (hDX : Disjoint D X) (hDY : Disjoint D Y)
    (g : TriangleGroup) {z : α} (hz : z ∈ D) (hgz : triangleLift a b ha hb g • z ∈ D) :
    (∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n) := by
  classical
  by_cases hg : g = 1
  · exact Or.inl ⟨0, by decide, by simpa using hg⟩
  let H : Bool → Type := fun i => cond i (Multiplicative (ZMod 4)) (Multiplicative (ZMod 3))
  let : ∀ i, Group (H i) :=
    Bool.rec (inferInstance : Group (Multiplicative (ZMod 3)))
      (inferInstance : Group (Multiplicative (ZMod 4)))
  let f : ∀ i, H i →* G := fun i =>
    match i with
    | false => cyclicPowerHom 3 a ha
    | true => cyclicPowerHom 4 b hb
  let toI : TriangleGroup →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* TriangleGroup :=
    Monoid.CoprodI.lift fun i =>
      match i with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id TriangleGroup := by
    apply triangle_hom_ext
    · simp [toI, fromI, triangleGenerator₁]
    · simp [toI, fromI, triangleGenerator₂]
  have hto_ne : toI g ≠ 1 := by
    intro h
    apply hg
    calc
      g = fromI (toI g) := (DFunLike.congr_fun hleft g).symm
      _ = 1 := by rw [h, map_one]
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  let W : Bool → Set α := fun i => cond i YB XB
  have hUW : ∀ i, U i ⊆ W i := by
    intro i
    cases i
    · exact hXXB
    · exact hYYB
  have hcross : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • W j ⊆ U i := by
    intro i j hij h hh
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact cyclicThree_closed_subset_mo1973_19798 a ha YB X ha₁ ha₂ h hh
    · exact cyclicFour_closed_subset_mo1973_19799 b hb XB Y hb₁ hb₂ hb₃ h hh
    · exact (hij rfl).elim
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • D ⊆ W i := by
    intro i h hh
    cases i
    · exact cyclicThree_closed_subset_mo1973_19798 a ha D XB hDa₁ hDa₂ h hh
    · exact cyclicFour_closed_subset_mo1973_19799 b hb D YB hDb₁ hDb₂ hDb₃ h hh
  let : (i : Bool) → DecidableEq (H i) := fun _ => Classical.decEq _
  let r := Monoid.CoprodI.Word.equiv (M := H) (toI g)
  have hr : r.prod = toI g := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply (toI g)
  have hr_ne : r ≠ Monoid.CoprodI.Word.empty := by
    intro h
    apply hto_ne
    rw [← hr, h, Monoid.CoprodI.Word.prod_empty]
  obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word r hr_ne
  have hwprod : w.prod = toI g := by
    change w.toWord.prod = toI g
    rw [hw]
    exact hr
  rcases lift_neWord_factor_or_strict_mo1973_19795 f U W D hUW hcross hstart w with ⟨x, hx⟩ |
    himage
  · have hfrom : fromI (Monoid.CoprodI.of x) = g := by
      rw [← hx, hwprod]
      exact DFunLike.congr_fun hleft g
    cases i
    · left
      refine ⟨x.toAdd.val, ZMod.val_lt x.toAdd, ?_⟩
      calc
        g = Monoid.Coprod.inl x := by simpa [fromI] using hfrom.symm
        _ = triangleGenerator₁ ^ x.toAdd.val := by
          rw [triangleGenerator₁, ← map_pow]
          exact congrArg Monoid.Coprod.inl (cyclic_eq_generator_pow_val_mo1973_19800 x)
    · right
      refine ⟨x.toAdd.val, ZMod.val_lt x.toAdd, ?_⟩
      calc
        g = Monoid.Coprod.inr x := by simpa [fromI] using hfrom.symm
        _ = triangleGenerator₂ ^ x.toAdd.val := by
          rw [triangleGenerator₂, ← map_pow]
          exact congrArg Monoid.Coprod.inr (cyclic_eq_generator_pow_val_mo1973_19800 x)
  · have heval : triangleLift a b ha hb g = Monoid.CoprodI.lift f (toI g) :=
      DFunLike.congr_fun hrepresentation g
    have hstrict : triangleLift a b ha hb g • z ∈ U i := by
      rw [heval, ← hwprod]
      exact Set.smul_set_subset_iff.mp himage hz
    cases i
    · exact (hDX.le_bot ⟨hgz, hstrict⟩).elim
    · exact (hDY.le_bot ⟨hgz, hstrict⟩).elim

theorem SpecialPeriods.Triangle.circularDoubleRegion_return_generator_pow
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ circularDoubleRegion)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ circularDoubleRegion) :
    (∃ n : ℕ, n < 3 ∧ g = SpecialPeriods.triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = SpecialPeriods.triangleGenerator₂ ^ n) := by
  exact
    SpecialPeriods.triangleLift_eq_generator_pow_of_closed_domain_mem generatorOnePerm
      generatorTwoPerm generatorOnePerm_cube generatorTwoPerm_fourth firstExcluded secondExcluded
      firstWeakExcluded secondWeakExcluded circularDoubleRegion
      firstExcluded_subset_firstWeakExcluded secondExcluded_subset_secondWeakExcluded
      (fun _ hw => generatorOnePerm_firstSector (secondWeakExcluded_subset_firstSector hw))
      (fun _ hw => generatorOnePerm_sq_firstSector (secondWeakExcluded_subset_firstSector hw))
      (fun _ hw => generatorTwoPerm_secondSector (firstWeakExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_sq_secondSector (firstWeakExcluded_subset_secondSector hw))
      (fun _ hw => generatorTwoPerm_cube_secondSector (firstWeakExcluded_subset_secondSector hw))
      (fun _ hw => generatorOne_closedFirstSector hw.1)
      (fun z hw => by
        change (generatorOnePerm ^ 2) z ∈ firstWeakExcluded
        rw [generatorOnePerm_pow_apply]
        exact generatorOne_sq_closedFirstSector hw.1)
      (fun _ hw => generatorTwo_closedSecondSector hw.2)
      (fun z hw => by
        change (generatorTwoPerm ^ 2) z ∈ secondWeakExcluded
        rw [generatorTwoPerm_pow_apply]
        exact generatorTwo_sq_closedSecondSector hw.2)
      (fun z hw => by
        change (generatorTwoPerm ^ 3) z ∈ secondWeakExcluded
        rw [generatorTwoPerm_pow_apply]
        exact generatorTwo_cube_closedSecondSector hw.2)
      circularDoubleRegion_disjoint_firstExcluded circularDoubleRegion_disjoint_secondExcluded g
      hz hgz

theorem SpecialPeriods.Triangle.circularDoubleRegion_orbit_point
    (g : SpecialPeriods.TriangleGroup) {z : ℍ} (hz : z ∈ circularDoubleRegion)
    (hgz : SpecialPeriods.triangleGeometricRepresentation g z ∈ circularDoubleRegion) :
    SpecialPeriods.triangleGeometricRepresentation g z = z ∨
      SpecialPeriods.triangleGeometricRepresentation g z = circleReflection z := by
  rcases circularDoubleRegion_return_generator_pow g hz hgz with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · simp only [map_pow, SpecialPeriods.triangleGeometricRepresentation_generator₁,
      generatorOnePerm_pow_apply] at hgz ⊢
    interval_cases n
    · exact Or.inl (by simp)
    · right
      simp only [pow_one] at hgz ⊢
      exact generatorOne_closed_return z hz hgz
    · exact Or.inr (generatorOne_sq_closed_return z hz hgz)
  · simp only [map_pow, SpecialPeriods.triangleGeometricRepresentation_generator₂,
      generatorTwoPerm_pow_apply] at hgz ⊢
    interval_cases n
    · exact Or.inl (by simp)
    · right
      simp only [pow_one] at hgz ⊢
      exact generatorTwo_closed_return z hz hgz
    · exact Or.inr (generatorTwo_sq_closed_return z hz hgz)
    · exact Or.inr (generatorTwo_cube_closed_return z hz hgz)

theorem SpecialPeriods.Triangle.circularDoubleRegion_orbit_point_of_eq
    (g : SpecialPeriods.TriangleGroup) {z w : ℍ} (hz : z ∈ circularDoubleRegion)
    (hw : w ∈ circularDoubleRegion)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) :
    w = z ∨ w = circleReflection z := by
  simpa only [hzw] using circularDoubleRegion_orbit_point g hz (hzw ▸ hw)

private def SpecialPeriods.Triangle.circularHalfPoint_mo1973_19807 (z : ℍ) : ℍ := by
  classical exact if 1 ≤ ‖(z : ℂ) + 1‖ then z else circleReflection z

private theorem SpecialPeriods.Triangle.circularHalfPoint_of_half_mo1973_19808 {z : ℍ}
    (hz : z ∈ halfFordRegion) : circularHalfPoint_mo1973_19807 z = z := by
  simp only [circularHalfPoint_mo1973_19807, if_pos hz.1.2.2.1]

private theorem SpecialPeriods.Triangle.circularHalfPoint_circle_of_half_mo1973_19809 {z : ℍ}
    (hz : z ∈ halfFordRegion) : circularHalfPoint_mo1973_19807 (circleReflection z) = z := by
  by_cases hn : 1 ≤ ‖(circleReflection z : ℂ) + 1‖
  · rw [circularHalfPoint_mo1973_19807, if_pos hn]
    apply circleReflection_eq_self_of_halfFordRegion_mem z hz
    exact
      (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion _).mp
        ⟨circleReflection_mapsTo_circularDoubleRegion
            (halfFordRegion_subset_circularDoubleRegion hz),
          hn⟩
  · rw [circularHalfPoint_mo1973_19807, if_neg hn, circleReflection_involutive z]

private theorem SpecialPeriods.Triangle.circularHalfPoint_circle_mo1973_19810 {z : ℍ}
    (hz : z ∈ circularDoubleRegion) :
    circularHalfPoint_mo1973_19807 (circleReflection z) = circularHalfPoint_mo1973_19807 z := by
  rw [circularDoubleRegion_eq_halfFordRegion_union_circle] at hz
  rcases hz with hz | ⟨w, hw, rfl⟩
  · rw [circularHalfPoint_circle_of_half_mo1973_19809 hz,
      circularHalfPoint_of_half_mo1973_19808 hz]
  · rw [circleReflection_involutive w, circularHalfPoint_of_half_mo1973_19808 hw,
      circularHalfPoint_circle_of_half_mo1973_19809 hw]

private def SpecialPeriods.Triangle.fordHalfPoint_mo1973_19811 (z : ℍ) : ℍ := by
  classical exact if z.re ≤ -(1 / 2) then z else rightReflection z

private theorem SpecialPeriods.Triangle.fordHalfPoint_mem_mo1973_19812 {z : ℍ}
    (hz : z ∈ fordRegion) : fordHalfPoint_mo1973_19811 z ∈ halfFordRegion := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordHalfPoint_mo1973_19811, if_pos hx]
    exact ⟨hz, hx⟩
  · rw [fordHalfPoint_mo1973_19811, if_neg hx]
    refine ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩
    change (rightReflection z).re ≤ -(1 / 2)
    rw [rightReflection_re]
    have hh := lt_of_not_ge hx
    linarith

private theorem SpecialPeriods.Triangle.eq_or_reflection_of_fordHalfPoint_eq_mo1973_19813
    {z w : ℍ} (h : fordHalfPoint_mo1973_19811 w = fordHalfPoint_mo1973_19811 z) :
    w = z ∨ w = rightReflection z := by
  by_cases hz : z.re ≤ -(1 / 2) <;> by_cases hw : w.re ≤ -(1 / 2)
  · left
    simpa only [fordHalfPoint_mo1973_19811, if_pos hz, if_pos hw] using h
  · right
    have hh : rightReflection w = z := by
      simpa only [fordHalfPoint_mo1973_19811, if_pos hz, if_neg hw] using h
    have he := congrArg rightReflection hh
    simpa only [rightReflection_involutive w] using he
  · right
    simpa only [fordHalfPoint_mo1973_19811, if_neg hz, if_pos hw] using h
  · left
    apply rightReflection.injective
    simpa only [fordHalfPoint_mo1973_19811, if_neg hz, if_neg hw] using h

private def SpecialPeriods.Triangle.fordCircularNormalizer_mo1973_19814 (z : ℍ) :
    SpecialPeriods.TriangleGroup := by
  classical exact if z.re ≤ -(1 / 2) then 1 else SpecialPeriods.triangleGenerator₁⁻¹

private def SpecialPeriods.Triangle.fordCircularPoint_mo1973_19815 (z : ℍ) : ℍ :=
  SpecialPeriods.triangleGeometricRepresentation (fordCircularNormalizer_mo1973_19814 z) z

private theorem SpecialPeriods.Triangle.generatorOne_inv_representation_apply_mo1973_19816
    (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z =
      generatorOneSL⁻¹ • z := by
  rw [map_inv, SpecialPeriods.triangleGeometricRepresentation_generator₁]
  change (realSLPermutation generatorOneSL)⁻¹ z = _
  rw [← map_inv]
  rfl

private theorem SpecialPeriods.Triangle.fordCircularPoint_of_left_mo1973_19817 {z : ℍ}
    (hz : z.re ≤ -(1 / 2)) : fordCircularPoint_mo1973_19815 z = z := by
  rw [fordCircularPoint_mo1973_19815, fordCircularNormalizer_mo1973_19814, if_pos hz, map_one]
  rfl

private theorem SpecialPeriods.Triangle.fordCircularPoint_of_right_mo1973_19818 {z : ℍ}
    (hz : ¬z.re ≤ -(1 / 2)) :
    fordCircularPoint_mo1973_19815 z = circleReflection (rightReflection z) := by
  rw [fordCircularPoint_mo1973_19815, fordCircularNormalizer_mo1973_19814, if_neg hz,
    generatorOne_inv_representation_apply_mo1973_19816, generatorOne_inv_reflections]

private theorem SpecialPeriods.Triangle.fordCircularPoint_mem_mo1973_19819 {z : ℍ}
    (hz : z ∈ fordRegion) : fordCircularPoint_mo1973_19815 z ∈ circularDoubleRegion := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordCircularPoint_of_left_mo1973_19817 hx]
    exact fordRegion_left_mem_circularDoubleRegion z hz hx
  · rw [fordCircularPoint_of_right_mo1973_19818 hx]
    apply circleReflection_mapsTo_circularDoubleRegion
    have hh := fordHalfPoint_mem_mo1973_19812 hz
    rw [fordHalfPoint_mo1973_19811, if_neg hx] at hh
    exact halfFordRegion_subset_circularDoubleRegion hh

private theorem SpecialPeriods.Triangle.circularHalfPoint_fordCircularPoint_mo1973_19820 {z : ℍ}
    (hz : z ∈ fordRegion) :
    circularHalfPoint_mo1973_19807 (fordCircularPoint_mo1973_19815 z) =
      fordHalfPoint_mo1973_19811 z := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordCircularPoint_of_left_mo1973_19817 hx, fordHalfPoint_mo1973_19811, if_pos hx]
    exact circularHalfPoint_of_half_mo1973_19808 ⟨hz, hx⟩
  · rw [fordCircularPoint_of_right_mo1973_19818 hx, fordHalfPoint_mo1973_19811, if_neg hx]
    apply circularHalfPoint_circle_of_half_mo1973_19809
    have hh := fordHalfPoint_mem_mo1973_19812 hz
    simpa only [fordHalfPoint_mo1973_19811, if_neg hx] using hh

private theorem SpecialPeriods.Triangle.fordHalfPoint_eq_of_orbit_mo1973_19821
    (g : SpecialPeriods.TriangleGroup) {z w : ℍ} (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) :
    fordHalfPoint_mo1973_19811 w = fordHalfPoint_mo1973_19811 z := by
  let h : SpecialPeriods.TriangleGroup :=
    fordCircularNormalizer_mo1973_19814 w * g * (fordCircularNormalizer_mo1973_19814 z)⁻¹
  have he :
    SpecialPeriods.triangleGeometricRepresentation h (fordCircularPoint_mo1973_19815 z) =
      fordCircularPoint_mo1973_19815 w := by
    dsimp only [h, fordCircularPoint_mo1973_19815]
    rw [map_mul, map_mul, map_inv]
    change
      SpecialPeriods.triangleGeometricRepresentation (fordCircularNormalizer_mo1973_19814 w)
          (SpecialPeriods.triangleGeometricRepresentation g
            ((SpecialPeriods.triangleGeometricRepresentation
                  (fordCircularNormalizer_mo1973_19814 z)).symm
              (SpecialPeriods.triangleGeometricRepresentation
                (fordCircularNormalizer_mo1973_19814 z) z))) =
        _
    rw [(SpecialPeriods.triangleGeometricRepresentation
            (fordCircularNormalizer_mo1973_19814 z)).symm_apply_apply
        z,
      hzw]
  have hor :=
    circularDoubleRegion_orbit_point_of_eq h (fordCircularPoint_mem_mo1973_19819 hz)
      (fordCircularPoint_mem_mo1973_19819 hw) he
  have hh :
    circularHalfPoint_mo1973_19807 (fordCircularPoint_mo1973_19815 w) =
      circularHalfPoint_mo1973_19807 (fordCircularPoint_mo1973_19815 z) := by
    rcases hor with hor | hor
    · exact congrArg circularHalfPoint_mo1973_19807 hor
    · rw [hor, circularHalfPoint_circle_mo1973_19810 (fordCircularPoint_mem_mo1973_19819 hz)]
  rwa [circularHalfPoint_fordCircularPoint_mo1973_19820 hw,
    circularHalfPoint_fordCircularPoint_mo1973_19820 hz] at hh

theorem SpecialPeriods.Triangle.fordRegion_orbit_point_of_eq (g : SpecialPeriods.TriangleGroup)
    {z w : ℍ} (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (hzw : SpecialPeriods.triangleGeometricRepresentation g z = w) :
    w = z ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  rcases
    eq_or_reflection_of_fordHalfPoint_eq_mo1973_19813
      (fordHalfPoint_eq_of_orbit_mo1973_19821 g hz hw hzw) with
    he | he
  · exact Or.inl he
  · by_cases hwz : w = z
    · exact Or.inl hwz
    · refine Or.inr ⟨he, ?_⟩
      intro hi
      have hwi : w ∈ fordInterior := he ▸ rightReflection_mapsTo_fordInterior hi
      have hg := eq_one_of_fordInterior_eq g hi hwi hzw
      apply hwz
      rw [hg, map_one] at hzw
      exact hzw.symm

theorem SpecialPeriods.Triangle.fordRegion_boundary_cases {z : ℍ} (hz : z ∈ fordRegion)
    (hi : z ∉ fordInterior) :
    z.re = stripLeft ∨ z.re = stripRight ∨ ‖(z : ℂ) + 1‖ = 1 ∨ ‖(z : ℂ)‖ = 1 := by
  by_cases hl : stripLeft < z.re
  · by_cases hr : z.re < stripRight
    · by_cases hc : 1 < ‖(z : ℂ) + 1‖
      · right; right; right
        apply le_antisymm _ hz.2.2.2
        apply le_of_not_gt
        intro hn
        exact hi ⟨hl, hr, hc, hn⟩
      · exact Or.inr (Or.inr (Or.inl (le_antisymm (le_of_not_gt hc) hz.2.2.1)))
    · exact Or.inr (Or.inl (le_antisymm hz.2.1 (le_of_not_gt hr)))
  · exact Or.inl (le_antisymm (le_of_not_gt hl) hz.1)

private theorem SpecialPeriods.Triangle.orbitProjection_rightReflection_of_right_side_mo1973_19825
    {z : ℍ} (hz : z.re = stripRight) :
    SpecialPeriods.triangleOrbitProjection (rightReflection z) =
      SpecialPeriods.triangleOrbitProjection z := by
  have h := SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleCuspGenerator z
  rw [SpecialPeriods.triangleGeometricRepresentation_cusp] at h
  change
    SpecialPeriods.triangleOrbitProjection (cuspSL • z) =
      SpecialPeriods.triangleOrbitProjection z at h
  rwa [cusp_eq_rightReflection_of_re_eq_stripRight z hz] at h

theorem SpecialPeriods.Triangle.orbitProjection_rightReflection_boundary {z : ℍ}
    (hz : z ∈ fordRegion) (hi : z ∉ fordInterior) :
    SpecialPeriods.triangleOrbitProjection (rightReflection z) =
      SpecialPeriods.triangleOrbitProjection z := by
  rcases fordRegion_boundary_cases hz hi with hl | hr | hc | hn
  · have hr' : (rightReflection z).re = stripRight :=
      (rightReflection_re_eq_stripRight_iff z).mpr hl
    have h := orbitProjection_rightReflection_of_right_side_mo1973_19825 hr'
    rw [rightReflection_involutive z] at h
    exact h.symm
  · exact orbitProjection_rightReflection_of_right_side_mo1973_19825 hr
  · have h := SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleGenerator₁ z
    rwa [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      generatorOne_eq_rightReflection_of_norm_add_one z hc] at h
  · have h := SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleGenerator₁⁻¹ z
    rwa [generatorOne_inv_representation_apply_mo1973_19816,
      generatorOne_inv_eq_rightReflection_of_norm z hn] at h

theorem SpecialPeriods.Triangle.orbitProjection_eq_iff_fordRegion {z w : ℍ} (hz : z ∈ fordRegion)
    (hw : w ∈ fordRegion) :
    SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitProjection w ↔
      z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp h.symm
    rcases fordRegion_orbit_point_of_eq g hz hw hg with he | he
    · exact Or.inl he.symm
    · exact Or.inr he
  · rintro (rfl | ⟨he, hi⟩)
    · rfl
    · rw [he]
      exact (orbitProjection_rightReflection_boundary hz hi).symm

theorem TriangleUniformizationGluing.exists_fordRepresentative
    (q : SpecialPeriods.TriangleOrbitSpace) :
    ∃ z : ℍ,
      z ∈ SpecialPeriods.Triangle.fordRegion ∧ SpecialPeriods.triangleOrbitProjection z = q := by
  obtain ⟨u, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  obtain ⟨g, hg⟩ := SpecialPeriods.triangle_exists_fordRegion_representative u
  exact
    ⟨SpecialPeriods.triangleGeometricRepresentation g u, hg,
      SpecialPeriods.triangleOrbitProjection_smul g u⟩

def TriangleUniformizationGluing.fordRepresentative (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.Triangle.fordRegion :=
  ⟨Classical.choose (exists_fordRepresentative q),
    (Classical.choose_spec (exists_fordRepresentative q)).1⟩

@[simp]
theorem TriangleUniformizationGluing.fordRepresentative_projection
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOrbitProjection (fordRepresentative q) = q :=
  (Classical.choose_spec (exists_fordRepresentative q)).2

theorem TriangleUniformizationGluing.BoundaryMap.foldedFordMap_eq_of_projection_eq
    (D : TriangleUniformizationGluing.BoundaryMap) {z w : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) (hw : w ∈ SpecialPeriods.Triangle.fordRegion)
    (he : SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitProjection w) :
    D.foldedFordMap z = D.foldedFordMap w := by
  rcases (SpecialPeriods.Triangle.orbitProjection_eq_iff_fordRegion hz hw).mp he with rfl |
    ⟨hr, hi⟩
  · rfl
  · rw [hr, D.foldedFordMap_rightReflection_boundary hz hi]

def TriangleUniformizationGluing.BoundaryMap.quotientMap
    (D : TriangleUniformizationGluing.BoundaryMap) (q : SpecialPeriods.TriangleOrbitSpace) : ℂ :=
  D.foldedFordMap (TriangleUniformizationGluing.fordRepresentative q)

theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_projection
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) :
    D.quotientMap (SpecialPeriods.triangleOrbitProjection z) = D.foldedFordMap z :=
  D.foldedFordMap_eq_of_projection_eq (TriangleUniformizationGluing.fordRepresentative _).property
    hz (TriangleUniformizationGluing.fordRepresentative_projection _)

def TriangleUniformizationGluing.BoundaryMap.upstairsMap
    (D : TriangleUniformizationGluing.BoundaryMap) (z : ℍ) : ℂ :=
  D.quotientMap (SpecialPeriods.triangleOrbitProjection z)

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_of_mem
    (D : TriangleUniformizationGluing.BoundaryMap) {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) : D.upstairsMap z = D.foldedFordMap z :=
  D.quotientMap_projection z hz

@[simp]
theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_smul
    (D : TriangleUniformizationGluing.BoundaryMap) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    D.upstairsMap (SpecialPeriods.triangleGeometricRepresentation g z) = D.upstairsMap z := by
  change
    D.quotientMap
        (SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.triangleGeometricRepresentation g z)) =
      _
  rw [SpecialPeriods.triangleOrbitProjection_smul]
  rfl

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_eqOn_translate
    (D : TriangleUniformizationGluing.BoundaryMap) (g : SpecialPeriods.TriangleGroup) :
    Set.EqOn D.upstairsMap
      (fun z => D.foldedFordMap (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
      (SpecialPeriods.triangleGeometricRepresentation g '' SpecialPeriods.Triangle.fordRegion) := by
  rintro z ⟨w, hw, rfl⟩
  change
    D.upstairsMap (SpecialPeriods.triangleGeometricRepresentation g w) =
      D.foldedFordMap
        (SpecialPeriods.triangleGeometricRepresentation g⁻¹
          (SpecialPeriods.triangleGeometricRepresentation g w))
  rw [D.upstairsMap_smul, map_inv]
  change
    D.upstairsMap w =
      D.foldedFordMap
        ((SpecialPeriods.triangleGeometricRepresentation g).symm
          (SpecialPeriods.triangleGeometricRepresentation g w))
  rw [(SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply w,
    D.upstairsMap_of_mem hw]

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_continuousOn_translate
    (D : TriangleUniformizationGluing.BoundaryMap) (g : SpecialPeriods.TriangleGroup) :
    ContinuousOn D.upstairsMap
      (SpecialPeriods.triangleGeometricRepresentation g '' SpecialPeriods.Triangle.fordRegion) := by
  have hc : Continuous (SpecialPeriods.triangleGeometricRepresentation g⁻¹ : ℍ → ℍ) :=
    (SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹).continuous
  have hm :
    Set.MapsTo (SpecialPeriods.triangleGeometricRepresentation g⁻¹)
      (SpecialPeriods.triangleGeometricRepresentation g '' SpecialPeriods.Triangle.fordRegion)
      SpecialPeriods.Triangle.fordRegion := by
    rintro z ⟨w, hw, rfl⟩
    rw [map_inv]
    change
      (SpecialPeriods.triangleGeometricRepresentation g).symm
          (SpecialPeriods.triangleGeometricRepresentation g w) ∈
        _
    rw [(SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply w]
    exact hw
  exact
    (D.foldedFordMap_continuousOn.comp hc.continuousOn hm).congr (D.upstairsMap_eqOn_translate g)

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_continuous
    (D : TriangleUniformizationGluing.BoundaryMap) : Continuous D.upstairsMap := by
  apply
    SpecialPeriods.Triangle.fordRegion_translates_locallyFinite.continuous
      SpecialPeriods.triangle_translates_fordRegion_cover
  · intro g
    have h :=
      (SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph.isClosedMap
        SpecialPeriods.Triangle.fordRegion SpecialPeriods.Triangle.fordRegion_closed
    have he :
      ((SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph : ℍ → ℍ) =
        SpecialPeriods.triangleGeometricRepresentation g :=
      rfl
    rwa [he] at h
  · exact D.upstairsMap_continuousOn_translate

theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_continuous
    (D : TriangleUniformizationGluing.BoundaryMap) : Continuous D.quotientMap := by
  apply SpecialPeriods.triangleOrbitProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  exact D.upstairsMap_continuous

abbrev TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    SpecialPeriods.TriangleOrbitSpace → ℂ :=
  D.toBoundaryMap.quotientMap

abbrev TriangleUniformizationGluing.SignedHalfPlaneMap.upstairsMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : ℍ → ℂ :=
  D.toBoundaryMap.upstairsMap

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_continuous
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Continuous D.quotientMap :=
  D.toBoundaryMap.quotientMap_continuous

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_surjective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Function.Surjective D.quotientMap := by
  intro w
  obtain ⟨z, hz, he⟩ := D.foldedFordMap_surjOn (Set.mem_univ w)
  refine ⟨SpecialPeriods.triangleOrbitProjection z, ?_⟩
  change D.toBoundaryMap.quotientMap (SpecialPeriods.triangleOrbitProjection z) = w
  rw [D.toBoundaryMap.quotientMap_projection z hz]
  exact he

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_injective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Function.Injective D.quotientMap := by
  intro q r he
  have hfold :
    D.foldedFordMap (TriangleUniformizationGluing.fordRepresentative q) =
      D.foldedFordMap (TriangleUniformizationGluing.fordRepresentative r) :=
    he
  have hor :=
    (SpecialPeriods.Triangle.orbitProjection_eq_iff_fordRegion
          (TriangleUniformizationGluing.fordRepresentative q).property
          (TriangleUniformizationGluing.fordRepresentative r).property).mpr
      ((D.foldedFordMap_eq_iff (TriangleUniformizationGluing.fordRepresentative q).property
            (TriangleUniformizationGluing.fordRepresentative r).property).mp
        hfold)
  simpa only [TriangleUniformizationGluing.fordRepresentative_projection] using hor

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_bijective
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) : Function.Bijective D.quotientMap :=
  ⟨D.quotientMap_injective, D.quotientMap_surjective⟩

def TriangleUniformizationGluing.SignedHalfPlaneMap.quotientEquiv
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap) :
    SpecialPeriods.TriangleOrbitSpace ≃ ℂ :=
  Equiv.ofBijective D.quotientMap D.quotientMap_bijective

theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_preimage_eq_image_ford
    (D : TriangleUniformizationGluing.BoundaryMap) (K : Set ℂ) :
    D.quotientMap ⁻¹' K =
      SpecialPeriods.triangleOrbitProjection ''
        (SpecialPeriods.Triangle.fordRegion ∩ D.foldedFordMap ⁻¹' K) := by
  ext q
  constructor
  · intro hq
    exact
      ⟨TriangleUniformizationGluing.fordRepresentative q,
        ⟨(TriangleUniformizationGluing.fordRepresentative q).property, hq⟩,
        TriangleUniformizationGluing.fordRepresentative_projection q⟩
  · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
    change D.quotientMap (SpecialPeriods.triangleOrbitProjection z) ∈ K
    rw [D.quotientMap_projection z hz]
    exact hzK

theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_isProperMap
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    IsProperMap D.quotientMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨D.quotientMap_continuous, ?_⟩
  intro K hK
  rw [D.quotientMap_preimage_eq_image_ford K]
  exact
    (D.foldedFordMap_compact_preimage hlocal K hK).image
      SpecialPeriods.triangleOrbitProjection_continuous

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_isProperMap
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    IsProperMap D.quotientMap :=
  D.toBoundaryMap.quotientMap_isProperMap hlocal

def TriangleUniformizationGluing.SignedHalfPlaneMap.quotientHomeomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    SpecialPeriods.TriangleOrbitSpace ≃ₜ ℂ :=
  D.quotientEquiv.toHomeomorphOfContinuousClosed D.quotientMap_continuous
    (D.quotientMap_isProperMap hlocal).isClosedMap

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientHomeomorph_projection
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.fordRegion) :
    D.quotientHomeomorph hlocal (SpecialPeriods.triangleOrbitProjection z) = D.foldedFordMap z :=
  D.toBoundaryMap.quotientMap_projection z hz

def TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z)) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace ≃ₜ RiemannSphere :=
  (D.quotientHomeomorph hlocal).onePointCongr

@[simp]
theorem TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph_openInclusion
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    D.compactifiedHomeomorph hlocal (SpecialPeriods.triangleOpenInclusion q) =
      (D.quotientMap q : RiemannSphere) :=
  rfl

def SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph :
    SpecialPeriods.TriangleOrbitSpace ≃ₜ ℂ :=
  RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap

def SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph :
    SpecialPeriods.TriangleCompactifiedOrbitSpace ≃ₜ RiemannSphere :=
  RiemannMapping.triangleSignedHalfPlaneMap.compactifiedHomeomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap

@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph_openInclusion
    (q : SpecialPeriods.TriangleOrbitSpace) :
    triangleSphereUniformizationHomeomorph (SpecialPeriods.triangleOpenInclusion q) =
      ((trianglePlaneUniformizationHomeomorph q : ℂ) : RiemannSphere) :=
  rfl

theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_projection {z : ℍ}
    (hz : z ∈ halfFordRegion) :
    trianglePlaneUniformizationHomeomorph (SpecialPeriods.triangleOrbitProjection z) =
      RiemannMapping.triangleSignedHalfPlaneMap z := by
  change
    RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph
        RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
        (SpecialPeriods.triangleOrbitProjection z) =
      _
  rw [RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph_projection
      RiemannMapping.triangleSignedHalfPlaneMap_isProperMap z hz.1]
  exact RiemannMapping.triangleSignedHalfPlaneMap.toBoundaryMap.foldedFordMap_of_left hz.2

@[simp]
theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_centerOne :
    trianglePlaneUniformizationHomeomorph SpecialPeriods.triangleOrbitCenterOne = 0 := by
  rw [show
      SpecialPeriods.triangleOrbitCenterOne = SpecialPeriods.triangleOrbitProjection centerOne
      from rfl,
    trianglePlaneUniformizationHomeomorph_projection centerOne_mem_halfFordRegion,
    RiemannMapping.triangleSignedHalfPlaneMap_centerOne]

@[simp]
theorem SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_centerTwo :
    trianglePlaneUniformizationHomeomorph SpecialPeriods.triangleOrbitCenterTwo = 1 := by
  rw [show
      SpecialPeriods.triangleOrbitCenterTwo = SpecialPeriods.triangleOrbitProjection centerTwo
      from rfl,
    trianglePlaneUniformizationHomeomorph_projection centerTwo_mem_halfFordRegion,
    RiemannMapping.triangleSignedHalfPlaneMap_centerTwo]

@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph_centerOne :
    triangleSphereUniformizationHomeomorph
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
      ((0 : ℂ) : RiemannSphere) := by
  rw [triangleSphereUniformizationHomeomorph_openInclusion,
    trianglePlaneUniformizationHomeomorph_centerOne]

@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformizationHomeomorph_centerTwo :
    triangleSphereUniformizationHomeomorph
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
      ((1 : ℂ) : RiemannSphere) := by
  rw [triangleSphereUniformizationHomeomorph_openInclusion,
    trianglePlaneUniformizationHomeomorph_centerTwo]

def TriangleUniformizationGluing.ContinuousRemovable (Ω S : Set ℂ) : Prop :=
  ∀ V : Set ℂ,
    IsOpen V →
      V ⊆ Ω →
        ∀ f : ℂ → ℂ,
          ContinuousOn f V → (∀ z ∈ V \ S, DifferentiableAt ℂ f z) → DifferentiableOn ℂ f V

theorem TriangleUniformizationGluing.continuousRemovable_empty (Ω : Set ℂ) :
    ContinuousRemovable Ω ∅ := by
  intro V _ _ f _ hd z hz
  exact (hd z ⟨hz, Set.notMem_empty z⟩).differentiableWithinAt

theorem TriangleUniformizationGluing.ContinuousRemovable.mono_domain {Ω Ω' S : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S) (hΩ : Ω' ⊆ Ω) :
    TriangleUniformizationGluing.ContinuousRemovable Ω' S := by
  intro V hV hVΩ f hf hd
  exact hS V hV (hVΩ.trans hΩ) f hf hd

theorem TriangleUniformizationGluing.ContinuousRemovable.mono_set_on {Ω S T : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S) (hTS : ∀ z ∈ Ω, z ∈ T → z ∈ S) :
    TriangleUniformizationGluing.ContinuousRemovable Ω T := by
  intro V hV hVΩ f hf hd
  apply hS V hV hVΩ f hf
  intro z hz
  exact hd z ⟨hz.1, fun hT => hz.2 (hTS z (hVΩ hz.1) hT)⟩

theorem TriangleUniformizationGluing.ContinuousRemovable.mono_set {Ω S T : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S) (hTS : T ⊆ S) :
    TriangleUniformizationGluing.ContinuousRemovable Ω T :=
  hS.mono_set_on (fun _ _ hz => hTS hz)

theorem TriangleUniformizationGluing.continuousRemovable_realAxis (Ω : Set ℂ) :
    ContinuousRemovable Ω {z : ℂ | z.im = 0} := by
  intro V hV _ f hf hd
  exact
    SchwarzReflection.differentiableOn_of_continuousOn_off_real hV hf
      (fun z hz him => hd z ⟨hz, him⟩)

theorem TriangleUniformizationGluing.ContinuousRemovable.preimage {Ω S : Set ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable (e '' Ω) S) (hΩ : Ω ⊆ e.source)
    (he : DifferentiableOn ℂ e e.source) (he' : DifferentiableOn ℂ e.symm e.target) :
    TriangleUniformizationGluing.ContinuousRemovable Ω (e ⁻¹' S) := by
  intro V hV hVΩ f hf hd
  have hVs : V ⊆ e.source := hVΩ.trans hΩ
  have hW : IsOpen (e '' V) := e.isOpen_image_of_subset_source hV hVs
  have hWt : e '' V ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hVs hz)
  have hinv : Set.MapsTo e.symm (e '' V) V := by
    rintro y ⟨z, hz, rfl⟩
    simpa only [e.left_inv (hVs hz)] using hz
  have hc : ContinuousOn (f ∘ e.symm) (e '' V) := hf.comp (e.symm.continuousOn.mono hWt) hinv
  have hd' : ∀ y ∈ (e '' V) \ S, DifferentiableAt ℂ (f ∘ e.symm) y := by
    intro y hy
    have hnot : e.symm y ∉ e ⁻¹' S := by
      change e (e.symm y) ∉ S
      rw [e.right_inv (hWt hy.1)]
      exact hy.2
    exact
      (hd (e.symm y) ⟨hinv hy.1, hnot⟩).comp y
        (he'.differentiableAt (e.open_target.mem_nhds (hWt hy.1)))
  have hdiff := hS (e '' V) hW (Set.image_mono hVΩ) (f ∘ e.symm) hc hd'
  have hcomp : DifferentiableOn ℂ ((f ∘ e.symm) ∘ e) V :=
    hdiff.comp (he.mono hVs) (fun z hz => ⟨z, hz, rfl⟩)
  apply hcomp.congr
  intro z hz
  simp only [Function.comp_apply, e.left_inv (hVs hz)]

theorem TriangleUniformizationGluing.ContinuousRemovable.image {Ω S : Set ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S)
    (hΩ : Ω ⊆ e.source) (hSΩ : S ⊆ Ω) (he : DifferentiableOn ℂ e e.source)
    (he' : DifferentiableOn ℂ e.symm e.target) :
    TriangleUniformizationGluing.ContinuousRemovable (e '' Ω) (e '' S) := by
  have htarget : e '' Ω ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hΩ hz)
  have hinverse : e.symm '' (e '' Ω) = Ω := e.toPartialEquiv.symm_image_image_of_subset_source hΩ
  have hS' : TriangleUniformizationGluing.ContinuousRemovable (e.symm '' (e '' Ω)) S := by
    rwa [hinverse]
  have hp : TriangleUniformizationGluing.ContinuousRemovable (e '' Ω) (e.symm ⁻¹' S) :=
    hS'.preimage (e := e.symm) htarget he' he
  apply hp.mono_set_on
  rintro y _ ⟨z, hz, rfl⟩
  change e.symm (e z) ∈ S
  simpa only [e.left_inv (hΩ (hSΩ hz))] using hz

theorem TriangleUniformizationGluing.continuousRemovable_preimage_realAxis
    (e : OpenPartialHomeomorph ℂ ℂ) (Ω : Set ℂ) (hΩ : Ω ⊆ e.source)
    (he : DifferentiableOn ℂ e e.source) (he' : DifferentiableOn ℂ e.symm e.target) :
    ContinuousRemovable Ω {z : ℂ | (e z).im = 0} :=
  (continuousRemovable_realAxis (e '' Ω)).preimage hΩ he he'

private def TriangleUniformizationGluing.verticalLineChart_mo1973_19880 (a : ℝ) : ℂ ≃ₜ ℂ
    where
  toFun z := Complex.I * (z - (a : ℂ))
  invFun w := -Complex.I * w + (a : ℂ)
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem TriangleUniformizationGluing.verticalLineChart_differentiable_mo1973_19881
    (a : ℝ) : Differentiable ℂ (verticalLineChart_mo1973_19880 a) := fun _ =>
  (differentiableAt_const Complex.I).mul (differentiableAt_id.sub_const _)

private theorem TriangleUniformizationGluing.verticalLineChart_symm_differentiable_mo1973_19882
    (a : ℝ) : Differentiable ℂ (verticalLineChart_mo1973_19880 a).symm := fun _ =>
  ((differentiableAt_const (-Complex.I)).mul differentiableAt_id).add_const _

theorem TriangleUniformizationGluing.continuousRemovable_verticalLine (a : ℝ) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | z.re = a} := by
  have h :=
    continuousRemovable_preimage_realAxis
      (verticalLineChart_mo1973_19880 a).toOpenPartialHomeomorph UpperHalfPlane.upperHalfPlaneSet
      (fun z _ => Set.mem_univ z)
      (verticalLineChart_differentiable_mo1973_19881 a).differentiableOn
      (verticalLineChart_symm_differentiable_mo1973_19882 a).differentiableOn
  apply h.mono_set
  intro z hz
  change (Complex.I * (z - (a : ℂ))).im = 0
  simpa using sub_eq_zero.mpr hz

private def TriangleUniformizationGluing.translatedUnitCircleChart_mo1973_19884 (a : ℝ) :
    OpenPartialHomeomorph ℂ ℂ :=
  (Homeomorph.subRight ((a : ℂ) + 1)).transOpenPartialHomeomorph
    SpecialPeriods.Triangle.circleBoundaryChart

private theorem
  TriangleUniformizationGluing.upperHalfPlane_subset_translatedUnitCircleChart_source_mo1973_19885
    (a : ℝ) :
    UpperHalfPlane.upperHalfPlaneSet ⊆ (translatedUnitCircleChart_mo1973_19884 a).source := by
  intro z hz
  change z - ((a : ℂ) + 1) + 2 ≠ 0
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.one_im, Complex.im_ofNat,
    add_zero, sub_zero, Complex.zero_im] at hi
  exact (show 0 < z.im from hz).ne' hi

private theorem
  TriangleUniformizationGluing.translatedUnitCircleChart_differentiableOn_mo1973_19886 (a : ℝ) :
    DifferentiableOn ℂ (translatedUnitCircleChart_mo1973_19884 a)
      (translatedUnitCircleChart_mo1973_19884 a).source := by
  intro z hz
  change
    DifferentiableWithinAt ℂ
      (fun w : ℂ => SpecialPeriods.Triangle.circleStraighten (w - ((a : ℂ) + 1))) _ z
  exact
    ((SpecialPeriods.Triangle.circleStraighten_analyticOnNhd _ hz).differentiableAt.comp z
        (differentiableAt_id.sub_const _)).differentiableWithinAt

private theorem
  TriangleUniformizationGluing.translatedUnitCircleChart_symm_differentiableOn_mo1973_19887
    (a : ℝ) :
    DifferentiableOn ℂ (translatedUnitCircleChart_mo1973_19884 a).symm
      (translatedUnitCircleChart_mo1973_19884 a).target := by
  intro z hz
  change
    DifferentiableWithinAt ℂ
      (fun w : ℂ => SpecialPeriods.Triangle.circleUnstraighten w + ((a : ℂ) + 1)) _ z
  exact
    ((SpecialPeriods.Triangle.circleUnstraighten_analyticOnNhd z hz).differentiableAt.add_const
        _).differentiableWithinAt

private theorem TriangleUniformizationGluing.translatedUnitCircleChart_im_eq_zero_iff_mo1973_19888
    (a : ℝ) {z : ℂ} (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (translatedUnitCircleChart_mo1973_19884 a z).im = 0 ↔ ‖z - (a : ℂ)‖ = 1 := by
  change (SpecialPeriods.Triangle.circleStraighten (z - ((a : ℂ) + 1))).im = 0 ↔ _
  rw [SpecialPeriods.Triangle.circleStraighten_im_eq_zero_iff (z := z - ((a : ℂ) + 1))
      (upperHalfPlane_subset_translatedUnitCircleChart_source_mo1973_19885 a hz)]
  rw [show z - ((a : ℂ) + 1) + 1 = z - (a : ℂ) by ring]

theorem TriangleUniformizationGluing.continuousRemovable_unitCircle (a : ℝ) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | ‖z - (a : ℂ)‖ = 1} := by
  have h :=
    continuousRemovable_preimage_realAxis (translatedUnitCircleChart_mo1973_19884 a)
      UpperHalfPlane.upperHalfPlaneSet
      (upperHalfPlane_subset_translatedUnitCircleChart_source_mo1973_19885 a)
      (translatedUnitCircleChart_differentiableOn_mo1973_19886 a)
      (translatedUnitCircleChart_symm_differentiableOn_mo1973_19887 a)
  exact
    h.mono_set_on
      (fun z hz hnorm => (translatedUnitCircleChart_im_eq_zero_iff_mo1973_19888 a hz).mpr hnorm)

def TriangleUniformizationGluing.triangleAmbientMap (g : SpecialPeriods.TriangleGroup) :
    OpenPartialHomeomorph ℂ ℂ :=
  (UpperHalfPlane.ofComplex.trans
        (SpecialPeriods.triangleGeometricBiholomorph
            g).toHomeomorph.toOpenPartialHomeomorph).trans
    UpperHalfPlane.ofComplex.symm

@[simp]
theorem TriangleUniformizationGluing.triangleAmbientMap_source
    (g : SpecialPeriods.TriangleGroup) :
    (triangleAmbientMap g).source = UpperHalfPlane.upperHalfPlaneSet := by
  simp [triangleAmbientMap, UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe]

@[simp]
theorem TriangleUniformizationGluing.triangleAmbientMap_target
    (g : SpecialPeriods.TriangleGroup) :
    (triangleAmbientMap g).target = UpperHalfPlane.upperHalfPlaneSet := by
  simp [triangleAmbientMap, UpperHalfPlane.ofComplex, UpperHalfPlane.range_coe]

theorem TriangleUniformizationGluing.triangleAmbientMap_apply (g : SpecialPeriods.TriangleGroup)
    (z : ℂ) :
    triangleAmbientMap g z =
      (SpecialPeriods.triangleGeometricRepresentation g (UpperHalfPlane.ofComplex z) : ℂ) :=
  rfl

@[simp]
theorem TriangleUniformizationGluing.triangleAmbientMap_apply_coe
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    triangleAmbientMap g (z : ℂ) = (SpecialPeriods.triangleGeometricRepresentation g z : ℂ) := by
  rw [triangleAmbientMap_apply, UpperHalfPlane.ofComplex_apply]

theorem TriangleUniformizationGluing.triangleAmbientMap_symm_apply
    (g : SpecialPeriods.TriangleGroup) (z : ℂ) :
    (triangleAmbientMap g).symm z =
      (SpecialPeriods.triangleGeometricRepresentation g⁻¹ (UpperHalfPlane.ofComplex z) : ℂ) := by
  rw [map_inv]
  rfl

@[simp]
theorem TriangleUniformizationGluing.triangleAmbientMap_symm (g : SpecialPeriods.TriangleGroup) :
    (triangleAmbientMap g).symm = triangleAmbientMap g⁻¹ := by
  apply OpenPartialHomeomorph.ext
  · intro z
    rw [triangleAmbientMap_symm_apply, triangleAmbientMap_apply]
  · intro z
    simp only [OpenPartialHomeomorph.symm_symm, triangleAmbientMap_apply,
      triangleAmbientMap_symm_apply, inv_inv]
  · simp only [OpenPartialHomeomorph.symm_source, triangleAmbientMap_source,
      triangleAmbientMap_target]

theorem TriangleUniformizationGluing.triangleAmbientMap_differentiableOn
    (g : SpecialPeriods.TriangleGroup) :
    DifferentiableOn ℂ (triangleAmbientMap g) (triangleAmbientMap g).source := by
  rw [triangleAmbientMap_source]
  exact
    UpperHalfPlane.mdifferentiable_iff.mp
      (UpperHalfPlane.mdifferentiable_coe.comp
        ((SpecialPeriods.triangleGeometricRepresentation_holomorphic g).mdifferentiable
          (by simp)))

theorem TriangleUniformizationGluing.triangleAmbientMap_symm_differentiableOn
    (g : SpecialPeriods.TriangleGroup) :
    DifferentiableOn ℂ (triangleAmbientMap g).symm (triangleAmbientMap g).target := by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target, triangleAmbientMap_symm] using
    triangleAmbientMap_differentiableOn g⁻¹

theorem TriangleUniformizationGluing.triangleAmbientMap_image_upperHalfPlaneSet
    (g : SpecialPeriods.TriangleGroup) :
    triangleAmbientMap g '' UpperHalfPlane.upperHalfPlaneSet = UpperHalfPlane.upperHalfPlaneSet :=
  by
  simpa only [triangleAmbientMap_source, triangleAmbientMap_target] using
    (triangleAmbientMap g).image_source_eq_target

theorem TriangleUniformizationGluing.triangleAmbientMap_image_coe
    (g : SpecialPeriods.TriangleGroup) (S : Set ℍ) :
    triangleAmbientMap g '' (((↑) : ℍ → ℂ) '' S) =
      ((↑) : ℍ → ℂ) '' (SpecialPeriods.triangleGeometricRepresentation g '' S) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro z _
  exact triangleAmbientMap_apply_coe g z

def SpecialPeriods.Triangle.halfEdgeCarrier : Fin 3 → Set ℍ :=
  ![{z | z.re = stripLeft}, {z | z.re = -(1 / 2)}, {z | ‖(z : ℂ) + 1‖ = 1}]

def SpecialPeriods.Triangle.halfFordEdge (k : Fin 3) : Set ℍ :=
  halfFordRegion ∩ halfEdgeCarrier k

theorem SpecialPeriods.Triangle.halfEdgeCarrier_isClosed (k : Fin 3) :
    IsClosed (halfEdgeCarrier k) := by
  fin_cases k
  · exact isClosed_eq UpperHalfPlane.continuous_re continuous_const
  · exact isClosed_eq UpperHalfPlane.continuous_re continuous_const
  · exact isClosed_eq (UpperHalfPlane.continuous_coe.add continuous_const).norm continuous_const

theorem SpecialPeriods.Triangle.halfFordEdge_isClosed (k : Fin 3) : IsClosed (halfFordEdge k) :=
  halfFordRegion_isClosed.inter (halfEdgeCarrier_isClosed k)

theorem SpecialPeriods.Triangle.halfFordEdge_subset_region (k : Fin 3) :
    halfFordEdge k ⊆ halfFordRegion :=
  Set.inter_subset_left

theorem SpecialPeriods.Triangle.halfFordEdge_subset_boundary (k : Fin 3) :
    halfFordEdge k ⊆ halfFordRegion \ halfFordInterior := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hi
  have hc := hz.2
  fin_cases k
  · change z.re = stripLeft at hc
    exact (ne_of_gt hi.1.1) hc
  · change z.re = -(1 / 2) at hc
    exact (ne_of_lt hi.2) hc
  · change ‖(z : ℂ) + 1‖ = 1 at hc
    exact (ne_of_gt hi.1.2.2.1) hc

theorem SpecialPeriods.Triangle.halfFordEdges_eq_boundary :
    (⋃ k : Fin 3, halfFordEdge k) = halfFordRegion \ halfFordInterior := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset halfFordEdge_subset_boundary
  · rintro z ⟨hz, hnot⟩
    by_cases hl : z.re = stripLeft
    · exact Set.mem_iUnion.mpr ⟨0, hz, hl⟩
    by_cases hr : z.re = -(1 / 2)
    · exact Set.mem_iUnion.mpr ⟨1, hz, hr⟩
    by_cases hn : ‖(z : ℂ) + 1‖ = 1
    · exact Set.mem_iUnion.mpr ⟨2, hz, hn⟩
    have hl' : stripLeft < z.re := lt_of_le_of_ne hz.1.1 (Ne.symm hl)
    have hr' : z.re < -(1 / 2) := lt_of_le_of_ne hz.2 hr
    have hn' : 1 < ‖(z : ℂ) + 1‖ := lt_of_le_of_ne hz.1.2.2.1 (Ne.symm hn)
    apply (hnot ?_).elim
    refine ⟨⟨hl', ?_, hn', one_lt_norm_of_re_lt_neg_half z hr' hn'⟩, hr'⟩
    linarith [stripRight_pos]

def SpecialPeriods.Triangle.halfTriangleEdge (i : SpecialPeriods.TriangleGroup × Bool)
    (k : Fin 3) : Set ℍ :=
  halfTriangleMap i '' halfFordEdge k

abbrev SpecialPeriods.Triangle.TriangleEdgeIndex :=
  (SpecialPeriods.TriangleGroup × Bool) × Fin 3

theorem SpecialPeriods.Triangle.halfTriangleEdge_eq (i : SpecialPeriods.TriangleGroup × Bool)
    (k : Fin 3) :
    halfTriangleEdge i k =
      SpecialPeriods.triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordEdge k) := by
  rw [Set.image_image]
  rfl

theorem SpecialPeriods.Triangle.halfTriangleEdge_isClosed
    (i : SpecialPeriods.TriangleGroup × Bool) (k : Fin 3) : IsClosed (halfTriangleEdge i k) :=
  (halfTriangleMap i).isClosedMap _ (halfFordEdge_isClosed k)

theorem SpecialPeriods.Triangle.halfTriangleEdge_subset_tile
    (i : SpecialPeriods.TriangleGroup × Bool) (k : Fin 3) :
    halfTriangleEdge i k ⊆ halfTriangleTile i :=
  Set.image_mono (halfFordEdge_subset_region k)

theorem SpecialPeriods.Triangle.halfTriangleEdges_eq_boundary
    (i : SpecialPeriods.TriangleGroup × Bool) :
    (⋃ k : Fin 3, halfTriangleEdge i k) = halfTriangleTile i \ halfTriangleOpenTile i := by
  unfold halfTriangleEdge halfTriangleTile halfTriangleOpenTile
  rw [← Set.image_iUnion, halfFordEdges_eq_boundary,
    Set.image_sdiff (halfTriangleMap i).injective]

theorem SpecialPeriods.Triangle.triangleEdges_cover_openTile_complement :
    (⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleOpenTile i)ᶜ ⊆
      ⋃ j : TriangleEdgeIndex, halfTriangleEdge j.1 j.2 := by
  intro z hz
  have hcover : z ∈ ⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleTile i := by
    rw [halfTriangleTiles_cover]
    exact Set.mem_univ z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcover
  have hb : z ∈ ⋃ k : Fin 3, halfTriangleEdge i k := by
    rw [halfTriangleEdges_eq_boundary]
    exact ⟨hi, fun h => hz (Set.mem_iUnion.mpr ⟨i, h⟩)⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨(i, k), hk⟩

theorem SpecialPeriods.Triangle.halfTriangleEdges_locallyFinite :
    LocallyFinite (fun j : TriangleEdgeIndex => halfTriangleEdge j.1 j.2) := by
  intro z
  obtain ⟨U, hU, hfin⟩ := halfTriangleTiles_locallyFinite z
  refine ⟨U, hU, (hfin.prod (Set.finite_univ : (Set.univ : Set (Fin 3)).Finite)).subset ?_⟩
  rintro j ⟨w, hw, hwU⟩
  exact ⟨⟨w, halfTriangleEdge_subset_tile j.1 j.2 hw, hwU⟩, Set.mem_univ _⟩

def SpecialPeriods.Triangle.triangleEdgeComplex (j : TriangleEdgeIndex) : Set ℂ :=
  ((↑) : ℍ → ℂ) '' halfTriangleEdge j.1 j.2

theorem SpecialPeriods.Triangle.triangleEdgeComplex_relative_compl_isOpen
    (j : TriangleEdgeIndex) : IsOpen (UpperHalfPlane.upperHalfPlaneSet \ triangleEdgeComplex j) :=
  by
  have h :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap (halfTriangleEdge j.1 j.2)ᶜ
      (halfTriangleEdge_isClosed j.1 j.2).isOpen_compl
  simpa only [triangleEdgeComplex,
    Set.image_compl_eq_range_sdiff_image UpperHalfPlane.coe_injective,
    UpperHalfPlane.range_coe] using h

theorem SpecialPeriods.Triangle.triangleEdgeComplex_locallyFinite :
    LocallyFinite
      (fun j : TriangleEdgeIndex =>
        ((↑) : UpperHalfPlane.upperHalfPlaneSet → ℂ) ⁻¹' triangleEdgeComplex j) := by
  let g : UpperHalfPlane.upperHalfPlaneSet → ℍ := fun z => ⟨z.1, z.2⟩
  have hg : Continuous g :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val
  have hpre :
    ∀ j : TriangleEdgeIndex,
      ((↑) : UpperHalfPlane.upperHalfPlaneSet → ℂ) ⁻¹' triangleEdgeComplex j =
        g ⁻¹' halfTriangleEdge j.1 j.2 := by
    intro j
    ext z
    simp only [triangleEdgeComplex, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwg : w = g z := UpperHalfPlane.coe_injective hwz
      simpa only [hwg] using hw
    · intro h
      exact ⟨g z, h, rfl⟩
  simp_rw [hpre]
  exact halfTriangleEdges_locallyFinite.preimage_continuous hg

theorem SpecialPeriods.Triangle.triangleEdgeComplex_cover_openTile_complement :
    UpperHalfPlane.upperHalfPlaneSet \
        (⋃ i : SpecialPeriods.TriangleGroup × Bool, ((↑) : ℍ → ℂ) '' halfTriangleOpenTile i) ⊆
      ⋃ j : TriangleEdgeIndex, triangleEdgeComplex j := by
  rintro z ⟨hz, hnot⟩
  let w : ℍ := ⟨z, hz⟩
  have hw : w ∈ (⋃ i : SpecialPeriods.TriangleGroup × Bool, halfTriangleOpenTile i)ᶜ := by
    intro hi
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hi
    exact hnot (Set.mem_iUnion.mpr ⟨i, w, hi, rfl⟩)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (triangleEdges_cover_openTile_complement hw)
  exact Set.mem_iUnion.mpr ⟨j, w, hj, rfl⟩

def SpecialPeriods.Triangle.foldedEdgeComplexCarrier (b : Bool) : Fin 3 → Set ℂ :=
  if b then ![{z | z.re = stripRight}, {z | z.re = -(1 / 2)}, {z | ‖z‖ = 1}]
  else ![{z | z.re = stripLeft}, {z | z.re = -(1 / 2)}, {z | ‖z + 1‖ = 1}]

theorem SpecialPeriods.Triangle.foldedEdgeComplex_subset_carrier (b : Bool) (k : Fin 3) :
    ((↑) : ℍ → ℂ) '' (halfFold b '' halfFordEdge k) ⊆ foldedEdgeComplexCarrier b k := by
  rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  have hc := hu.2
  cases b <;> fin_cases k
  · exact hc
  · exact hc
  · exact hc
  · change u.re = stripLeft at hc
    change (rightReflection u).re = stripRight
    rw [rightReflection_re, hc]
    linarith [stripLeft_add_stripRight]
  · change u.re = -(1 / 2) at hc
    change (rightReflection u).re = -(1 / 2)
    rw [rightReflection_re, hc]
    norm_num
  · change ‖(u : ℂ) + 1‖ = 1 at hc
    change ‖(rightReflection u : ℂ)‖ = 1
    rw [rightReflection_norm]
    exact hc

theorem TriangleUniformizationGluing.ContinuousRemovable.union {Ω S T : Set ℂ}
    (hS : TriangleUniformizationGluing.ContinuousRemovable Ω S)
    (hT : TriangleUniformizationGluing.ContinuousRemovable Ω T) (hclosedT : IsOpen (Ω \ T)) :
    TriangleUniformizationGluing.ContinuousRemovable Ω (S ∪ T) := by
  intro V hV hVΩ f hf hd
  have hVT : IsOpen (V \ T) := by
    have he : V \ T = V ∩ (Ω \ T) := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, hVΩ hz.1, hz.2⟩
      · intro hz
        exact ⟨hz.1, hz.2.2⟩
    rw [he]
    exact hV.inter hclosedT
  have hdiff : DifferentiableOn ℂ f (V \ T) := by
    apply hS (V \ T) hVT (Set.sdiff_subset.trans hVΩ) f (hf.mono Set.sdiff_subset)
    intro z hz
    exact hd z ⟨hz.1.1, fun hu => hu.elim hz.2 hz.1.2⟩
  apply hT V hV hVΩ f hf
  intro z hz
  exact hdiff.differentiableAt (hVT.mem_nhds hz)

theorem TriangleUniformizationGluing.continuousRemovable_biUnion_finset {ι : Type*} {Ω : Set ℂ}
    {S : ι → Set ℂ} (t : Finset ι) (hS : ∀ i ∈ t, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i ∈ t, IsOpen (Ω \ S i)) : ContinuousRemovable Ω (⋃ i ∈ t, S i) := by
  classical
  revert hS hclosed
  induction t using Finset.induction_on with
  | empty =>
    intro _ _
    simpa using continuousRemovable_empty Ω
  | @insert a t hat ih =>
    intro hS hclosed
    have ht : ContinuousRemovable Ω (⋃ i ∈ t, S i) :=
      ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
        (fun i hi => hclosed i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Set.union_comm] using
      ht.union (hS a (Finset.mem_insert_self a t)) (hclosed a (Finset.mem_insert_self a t))

theorem TriangleUniformizationGluing.continuousRemovable_of_locally {Ω S : Set ℂ}
    (hlocal : ∀ z ∈ Ω, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧ ContinuousRemovable W S) :
    ContinuousRemovable Ω S := by
  intro V hV hVΩ f hf hd z hz
  obtain ⟨W, hW, hzW, hrem⟩ := hlocal z (hVΩ hz)
  have hVW : IsOpen (V ∩ W) := hV.inter hW
  have hdiff : DifferentiableOn ℂ f (V ∩ W) := by
    apply hrem (V ∩ W) hVW Set.inter_subset_right f (hf.mono Set.inter_subset_left)
    intro x hx
    exact hd x ⟨hx.1.1, hx.2⟩
  exact (hdiff.differentiableAt (hVW.mem_nhds ⟨hz, hzW⟩)).differentiableWithinAt

theorem TriangleUniformizationGluing.continuousRemovable_iUnion_of_locallyFinite {ι : Type*}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (S : ι → Set ℂ) (hS : ∀ i, ContinuousRemovable Ω (S i))
    (hclosed : ∀ i, IsOpen (Ω \ S i))
    (hloc : LocallyFinite (fun i => (Subtype.val : Ω → ℂ) ⁻¹' S i)) :
    ContinuousRemovable Ω (⋃ i, S i) := by
  classical
  apply continuousRemovable_of_locally
  intro z hz
  obtain ⟨N, hN, hfin⟩ := hloc ⟨z, hz⟩
  obtain ⟨W, hWN, hW, hzW⟩ := mem_nhds_iff.mp hN
  let t := hfin.toFinset
  have hWΩ : (Subtype.val '' W : Set ℂ) ⊆ Ω := by
    rintro x ⟨w, hw, rfl⟩
    exact w.property
  have hrem : ContinuousRemovable Ω (⋃ i ∈ t, S i) :=
    continuousRemovable_biUnion_finset t (fun i _ => hS i) (fun i _ => hclosed i)
  refine ⟨Subtype.val '' W, hΩ.isOpenMap_subtype_val _ hW, Set.mem_image_of_mem _ hzW, ?_⟩
  apply (hrem.mono_domain hWΩ).mono_set_on
  rintro x ⟨w, hw, rfl⟩ hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion₂.mpr
  refine ⟨i, ?_, hi⟩
  exact hfin.mem_toFinset.mpr ⟨w, hi, hWN hw⟩

theorem TriangleUniformizationGluing.continuousRemovable_foldedEdgeComplexCarrier (b : Bool)
    (k : Fin 3) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (SpecialPeriods.Triangle.foldedEdgeComplexCarrier b k) := by
  cases b <;> fin_cases k
  · exact continuousRemovable_verticalLine SpecialPeriods.Triangle.stripLeft
  · exact continuousRemovable_verticalLine (-(1 / 2))
  · change ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | ‖z + 1‖ = 1}
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, sub_neg_eq_add] using
      continuousRemovable_unitCircle (-1)
  · exact continuousRemovable_verticalLine SpecialPeriods.Triangle.stripRight
  · exact continuousRemovable_verticalLine (-(1 / 2))
  · change ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | ‖z‖ = 1}
    simpa only [Complex.ofReal_zero, sub_zero] using continuousRemovable_unitCircle 0

theorem TriangleUniformizationGluing.continuousRemovable_foldedHalfEdge (b : Bool) (k : Fin 3) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (((↑) : ℍ → ℂ) ''
        (SpecialPeriods.Triangle.halfFold b '' SpecialPeriods.Triangle.halfFordEdge k)) :=
  (continuousRemovable_foldedEdgeComplexCarrier b k).mono_set
    (SpecialPeriods.Triangle.foldedEdgeComplex_subset_carrier b k)

theorem TriangleUniformizationGluing.continuousRemovable_triangleEdgeComplex
    (j : SpecialPeriods.Triangle.TriangleEdgeIndex) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (SpecialPeriods.Triangle.triangleEdgeComplex j) := by
  rcases j with ⟨⟨g, b⟩, k⟩
  have hsource : UpperHalfPlane.upperHalfPlaneSet ⊆ (triangleAmbientMap g).source := by
    rw [triangleAmbientMap_source]
  have hsubset :
    ((↑) : ℍ → ℂ) ''
        (SpecialPeriods.Triangle.halfFold b '' SpecialPeriods.Triangle.halfFordEdge k) ⊆
      UpperHalfPlane.upperHalfPlaneSet := by
    rintro z ⟨w, _, rfl⟩
    exact w.im_pos
  have h :=
    (continuousRemovable_foldedHalfEdge b k).image (e := triangleAmbientMap g) hsource hsubset
      (triangleAmbientMap_differentiableOn g) (triangleAmbientMap_symm_differentiableOn g)
  simpa only [triangleAmbientMap_image_upperHalfPlaneSet, triangleAmbientMap_image_coe,
    SpecialPeriods.Triangle.triangleEdgeComplex,
    SpecialPeriods.Triangle.halfTriangleEdge_eq] using h

theorem TriangleUniformizationGluing.continuousRemovable_triangleEdges :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      (⋃ j : SpecialPeriods.Triangle.TriangleEdgeIndex,
        SpecialPeriods.Triangle.triangleEdgeComplex j) :=
  continuousRemovable_iUnion_of_locallyFinite UpperHalfPlane.isOpen_upperHalfPlaneSet
    SpecialPeriods.Triangle.triangleEdgeComplex continuousRemovable_triangleEdgeComplex
    SpecialPeriods.Triangle.triangleEdgeComplex_relative_compl_isOpen
    SpecialPeriods.Triangle.triangleEdgeComplex_locallyFinite

theorem TriangleUniformizationGluing.differentiableOn_of_continuousOn_halfTriangleOpenTiles
    {f : ℂ → ℂ} (hf : ContinuousOn f UpperHalfPlane.upperHalfPlaneSet)
    (hd :
      ∀ i : SpecialPeriods.TriangleGroup × Bool,
        DifferentiableOn ℂ f (((↑) : ℍ → ℂ) '' SpecialPeriods.Triangle.halfTriangleOpenTile i)) :
    DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet := by
  apply
    continuousRemovable_triangleEdges UpperHalfPlane.upperHalfPlaneSet
      UpperHalfPlane.isOpen_upperHalfPlaneSet Set.Subset.rfl f hf
  intro z hz
  have htile :
    z ∈
      ⋃ i : SpecialPeriods.TriangleGroup × Bool,
        ((↑) : ℍ → ℂ) '' SpecialPeriods.Triangle.halfTriangleOpenTile i := by
    by_contra hnot
    exact
      hz.2 (SpecialPeriods.Triangle.triangleEdgeComplex_cover_openTile_complement ⟨hz.1, hnot⟩)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htile
  exact
    (hd i).differentiableAt
      ((UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
            (SpecialPeriods.Triangle.halfTriangleOpenTile_isOpen i)).mem_nhds
        hi)

theorem TriangleUniformizationGluing.contMDiff_of_continuous_of_halfTriangleOpenTiles {f : ℍ → ℂ}
    (hf : Continuous f)
    (hd :
      ∀ i : SpecialPeriods.TriangleGroup × Bool,
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f (SpecialPeriods.Triangle.halfTriangleOpenTile i)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have hfc : ContinuousOn (f ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    exact
      (hf.continuousAt.comp
          (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) hz).continuousAt).continuousWithinAt
  have hfd :
    ∀ i : SpecialPeriods.TriangleGroup × Bool,
      DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex)
        (((↑) : ℍ → ℂ) '' SpecialPeriods.Triangle.halfTriangleOpenTile i) := by
    intro i z hz
    rcases hz with ⟨w, hw, rfl⟩
    have ht : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f w :=
      (hd i w hw).contMDiffAt
        ((SpecialPeriods.Triangle.halfTriangleOpenTile_isOpen i).mem_nhds hw)
    exact
      ((UpperHalfPlane.contMDiffAt_iff.mp ht).differentiableAt (by simp)).differentiableWithinAt
  have hglobal := differentiableOn_of_continuousOn_halfTriangleOpenTiles hfc hfd
  intro z
  apply UpperHalfPlane.contMDiffAt_iff.mpr
  exact (hglobal.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet z z.im_pos).contDiffAt

private theorem TriangleUniformizationGluing.differentiableAt_conj_affine_reflection_mo1973_19938
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (-1 - conj z)) :
    DifferentiableAt ℂ (fun w => conj (f (-1 - conj w))) z := by
  have hc : DifferentiableAt ℂ (conj ∘ f ∘ conj) (-1 - z) := by
    simpa only [map_sub, map_neg, map_one, Complex.conj_conj] using hf.conj_conj
  have ha : DifferentiableAt ℂ (fun w : ℂ => -1 - w) z :=
    (differentiableAt_const (-1 : ℂ)).sub differentiableAt_id
  simpa only [Function.comp_def, map_sub, map_neg, map_one] using hc.comp z ha

theorem TriangleUniformizationGluing.contMDiffOn_conj_rightReflection {f : ℍ → ℂ} {S : Set ℍ}
    (hS : IsOpen S) (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f S) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun z => conj (f (SpecialPeriods.Triangle.rightReflection z)))
      (SpecialPeriods.Triangle.rightReflection '' S) := by
  let F : ℂ → ℂ := fun z => conj (f (UpperHalfPlane.ofComplex (-1 - conj z)))
  have hU : IsOpen (((↑) : ℍ → ℂ) '' (SpecialPeriods.Triangle.rightReflection '' S)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
      (SpecialPeriods.Triangle.rightReflection.isOpenMap _ hS)
  have hF :
    DifferentiableOn ℂ F (((↑) : ℍ → ℂ) '' (SpecialPeriods.Triangle.rightReflection '' S)) := by
    rintro z ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    have hfx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := (hf x hx).contMDiffAt (hS.mem_nhds hx)
    have hfd : DifferentiableAt ℂ (f ∘ UpperHalfPlane.ofComplex) (x : ℂ) :=
      (UpperHalfPlane.contMDiffAt_iff.mp hfx).differentiableAt (by simp)
    have hr : (-1 : ℂ) - conj (SpecialPeriods.Triangle.rightReflection x : ℂ) = (x : ℂ) :=
      (SpecialPeriods.Triangle.rightReflection_coe
            (SpecialPeriods.Triangle.rightReflection x)).symm.trans
        (congrArg ((↑) : ℍ → ℂ) (SpecialPeriods.Triangle.rightReflection_involutive x))
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_conj_affine_reflection_mo1973_19938 (f := f ∘ UpperHalfPlane.ofComplex)
    rw [hr]
    exact hfd
  have hFM :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω F (((↑) : ℍ → ℂ) '' (SpecialPeriods.Triangle.rightReflection '' S)) :=
    contMDiffOn_iff_contDiffOn.mpr ((hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn)
  have hcomp :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (F ∘ ((↑) : ℍ → ℂ)) (SpecialPeriods.Triangle.rightReflection '' S) :=
    hFM.comp UpperHalfPlane.contMDiff_coe.contMDiffOn (fun z hz => ⟨z, hz, rfl⟩)
  apply hcomp.congr
  intro z _
  change
    conj (f (SpecialPeriods.Triangle.rightReflection z)) =
      conj (f (UpperHalfPlane.ofComplex (-1 - conj (z : ℂ))))
  rw [← SpecialPeriods.Triangle.rightReflection_coe, UpperHalfPlane.ofComplex_apply]

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_half
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap SpecialPeriods.Triangle.halfFordInterior := by
  apply hd.congr
  intro z hz
  have hclosed := SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hz
  rw [D.upstairsMap_of_mem hclosed.1, D.foldedFordMap_of_left hclosed.2]

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_reflected_half
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap
      (SpecialPeriods.Triangle.rightReflection '' SpecialPeriods.Triangle.halfFordInterior) := by
  have href :=
    TriangleUniformizationGluing.contMDiffOn_conj_rightReflection
      SpecialPeriods.Triangle.halfFordInterior_isOpen hd
  apply href.congr
  rintro z ⟨w, hw, rfl⟩
  have hclosed := SpecialPeriods.Triangle.halfFordInterior_subset_halfFordRegion hw
  rw [D.upstairsMap_of_mem (SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hclosed.1)]
  exact D.foldedFordMap_eqOn_right ⟨w, hclosed, rfl⟩

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_fold
    (D : TriangleUniformizationGluing.BoundaryMap) (b : Bool)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap
      (SpecialPeriods.Triangle.halfFold b '' SpecialPeriods.Triangle.halfFordInterior) := by
  cases b
  · change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (id '' SpecialPeriods.Triangle.halfFordInterior)
    rw [Set.image_id]
    exact D.upstairsMap_holomorphicOn_half hd
  · exact D.upstairsMap_holomorphicOn_reflected_half hd

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphicOn_tile
    (D : TriangleUniformizationGluing.BoundaryMap) (i : SpecialPeriods.TriangleGroup × Bool)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap (SpecialPeriods.Triangle.halfTriangleOpenTile i) := by
  rw [SpecialPeriods.Triangle.halfTriangleOpenTile_eq]
  have hm :
    Set.MapsTo (SpecialPeriods.triangleGeometricRepresentation i.1⁻¹)
      (SpecialPeriods.triangleGeometricRepresentation i.1 ''
        (SpecialPeriods.Triangle.halfFold i.2 '' SpecialPeriods.Triangle.halfFordInterior))
      (SpecialPeriods.Triangle.halfFold i.2 '' SpecialPeriods.Triangle.halfFordInterior) := by
    rintro z ⟨w, hw, rfl⟩
    rw [map_inv]
    change
      (SpecialPeriods.triangleGeometricRepresentation i.1).symm
          (SpecialPeriods.triangleGeometricRepresentation i.1 w) ∈
        _
    rw [(SpecialPeriods.triangleGeometricRepresentation i.1).symm_apply_apply w]
    exact hw
  have hc :=
    (D.upstairsMap_holomorphicOn_fold i.2 hd).comp
      (SpecialPeriods.triangleGeometricRepresentation_holomorphic i.1⁻¹).contMDiffOn hm
  apply hc.congr
  intro z _
  exact (D.upstairsMap_smul i.1⁻¹ z).symm

theorem TriangleUniformizationGluing.BoundaryMap.upstairsMap_holomorphic
    (D : TriangleUniformizationGluing.BoundaryMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap :=
  TriangleUniformizationGluing.contMDiff_of_continuous_of_halfTriangleOpenTiles
    D.upstairsMap_continuous (fun i => D.upstairsMap_holomorphicOn_tile i hd)

theorem TriangleUniformizationGluing.SignedHalfPlaneMap.upstairsMap_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap :=
  D.toBoundaryMap.upstairsMap_holomorphic hd

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem TriangleUniformizationGluing.instIsManifold1 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_holomorphicAt_of_not_elliptic
    (D : TriangleUniformizationGluing.BoundaryMap) (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap)
    {q : SpecialPeriods.TriangleOrbitSpace} (h₁ : q ≠ SpecialPeriods.triangleOrbitCenterOne)
    (h₂ : q ≠ SpecialPeriods.triangleOrbitCenterTwo) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap q := by
  obtain ⟨z, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  have hp := SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic h₁ h₂
  have h :=
    hup.contMDiffAt.comp (SpecialPeriods.triangleOrbitProjection z) hp.localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with y hy
  change
    D.quotientMap y = D.quotientMap (SpecialPeriods.triangleOrbitProjection (hp.localInverse y))
  rw [show SpecialPeriods.triangleOrbitProjection (hp.localInverse y) = y from hy]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
theorem TriangleUniformizationGluing.BoundaryMap.quotientMap_holomorphic
    (D : TriangleUniformizationGluing.BoundaryMap) (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap := by
  apply
    TriangleUniformizationGluing.contMDiff_of_continuous_of_finite D.quotientMap_continuous
      ((Set.finite_singleton SpecialPeriods.triangleOrbitCenterTwo).insert
        SpecialPeriods.triangleOrbitCenterOne)
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hq
  exact D.quotientMap_holomorphicAt_of_not_elliptic hup hq.1 hq.2

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientMap_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap :=
  D.toBoundaryMap.quotientMap_holomorphic hup

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold1 in
theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientHomeomorph_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.quotientHomeomorph hlocal) :=
  D.quotientMap_holomorphic hup

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem TriangleUniformizationGluing.instIsManifold2 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold2 in
theorem
  TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph_holomorphicAt_of_ne_cusp
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hq : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.quotientMap) {p : SpecialPeriods.TriangleCompactifiedOrbitSpace}
    (hp : p ≠ SpecialPeriods.triangleCuspPoint) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedHomeomorph hlocal) p := by
  obtain ⟨q, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
  have hfinite : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → RiemannSphere) :=
    RiemannSphere.standardCharts.affineMap_holomorphic Bool.false
  have hcomp :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      ((D.compactifiedHomeomorph hlocal) ∘ SpecialPeriods.triangleOpenInclusion) := by
    simpa only [Function.comp_def, D.compactifiedHomeomorph_openInclusion hlocal] using
      hfinite.comp hq
  have hi := SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph q
  have h :=
    hcomp.contMDiffAt.comp (SpecialPeriods.triangleOpenInclusion q) hi.localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [hi.localInverse_eventuallyEq_right] with z hz
  change
    D.compactifiedHomeomorph hlocal z =
      D.compactifiedHomeomorph hlocal (SpecialPeriods.triangleOpenInclusion (hi.localInverse z))
  rw [show SpecialPeriods.triangleOpenInclusion (hi.localInverse z) = z from hz]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold2 in
theorem TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedHomeomorph_holomorphic
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hup : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D.upstairsMap) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.compactifiedHomeomorph hlocal) := by
  apply
    TriangleUniformizationGluing.contMDiff_of_continuous_of_finite
      (D.compactifiedHomeomorph hlocal).continuous
      (Set.finite_singleton SpecialPeriods.triangleCuspPoint)
  intro p hp
  exact
    D.compactifiedHomeomorph_holomorphicAt_of_ne_cusp hlocal (D.quotientMap_holomorphic hup)
      (by simpa only [Set.mem_singleton_iff] using hp)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem TriangleUniformizationGluing.instIsManifold3 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3 in
theorem TriangleUniformizationGluing.instIsManifold4 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3
    TriangleUniformizationGluing.instIsManifold4 in
def TriangleUniformizationGluing.SignedHalfPlaneMap.quotientBiholomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph (D.quotientHomeomorph hlocal)
    (D.quotientHomeomorph_holomorphic hlocal (D.upstairsMap_holomorphic hd))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3
    TriangleUniformizationGluing.instIsManifold4 in
def TriangleUniformizationGluing.SignedHalfPlaneMap.compactifiedBiholomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph (D.compactifiedHomeomorph hlocal)
    (D.compactifiedHomeomorph_holomorphic hlocal (D.upstairsMap_holomorphic hd))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] TriangleUniformizationGluing.instIsManifold3
    TriangleUniformizationGluing.instIsManifold4 in
@[simp]
theorem TriangleUniformizationGluing.SignedHalfPlaneMap.quotientBiholomorph_toHomeomorph
    (D : TriangleUniformizationGluing.SignedHalfPlaneMap)
    (hlocal : IsProperMap (fun z : SpecialPeriods.Triangle.halfFordRegion => D.toFun z))
    (hd : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.toFun : ℍ → ℂ) SpecialPeriods.Triangle.halfFordInterior) :
    (D.quotientBiholomorph hlocal hd).toHomeomorph = D.quotientHomeomorph hlocal :=
  TriangleUniformizationGluing.biholomorphOfHomeomorph_toHomeomorph _ _

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Triangle.trianglePlaneUniformization :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω :=
  RiemannMapping.triangleSignedHalfPlaneMap.quotientBiholomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
    RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Triangle.triangleSphereUniformization :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω :=
  RiemannMapping.triangleSignedHalfPlaneMap.compactifiedBiholomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
    RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.trianglePlaneUniformization_toHomeomorph :
    trianglePlaneUniformization.toHomeomorph = trianglePlaneUniformizationHomeomorph :=
  RiemannMapping.triangleSignedHalfPlaneMap.quotientBiholomorph_toHomeomorph
    RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
    RiemannMapping.triangleSignedHalfPlaneMap_holomorphicOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformization_cusp :
    triangleSphereUniformization SpecialPeriods.triangleCuspPoint =
      ((OnePoint.infty) : RiemannSphere) :=
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformization_openInclusion
    (q : SpecialPeriods.TriangleOrbitSpace) :
    triangleSphereUniformization (SpecialPeriods.triangleOpenInclusion q) =
      ((trianglePlaneUniformization q : ℂ) : RiemannSphere) :=
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.trianglePlaneUniformization_centerOne :
    trianglePlaneUniformization SpecialPeriods.triangleOrbitCenterOne = 0 :=
  trianglePlaneUniformizationHomeomorph_centerOne

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.trianglePlaneUniformization_centerTwo :
    trianglePlaneUniformization SpecialPeriods.triangleOrbitCenterTwo = 1 :=
  trianglePlaneUniformizationHomeomorph_centerTwo

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformization_centerOne :
    triangleSphereUniformization
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
      ((0 : ℂ) : RiemannSphere) :=
  triangleSphereUniformizationHomeomorph_centerOne

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo :
    triangleSphereUniformization
        (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
      ((1 : ℂ) : RiemannSphere) :=
  triangleSphereUniformizationHomeomorph_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.specialPeriodMap : HolomorphicPeriodMap ℂ ℍ :=
  Construction.periodMapOfSphere Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.specialPeriodMap_generator₁ (z : ℍ) :
    specialPeriodMap.point (Triangle.generatorOneSL • z) = (specialPeriodMap.point z).step₁ :=
  Construction.periodMapOfSphere_generator₁ Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.specialPeriodMap_generator₂ (z : ℍ) :
    specialPeriodMap.point (Triangle.generatorTwoSL • z) = (specialPeriodMap.point z).step₂ :=
  Construction.periodMapOfSphere_generator₂ Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.specialCuspData : CuspFamily.Data :=
  Construction.cuspDataOfSphere Triangle.triangleSphereUniformization
    Triangle.triangleSphereUniformization_cusp Triangle.triangleSphereUniformization_centerOne
    Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialBaseCover : BaseCover :=
  baseCoverOfSphere SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialBaseCover_cusp_radius_bounds :
    0 < specialBaseCover.radius Option.none ∧
      specialBaseCover.radius Option.none < SpecialPeriods.specialCuspData.radius ∧
        specialBaseCover.radius Option.none <
          SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width :=
  baseCoverOfSphere_cusp_radius_bounds SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.regularPatchPoint : regularPatch := by
  let x := SpecialPeriods.Triangle.triangleSphereUniformization.symm ((2 : ℂ) : RiemannSphere)
  have hx : SpecialPeriods.Triangle.triangleSphereUniformization x = ((2 : ℂ) : RiemannSphere) :=
    SpecialPeriods.Triangle.triangleSphereUniformization.apply_symm_apply _
  refine ⟨x, (mem_regularPatch x).mpr ⟨?_, ?_, ?_⟩⟩
  · intro h
    have he := congrArg SpecialPeriods.Triangle.triangleSphereUniformization h
    rw [hx, SpecialPeriods.Triangle.triangleSphereUniformization_cusp] at he
    exact OnePoint.coe_ne_infty (2 : ℂ) he
  · intro h
    have he := congrArg SpecialPeriods.Triangle.triangleSphereUniformization h
    change
      SpecialPeriods.Triangle.triangleSphereUniformization x =
        SpecialPeriods.Triangle.triangleSphereUniformization
          (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) at he
    rw [hx, SpecialPeriods.Triangle.triangleSphereUniformization_centerOne] at he
    have he' := OnePoint.coe_injective he
    norm_num at he'
  · intro h
    have he := congrArg SpecialPeriods.Triangle.triangleSphereUniformization h
    change
      SpecialPeriods.Triangle.triangleSphereUniformization x =
        SpecialPeriods.Triangle.triangleSphereUniformization
          (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) at he
    rw [hx, SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo] at he
    have he' := OnePoint.coe_injective he
    norm_num at he'

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.SpecialRegularFamily :=
  RegularFamily SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.specialRegularFamilyChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) SpecialRegularFamily :=
  regularFamilyChartedSpace SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialRegularFamilyProjection :
    SpecialRegularFamily → regularPatch :=
  regularFamilyProjection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialRegularFamilyProjectionToBase :
    SpecialRegularFamily → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  regularFamilyProjectionToBase SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialRegularFamilyProjection_proper :
    IsProperMap specialRegularFamilyProjection :=
  regularFamilyProjection_proper SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialRegularFamily_t2Space : T2Space SpecialRegularFamily :=
  regularFamily_t2Space SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialRegularFamily_secondCountable :
    SecondCountableTopology SpecialRegularFamily :=
  regularFamily_secondCountable SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialRegularFamily_isManifold :
    letI := specialRegularFamilyChartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω SpecialRegularFamily :=
  regularFamily_isManifold SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialRegularFamilyPoint : SpecialRegularFamily :=
  regularFamilyZeroSection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    regularPatchPoint

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialRegularFamily_nonempty : Nonempty SpecialRegularFamily :=
  ⟨specialRegularFamilyPoint⟩

structure Elliptic.Equivariant.Data (j : Elliptic.Kind) where
  periods : HolomorphicPeriodMap ℂ SpecialPeriods.Disc
  covariance :
    ∀ z, periods.point (Elliptic.familyRotation j z) = Elliptic.periodStep j (periods.point z)

abbrev Elliptic.Equivariant.Data.TotalSpace {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :=
  D.periods.TotalSpace

def Elliptic.Equivariant.Data.permutation {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) : Equiv.Perm D.TotalSpace :=
  Elliptic.familyPermutation j v

@[simp]
theorem Elliptic.Equivariant.Data.permutation_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : D.TotalSpace) :
    D.permutation v x = (Elliptic.familyRotation j x.1, Elliptic.flatTorusAffine j v x.2) :=
  rfl

theorem Elliptic.Equivariant.Data.permutation_pow_order {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    D.permutation v ^ j.order = 1 :=
  Elliptic.familyPermutation_pow_order j v hv

@[instance_reducible]
def Elliptic.Equivariant.Data.action {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : MulAction (Elliptic.CyclicGroup j) D.TotalSpace :=
  Elliptic.familyAction j v hv

theorem Elliptic.Equivariant.Data.action_apply {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    g • x =
      ((Elliptic.familyRotation j)^[g.toAdd.val] x.1,
        (Elliptic.flatTorusAffine j v)^[g.toAdd.val] x.2) :=
  Elliptic.familyAction_apply j v hv g x

theorem Elliptic.Equivariant.Data.action_free {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.action v hv.1
    IsCancelSMul (Elliptic.CyclicGroup j) D.TotalSpace :=
  Elliptic.familyAction_free j v hv

theorem Elliptic.Equivariant.Data.action_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.action v hv
    ContinuousConstSMul (Elliptic.CyclicGroup j) D.TotalSpace :=
  Elliptic.familyAction_continuous j v hv

theorem Elliptic.Equivariant.Data.action_discPower {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    Elliptic.discPower j.order j.order_pos (g • x).1 =
      Elliptic.discPower j.order j.order_pos x.1 :=
  Elliptic.familyAction_discPower j v hv g x

def Elliptic.Equivariant.Data.centralPeriod {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : Elliptic.FixedPeriod j :=
  ⟨D.periods.point SpecialPeriods.discZero,
    (D.covariance SpecialPeriods.discZero).symm.trans
      (congrArg D.periods.point (Elliptic.familyRotation_zero j))⟩

theorem Elliptic.Equivariant.Data.periodEquiv_matrix {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.periods.periodEquiv z x = (D.periods.point z).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem Elliptic.Equivariant.Data.periodEquiv_eq_periodEquiv {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.periods.periodEquiv z x = Elliptic.periodEquiv (D.periods.point z) x := by
  rw [D.periodEquiv_matrix, Elliptic.periodEquiv_matrix]

theorem Elliptic.Equivariant.Data.matrix_covariance {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) :
    (D.periods.point (Elliptic.familyRotation j z)).val.matrix *
        j.matrix.map (Int.castRingHom ℂ) =
      Elliptic.linearMatrix j (D.periods.point z) * (D.periods.point z).val.matrix := by
  rw [D.covariance z]
  cases j
  · change
      (D.periods.point z).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) =
        (D.periods.point z).val.R₁ * (D.periods.point z).val.matrix
    rw [PeriodPoint.step₁_matrix _
        ((D.periods.point z).val.τ_ne_zero (D.periods.point z).property.1),
      Matrix.mul_assoc]
    have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
      change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
      rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
      simp
    rw [h, Matrix.mul_one]
  · change
      (D.periods.point z).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) =
        (D.periods.point z).val.R₂ * (D.periods.point z).val.matrix
    rw [PeriodPoint.step₂_matrix _
        ((D.periods.point z).val.τ_ne_zero (D.periods.point z).property.1),
      Matrix.mul_assoc]
    have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
      change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
      rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
      simp
    rw [h, Matrix.mul_one]

theorem Elliptic.Equivariant.Data.periodEquiv_flatLinear {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (x : Elliptic.RealCoordinates) :
    D.periods.periodEquiv (Elliptic.familyRotation j z) (Elliptic.flatLinear j x) =
      Elliptic.linearMatrix j (D.periods.point z) *ᵥ D.periods.periodEquiv z x := by
  rw [D.periodEquiv_matrix, Elliptic.flatLinear_complexCast, Matrix.mulVec_mulVec,
    D.periodEquiv_matrix, Matrix.mulVec_mulVec, D.matrix_covariance]

theorem Elliptic.Equivariant.Data.periodEquiv_symm_linearMatrix {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (z : SpecialPeriods.Disc) (w : ComplexPlane₂) :
    (D.periods.periodEquiv (Elliptic.familyRotation j z)).symm
        (Elliptic.linearMatrix j (D.periods.point z) *ᵥ w) =
      Elliptic.flatLinear j ((D.periods.periodEquiv z).symm w) := by
  apply (D.periods.periodEquiv (Elliptic.familyRotation j z)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_flatLinear, LinearEquiv.apply_symm_apply]

@[instance_reducible]
def Elliptic.Equivariant.Data.equivariantCoveringChartedSpace :
    ChartedSpace Elliptic.FamilyModel (SpecialPeriods.Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (SpecialPeriods.Disc × ComplexPlane₂))

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace in
theorem Elliptic.Equivariant.Data.equivariantCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (SpecialPeriods.Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ComplexPlane₂)
      SpecialPeriods.Disc ComplexPlane₂

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
def Elliptic.Equivariant.Data.complexLift {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    SpecialPeriods.Disc × ComplexPlane₂ :=
  (Elliptic.familyRotation j x.1,
    Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2 +
      D.periods.periodEquiv (Elliptic.familyRotation j x.1)
        ((1 / (j.order : ℝ)) • Elliptic.realCast v))

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
theorem Elliptic.Equivariant.Data.complexLift_quotientMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    D.periods.quotientMap (D.complexLift v x) = D.permutation v (D.periods.quotientMap x) := by
  change
    (Elliptic.familyRotation j x.1,
        standardLattice.mkQ
          ((D.periods.periodEquiv (Elliptic.familyRotation j x.1)).symm
            (Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2 +
              D.periods.periodEquiv (Elliptic.familyRotation j x.1)
                ((1 / (j.order : ℝ)) • Elliptic.realCast v)))) =
      (Elliptic.familyRotation j x.1,
        Elliptic.flatTorusAffine j v (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [Elliptic.flatTorusAffine_mkQ, map_add, LinearEquiv.symm_apply_apply,
    D.periodEquiv_symm_linearMatrix]
  rfl

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
theorem Elliptic.Equivariant.Data.linearLift_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ =>
        Elliptic.linearMatrix j (D.periods.point x.1) *ᵥ x.2) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.Disc) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (Prod.snd : SpecialPeriods.Disc × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hτ := D.periods.holomorphic_tau.comp hf
  have hμ := D.periods.holomorphic_mu.comp hf
  have hτ0 : ∀ x : SpecialPeriods.Disc × ComplexPlane₂, (D.periods.point x.1).val.τ ≠ 0 :=
    fun x => (D.periods.point x.1).val.τ_ne_zero (D.periods.point x.1).property.1
  have h₀ := (contMDiff_pi_space.mp hs) 0
  have h₁ := (contMDiff_pi_space.mp hs) 1
  cases j
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (-1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((((contMDiff_const (c := (1 : ℂ))).sub hμ).div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((hμ.neg.div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [Elliptic.linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
theorem Elliptic.Equivariant.Data.complexLift_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.complexLift v) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ => Elliptic.familyRotation j x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (Elliptic.familyRotation j).contMDiff_toFun.comp contMDiff_fst
  have hw :=
    D.linearLift_holomorphic.add
      ((D.periods.holomorphic_periodEquiv_const ((1 / (j.order : ℝ)) • Elliptic.realCast v)).comp
        hf)
  rw [modelWithCornersSelf_prod] at hf hw ⊢
  exact hf.prodMk hw

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
theorem Elliptic.Equivariant.Data.permutation_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.permutation v) := by
  let := D.periods.coveringAction
  let := D.periods.totalChartedSpace
  apply
    CoveringQuotient.contMDiff_of_comp (E := Elliptic.FamilyModel) D.periods.quotientCoveringMap
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
  have h := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic v)
  convert! h using 1
  funext x
  exact (D.complexLift_quotientMap v x).symm

attribute [local instance] Elliptic.Equivariant.Data.equivariantCoveringChartedSpace
    Elliptic.Equivariant.Data.equivariantCoveringManifold in
theorem Elliptic.Equivariant.Data.action_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    letI := D.action v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fun x : D.TotalSpace => g • x) := by
  let := D.periods.totalChartedSpace
  exact
    Elliptic.CyclicAction.smul_contMDiff (D.permutation v) (D.permutation_pow_order v hv)
      (D.permutation_holomorphic v) g

theorem Elliptic.Equivariant.Data.discLocallyCompact : LocallyCompactSpace SpecialPeriods.Disc :=
  SpecialPeriods.unitDisc.isOpen.locallyCompactSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
def Elliptic.Equivariant.Data.upstairsProjection {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (x : D.TotalSpace) : SpecialPeriods.Disc :=
  Elliptic.discPower j.order j.order_pos x.1

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.upstairsProjection_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : Function.Surjective D.upstairsProjection :=
  (Elliptic.discPower_surjective j.order j.order_pos).comp D.periods.projection_surjective

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.upstairsProjection_proper {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) : IsProperMap D.upstairsProjection :=
  (Elliptic.discPower_isProperMap j.order j.order_pos).comp D.periods.projection_proper

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.upstairsProjection_invariant {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    D.upstairsProjection (g • x) = D.upstairsProjection x :=
  D.action_discPower v hv g x

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
def Elliptic.Equivariant.Data.Space {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : Type :=
  @Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) D.TotalSpace _ (D.action v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
instance Elliptic.Equivariant.Data.spaceTopology {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    TopologicalSpace (D.Space v hv) :=
  inferInstanceAs
    (TopologicalSpace
      (@Elliptic.FiniteQuotient.Space (Elliptic.CyclicGroup j) D.TotalSpace _ (D.action v hv.1)))

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
def Elliptic.Equivariant.Data.quotient {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : D.TotalSpace → D.Space v hv :=
  @Elliptic.FiniteQuotient.project (Elliptic.CyclicGroup j) D.TotalSpace _ (D.action v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotient_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Surjective (D.quotient v hv) :=
  Quotient.mk_surjective

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotient_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (D.quotient v hv) := by
  let := D.action v hv.1
  exact Elliptic.FiniteQuotient.project_continuous (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotient_eq_iff_mem_orbit {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x y : D.TotalSpace) :
    letI := D.action v hv.1
    D.quotient v hv x = D.quotient v hv y ↔ x ∈ MulAction.orbit (Elliptic.CyclicGroup j) y := by
  let := D.action v hv.1
  exact Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j) D.TotalSpace x y

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
@[simp]
theorem Elliptic.Equivariant.Data.quotient_smul {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (g : Elliptic.CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv.1
    D.quotient v hv (g • x) = D.quotient v hv x := by
  let := D.action v hv.1
  exact Elliptic.FiniteQuotient.project_smul (Elliptic.CyclicGroup j) D.TotalSpace g x

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
instance Elliptic.Equivariant.Data.spaceT2 {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : T2Space (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact Elliptic.FiniteQuotient.spaceT2Space (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
instance Elliptic.Equivariant.Data.spaceSecondCountable {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    SecondCountableTopology (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact Elliptic.FiniteQuotient.spaceSecondCountableTopology (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotientCoveringMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.action v hv.1
    IsQuotientCoveringMap (D.quotient v hv) (Elliptic.CyclicGroup j) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  exact
    Elliptic.FiniteQuotient.project_isQuotientCoveringMap (Elliptic.CyclicGroup j) D.TotalSpace

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotient_isCoveringMap {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    IsCoveringMap (D.quotient v hv) := by
  let := D.action v hv.1
  exact (D.quotientCoveringMap v hv).isCoveringMap

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
@[instance_reducible]
def Elliptic.Equivariant.Data.chartedSpace {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    ChartedSpace Elliptic.FamilyModel (D.Space v hv) := by
  let := D.periods.totalChartedSpace
  let := D.action v hv.1
  exact CoveringQuotient.chartedSpace (E := Elliptic.FamilyModel) (D.quotientCoveringMap v hv)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.isManifold {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.Space v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact CoveringQuotient.isManifold (D.quotientCoveringMap v hv) ω (D.action_holomorphic v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotient_holomorphic {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (D.quotient v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact
    CoveringQuotient.contMDiff_project (D.quotientCoveringMap v hv) ω
      (D.action_holomorphic v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.quotient_fibre_card {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (y : D.Space v hv) : Nat.card (D.quotient v hv ⁻¹' { y }) = j.order := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  calc
    _ = Nat.card (Elliptic.CyclicGroup j) :=
      Elliptic.FiniteQuotient.fibre_card (Elliptic.CyclicGroup j) D.TotalSpace y
    _ = j.order := by simp [Elliptic.CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
def Elliptic.Equivariant.Data.projection {j : Elliptic.Kind} (D : Elliptic.Equivariant.Data j)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) : D.Space v hv → SpecialPeriods.Disc := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend D.upstairsProjection (D.upstairsProjection_invariant v hv.1)

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
@[simp]
theorem Elliptic.Equivariant.Data.projection_quotient {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : D.TotalSpace) :
    D.projection v hv (D.quotient v hv x) = Elliptic.discPower j.order j.order_pos x.1 :=
  rfl

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.projection_surjective {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Function.Surjective (D.projection v hv) := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend_surjective D.upstairsProjection
      (D.upstairsProjection_invariant v hv.1) D.upstairsProjection_surjective

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.projection_proper {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    IsProperMap (D.projection v hv) := by
  let := D.action v hv.1
  exact
    Elliptic.FiniteQuotient.descend_isProperMap D.upstairsProjection
      (D.upstairsProjection_invariant v hv.1) D.upstairsProjection_proper

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.projection_continuous {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    Continuous (D.projection v hv) :=
  (D.projection_proper v hv).continuous

attribute [local instance] Elliptic.Equivariant.Data.discLocallyCompact in
theorem Elliptic.Equivariant.Data.projection_central_fibre {j : Elliptic.Kind}
    (D : Elliptic.Equivariant.Data j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    D.projection v hv ⁻¹' { Elliptic.discZero } =
      D.quotient v hv '' {x : D.TotalSpace | x.1 = Elliptic.discZero} := by
  let := D.action v hv.1
  change
    Elliptic.FiniteQuotient.descend D.upstairsProjection
          (D.upstairsProjection_invariant v hv.1) ⁻¹'
        { Elliptic.discZero } =
      _
  rw [Elliptic.FiniteQuotient.descend_preimage_eq_image]
  congr 1
  ext x
  exact Elliptic.discPower_eq_zero_iff j.order j.order_pos x.1

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.ellipticNeighborhoodChart_symm_generator
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    letI := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
    (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z) =
      SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
        (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z := by
  let := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
  apply (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).injective
  change
    SpecialPeriods.Triangle.ellipticNeighborhoodChart j
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm
          (Elliptic.familyRotation j z)) =
      SpecialPeriods.Triangle.ellipticNeighborhoodChart j
        (SpecialPeriods.Triangle.ellipticStabilizerGenerator j •
          (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z)
  rw [Diffeomorph.apply_symm_apply, SpecialPeriods.Triangle.ellipticNeighborhoodChart_generator,
    Diffeomorph.apply_symm_apply]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.ellipticNeighborhoodChart_symm_generatorSL
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm (Elliptic.familyRotation j z) :
        ℍ) =
      SpecialPeriods.Triangle.ellipticGeneratorSL j •
        ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z : ℍ) := by
  let := SpecialPeriods.Triangle.ellipticNeighborhoodAction j
  have h :=
    congrArg (Subtype.val : SpecialPeriods.Triangle.ellipticNeighborhood j → ℍ)
      (ellipticNeighborhoodChart_symm_generator j z)
  simpa only [SpecialPeriods.Triangle.ellipticNeighborhood_smul_val,
    SpecialPeriods.Triangle.ellipticStabilizerGenerator_val,
    SpecialPeriods.Triangle.ellipticGenerator_smul] using h

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.neighborhoodLift (j : Elliptic.Kind)
    (z : SpecialPeriods.Disc) : ℍ :=
  ((SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm z : ℍ)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.neighborhoodLift_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (neighborhoodLift j) :=
  contMDiff_subtype_val.comp (SpecialPeriods.Triangle.ellipticNeighborhoodChart j).symm.contMDiff

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.neighborhoodLift_rotation (j : Elliptic.Kind)
    (z : SpecialPeriods.Disc) :
    neighborhoodLift j (Elliptic.familyRotation j z) =
      SpecialPeriods.Triangle.ellipticGeneratorSL j • neighborhoodLift j z :=
  ellipticNeighborhoodChart_symm_generatorSL j z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.localPeriods (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) : HolomorphicPeriodMap ℂ SpecialPeriods.Disc
    where
  point z := P.point (neighborhoodLift j z)
  holomorphic_tau := P.holomorphic_tau.comp (neighborhoodLift_holomorphic j)
  holomorphic_mu := P.holomorphic_mu.comp (neighborhoodLift_holomorphic j)
  holomorphic_beta := P.holomorphic_beta.comp (neighborhoodLift_holomorphic j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.EllipticFilling.localPeriods_point (P : HolomorphicPeriodMap ℂ ℍ)
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    (localPeriods P j).point z = P.point (neighborhoodLift j z) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.localPeriods_covariance (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) (z : SpecialPeriods.Disc) :
    (localPeriods P j).point (Elliptic.familyRotation j z) =
      Elliptic.periodStep j ((localPeriods P j).point z) := by
  simp only [localPeriods_point, neighborhoodLift_rotation]
  cases j
  · exact h₁ _
  · exact h₂ _

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.localData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Elliptic.Equivariant.Data j
    where
  periods := localPeriods P j
  covariance := localPeriods_covariance P h₁ h₂ j

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.EllipticFilling.localData_periods (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : (localData P h₁ h₂ j).periods = localPeriods P j :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
abbrev SpecialPeriods.EllipticFilling.fillingSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :=
  (localData P h₁ h₂ j).Space j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.fillingQuotient (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : (localPeriods P j).TotalSpace → fillingSpace P h₁ h₂ j :=
  (localData P h₁ h₂ j).quotient j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.EllipticFilling.fillingProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : fillingSpace P h₁ h₂ j → SpecialPeriods.Disc :=
  (localData P h₁ h₂ j).projection j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[instance_reducible]
def SpecialPeriods.EllipticFilling.fillingChartedSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : ChartedSpace Elliptic.FamilyModel (fillingSpace P h₁ h₂ j) :=
  (localData P h₁ h₂ j).chartedSpace j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.filling_isManifold (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (fillingSpace P h₁ h₂ j) :=
  (localData P h₁ h₂ j).isManifold j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.fillingQuotient_isCoveringMap
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : IsCoveringMap (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_isCoveringMap j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.fillingQuotient_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Function.Surjective (fillingQuotient P h₁ h₂ j) :=
  (localData P h₁ h₂ j).quotient_surjective j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.fillingProjection_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : IsProperMap (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_proper j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.fillingProjection_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Function.Surjective (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_surjective j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.EllipticFilling.fillingProjection_continuous (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (j : Elliptic.Kind) : Continuous (fillingProjection P h₁ h₂ j) :=
  (localData P h₁ h₂ j).projection_continuous j.twist (Elliptic.mainTwist_admissible j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.EllipticFilling.smallDisc (r : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.Disc :=
  ⟨{z | ‖(z : ℂ)‖ < r}, isOpen_lt continuous_subtype_val.norm continuous_const⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.EllipticFilling.smallDiscHomeomorph (r : ℝ) (hr : r < 1) :
    smallDisc r ≃ₜ SpecialPeriods.Threefold.coordinateBall r
    where
  toFun
    z :=
    ⟨((z : SpecialPeriods.Disc) : ℂ), by
      simpa [SpecialPeriods.Threefold.coordinateBall, smallDisc] using z.property⟩
  invFun
    z := by
    have hz : ‖(z : ℂ)‖ < r := by
      simpa [SpecialPeriods.Threefold.coordinateBall, smallDisc] using z.property
    exact ⟨⟨(z : ℂ), by simpa [SpecialPeriods.unitDisc] using hz.trans hr⟩, hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.EllipticFilling.pieceDomain (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    TopologicalSpace.Opens (fillingSpace P h₁ h₂ j) :=
  ⟨{y | ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (Option.some j)},
    isOpen_lt (continuous_subtype_val.comp (fillingProjection_continuous P h₁ h₂ j)).norm
      continuous_const⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.EllipticFilling.Piece (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :=
  pieceDomain P h₁ h₂ C j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.EllipticFilling.pieceChartedSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    ChartedSpace Elliptic.FamilyModel (Piece P h₁ h₂ C j) := by
  letI := fillingChartedSpace P h₁ h₂ j
  infer_instance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.piece_t2Space (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) : T2Space (Piece P h₁ h₂ C j) :=
  inferInstance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.piece_secondCountable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    SecondCountableTopology (Piece P h₁ h₂ C j) :=
  inferInstance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.piece_isManifold (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    letI := pieceChartedSpace P h₁ h₂ C j
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (Piece P h₁ h₂ C j) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := filling_isManifold P h₁ h₂ j
  infer_instance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.EllipticFilling.pieceCoordinate (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Piece P h₁ h₂ C j → SpecialPeriods.Threefold.coordinateBall (C.radius (Option.some j)) :=
  fun y =>
  ⟨(fillingProjection P h₁ h₂ j y : ℂ),
    by
    change (fillingProjection P h₁ h₂ j y : ℂ) ∈ Metric.ball 0 (C.radius (Option.some j))
    rw [Metric.mem_ball, dist_zero_right]
    exact y.property⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.pieceCoordinate_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Function.Surjective (pieceCoordinate P h₁ h₂ C j) := by
  intro z
  have hz : ‖(z : ℂ)‖ < C.radius (Option.some j) := by
    simpa only [SpecialPeriods.Threefold.mem_coordinateBall, Metric.mem_ball,
      dist_zero_right] using z.property
  have hr : C.radius (Option.some j) < 1 := C.radius_lt_chart (Option.some j)
  let w : SpecialPeriods.Disc :=
    ⟨z, by
      change (z : ℂ) ∈ Metric.ball 0 1
      simpa only [Metric.mem_ball, dist_zero_right] using hz.trans hr⟩
  obtain ⟨y, hy⟩ := fillingProjection_surjective P h₁ h₂ j w
  have hy' : y ∈ pieceDomain P h₁ h₂ C j := by
    change ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (Option.some j)
    rw [hy]
    exact hz
  refine ⟨⟨y, hy'⟩, Subtype.ext ?_⟩
  exact congrArg (Subtype.val : SpecialPeriods.Disc → ℂ) hy

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.pieceCoordinate_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    IsProperMap (pieceCoordinate P h₁ h₂ C j) :=
  (smallDiscHomeomorph (C.radius (Option.some j))
        (C.radius_lt_chart (Option.some j))).isProperMap.comp
    ((fillingProjection_proper P h₁ h₂ j).restrictPreimage
      (smallDisc (C.radius (Option.some j)) : Set SpecialPeriods.Disc))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.EllipticFilling.pieceProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Piece P h₁ h₂ C j → C.fillingPatch (Option.some j) :=
  (C.fillingChart (Option.some j)).symm ∘ pieceCoordinate P h₁ h₂ C j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.pieceProjection_surjective (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Function.Surjective (pieceProjection P h₁ h₂ C j) :=
  (C.fillingChart (Option.some j)).symm.surjective.comp (pieceCoordinate_surjective P h₁ h₂ C j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.pieceProjection_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    IsProperMap (pieceProjection P h₁ h₂ C j) :=
  (C.fillingChart (Option.some j)).symm.toHomeomorph.isProperMap.comp
    (pieceCoordinate_proper P h₁ h₂ C j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.EllipticFilling.pieceProjectionToBase (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) :
    Piece P h₁ h₂ C j → SpecialPeriods.TriangleCompactifiedOrbitSpace := fun y =>
  (pieceProjection P h₁ h₂ C j y : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.EllipticFilling.pieceProjectionToBase_mem_regular_iff
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (C : SpecialPeriods.Threefold.BaseCover) (j : Elliptic.Kind) (y : Piece P h₁ h₂ C j) :
    pieceProjectionToBase P h₁ h₂ C j y ∈ SpecialPeriods.Threefold.regularPatch ↔
      (fillingProjection P h₁ h₂ j y : ℂ) ≠ 0 :=
  C.fillingEmbedding_mem_regular_iff (Option.some j) (pieceCoordinate P h₁ h₂ C j y)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.SpecialEllipticPiece (j : Elliptic.Kind) :=
  SpecialPeriods.EllipticFilling.Piece SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.specialEllipticPieceChartedSpace (j : Elliptic.Kind) :
    ChartedSpace (ℂ × ComplexPlane₂) (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.pieceChartedSpace SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialEllipticPieceProjection (j : Elliptic.Kind) :
    SpecialEllipticPiece j → specialBaseCover.fillingPatch (Option.some j) :=
  SpecialPeriods.EllipticFilling.pieceProjection SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.specialEllipticPieceProjectionToBase (j : Elliptic.Kind) :
    SpecialEllipticPiece j → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.EllipticFilling.pieceProjectionToBase SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPieceProjection_proper (j : Elliptic.Kind) :
    IsProperMap (specialEllipticPieceProjection j) :=
  SpecialPeriods.EllipticFilling.pieceProjection_proper SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPieceProjection_surjective (j : Elliptic.Kind) :
    Function.Surjective (specialEllipticPieceProjection j) :=
  SpecialPeriods.EllipticFilling.pieceProjection_surjective SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPiece_t2Space (j : Elliptic.Kind) :
    T2Space (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.piece_t2Space SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPiece_secondCountable (j : Elliptic.Kind) :
    SecondCountableTopology (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.piece_secondCountable SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPiece_isManifold (j : Elliptic.Kind) :
    letI := specialEllipticPieceChartedSpace j
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (SpecialEllipticPiece j) :=
  SpecialPeriods.EllipticFilling.piece_isManifold SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂
    specialBaseCover j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.specialEllipticPiece_nonempty (j : Elliptic.Kind) :
    Nonempty (SpecialEllipticPiece j) := by
  obtain ⟨x, _⟩ :=
    specialEllipticPieceProjection_surjective j
      ⟨puncturePoint (Option.some j), specialBaseCover.point_mem_fillingPatch (Option.some j)⟩
  exact ⟨x⟩

def SpecialPeriods.CuspFamily.Data.shrink (D : SpecialPeriods.CuspFamily.Data) (r : ℝ)
    (hr : 0 < r) (hrD : r ≤ D.radius) : SpecialPeriods.CuspFamily.Data
    where
  μ := D.μ
  b := D.b
  h := D.h
  radius := r
  radius_pos := hr
  radius_lt_one := hrD.trans_lt D.radius_lt_one
  holomorphic i j := (D.holomorphic i j).mono (Metric.ball_subset_ball hrD)
  smallDrift := D.smallDrift.mono hrD

private theorem SpecialPeriods.CuspFamily.complex_width_ne_zero_mo1973_20202 :
    (SpecialPeriods.Triangle.width : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr SpecialPeriods.Triangle.width_ne_zero

theorem SpecialPeriods.CuspFamily.qParam_width_mul (s : ℂ) :
    Function.Periodic.qParam SpecialPeriods.Triangle.width
        ((SpecialPeriods.Triangle.width : ℂ) * s) =
      CuspUniformization.exponential s := by
  unfold Function.Periodic.qParam CuspUniformization.exponential
  congr 1
  rw [mul_left_comm, mul_div_cancel_left₀ _ complex_width_ne_zero_mo1973_20202]

theorem SpecialPeriods.CuspFamily.exponential_div_width (z : ℍ) :
    CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width) =
      SpecialPeriods.Triangle.cuspQ z := by
  simp only [CuspUniformization.exponential, SpecialPeriods.Triangle.cuspQ,
    Function.Periodic.qParam, mul_div_assoc]

private theorem SpecialPeriods.CuspFamily.logBase_scaled_height_mo1973_20205 (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    SpecialPeriods.Triangle.width < ((SpecialPeriods.Triangle.width : ℂ) * (s : ℂ)).im := by
  apply
    (Function.Periodic.norm_qParam_lt_iff SpecialPeriods.Triangle.width_pos
        SpecialPeriods.Triangle.width _).mp
  rw [qParam_width_mul]
  exact ((mem_logBase r s).mp s.property).trans_le hrcap

def SpecialPeriods.CuspFamily.cuspOverlapUpperDomain (r : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | ‖SpecialPeriods.Triangle.cuspQ z‖ < r},
    isOpen_lt SpecialPeriods.Triangle.cuspQ_continuous.norm continuous_const⟩

@[simp]
theorem SpecialPeriods.CuspFamily.mem_cuspOverlapUpperDomain (r : ℝ) (z : ℍ) :
    z ∈ cuspOverlapUpperDomain r ↔ ‖SpecialPeriods.Triangle.cuspQ z‖ < r :=
  Iff.rfl

theorem SpecialPeriods.CuspFamily.cuspOverlapUpperDomain_subset_horodisc (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    (cuspOverlapUpperDomain r : Set ℍ) ⊆
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width := by
  intro z hz
  exact
    (SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff SpecialPeriods.Triangle.width z).mp
      (hz.trans_le hrcap)

theorem SpecialPeriods.CuspFamily.cuspOverlapUpperDomain_subset_regular (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    (cuspOverlapUpperDomain r : Set ℍ) ⊆ SpecialPeriods.triangleRegularLocus :=
  (cuspOverlapUpperDomain_subset_horodisc r hrcap).trans
    (SpecialPeriods.Triangle.horodisc_subset_triangleRegularLocus SpecialPeriods.Triangle.width
      le_rfl)

def SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane (r : ℝ)
    (_hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : ℍ :=
  UpperHalfPlane.ofComplex ((SpecialPeriods.Triangle.width : ℂ) * (s : ℂ))

@[simp]
theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_coe (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    (logBaseToUpperHalfPlane r hrcap s : ℂ) = (SpecialPeriods.Triangle.width : ℂ) * (s : ℂ) :=
  congrArg UpperHalfPlane.coe
    (UpperHalfPlane.ofComplex_apply_of_im_pos
      (SpecialPeriods.Triangle.width_pos.trans (logBase_scaled_height_mo1973_20205 r hrcap s)))

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_mem_horodisc (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    logBaseToUpperHalfPlane r hrcap s ∈
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width := by
  change SpecialPeriods.Triangle.width < (logBaseToUpperHalfPlane r hrcap s).im
  rw [← UpperHalfPlane.coe_im, logBaseToUpperHalfPlane_coe]
  exact logBase_scaled_height_mo1973_20205 r hrcap s

@[simp]
theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_cuspQ (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    SpecialPeriods.Triangle.cuspQ (logBaseToUpperHalfPlane r hrcap s) =
      CuspUniformization.exponential s := by
  rw [SpecialPeriods.Triangle.cuspQ, logBaseToUpperHalfPlane_coe, qParam_width_mul]

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_mem_domain (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : logBaseToUpperHalfPlane r hrcap s ∈ cuspOverlapUpperDomain r := by
  rw [mem_cuspOverlapUpperDomain, logBaseToUpperHalfPlane_cuspQ]
  exact (mem_logBase r s).mp s.property

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_holomorphic (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToUpperHalfPlane r hrcap) := by
  have h :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun s : LogBase r => (SpecialPeriods.Triangle.width : ℂ) * (s : ℂ)) :=
    contMDiff_const.mul contMDiff_subtype_val
  intro s
  exact
    (UpperHalfPlane.contMDiffAt_ofComplex
          (SpecialPeriods.Triangle.width_pos.trans
            (logBase_scaled_height_mo1973_20205 r hrcap s))).comp
      s (h s)

def SpecialPeriods.CuspFamily.logBaseToOverlapUpperDomain (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : cuspOverlapUpperDomain r :=
  ⟨logBaseToUpperHalfPlane r hrcap s, logBaseToUpperHalfPlane_mem_domain r hrcap s⟩

def SpecialPeriods.CuspFamily.overlapUpperToLogBase (r : ℝ) (z : cuspOverlapUpperDomain r) :
    LogBase r :=
  ⟨(z.val : ℂ) / SpecialPeriods.Triangle.width,
    by
    rw [mem_logBase, exponential_div_width]
    exact z.property⟩

@[simp]
theorem SpecialPeriods.CuspFamily.overlapUpperToLogBase_coe (r : ℝ)
    (z : cuspOverlapUpperDomain r) :
    (overlapUpperToLogBase r z : ℂ) = (z.val : ℂ) / SpecialPeriods.Triangle.width :=
  rfl

theorem SpecialPeriods.CuspFamily.logBaseToOverlapUpperDomain_holomorphic (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToOverlapUpperDomain r hrcap) := by
  intro s
  have hi :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ logBaseToOverlapUpperDomain r hrcap) s ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToOverlapUpperDomain r hrcap) s :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (logBaseToUpperHalfPlane_holomorphic r hrcap s)

theorem SpecialPeriods.CuspFamily.overlapUpperToLogBase_holomorphic (r : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (overlapUpperToLogBase r) := by
  have h :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : cuspOverlapUpperDomain r => (z.val : ℂ) / SpecialPeriods.Triangle.width) :=
    (UpperHalfPlane.contMDiff_coe.comp contMDiff_subtype_val).div_const
      (SpecialPeriods.Triangle.width : ℂ)
  intro z
  have hi :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ overlapUpperToLogBase r) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (overlapUpperToLogBase r) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (h z)

def SpecialPeriods.CuspFamily.logBaseBiholomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (LogBase r) (cuspOverlapUpperDomain r) ω
    where
  toFun := logBaseToOverlapUpperDomain r hrcap
  invFun := overlapUpperToLogBase r
  left_inv
    s := by
    apply Subtype.ext
    change (logBaseToUpperHalfPlane r hrcap s : ℂ) / SpecialPeriods.Triangle.width = (s : ℂ)
    rw [logBaseToUpperHalfPlane_coe, mul_div_cancel_left₀ _ complex_width_ne_zero_mo1973_20202]
  right_inv
    z := by
    apply Subtype.ext
    apply UpperHalfPlane.ext
    change (logBaseToUpperHalfPlane r hrcap (overlapUpperToLogBase r z) : ℂ) = (z.val : ℂ)
    rw [logBaseToUpperHalfPlane_coe, overlapUpperToLogBase_coe,
      mul_div_cancel₀ _ complex_width_ne_zero_mo1973_20202]
  contMDiff_toFun := logBaseToOverlapUpperDomain_holomorphic r hrcap
  contMDiff_invFun := overlapUpperToLogBase_holomorphic r

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_injective (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Injective (logBaseToUpperHalfPlane r hrcap) := by
  intro s t h
  exact (logBaseBiholomorph r hrcap).injective (Subtype.ext h)

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToUpperHalfPlane r hrcap) := by
  intro s
  exact
    ((logBaseBiholomorph r hrcap).isLocalDiffeomorph s).comp (K := 𝓘(ℂ)) (P := ℍ)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) (cuspOverlapUpperDomain r)
        (logBaseBiholomorph r hrcap s))

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_range (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Set.range (logBaseToUpperHalfPlane r hrcap) = (cuspOverlapUpperDomain r : Set ℍ) := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact logBaseToUpperHalfPlane_mem_domain r hrcap s
  · intro hz
    obtain ⟨s, hs⟩ := (logBaseBiholomorph r hrcap).surjective ⟨z, hz⟩
    exact ⟨s, congrArg Subtype.val hs⟩

def SpecialPeriods.CuspFamily.logBaseToRegular (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) : SpecialPeriods.TriangleRegularPoint :=
  ⟨logBaseToUpperHalfPlane r hrcap s,
    (cuspOverlapUpperDomain_subset_regular r hrcap)
      (logBaseToUpperHalfPlane_mem_domain r hrcap s)⟩

@[simp]
theorem SpecialPeriods.CuspFamily.logBaseToRegular_coe (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    ((logBaseToRegular r hrcap s : ℍ) : ℂ) = (SpecialPeriods.Triangle.width : ℂ) * (s : ℂ) :=
  logBaseToUpperHalfPlane_coe r hrcap s

theorem SpecialPeriods.CuspFamily.logBaseToRegular_mem_horodisc (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    (logBaseToRegular r hrcap s : ℍ) ∈
      SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width :=
  logBaseToUpperHalfPlane_mem_horodisc r hrcap s

@[simp]
theorem SpecialPeriods.CuspFamily.logBaseToRegular_cuspQ (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width)
    (s : LogBase r) :
    SpecialPeriods.Triangle.cuspQ (logBaseToRegular r hrcap s : ℍ) =
      CuspUniformization.exponential s :=
  logBaseToUpperHalfPlane_cuspQ r hrcap s

theorem SpecialPeriods.CuspFamily.logBaseToRegular_injective (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    Function.Injective (logBaseToRegular r hrcap) := by
  intro s t h
  exact logBaseToUpperHalfPlane_injective r hrcap (congrArg Subtype.val h)

theorem SpecialPeriods.CuspFamily.logBaseToRegular_isLocalDiffeomorph (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToRegular r hrcap) :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ)
    (logBaseToUpperHalfPlane_isLocalDiffeomorph r hrcap) SpecialPeriods.triangleRegularDomain
    (fun s => (logBaseToRegular r hrcap s).property)

theorem SpecialPeriods.CuspFamily.logBaseToRegular_holomorphic (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (logBaseToRegular r hrcap) :=
  (logBaseToRegular_isLocalDiffeomorph r hrcap).contMDiff

theorem SpecialPeriods.CuspFamily.logBaseToUpperHalfPlane_translate (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) (k : ℤ)
    (s : LogBase r) :
    logBaseToUpperHalfPlane r hrcap (logBaseTranslate r k s) =
      SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ k)
        (logBaseToUpperHalfPlane r hrcap s) := by
  apply UpperHalfPlane.ext
  rw [logBaseToUpperHalfPlane_coe, logBaseTranslate_coe,
    SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe, logBaseToUpperHalfPlane_coe]
  ring

theorem SpecialPeriods.CuspFamily.logBaseToRegular_translate (r : ℝ)
    (hrcap : r ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width) (k : ℤ)
    (s : LogBase r) :
    logBaseToRegular r hrcap (logBaseTranslate r k s) =
      (SpecialPeriods.triangleCuspGenerator ^ k) • logBaseToRegular r hrcap s :=
  Subtype.ext (logBaseToUpperHalfPlane_translate r hrcap k s)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.CuspPiece.restrictedData (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    SpecialPeriods.CuspFamily.Data :=
  D.shrink (C.radius Option.none) (C.radius_pos Option.none) hcap

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.CuspPiece.Space (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) :=
  CuspQuotient.QuotientSpace D.correction (C.radius Option.none)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.CuspPiece.nativeChartedSpace (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    ChartedSpace (ToricCharts.CoordinateSpace 3) (Space D C) :=
  CuspQuotient.chartedSpace D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.space_t2Space (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    T2Space (Space D C) :=
  CuspQuotient.quotient_t2Space D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.space_secondCountable
    (D : SpecialPeriods.CuspFamily.Data) (C : SpecialPeriods.Threefold.BaseCover)
    (hcap : C.radius Option.none ≤ D.radius) : SecondCountableTopology (Space D C) :=
  CuspQuotient.quotient_secondCountable D.correction (C.radius Option.none)
    (C.radius_pos Option.none) (restrictedData D C hcap).radius_lt_one
    (restrictedData D C hcap).holomorphic (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.space_connected (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) : ConnectedSpace (Space D C) :=
  CuspQuotient.quotient_connected D.correction (C.radius Option.none) (C.radius_pos Option.none)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.space_nonempty (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) : Nonempty (Space D C) := by
  let := space_connected D C
  infer_instance

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.native_isManifold (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    IsManifold (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (Space D C) :=
  CuspQuotient.isManifold D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.CuspPiece.coordinate (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) :
    Space D C → SpecialPeriods.Threefold.coordinateBall (C.radius Option.none) :=
  CuspQuotient.baseMap D.correction (C.radius Option.none)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.coordinate_proper (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    IsProperMap (coordinate D C) :=
  CuspQuotient.baseMap_proper D.correction (C.radius Option.none) (C.radius_pos Option.none)
    (restrictedData D C hcap).radius_lt_one (restrictedData D C hcap).holomorphic
    (restrictedData D C hcap).smallDrift

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.CuspPiece.projection (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) : Space D C → C.fillingPatch Option.none :=
  (C.fillingChart Option.none).symm ∘ coordinate D C

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.projection_proper (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    IsProperMap (projection D C) :=
  (C.fillingChart Option.none).symm.toHomeomorph.isProperMap.comp (coordinate_proper D C hcap)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.CuspPiece.projectionToBase (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) :
    Space D C → SpecialPeriods.TriangleCompactifiedOrbitSpace := fun x =>
  (projection D C x : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.CuspPiece.projectionToBase_apply
    (D : SpecialPeriods.CuspFamily.Data) (C : SpecialPeriods.Threefold.BaseCover)
    (x : Space D C) :
    projectionToBase D C x =
      (SpecialPeriods.Threefold.punctureChart Option.none).symm
        (CuspQuotient.projection D.correction (C.radius Option.none) x) :=
  rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.projectionToBase_mem_regular_iff
    (D : SpecialPeriods.CuspFamily.Data) (C : SpecialPeriods.Threefold.BaseCover)
    (x : Space D C) :
    projectionToBase D C x ∈ SpecialPeriods.Threefold.regularPatch ↔
      CuspQuotient.projection D.correction (C.radius Option.none) x ≠ 0 :=
  C.fillingEmbedding_mem_regular_iff Option.none (coordinate D C x)

def SpecialPeriods.Threefold.cuspModelEquiv :
    ToricCharts.CoordinateSpace 3 ≃L[ℂ] (ℂ × ComplexPlane₂)
    where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := ![x.1, x.2 0, x.2 1]
  left_inv
    x := by
    ext i
    fin_cases i <;> rfl
  right_inv
    x := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  map_add' x y := rfl
  map_smul' r x := rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun :=
    continuous_pi fun i => by
      fin_cases i
      · exact continuous_fst
      · exact (continuous_apply 0).comp continuous_snd
      · exact (continuous_apply 1).comp continuous_snd

@[instance_reducible]
def SpecialPeriods.Threefold.ModelChange.chartedSpace {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] : ChartedSpace F X
    where
  atlas :=
    (fun c : OpenPartialHomeomorph X E => c.trans e.toHomeomorph.toOpenPartialHomeomorph) ''
      atlas E X
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [mfld_simps]
  chart_mem_atlas x := Set.mem_image_of_mem _ (chart_mem_atlas E x)

@[simp]
theorem SpecialPeriods.Threefold.ModelChange.chartAt_target {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    letI := chartedSpace e X
    (chartAt F x).target = e.symm ⁻¹' (chartAt E x).target := by
  simp [chartAt, ChartedSpace.chartAt]

def SpecialPeriods.Threefold.ModelChange.diffeomorph {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (n : ℕ∞ω) :
    letI := chartedSpace e X
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) X X n := by
  let := chartedSpace e X
  have hchart (x y : X) : chartAt F x y = e (chartAt E x y) := rfl
  have hsymm (x : X) (y : F) : (chartAt F x).symm y = (chartAt E x).symm (e.symm y) := rfl
  refine { toEquiv := Equiv.refl X, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    apply contMDiffWithinAt_iff'.2
    refine ⟨continuousWithinAt_id, ?_⟩
    apply e.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      have hy' : y ∈ (chartAt E x).target := by simpa [hchart, hsymm] using hy.1
      simpa [hchart, hsymm, extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using
        congrArg e ((chartAt E x).right_inv hy')
    · simp only [mfld_simps]
  · intro x
    apply contMDiffWithinAt_iff'.2
    refine ⟨continuousWithinAt_id, ?_⟩
    apply e.symm.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      have hy' : e.symm y ∈ (chartAt E x).target := by
        simpa only [mfld_simps, chartAt_target] using hy.1
      simpa [hchart, hsymm, extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using
        (chartAt E x).right_inv hy'
    · simp only [mfld_simps]

theorem SpecialPeriods.Threefold.ModelChange.isManifold {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n X] :
    letI := chartedSpace e X
    IsManifold (modelWithCornersSelf ℂ F) n X := by
  let := chartedSpace e X
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have hcd : ContDiffOn ℂ n (c.symm.trans d) (c.symm.trans d).source := by
    simpa [contDiffPregroupoid] using
      ((contDiffGroupoid n (modelWithCornersSelf ℂ E)).compatible hc hd).1
  have hcomp :=
    e.contDiff.comp_contDiffOn
      (hcd.comp e.symm.contDiff.contDiffOn
        (show Set.MapsTo e.symm (e.symm ⁻¹' (c.symm.trans d).source) (c.symm.trans d).source from
          fun _ hy => hy))
  simpa [Set.preimage_preimage, Function.comp_def, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_target] using hcomp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
def SpecialPeriods.Threefold.CuspPiece.commonChartedSpace (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    ChartedSpace (ℂ × ComplexPlane₂) (Space D C) := by
  let := nativeChartedSpace D C hcap
  exact
    SpecialPeriods.Threefold.ModelChange.chartedSpace SpecialPeriods.Threefold.cuspModelEquiv
      (Space D C)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.CuspPiece.common_isManifold (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    letI := commonChartedSpace D C hcap
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (Space D C) := by
  let := nativeChartedSpace D C hcap
  let := native_isManifold D C hcap
  exact
    SpecialPeriods.Threefold.ModelChange.isManifold SpecialPeriods.Threefold.cuspModelEquiv
      (Space D C) ω

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.CuspPiece.nativeToCommon (D : SpecialPeriods.CuspFamily.Data)
    (C : SpecialPeriods.Threefold.BaseCover) (hcap : C.radius Option.none ≤ D.radius) :
    letI := nativeChartedSpace D C hcap
    letI := commonChartedSpace D C hcap
    Diffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (Space D C) (Space D C) ω := by
  let := nativeChartedSpace D C hcap
  exact
    SpecialPeriods.Threefold.ModelChange.diffeomorph SpecialPeriods.Threefold.cuspModelEquiv
      (Space D C) ω

end Mathoverflow1973

end
