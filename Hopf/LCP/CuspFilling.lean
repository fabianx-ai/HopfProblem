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
import Hopf.LCP.LocalModels
import Lib.AlgebraicTopology.SingularHomology.Naturality
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.Topology.Homotopy.LocalCollapse
import Lib.Topology.Covering.InvariantSubset

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

abbrev CuspPositiveRetraction.Orthant :=
  { r : Fin 3 → ℝ // ∀ i, 0 ≤ r i }

theorem CuspPositiveRetraction.orthant_isClosed : IsClosed {r : Fin 3 → ℝ | ∀ i, 0 ≤ r i} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

instance CuspPositiveRetraction.instLocal1 : ProperSpace Orthant :=
  ProperSpace.of_isClosed orthant_isClosed

def CuspPositiveRetraction.height (r : Orthant) : ℝ :=
  ∏ i, r.1 i

theorem CuspPositiveRetraction.height_nonneg (r : Orthant) : 0 ≤ height r :=
  Finset.prod_nonneg fun i _ => r.2 i

theorem CuspPositiveRetraction.height_eq_zero_iff (r : Orthant) : height r = 0 ↔ ∃ i, r.1 i = 0 :=
  by simp only [height, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

def CuspPositiveRetraction.minimum (r : Orthant) : ℝ :=
  Min.min (r.1 0) (Min.min (r.1 1) (r.1 2))

theorem CuspPositiveRetraction.minimum_nonneg (r : Orthant) : 0 ≤ minimum r :=
  le_min (r.2 0) (le_min (r.2 1) (r.2 2))

theorem CuspPositiveRetraction.minimum_le (r : Orthant) (i : Fin 3) : minimum r ≤ r.1 i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem CuspPositiveRetraction.minimum_eq_coordinate (r : Orthant) :
    ∃ i : Fin 3, minimum r = r.1 i := by
  rcases min_choice (r.1 0) (Min.min (r.1 1) (r.1 2)) with h | h
  · exact ⟨0, h⟩
  · rcases min_choice (r.1 1) (r.1 2) with h' | h'
    · exact ⟨1, h.trans h'⟩
    · exact ⟨2, h.trans h'⟩

theorem CuspPositiveRetraction.minimum_eq_zero_iff (r : Orthant) : minimum r = 0 ↔ height r = 0 :=
  by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := minimum_eq_coordinate r
    exact (height_eq_zero_iff r).mpr ⟨i, hi.symm.trans h⟩
  · intro h
    obtain ⟨i, hi⟩ := (height_eq_zero_iff r).mp h
    exact le_antisymm (by simpa only [hi] using minimum_le r i) (minimum_nonneg r)

theorem CuspPositiveRetraction.minimum_continuous : Continuous minimum :=
  ((continuous_apply 0).comp continuous_subtype_val).min
    (((continuous_apply 1).comp continuous_subtype_val).min
      ((continuous_apply 2).comp continuous_subtype_val))

def CuspPositiveRetraction.shrink (s : unitInterval) (r : Orthant) : Orthant :=
  ⟨fun i => r.1 i - (s : ℝ) * minimum r, fun i =>
    sub_nonneg.mpr ((mul_le_of_le_one_left (minimum_nonneg r) s.2.2).trans (minimum_le r i))⟩

@[simp]
theorem CuspPositiveRetraction.shrink_apply (s : unitInterval) (r : Orthant) (i : Fin 3) :
    (shrink s r).1 i = r.1 i - (s : ℝ) * minimum r :=
  rfl

theorem CuspPositiveRetraction.shrink_continuous :
    Continuous (fun p : unitInterval × Orthant => shrink p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).sub
      ((continuous_subtype_val.comp continuous_fst).mul (minimum_continuous.comp continuous_snd))

@[simp]
theorem CuspPositiveRetraction.shrink_zero (r : Orthant) : shrink 0 r = r := by
  apply Subtype.ext
  funext i
  simp only [shrink_apply, Set.Icc.coe_zero, MulZeroClass.zero_mul, sub_zero]

theorem CuspPositiveRetraction.shrink_one_height (r : Orthant) : height (shrink 1 r) = 0 := by
  obtain ⟨i, hi⟩ := minimum_eq_coordinate r
  apply (height_eq_zero_iff _).mpr
  refine ⟨i, ?_⟩
  simp only [shrink_apply, Set.Icc.coe_one, one_mul, hi, sub_self]

theorem CuspPositiveRetraction.shrink_fixed (s : unitInterval) {r : Orthant} (hr : height r = 0) :
    shrink s r = r := by
  apply Subtype.ext
  funext i
  simp only [shrink_apply, (minimum_eq_zero_iff r).mpr hr, MulZeroClass.mul_zero, sub_zero]

theorem CuspPositiveRetraction.shrink_coordinate_le (s : unitInterval) (r : Orthant) (i : Fin 3) :
    (shrink s r).1 i ≤ r.1 i :=
  sub_le_self _ (mul_nonneg s.2.1 (minimum_nonneg r))

theorem CuspPositiveRetraction.shrink_height_le (s : unitInterval) (r : Orthant) :
    height (shrink s r) ≤ height r :=
  Finset.prod_le_prod (fun i _ => (shrink s r).2 i) (fun i _ => shrink_coordinate_le s r i)

theorem CuspPositiveRetraction.shrink_dist_eq (s : unitInterval) (r : Orthant) :
    Dist.dist (shrink s r) r = (s : ℝ) * minimum r := by
  rw [Subtype.dist_eq, dist_eq_norm]
  have he : (shrink s r).1 - r.1 = fun _ : Fin 3 => -((s : ℝ) * minimum r) := by
    funext i
    simp only [Pi.sub_apply, shrink_apply]
    ring
  rw [he, pi_norm_const, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg s.2.1 (minimum_nonneg r))]

theorem CuspPositiveRetraction.shrink_dist_le_minimum (s : unitInterval) (r : Orthant) :
    Dist.dist (shrink s r) r ≤ minimum r := by
  rw [shrink_dist_eq]
  exact mul_le_of_le_one_left (minimum_nonneg r) s.2.2

theorem CuspPositiveRetraction.minimum_le_dist_of_height_eq_zero (r : Orthant) {r₀ : Orthant}
    (hr₀ : height r₀ = 0) : minimum r ≤ Dist.dist r r₀ := by
  obtain ⟨i, hi⟩ := (height_eq_zero_iff r₀).mp hr₀
  calc
    minimum r ≤ r.1 i := minimum_le r i
    _ = ‖(r.1 - r₀.1) i‖ := by
      simp only [Pi.sub_apply, hi, sub_zero, Real.norm_eq_abs, abs_of_nonneg (r.2 i)]
    _ ≤ ‖r.1 - r₀.1‖ := (norm_le_pi_norm _ i)
    _ = Dist.dist r r₀ := (dist_eq_norm _ _).symm

theorem CuspPositiveRetraction.shrink_dist_le_twice_dist (s : unitInterval) (r : Orthant)
    {r₀ : Orthant} (hr₀ : height r₀ = 0) : Dist.dist (shrink s r) r₀ ≤ 2 * Dist.dist r r₀ := by
  calc
    Dist.dist (shrink s r) r₀ ≤ Dist.dist (shrink s r) r + Dist.dist r r₀ := dist_triangle _ _ _
    _ ≤ minimum r + Dist.dist r r₀ := (add_le_add (shrink_dist_le_minimum s r) le_rfl)
    _ ≤ Dist.dist r r₀ + Dist.dist r r₀ :=
      (add_le_add (minimum_le_dist_of_height_eq_zero r hr₀) le_rfl)
    _ = 2 * Dist.dist r r₀ := (two_mul _).symm

def CuspPositiveRetraction.cutoff (r₀ : Orthant) (R : ℝ) (r : Orthant) : ℝ :=
  Max.max 0 (Min.min 1 (4 - 12 * Dist.dist r r₀ / R))

theorem CuspPositiveRetraction.cutoff_nonneg (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    0 ≤ cutoff r₀ R r :=
  le_max_left _ _

theorem CuspPositiveRetraction.cutoff_le_one (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    cutoff r₀ R r ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem CuspPositiveRetraction.cutoff_continuous (r₀ : Orthant) (R : ℝ) :
    Continuous (cutoff r₀ R) :=
  continuous_const.max
    (continuous_const.min
      (continuous_const.sub
        ((continuous_const.mul (continuous_id.dist continuous_const)).div_const R)))

theorem CuspPositiveRetraction.cutoff_eq_one_of_dist_le (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : Dist.dist r r₀ ≤ R / 4) : cutoff r₀ R r = 1 := by
  have hdiv : 12 * Dist.dist r r₀ / R ≤ 3 := (div_le_iff₀ hR).mpr (by linarith)
  have h : 1 ≤ 4 - 12 * Dist.dist r r₀ / R := by linarith
  exact (congrArg (Max.max (0 : ℝ)) (min_eq_left h)).trans (max_eq_right zero_le_one)

theorem CuspPositiveRetraction.cutoff_eq_zero_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    {r : Orthant} (hr : R / 3 ≤ Dist.dist r r₀) : cutoff r₀ R r = 0 := by
  have hdiv : 4 ≤ 12 * Dist.dist r r₀ / R := (le_div_iff₀ hR).mpr (by linarith)
  have h : 4 - 12 * Dist.dist r r₀ / R ≤ 0 := by linarith
  exact (congrArg (Max.max (0 : ℝ)) (min_eq_right (h.trans zero_le_one))).trans (max_eq_left h)

def CuspPositiveRetraction.cutoffParameter (r₀ : Orthant) (R : ℝ) (r : Orthant) : unitInterval :=
  ⟨cutoff r₀ R r, cutoff_nonneg r₀ R r, cutoff_le_one r₀ R r⟩

theorem CuspPositiveRetraction.cutoffParameter_eq_one_of_dist_le (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : Dist.dist r r₀ ≤ R / 4) : cutoffParameter r₀ R r = 1 :=
  Subtype.ext (cutoff_eq_one_of_dist_le r₀ hR hr)

theorem CuspPositiveRetraction.cutoffParameter_eq_zero_of_le_dist (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : R / 3 ≤ Dist.dist r r₀) : cutoffParameter r₀ R r = 0 :=
  Subtype.ext (cutoff_eq_zero_of_le_dist r₀ hR hr)

def CuspPositiveRetraction.localShrink (r₀ : Orthant) (R : ℝ) (s : unitInterval) (r : Orthant) :
    Orthant :=
  shrink (s * cutoffParameter r₀ R r) r

theorem CuspPositiveRetraction.localShrink_continuous (r₀ : Orthant) (R : ℝ) :
    Continuous (fun p : unitInterval × Orthant => localShrink r₀ R p.1 p.2) := by
  have hp : Continuous (fun p : unitInterval × Orthant => p.1 * cutoffParameter r₀ R p.2) := by
    apply Continuous.subtype_mk
    exact
      (continuous_subtype_val.comp continuous_fst).mul
        ((cutoff_continuous r₀ R).comp continuous_snd)
  exact shrink_continuous.comp (hp.prodMk continuous_snd)

@[simp]
theorem CuspPositiveRetraction.localShrink_zero (r₀ : Orthant) (R : ℝ) (r : Orthant) :
    localShrink r₀ R 0 r = r := by simp only [localShrink, MulZeroClass.zero_mul, shrink_zero]

theorem CuspPositiveRetraction.localShrink_fixed (r₀ : Orthant) (R : ℝ) (s : unitInterval)
    {r : Orthant} (hr : height r = 0) : localShrink r₀ R s r = r :=
  shrink_fixed _ hr

theorem CuspPositiveRetraction.localShrink_height_le (r₀ : Orthant) (R : ℝ) (s : unitInterval)
    (r : Orthant) : height (localShrink r₀ R s r) ≤ height r :=
  shrink_height_le _ r

theorem CuspPositiveRetraction.localShrink_dist_le_twice_dist {r₀ : Orthant} (hr₀ : height r₀ = 0)
    (R : ℝ) (s : unitInterval) (r : Orthant) :
    Dist.dist (localShrink r₀ R s r) r₀ ≤ 2 * Dist.dist r r₀ :=
  shrink_dist_le_twice_dist _ r hr₀

theorem CuspPositiveRetraction.localShrink_eq_self_of_le_dist (r₀ : Orthant) {R : ℝ} (hR : 0 < R)
    (s : unitInterval) {r : Orthant} (hr : R / 3 ≤ Dist.dist r r₀) : localShrink r₀ R s r = r := by
  rw [localShrink, cutoffParameter_eq_zero_of_le_dist r₀ hR hr, MulZeroClass.mul_zero,
    shrink_zero]

theorem CuspPositiveRetraction.localShrink_eq_self_of_not_mem_closedBall (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) (s : unitInterval) {r : Orthant} (hr : r ∉ Metric.closedBall r₀ (R / 3)) :
    localShrink r₀ R s r = r :=
  localShrink_eq_self_of_le_dist r₀ hR s (not_le.mp hr).le

theorem CuspPositiveRetraction.localShrink_one_height_of_dist_le (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : Dist.dist r r₀ ≤ R / 4) :
    height (localShrink r₀ R 1 r) = 0 := by
  rw [localShrink, cutoffParameter_eq_one_of_dist_le r₀ hR hr, one_mul]
  exact shrink_one_height r

theorem CuspPositiveRetraction.localShrink_one_height_of_mem_ball (r₀ : Orthant) {R : ℝ}
    (hR : 0 < R) {r : Orthant} (hr : r ∈ Metric.ball r₀ (R / 4)) :
    height (localShrink r₀ R 1 r) = 0 :=
  localShrink_one_height_of_dist_le r₀ hR hr.le

theorem CuspPositiveRetraction.localShrink_mapsTo_ball {r₀ : Orthant} (hr₀ : height r₀ = 0)
    {R : ℝ} (hR : 0 < R) (s : unitInterval) :
    Set.MapsTo (localShrink r₀ R s) (Metric.ball r₀ R) (Metric.ball r₀ R) := by
  intro r hr
  by_cases hd : Dist.dist r r₀ < R / 3
  · have hb := localShrink_dist_le_twice_dist hr₀ R s r
    change Dist.dist (localShrink r₀ R s r) r₀ < R
    linarith
  · rw [localShrink_eq_self_of_le_dist r₀ hR s (le_of_not_gt hd)]
    exact hr

theorem CuspPositiveRetraction.localShrink_map_ball {r₀ : Orthant} (hr₀ : height r₀ = 0) {R : ℝ}
    (hR : 0 < R) (s : unitInterval) {r : Orthant} (hr : r ∈ Metric.ball r₀ R) :
    localShrink r₀ R s r ∈ Metric.ball r₀ R :=
  localShrink_mapsTo_ball hr₀ hR s hr

noncomputable def CuspPositiveRetraction.Supported.extend {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (p : S × Y) : Y := by
  classical exact if hy : p.2 ∈ e.target then e (H (p.1, ⟨e.symm p.2, e.map_target hy⟩)) else p.2

theorem CuspPositiveRetraction.Supported.extend_target {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (y : Y) (hy : y ∈ e.target) :
    CuspPositiveRetraction.Supported.extend e H (s, y) = e (H (s, ⟨e.symm y, e.map_target hy⟩)) :=
  by exact dif_pos hy

theorem CuspPositiveRetraction.Supported.extend_not_mem_target {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (y : Y) (hy : y ∉ e.target) :
    CuspPositiveRetraction.Supported.extend e H (s, y) = y := by exact dif_neg hy

theorem CuspPositiveRetraction.Supported.extend_chart {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (x : e.source) :
    CuspPositiveRetraction.Supported.extend e H (s, e x) = e (H (s, x)) := by
  rw [extend_target e H s (e x) (e.map_source x.2)]
  exact congrArg (fun z : e.source => e (H (s, z))) (Subtype.ext (e.left_inv x.2))

theorem CuspPositiveRetraction.Supported.extend_not_mem_image {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x) (s : S) (y : Y)
    (hyK : y ∉ e '' K) : CuspPositiveRetraction.Supported.extend e H (s, y) = y := by
  by_cases hy : y ∈ e.target
  · rw [extend_target e H s y hy]
    have hxK : e.symm y ∉ K := fun hx => hyK ⟨e.symm y, hx, e.right_inv hy⟩
    rw [hfix s ⟨e.symm y, e.map_target hy⟩ hxK]
    exact e.right_inv hy
  · exact extend_not_mem_target e H s y hy

theorem CuspPositiveRetraction.Supported.extend_continuousOn_target {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) :
    ContinuousOn (CuspPositiveRetraction.Supported.extend e H) (Prod.snd ⁻¹' e.target) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let g : (Prod.snd ⁻¹' e.target : Set (S × Y)) → S × e.source := fun p =>
    (p.1.1, e.toHomeomorphSourceTarget.symm ⟨p.1.2, p.2⟩)
  have hg : Continuous g :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (e.toHomeomorphSourceTarget.symm.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hc :=
    continuous_subtype_val.comp
      (e.toHomeomorphSourceTarget.continuous.comp (H.continuous.comp hg))
  apply hc.congr
  intro p
  exact (extend_target e H p.1.1 p.1.2 p.2).symm

theorem CuspPositiveRetraction.Supported.extend_continuous {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x) :
    Continuous (CuspPositiveRetraction.Supported.extend e H) := by
  have hclosed : IsClosed (e '' K) :=
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed
  have hout :
    ContinuousOn (CuspPositiveRetraction.Supported.extend e H) (Prod.snd ⁻¹' (e '' K)ᶜ) :=
    continuous_snd.continuousOn.congr fun p hp => extend_not_mem_image e H K hfix p.1 p.2 hp
  have hcover : (Prod.snd ⁻¹' e.target : Set (S × Y)) ∪ (Prod.snd ⁻¹' (e '' K)ᶜ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : p.2 ∈ e.target
    · exact Or.inl hp
    · right
      rintro ⟨x, hx, hxy⟩
      exact hp (hxy ▸ e.map_source (hKs hx))
  rw [← continuousOn_univ, ← hcover]
  exact
    (extend_continuousOn_target e H).union_of_isOpen hout (e.open_target.preimage continuous_snd)
      (hclosed.isOpen_compl.preimage continuous_snd)

private noncomputable def CuspPositiveRetraction.Supported.embeddingLocalMap_mo1973_10473
    {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (e : X → Y) (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) :
    C(S × (he.toOpenPartialHomeomorph e).source, (he.toOpenPartialHomeomorph e).source)
    where
  toFun p := ⟨H (p.1, p.2.1), Set.mem_univ _⟩
  continuous_toFun :=
    (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

noncomputable def CuspPositiveRetraction.Supported.embeddingExtend {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) : S × Y → Y :=
  CuspPositiveRetraction.Supported.extend (he.toOpenPartialHomeomorph e)
    (embeddingLocalMap_mo1973_10473 e he H)

theorem CuspPositiveRetraction.Supported.embeddingExtend_chart {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (s : S) (x : X) :
    embeddingExtend e he H (s, e x) = e (H (s, x)) := by
  let x' : (he.toOpenPartialHomeomorph e).source := ⟨x, Set.mem_univ _⟩
  simpa only [embeddingExtend, embeddingLocalMap_mo1973_10473, ContinuousMap.coe_mk,
    he.toOpenPartialHomeomorph_apply e] using
    extend_chart (he.toOpenPartialHomeomorph e) (embeddingLocalMap_mo1973_10473 e he H) s x'

theorem CuspPositiveRetraction.Supported.embeddingExtend_not_mem_range {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (s : S) (y : Y) (hy : y ∉ Set.range e) :
    embeddingExtend e he H (s, y) = y := by
  exact
    extend_not_mem_target (he.toOpenPartialHomeomorph e) (embeddingLocalMap_mo1973_10473 e he H) s
      y (by simpa only [he.toOpenPartialHomeomorph_target e] using hy)

theorem CuspPositiveRetraction.Supported.embeddingExtend_continuous {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [T2Space Y]
    (e : X → Y) (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x) : Continuous (embeddingExtend e he H) := by
  apply
    extend_continuous (he.toOpenPartialHomeomorph e) (embeddingLocalMap_mo1973_10473 e he H) K hK
  · rw [he.toOpenPartialHomeomorph_source e]
    exact Set.subset_univ K
  · intro s x hx
    exact Subtype.ext (hfix s x hx)

noncomputable def CuspPositiveRetraction.Supported.embeddingMap {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [T2Space Y]
    (e : X → Y) (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x) : C(S × Y, Y) :=
  ⟨embeddingExtend e he H, embeddingExtend_continuous e he H K hK hfix⟩

theorem CuspPositiveRetraction.Supported.embeddingExtend_id {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (s : S) (hs : ∀ x : X, H (s, x) = x)
    (y : Y) : embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H, hs]
  · exact embeddingExtend_not_mem_range e he H s y hy

theorem CuspPositiveRetraction.Supported.embeddingExtend_fixed {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (A : Set Y)
    (hfix : ∀ (s : S) (x : X), e x ∈ A → H (s, x) = x) (s : S) (y : Y) (hyA : y ∈ A) :
    embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H, hfix s x hyA]
  · exact embeddingExtend_not_mem_range e he H s y hy

theorem CuspPositiveRetraction.Supported.embeddingExtend_rel {S X Y : Type*} [TopologicalSpace S]
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (R : Y → Y → Prop) (hrefl : ∀ y, R y y)
    (hlocal : ∀ (s : S) (x : X), R (e x) (e (H (s, x)))) (s : S) (y : Y) :
    R y (embeddingExtend e he H (s, y)) := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H]
    exact hlocal s x
  · rw [embeddingExtend_not_mem_range e he H s y hy]
    exact hrefl y

theorem CuspPositiveRetraction.Supported.embeddingExtend_height_nonincrease {S X Y : Type*}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] (e : X → Y)
    (he : Topology.IsOpenEmbedding e) (H : C(S × X, X)) (f : Y → ℝ)
    (hlocal : ∀ (s : S) (x : X), f (e (H (s, x))) ≤ f (e x)) (s : S) (y : Y) :
    f (embeddingExtend e he H (s, y)) ≤ f y :=
  embeddingExtend_rel e he H (fun y z => f z ≤ f y) (fun _ => le_rfl) hlocal s y

theorem CuspPositiveRetraction.exists_localCollapse_of_orthant_chart {X : Type*}
    [TopologicalSpace X] [T2Space X] (f : C(X, ℝ)) (e : OpenPartialHomeomorph Orthant X)
    {r₀ : Orthant} (hr₀ : r₀ ∈ e.source) (hzero : height r₀ = 0)
    (hheight : ∀ r ∈ e.source, f (e r) = height r) :
    ∃ A : CuspRetraction.Patching.LocalCollapse f, e r₀ ∈ A.collapseSet := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp e.open_source r₀ hr₀
  let U := Metric.ball r₀ R
  let : Nonempty U := ⟨⟨r₀, Metric.mem_ball_self hR⟩⟩
  let ep : U → X := fun r => e r.1
  have hep : Topology.IsOpenEmbedding ep := by
    exact
      e.isOpenEmbedding_restrict.comp
        (Topology.IsOpenEmbedding.inclusion hball
          (Metric.isOpen_ball.preimage continuous_subtype_val))
  let H : C(unitInterval × U, U) :=
    ⟨fun p => ⟨localShrink r₀ R p.1 p.2.1, localShrink_map_ball hzero hR p.1 p.2.2⟩,
      ((localShrink_continuous r₀ R).comp
            (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
        _⟩
  let K : Set U := Subtype.val ⁻¹' Metric.closedBall r₀ (R / 3)
  have hK : IsCompact K := by
    apply
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
        (ProperSpace.isCompact_closedBall r₀ (R / 3))
    intro r hr
    have hrU : r ∈ U := by
      change Dist.dist r r₀ < R
      have hd : Dist.dist r r₀ ≤ R / 3 := hr
      linarith
    exact ⟨⟨r, hrU⟩, rfl⟩
  have hfix : ∀ (s : unitInterval) (r : U), r ∉ K → H (s, r) = r := by
    intro s r hr
    exact Subtype.ext (localShrink_eq_self_of_not_mem_closedBall r₀ hR s hr)
  have hH0 : ∀ r : U, H (0, r) = r := by
    intro r
    exact Subtype.ext (localShrink_zero r₀ R r.1)
  have hHfix : ∀ (s : unitInterval) (r : U), f (ep r) = 0 → H (s, r) = r := by
    intro s r hr
    have hz : height r.1 = 0 := (hheight r.1 (hball r.2)).symm.trans hr
    exact Subtype.ext (localShrink_fixed r₀ R s hz)
  have hHle : ∀ (s : unitInterval) (r : U), f (ep (H (s, r))) ≤ f (ep r) := by
    intro s r
    change f (e (H (s, r)).1) ≤ f (e r.1)
    rw [hheight (H (s, r)).1 (hball (H (s, r)).2), hheight r.1 (hball r.2)]
    exact localShrink_height_le r₀ R s r.1
  let L : Set U := Subtype.val ⁻¹' Metric.ball r₀ (R / 4)
  have hL : IsOpen L := Metric.isOpen_ball.preimage continuous_subtype_val
  let A : CuspRetraction.Patching.LocalCollapse f :=
    { homotopy := Supported.embeddingMap ep hep H K hK hfix
      map_zero := Supported.embeddingExtend_id ep hep H 0 hH0
      fixes_zero := fun s x hx =>
        Supported.embeddingExtend_fixed ep hep H {y | f y = 0} hHfix s x hx
      nonincreasing := Supported.embeddingExtend_height_nonincrease ep hep H f hHle
      collapseSet := ep '' L
      isOpen_collapseSet := hep.isOpenMap L hL
      map_one_zero := by
        rintro x ⟨r, hr, rfl⟩
        change f (Supported.embeddingExtend ep hep H (1, ep r)) = 0
        rw [Supported.embeddingExtend_chart]
        change f (e (H (1, r)).1) = 0
        rw [hheight (H (1, r)).1 (hball (H (1, r)).2)]
        exact localShrink_one_height_of_mem_ball r₀ hR hr }
  refine ⟨A, ⟨⟨r₀, Metric.mem_ball_self hR⟩, ?_, rfl⟩⟩
  exact Metric.mem_ball_self (by linarith)

theorem CuspPositiveRetraction.exists_small_sublevel_collapse_of_orthant_charts {X : Type*}
    [TopologicalSpace X] [T2Space X] (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact {x : X | f x ≤ r})
    (hcharts :
      ∀ x : X,
        f x = 0 →
          ∃ (e : OpenPartialHomeomorph Orthant X) (r₀ : Orthant),
            r₀ ∈ e.source ∧ e r₀ = x ∧ ∀ r ∈ e.source, f (e r) = height r) :
    ∃ η : ℝ,
      0 < η ∧
        η ≤ r ∧
          ∃ A : CuspRetraction.Patching.LocalCollapse f, {x : X | f x ≤ η} ⊆ A.collapseSet := by
  apply CuspRetraction.Patching.exists_small_sublevel_localCollapse f hf hr hcompact
  intro x hx
  obtain ⟨e, r₀, hr₀, he, hh⟩ := hcharts x hx
  have hzero : height r₀ = 0 := (hh r₀ hr₀).symm.trans (he ▸ hx)
  obtain ⟨A, hA⟩ := exists_localCollapse_of_orthant_chart f e hr₀ hzero hh
  exact ⟨A, he ▸ hA⟩

def CuspPositiveRetraction.Covering.pullback {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B)) :
    C(unitInterval × E, B) where
  toFun p := H (p.1, q p.2)
  continuous_toFun :=
    H.continuous.comp
      (continuous_fst.prodMk (hq.isLocalHomeomorph.continuous.comp continuous_snd))

def CuspPositiveRetraction.Covering.lift {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B)) (hzero : ∀ b, H (0, b) = b) :
    C(unitInterval × E, E) :=
  hq.liftHomotopy (pullback hq H) (ContinuousMap.id E) (fun x => hzero (q x))

@[simp]
theorem CuspPositiveRetraction.Covering.lift_zero {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (x : E) :
    CuspPositiveRetraction.Covering.lift hq H hzero (0, x) = x :=
  hq.liftHomotopy_zero _ _ _ x

theorem CuspPositiveRetraction.Covering.lift_projection {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (s : unitInterval) (x : E) :
    q (CuspPositiveRetraction.Covering.lift hq H hzero (s, x)) = H (s, q x) :=
  congr_fun (hq.liftHomotopy_lifts (pullback hq H) (ContinuousMap.id E) (fun y => hzero (q y)))
    (s, x)

theorem CuspPositiveRetraction.Covering.lift_fixed {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (x : E) (hx : ∀ s : unitInterval, H (s, q x) = q x)
    (s : unitInterval) : CuspPositiveRetraction.Covering.lift hq H hzero (s, x) = x := by
  have hc :
    Continuous (fun t : unitInterval => CuspPositiveRetraction.Covering.lift hq H hzero (t, x)) :=
    (CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
      (continuous_id.prodMk continuous_const)
  have h := hq.const_of_comp hc (fun t t' => by simp only [lift_projection hq H hzero, hx]) s 0
  exact h.trans (lift_zero hq H hzero x)

theorem CuspPositiveRetraction.Covering.lift_equivariant {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    (hdeck : ∀ (g : G) (x : E), q (g • x) = q x) (g : G) (s : unitInterval) (x : E) :
    CuspPositiveRetraction.Covering.lift hq H hzero (s, g • x) =
      g • CuspPositiveRetraction.Covering.lift hq H hzero (s, x) := by
  have hleft :
    Continuous
      (fun t : unitInterval => CuspPositiveRetraction.Covering.lift hq H hzero (t, g • x)) :=
    (CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hright :
    Continuous
      (fun t : unitInterval => g • CuspPositiveRetraction.Covering.lift hq H hzero (t, x)) :=
    (ContinuousConstSMul.continuous_const_smul g).comp
      ((CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
        (continuous_id.prodMk continuous_const))
  have he :
    q ∘ (fun t : unitInterval => CuspPositiveRetraction.Covering.lift hq H hzero (t, g • x)) =
      q ∘ (fun t : unitInterval => g • CuspPositiveRetraction.Covering.lift hq H hzero (t, x)) := by
    funext t
    simp only [Function.comp_apply, lift_projection hq H hzero, hdeck]
  exact congr_fun (hq.eq_of_comp_eq hleft hright he 0 (by simp only [lift_zero])) s

theorem CuspPositiveRetraction.Covering.lift_height_le {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (f : B → ℝ) (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b)
    (s : unitInterval) (x : E) :
    f (q (CuspPositiveRetraction.Covering.lift hq H hzero (s, x))) ≤ f (q x) := by
  rw [lift_projection hq H hzero]
  exact hsize s (q x)

def CuspPositiveRetraction.Covering.liftSublevel {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {q : E → B} (hq : IsCoveringMap q) (H : C(unitInterval × B, B))
    (hzero : ∀ b, H (0, b) = b) (f : B → ℝ) (η : ℝ)
    (hsize : ∀ (s : unitInterval) b, f (H (s, b)) ≤ f b) :
    C(unitInterval × { x : E // f (q x) ≤ η }, { x : E // f (q x) ≤ η })
    where
  toFun
    p :=
    ⟨CuspPositiveRetraction.Covering.lift hq H hzero (p.1, p.2.1),
      (lift_height_le hq H hzero f hsize p.1 p.2.1).trans p.2.2⟩
  continuous_toFun :=
    ((CuspPositiveRetraction.Covering.lift hq H hzero).continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

def ToricCharts.coordinateModulus {d : ℕ} (z : CoordinateSpace d) : CoordinateSpace d := fun i =>
  (‖z i‖ : ℂ)

@[simp]
theorem ToricCharts.coordinateModulus_apply {d : ℕ} (z : CoordinateSpace d) (i : Fin d) :
    coordinateModulus z i = (‖z i‖ : ℂ) :=
  rfl

theorem ToricCharts.coordinateModulus_continuous {d : ℕ} :
    Continuous (coordinateModulus : CoordinateSpace d → CoordinateSpace d) := by
  exact continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i).norm

@[simp]
theorem ToricCharts.coordinateModulus_idempotent {d : ℕ} (z : CoordinateSpace d) :
    coordinateModulus (coordinateModulus z) = coordinateModulus z := by
  funext i
  simp [coordinateModulus]

@[simp]
theorem ToricCharts.coordinateModulus_mem_domain_iff {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (z : CoordinateSpace d) : coordinateModulus z ∈ domain A ↔ z ∈ domain A := by simp [domain]

@[simp]
theorem ToricCharts.coordinateModulus_mem_torus_iff {d : ℕ} (z : CoordinateSpace d) :
    coordinateModulus z ∈ torus ↔ z ∈ torus := by simp [torus]

theorem ToricCharts.monomial_coordinateModulus {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (z : CoordinateSpace d) :
    monomial A (coordinateModulus z) = coordinateModulus (monomial A z) := by
  funext i
  simp [monomial, coordinateModulus, norm_prod, norm_zpow]

def ToricCharts.nonnegativeCoordinates {d : ℕ} : Set (CoordinateSpace d) :=
  {z | ∃ r : Fin d → ℝ, (∀ i, 0 ≤ r i) ∧ z = fun i => (r i : ℂ)}

theorem ToricCharts.coordinateModulus_eq_self_iff {d : ℕ} (z : CoordinateSpace d) :
    coordinateModulus z = z ↔ z ∈ nonnegativeCoordinates := by
  constructor
  · intro hz
    exact ⟨fun i => ‖z i‖, fun i => norm_nonneg _, hz.symm⟩
  · rintro ⟨r, hr, rfl⟩
    funext i
    exact congrArg Complex.ofReal (Complex.norm_of_nonneg (hr i))

theorem ToricSpace.chartChange_coordinateModulus (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.chartChange s t (ToricCharts.coordinateModulus z) =
      ToricCharts.coordinateModulus (ToricFan.Triangle.chartChange s t z) :=
  ToricCharts.monomial_coordinateModulus (ToricFan.Triangle.transition s t) z

theorem ToricSpace.coordinateModulus_overlap (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion t (ToricCharts.coordinateModulus (ToricFan.Triangle.chartChange s t z)) =
      ToricSpace.inclusion s (ToricCharts.coordinateModulus z) := by
  symm
  apply (inclusion_eq_iff s t _ _).mpr
  refine ⟨?_, chartChange_coordinateModulus s t z⟩
  simpa only [ToricFan.Triangle.chartChange_source,
    ToricCharts.coordinateModulus_mem_domain_iff] using hz

def ToricSpace.modulus : Space → Space :=
  descend fun s z => ToricSpace.inclusion s (ToricCharts.coordinateModulus z)

@[simp]
theorem ToricSpace.modulus_inclusion (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    modulus (ToricSpace.inclusion s z) =
      ToricSpace.inclusion s (ToricCharts.coordinateModulus z) :=
  descend_inclusion _ (fun s t _z hz => coordinateModulus_overlap s t hz) s z

theorem ToricSpace.modulus_continuous : Continuous modulus := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  apply
    ((parametrization s).continuousAt_iff_continuousAt_comp_right
        (show ToricSpace.inclusion s z ∈ (parametrization s).target by simp)).mpr
  have h : modulus ∘ parametrization s = ToricSpace.inclusion s ∘ ToricCharts.coordinateModulus :=
    by
    funext w
    exact modulus_inclusion s w
  rw [h]
  exact
    ((inclusion_openEmbedding s).continuous.comp
        ToricCharts.coordinateModulus_continuous).continuousAt

@[simp]
theorem ToricSpace.modulus_idempotent (x : Space) : modulus (modulus x) = modulus x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp only [modulus_inclusion, ToricCharts.coordinateModulus_idempotent]

@[simp]
theorem ToricSpace.time_modulus (x : Space) : time (modulus x) = (‖time x‖ : ℂ) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [ToricFan.Triangle.time]

def ToricSpace.positivePart : Set Space :=
  {x | modulus x = x}

abbrev ToricSpace.PositivePart :=
  positivePart

theorem ToricSpace.positivePart_isClosed : IsClosed positivePart :=
  isClosed_eq modulus_continuous continuous_id

@[simp]
theorem ToricSpace.inclusion_mem_positivePart_iff (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z ∈ positivePart ↔ z ∈ ToricCharts.nonnegativeCoordinates := by
  change modulus (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔ _
  rw [modulus_inclusion, (inclusion_openEmbedding s).injective.eq_iff,
    ToricCharts.coordinateModulus_eq_self_iff]

@[simp]
theorem ToricSpace.modulus_mem_positivePart (x : Space) : modulus x ∈ positivePart :=
  modulus_idempotent x

def ToricSpace.modulusRetraction (x : Space) : PositivePart :=
  ⟨modulus x, modulus_mem_positivePart x⟩

@[simp]
theorem ToricSpace.modulusRetraction_coe (x : Space) :
    (modulusRetraction x : Space) = modulus x :=
  rfl

abbrev ToricSpace.CompactTorus :=
  Fin 3 → Circle

def ToricSpace.compactTorusUnits : CompactTorus →* ActingTorus
    where
  toFun u i := Circle.toUnits (u i)
  map_one' := by
    funext i
    exact Circle.toUnits.map_one
  map_mul' u
    v := by
    funext i
    exact Circle.toUnits.map_mul (u i) (v i)

@[simp]
theorem ToricSpace.compactTorusUnits_apply (u : CompactTorus) (i : Fin 3) :
    (compactTorusUnits u i : ℂ) = (u i : ℂ) :=
  rfl

theorem ToricSpace.compactTorusUnits_continuous : Continuous compactTorusUnits := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  have h : Continuous (fun u : CompactTorus => (u i : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact ⟨h, h.inv₀ (fun u => (u i).coe_ne_zero)⟩

def ToricSpace.compactTorusAction (u : CompactTorus) (x : Space) : Space :=
  torusAction (compactTorusUnits u) x

@[simp]
theorem ToricSpace.compactTorusAction_one (x : Space) : compactTorusAction 1 x = x := by
  simp [compactTorusAction]

theorem ToricSpace.compactTorusAction_mul (u v : CompactTorus) (x : Space) :
    compactTorusAction u (compactTorusAction v x) = compactTorusAction (u * v) x := by
  simp [compactTorusAction, torusAction_mul]

instance ToricSpace.compactTorusMulAction : MulAction CompactTorus Space
    where
  smul := compactTorusAction
  one_smul := compactTorusAction_one
  mul_smul u v x := (compactTorusAction_mul u v x).symm

theorem ToricSpace.compactTorusAction_continuous :
    Continuous (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) := by
  have h : Continuous (fun p : CompactTorus × Space => (compactTorusUnits p.1, p.2)) :=
    (compactTorusUnits_continuous.comp continuous_fst).prodMk continuous_snd
  change
    Continuous
      ((fun p : ActingTorus × Space => torusAction p.1 p.2) ∘
        (fun p : CompactTorus × Space => (compactTorusUnits p.1, p.2)))
  exact torusAction_joint_continuous.comp h

instance ToricSpace.compactTorusContinuousSMul : ContinuousSMul CompactTorus Space :=
  ⟨compactTorusAction_continuous⟩

@[simp]
theorem ToricSpace.norm_factors_compactTorusUnits (s : ToricFan.Triangle) (u : CompactTorus)
    (i : Fin 3) : ‖factors s (compactTorusUnits u) i‖ = 1 := by
  simp [factors, ToricCharts.monomial, norm_prod, norm_zpow, Circle.norm_coe]

theorem ToricSpace.coordinateModulus_scale_compactTorusUnits (s : ToricFan.Triangle)
    (u : CompactTorus) (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.coordinateModulus (scale s (compactTorusUnits u) z) =
      ToricCharts.coordinateModulus z := by
  funext i
  change (‖factors s (compactTorusUnits u) i * z i‖ : ℂ) = (‖z i‖ : ℂ)
  rw [norm_mul, norm_factors_compactTorusUnits, one_mul]

@[simp]
theorem ToricSpace.modulus_compactTorusAction (u : CompactTorus) (x : Space) :
    modulus (compactTorusAction u x) = modulus x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [compactTorusAction, coordinateModulus_scale_compactTorusUnits]

@[simp]
theorem ToricSpace.norm_time_compactTorusAction (u : CompactTorus) (x : Space) :
    ‖time (compactTorusAction u x)‖ = ‖time x‖ := by
  simp [compactTorusAction, time_torusAction, Circle.norm_coe]

theorem ToricSpace.exists_unitNorm_scale_modulus (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ∃ u : ActingTorus, (∀ i, ‖(u i : ℂ)‖ = 1) ∧ scale s u (ToricCharts.coordinateModulus z) = z :=
  by
  classical
  have hphase (c : ℂ) : ∃ w : ℂ, ‖w‖ = 1 ∧ w * (‖c‖ : ℂ) = c := by
    by_cases hc : c = 0
    · exact ⟨1, NormOneClass.norm_one, by simp [hc]⟩
    · refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hc)]
      · exact
          div_mul_cancel₀ _ (by simpa only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero] using hc)
  choose w hw hmul using fun i => hphase (z i)
  have hw0 : w ∈ ToricCharts.torus := by
    intro i hi
    have h := hw i
    rw [hi, norm_zero] at h
    exact zero_ne_one h
  let u : ActingTorus := fun i =>
    Units.mk0 (ToricCharts.monomial s.rays w i) (ToricCharts.monomial_mapsTo_torus s.rays hw0 i)
  have hu : ∀ i, ‖(u i : ℂ)‖ = 1 := by
    intro i
    change ‖ToricCharts.monomial s.rays w i‖ = 1
    simp only [ToricCharts.monomial, norm_prod, norm_zpow, hw, one_zpow, Finset.prod_const_one]
  refine ⟨u, hu, ?_⟩
  have hf : factors s u = w := by
    change ToricCharts.monomial s.dual (ToricCharts.monomial s.rays w) = w
    rw [ToricCharts.monomial_mul_on_torus _ _ hw0, ToricFan.Triangle.dual_rays,
      ToricCharts.monomial_one]
  ext i
  change factors s u i * (‖z i‖ : ℂ) = z i
  rw [hf]
  exact hmul i

theorem ToricSpace.exists_compactTorus_scale_modulus (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ∃ u : CompactTorus, scale s (compactTorusUnits u) (ToricCharts.coordinateModulus z) = z := by
  obtain ⟨u, hu, hz⟩ := exists_unitNorm_scale_modulus s z
  let v : CompactTorus := fun i => ⟨(u i : ℂ), mem_sphere_zero_iff_norm.mpr (hu i)⟩
  refine ⟨v, ?_⟩
  have hv : compactTorusUnits v = u := by
    funext i
    apply Units.ext
    rfl
  rw [hv]
  exact hz

theorem ToricSpace.exists_compactTorusAction_modulus (x : Space) :
    ∃ u : CompactTorus, compactTorusAction u (modulus x) = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨u, hu⟩ := exists_compactTorus_scale_modulus s z
  refine ⟨u, ?_⟩
  change
    torusAction (compactTorusUnits u) (modulus (ToricSpace.inclusion s z)) =
      ToricSpace.inclusion s z
  rw [modulus_inclusion, torusAction_inclusion, hu]

def ToricSpace.polarMultiplication (p : CompactTorus × PositivePart) : Space :=
  compactTorusAction p.1 p.2

theorem ToricSpace.polarMultiplication_continuous : Continuous polarMultiplication := by
  have h : Continuous (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  change
    Continuous
      ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
        (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_continuous.comp h

theorem ToricSpace.polarMultiplication_surjective : Function.Surjective polarMultiplication := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactTorusAction_modulus x
  exact ⟨(u, modulusRetraction x), hu⟩

theorem ToricSpace.compactTorusAction_injective_of_time_ne_zero {x : Space} (hx : time x ≠ 0) :
    Function.Injective (fun u : CompactTorus => compactTorusAction u x) := by
  intro u v huv
  have hxt : x ∈ openTorus := (mem_openTorus_iff x).mpr hx
  have he := congrArg torusCoordinates huv
  change
    torusCoordinates (torusAction (compactTorusUnits u) x) =
      torusCoordinates (torusAction (compactTorusUnits v) x) at he
  rw [torusCoordinates_action _ hxt, torusCoordinates_action _ hxt] at he
  funext i
  apply Circle.ext
  exact mul_right_cancel₀ (torusCoordinates_nonzero hxt i) (congrFun he i)

def ToricSpace.compactTorusActionShear : CompactTorus × Space ≃ₜ CompactTorus × Space
    where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk ContinuousSMul.continuous_smul
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.smul continuous_snd)

theorem ToricSpace.compactTorusAction_isClosedMap :
    IsClosedMap (fun p : CompactTorus × Space => compactTorusAction p.1 p.2) :=
  isClosedMap_snd_of_compactSpace.comp compactTorusActionShear.isClosedMap

theorem ToricSpace.polarMultiplication_isClosedMap : IsClosedMap polarMultiplication := by
  have h : IsClosedMap (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))) :=
    ((Homeomorph.refl CompactTorus).isClosedEmbedding.prodMap
        positivePart_isClosed.isClosedEmbedding_subtypeVal).isClosedMap
  change
    IsClosedMap
      ((fun p : CompactTorus × Space => compactTorusAction p.1 p.2) ∘
        (fun p : CompactTorus × PositivePart => (p.1, (p.2 : Space))))
  exact compactTorusAction_isClosedMap.comp h

abbrev ToricSpace.ClosedPositiveTube (η : ℝ) :=
  { x : PositivePart // ‖time (x : Space)‖ ≤ η }

theorem ToricSpace.closedPolarMap_mem_iff (η : ℝ) (p : CompactTorus × PositivePart) :
    polarMultiplication p ∈ {x : Space | ‖time x‖ ≤ η} ↔
      p.2 ∈ {x : PositivePart | ‖time (x : Space)‖ ≤ η} := by
  change ‖time (compactTorusAction p.1 p.2)‖ ≤ η ↔ ‖time (p.2 : Space)‖ ≤ η
  rw [norm_time_compactTorusAction]

def ToricSpace.closedPolarMap (η : ℝ) :
    CompactTorus × ClosedPositiveTube η → { x : Space // ‖time x‖ ≤ η } :=
  ProductRestriction.productRestriction polarMultiplication
    {x : PositivePart | ‖time (x : Space)‖ ≤ η} {x : Space | ‖time x‖ ≤ η}
    (closedPolarMap_mem_iff η)

@[simp]
theorem ToricSpace.closedPolarMap_coe (η : ℝ) (p : CompactTorus × ClosedPositiveTube η) :
    (closedPolarMap η p : Space) = compactTorusAction p.1 (p.2.1 : Space) :=
  rfl

theorem ToricSpace.closedPolarMap_continuous (η : ℝ) : Continuous (closedPolarMap η) :=
  ProductRestriction.productRestriction_continuous _ _ _ _ polarMultiplication_continuous

theorem ToricSpace.closedPolarMap_isClosedMap (η : ℝ) : IsClosedMap (closedPolarMap η) :=
  ProductRestriction.productRestriction_isClosedMap _ _ _ _ polarMultiplication_isClosedMap

theorem ToricSpace.closedPolarMap_surjective (η : ℝ) : Function.Surjective (closedPolarMap η) :=
  ProductRestriction.productRestriction_surjective _ _ _ _ polarMultiplication_surjective

theorem ToricSpace.closedPolarMap_isQuotientMap (η : ℝ) :
    Topology.IsQuotientMap (closedPolarMap η) :=
  (closedPolarMap_isClosedMap η).isQuotientMap (closedPolarMap_continuous η)
    (closedPolarMap_surjective η)

def ToricSpace.closedModulusRetraction (η : ℝ) (x : { x : Space // ‖time x‖ ≤ η }) :
    ClosedPositiveTube η :=
  ⟨modulusRetraction x, by
    change ‖time (modulus (x : Space))‖ ≤ η
    simpa only [time_modulus, Complex.norm_real, norm_norm] using x.property⟩

@[simp]
theorem ToricSpace.closedModulusRetraction_closedPolarMap (η : ℝ)
    (p : CompactTorus × ClosedPositiveTube η) :
    closedModulusRetraction η (closedPolarMap η p) = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change modulus (compactTorusAction p.1 (p.2.1 : Space)) = (p.2.1 : Space)
  rw [modulus_compactTorusAction]
  exact p.2.1.property

def CuspPositive.positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (_t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => Complex.I * ((C₀ i j).im : ℂ)

theorem CuspPositive.positiveTwist_holomorphic (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ContDiff ℂ ω (fun t => positiveTwist C₀ t i j) :=
  contDiff_const

@[simp]
theorem CuspPositive.driftMatrix_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ToricSpace.driftMatrix (positiveTwist C₀) t = ToricSpace.driftMatrix (fun _ => C₀) 0 := by
  ext i j
  simp [ToricSpace.driftMatrix, positiveTwist, Complex.mul_im]

theorem CuspPositive.smallDrift_positiveTwist_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    ToricSpace.SmallDrift (positiveTwist C₀) ε ↔ ToricSpace.SmallDrift (fun _ => C₀) ε := by
  simp only [ToricSpace.SmallDrift, driftMatrix_positiveTwist]
  rfl

theorem CuspPositive.smallDrift_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hR : ToricSpace.SmallDrift (fun _ => C₀) ε) : ToricSpace.SmallDrift (positiveTwist C₀) ε :=
  (smallDrift_positiveTwist_iff C₀ ε).mpr hR

theorem CuspPositive.exponentialMultiplier_positiveTwist_eq_norm (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ) =
      (‖(ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ)‖ : ℂ) := by
  simp only [ToricSpace.exponentialMultiplier, Units.val_mk0, Complex.norm_exp,
    Complex.ofReal_exp]
  congr 1
  apply Complex.ext <;>
    simp [positiveTwist, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]

theorem CuspPositive.exponentialMultiplier_positiveTwist_norm (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    ‖(ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ)‖ =
      ‖(ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ)‖ := by
  rw [exponentialMultiplier_positiveTwist_eq_norm]
  simp

theorem CuspPositive.exponentialMultiplier_positiveTwist_ofReal_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    (‖(ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ)‖ : ℂ) =
      (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t i : ℂ) := by
  rw [exponentialMultiplier_positiveTwist_norm, exponentialMultiplier_positiveTwist_eq_norm]

theorem CuspPositive.fibreMultiplier_positiveTwist_ofReal_norm (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 3) :
    (‖(ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t) i :
            ℂ)‖ :
        ℂ) =
      (ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v t) i :
        ℂ) := by
  fin_cases i
  · exact exponentialMultiplier_positiveTwist_ofReal_norm C₀ v t 0
  · exact exponentialMultiplier_positiveTwist_ofReal_norm C₀ v t 1
  · simp [ToricSpace.fibreMultiplier]

@[simp]
theorem CuspPositive.modulus_translate (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.modulus (ToricSpace.translate v x) =
      ToricSpace.translate v (ToricSpace.modulus x) := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  simp only [ToricSpace.translate_inclusion, ToricSpace.modulus_inclusion]

theorem CuspPositive.coordinateModulus_mul {d : ℕ} (z w : ToricCharts.CoordinateSpace d) :
    ToricCharts.coordinateModulus (z * w) =
      ToricCharts.coordinateModulus z * ToricCharts.coordinateModulus w := by
  funext i
  simp [ToricCharts.coordinateModulus]

theorem CuspPositive.coordinateModulus_factors_of_nonnegative (s : ToricFan.Triangle)
    (u : ToricSpace.ActingTorus) (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) :
    ToricCharts.coordinateModulus (ToricSpace.factors s u) = ToricSpace.factors s u := by
  change ToricCharts.coordinateModulus (ToricCharts.monomial s.dual (fun i => (u i : ℂ))) = _
  rw [← ToricCharts.monomial_coordinateModulus]
  have he : ToricCharts.coordinateModulus (fun i => (u i : ℂ)) = fun i => (u i : ℂ) := by
    funext i
    exact hu i
  rw [he]
  rfl

theorem CuspPositive.coordinateModulus_scale_of_nonnegative (s : ToricFan.Triangle)
    (u : ToricSpace.ActingTorus) (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ))
    (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.coordinateModulus (ToricSpace.scale s u z) =
      ToricSpace.scale s u (ToricCharts.coordinateModulus z) := by
  rw [ToricSpace.scale, coordinateModulus_mul, coordinateModulus_factors_of_nonnegative s u hu]
  rfl

theorem CuspPositive.modulus_torusAction_of_nonnegative (u : ToricSpace.ActingTorus)
    (hu : ∀ i, (‖(u i : ℂ)‖ : ℂ) = (u i : ℂ)) (x : ToricSpace.Space) :
    ToricSpace.modulus (ToricSpace.torusAction u x) =
      ToricSpace.torusAction u (ToricSpace.modulus x) := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  simp only [ToricSpace.torusAction_inclusion, ToricSpace.modulus_inclusion,
    coordinateModulus_scale_of_nonnegative s u hu]

theorem CuspPositive.twistedTranslate_positiveTwist_eq (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (positiveTwist C₀) v x =
      ToricSpace.torusAction
        (ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0))
        (ToricSpace.translate (ToricSpace.cuspVector v) x) :=
  rfl

theorem CuspPositive.modulus_twistedTranslate_positiveTwist (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.modulus (ToricSpace.twistedTranslate (positiveTwist C₀) v x) =
      ToricSpace.twistedTranslate (positiveTwist C₀) v (ToricSpace.modulus x) := by
  rw [twistedTranslate_positiveTwist_eq,
    modulus_torusAction_of_nonnegative _ (fibreMultiplier_positiveTwist_ofReal_norm C₀ v 0),
    modulus_translate, twistedTranslate_positiveTwist_eq]

theorem CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    Set.MapsTo (ToricSpace.twistedTranslate (positiveTwist C₀) v) ToricSpace.positivePart
      ToricSpace.positivePart := by
  intro x hx
  change ToricSpace.modulus (ToricSpace.twistedTranslate (positiveTwist C₀) v x) = _
  rw [modulus_twistedTranslate_positiveTwist]
  exact congrArg (ToricSpace.twistedTranslate (positiveTwist C₀) v) hx

@[simp]
theorem CuspPositive.twistedTranslate_positiveTwist_mem_positivePart_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (positiveTwist C₀) v x ∈ ToricSpace.positivePart ↔
      x ∈ ToricSpace.positivePart := by
  constructor
  · intro hx
    have h := twistedTranslate_positiveTwist_preserves_positivePart C₀ (-v) hx
    simpa only [ToricSpace.twistedTranslate_add, neg_add_cancel,
      ToricSpace.twistedTranslate_zero] using h
  · intro hx
    exact twistedTranslate_positiveTwist_preserves_positivePart C₀ v hx

abbrev CuspPositive.LatticeGroup :=
  CuspQuotient.LatticeGroup

def CuspPositive.positiveTubeSet (ε : ℝ) : Set (ToricSpace.Tube (CuspQuotient.disc ε)) :=
  Subtype.val ⁻¹' ToricSpace.positivePart

abbrev CuspPositive.PositiveTube (ε : ℝ) :=
  positiveTubeSet ε

theorem CuspPositive.positiveTubeSet_isClosed (ε : ℝ) : IsClosed (positiveTubeSet ε) :=
  ToricSpace.positivePart_isClosed.preimage continuous_subtype_val

instance CuspPositive.positiveTube_locallyCompactSpace (ε : ℝ) :
    LocallyCompactSpace (PositiveTube ε) :=
  (positiveTubeSet_isClosed ε).locallyCompactSpace

def CuspPositive.positiveTubeToPositive (ε : ℝ) (x : PositiveTube ε) : ToricSpace.PositivePart :=
  ⟨(x.1 : ToricSpace.Space), x.2⟩

theorem CuspPositive.positiveTube_norm_time_lt (ε : ℝ) (x : PositiveTube ε) :
    ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ < ε := by
  have hx : ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 ε := x.1.2
  simpa only [Metric.mem_ball, dist_zero_right] using hx

def CuspPositive.positiveTubeHomeomorph (ε : ℝ) :
    PositiveTube ε ≃ₜ
      { x : ToricSpace.PositivePart // ‖ToricSpace.time (x : ToricSpace.Space)‖ < ε }
    where
  toFun x := ⟨positiveTubeToPositive ε x, positiveTube_norm_time_lt ε x⟩
  invFun
    x :=
    ⟨⟨(x.1 : ToricSpace.Space),
        by
        change ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 ε
        simpa only [Metric.mem_ball, dist_zero_right] using x.2⟩,
      x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def CuspPositive.positiveTubeTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (v : Fin 2 → ℤ)
    (x : PositiveTube ε) : PositiveTube ε :=
  ⟨ToricSpace.tubeTranslate (positiveTwist C₀) (CuspQuotient.disc ε) v x.1,
    (twistedTranslate_positiveTwist_mem_positivePart_iff C₀ v (x.1 : ToricSpace.Space)).mpr x.2⟩

@[instance_reducible]
def CuspPositive.positiveAction (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    MulAction LatticeGroup (PositiveTube ε)
    where
  smul g x := positiveTubeTranslate C₀ ε g.toAdd x
  one_smul
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact ToricSpace.twistedTranslate_zero (positiveTwist C₀) (x.1 : ToricSpace.Space)
  mul_smul g h
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (ToricSpace.twistedTranslate_add (positiveTwist C₀) g.toAdd h.toAdd
          (x.1 : ToricSpace.Space)).symm

theorem CuspPositive.positiveAction_compatible (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    letI := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
    letI := positiveAction C₀ ε
    ∀ (g : LatticeGroup) (x : PositiveTube ε), (g • x).1 = g • x.1 := by
  intros
  rfl

theorem CuspPositive.positiveAction_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    letI := positiveAction C₀ ε
    ContinuousConstSMul LatticeGroup (PositiveTube ε) := by
  let := positiveAction C₀ ε
  constructor
  intro g
  exact
    ((ToricSpace.tubeTranslate_holomorphic (positiveTwist C₀) (CuspQuotient.disc ε) g.toAdd
              (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn)).continuous.comp
          continuous_subtype_val).subtype_mk
      _

theorem CuspPositive.positiveAction_free (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    IsCancelSMul LatticeGroup (PositiveTube ε) := by
  let := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let :=
    CuspQuotient.free_action (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR
  let := positiveAction C₀ ε
  constructor
  intro g h x he
  exact IsCancelSMul.right_cancel g h x.1 (congrArg Subtype.val he)

theorem CuspPositive.positiveAction_properlyDiscontinuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    ProperlyDiscontinuousSMul LatticeGroup (PositiveTube ε) := by
  let := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let :=
    CuspQuotient.proper_action (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR
  let := positiveAction C₀ ε
  constructor
  intro K L hK hL
  have hf :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := LatticeGroup)
      (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)
  apply hf.subset
  rintro g ⟨z, ⟨y, hy, rfl⟩, hz⟩
  refine ⟨(g • y).1, ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
  exact ⟨g • y, hz, rfl⟩

def CuspPositive.relation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : Setoid (PositiveTube ε) :=
  let := positiveAction C₀ ε
  MulAction.orbitRel LatticeGroup (PositiveTube ε)

abbrev CuspPositive.QuotientSpace (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  Quotient (relation C₀ ε)

def CuspPositive.project (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    PositiveTube ε → QuotientSpace C₀ ε :=
  Quotient.mk (relation C₀ ε)

theorem CuspPositive.project_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Function.Surjective (project C₀ ε) :=
  Quotient.mk_surjective

@[simp]
theorem CuspPositive.project_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (v : Fin 2 → ℤ)
    (x : PositiveTube ε) : project C₀ ε (positiveTubeTranslate C₀ ε v x) = project C₀ ε x := by
  let := positiveAction C₀ ε
  exact MulAction.orbitRel.Quotient.quotient_smul_eq (g := Multiplicative.ofAdd v) (a := x)

theorem CuspPositive.project_covering (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    IsQuotientCoveringMap (project C₀ ε) LatticeGroup := by
  let := positiveAction C₀ ε
  let := positiveAction_continuous C₀ ε
  let := positiveAction_free C₀ ε hε hε1 hR
  let := positiveAction_properlyDiscontinuous C₀ ε hε hε1 hR
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem CuspPositive.quotient_t2Space (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    T2Space (QuotientSpace C₀ ε) := by
  let := positiveAction C₀ ε
  let := positiveAction_continuous C₀ ε
  let := positiveAction_properlyDiscontinuous C₀ ε hε hε1 hR
  change T2Space (Quotient (MulAction.orbitRel LatticeGroup (PositiveTube ε)))
  infer_instance

def CuspPositive.quotientInclusion (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    QuotientSpace C₀ ε → CuspQuotient.QuotientSpace (positiveTwist C₀) ε :=
  Quotient.lift (fun x : PositiveTube ε => CuspQuotient.quotientMap (positiveTwist C₀) ε x.1)
    (by
      let := positiveAction C₀ ε
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact CuspQuotient.quotientMap_translate (positiveTwist C₀) ε g.toAdd y.1)

theorem CuspPositive.quotientInclusion_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (quotientInclusion C₀ ε) :=
  ((CuspQuotient.quotientMap_continuous (positiveTwist C₀) ε).comp
        continuous_subtype_val).quotient_lift
    _

def CuspPositive.height (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (x : QuotientSpace C₀ ε) : ℝ :=
  ‖CuspQuotient.projection (positiveTwist C₀) ε (quotientInclusion C₀ ε x)‖

@[simp]
theorem CuspPositive.height_project (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (x : PositiveTube ε) :
    height C₀ ε (project C₀ ε x) = ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ :=
  rfl

theorem CuspPositive.height_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (height C₀ ε) :=
  ((CuspQuotient.projection_continuous (positiveTwist C₀) ε).comp
      (quotientInclusion_continuous C₀ ε)).norm

theorem CuspPositive.height_nonneg (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : QuotientSpace C₀ ε) : 0 ≤ height C₀ ε x :=
  norm_nonneg _

def CoveringOrthant.localChart {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    OpenPartialHomeomorph Q H :=
  (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).trans e

theorem CoveringOrthant.self_mem_localChart_source {G M Q H : Type*} [Group G]
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) (ha : a ∈ e.source) :
    q a ∈ (localChart hq e a).source := by
  change
    q a ∈ (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).source ∧
      hq.isCoveringMap.isLocalHomeomorph.localInverseAt a (q a) ∈ e.source
  exact
    ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source, by
      simpa only [IsLocalHomeomorph.localInverseAt_apply_self] using ha⟩

theorem CoveringOrthant.localChart_symm {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    ((localChart hq e a).symm : H → Q) = q ∘ e.symm := by
  simp only [localChart, OpenPartialHomeomorph.coe_trans_symm,
    IsLocalHomeomorph.localInverseAt_symm]

@[simp]
theorem CoveringOrthant.localChart_symm_apply {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) (z : H) :
    (localChart hq e a).symm z = q (e.symm z) := by rw [localChart_symm, Function.comp_apply]

theorem CoveringOrthant.localChart_target_subset {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    (localChart hq e a).target ⊆ e.target := fun _ hz => hz.1

theorem CoveringOrthant.localChart_coordinate_identity {G M Q H : Type*} [Group G]
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) {R : Type*}
    (f : Q → R) (F : H → R) (he : ∀ x ∈ e.source, f (q x) = F (e x)) :
    ∀ z ∈ (localChart hq e a).target, f ((localChart hq e a).symm z) = F z := by
  intro z hz
  have hze := localChart_target_subset hq e a hz
  rw [localChart_symm_apply, he (e.symm z) (e.map_target hze), e.right_inv hze]

def CuspPositive.positiveImage (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Set (CuspQuotient.QuotientSpace (positiveTwist C₀) ε) :=
  CuspQuotient.quotientMap (positiveTwist C₀) ε '' positiveTubeSet ε

theorem CuspPositive.positiveImage_isClosed (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    IsClosed (positiveImage C₀ ε) := by
  let := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let := positiveAction C₀ ε
  exact
    InvariantSubsetQuotient.isClosed_image
      (CuspQuotient.quotientMap_covering (positiveTwist C₀) ε hε hε1
        (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR)
      (positiveAction_compatible C₀ ε) (positiveTubeSet_isClosed ε)

def CuspPositive.quotientHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    QuotientSpace C₀ ε ≃ₜ positiveImage C₀ ε := by
  letI := ToricSpace.tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  letI := positiveAction C₀ ε
  exact
    InvariantSubsetQuotient.quotientHomeomorph
      (CuspQuotient.quotientMap_covering (positiveTwist C₀) ε hε hε1
        (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR)
      (positiveAction_compatible C₀ ε)

theorem CuspPositive.quotientHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (x : QuotientSpace C₀ ε) :
    (quotientHomeomorph C₀ ε hε hε1 hR x : CuspQuotient.QuotientSpace (positiveTwist C₀) ε) =
      quotientInclusion C₀ ε x := by
  obtain ⟨y, rfl⟩ := project_surjective C₀ ε x
  rfl

theorem CuspPositive.quotientInclusion_isClosedEmbedding (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) :
    Topology.IsClosedEmbedding (quotientInclusion C₀ ε) := by
  have h :=
    (positiveImage_isClosed C₀ ε hε hε1 hR).isClosedEmbedding_subtypeVal.comp
      (quotientHomeomorph C₀ ε hε hε1 hR).isClosedEmbedding
  have he : Subtype.val ∘ quotientHomeomorph C₀ ε hε hε1 hR = quotientInclusion C₀ ε :=
    funext (quotientHomeomorph_coe C₀ ε hε hε1 hR)
  rw [he] at h
  exact h

theorem CuspPositive.height_sublevel_isCompact (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) {η : ℝ}
    (hηε : η < ε) : IsCompact {x : QuotientSpace C₀ ε | height C₀ ε x ≤ η} := by
  obtain ⟨τ, hτ, hτε⟩ := exists_between (max_lt hηε hε)
  have hτ0 : 0 < τ := (le_max_right η 0).trans_lt hτ
  have hcompact :=
    CuspQuotient.closedDisc_preimage_compact (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR hτ0 hτε
  have hpre :=
    (quotientInclusion_isClosedEmbedding C₀ ε hε hε1 hR).isProperMap |>.isCompact_preimage
      hcompact
  apply hpre.of_isClosed_subset (isClosed_le (height_continuous C₀ ε) continuous_const)
  intro x hx
  change
    CuspQuotient.projection (positiveTwist C₀) ε (quotientInclusion C₀ ε x) ∈
      Metric.closedBall 0 τ
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.trans ((le_max_left η 0).trans hτ.le)

def CuspPositive.orthantComplexHomeomorph :
    CuspPositiveRetraction.Orthant ≃ₜ
      (ToricCharts.nonnegativeCoordinates : Set (ToricCharts.CoordinateSpace 3))
    where
  toFun r := ⟨fun i => (r.1 i : ℂ), ⟨r.1, r.2, rfl⟩⟩
  invFun
    z :=
    ⟨fun i => (z.1 i).re, by
      obtain ⟨r, hr, hz⟩ := z.2
      intro i
      rw [hz]
      exact hr i⟩
  left_inv
    r := by
    apply Subtype.ext
    rfl
  right_inv
    z := by
    apply Subtype.ext
    obtain ⟨r, hr, hz⟩ := z.2
    simp only [hz, Complex.ofReal_re]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_pi fun i =>
        Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      continuous_pi fun i =>
        Complex.continuous_re.comp ((continuous_apply i).comp continuous_subtype_val)

theorem CuspPositive.inclusion_preimage_positivePart (s : ToricFan.Triangle) :
    ToricSpace.inclusion s ⁻¹' ToricSpace.positivePart =
      (ToricCharts.nonnegativeCoordinates : Set (ToricCharts.CoordinateSpace 3)) := by
  ext z
  exact ToricSpace.inclusion_mem_positivePart_iff s z

def CuspPositive.positiveInclusion (s : ToricFan.Triangle) (r : CuspPositiveRetraction.Orthant) :
    ToricSpace.PositivePart :=
  ⟨ToricSpace.inclusion s (fun i => (r.1 i : ℂ)),
    (ToricSpace.inclusion_mem_positivePart_iff s _).mpr ⟨r.1, r.2, rfl⟩⟩

theorem CuspPositive.positiveInclusion_openEmbedding (s : ToricFan.Triangle) :
    Topology.IsOpenEmbedding (positiveInclusion s) := by
  let e :
    CuspPositiveRetraction.Orthant ≃ₜ (ToricSpace.inclusion s ⁻¹' ToricSpace.positivePart) :=
    orthantComplexHomeomorph.trans (Homeomorph.setCongr (inclusion_preimage_positivePart s).symm)
  have h :
    Topology.IsOpenEmbedding
      ((ToricSpace.positivePart.restrictPreimage (ToricSpace.inclusion s)) ∘ e) :=
    ((ToricSpace.inclusion_openEmbedding s).restrictPreimage ToricSpace.positivePart).comp
      e.isOpenEmbedding
  have he :
    ((ToricSpace.positivePart.restrictPreimage (ToricSpace.inclusion s)) ∘ e) =
      positiveInclusion s := by
    funext r
    apply Subtype.ext
    rfl
  rwa [he] at h

def CuspPositive.positiveParametrization (s : ToricFan.Triangle) :
    OpenPartialHomeomorph CuspPositiveRetraction.Orthant ToricSpace.PositivePart := by
  letI : Nonempty CuspPositiveRetraction.Orthant := ⟨⟨fun _ => 0, fun _ => le_rfl⟩⟩
  exact (positiveInclusion_openEmbedding s).toOpenPartialHomeomorph (positiveInclusion s)

@[simp]
theorem CuspPositive.positiveParametrization_apply (s : ToricFan.Triangle)
    (r : CuspPositiveRetraction.Orthant) : positiveParametrization s r = positiveInclusion s r :=
  rfl

@[simp]
theorem CuspPositive.positiveParametrization_target (s : ToricFan.Triangle) :
    (positiveParametrization s).target = Set.range (positiveInclusion s) := by
  simp [positiveParametrization]

theorem CuspPositive.positiveInclusion_positiveParametrization_symm (s : ToricFan.Triangle)
    {x : ToricSpace.PositivePart} (hx : x ∈ Set.range (positiveInclusion s)) :
    positiveInclusion s ((positiveParametrization s).symm x) = x := by
  have h :=
    (positiveParametrization s).right_inv
      (show x ∈ (positiveParametrization s).target by
        simpa only [positiveParametrization_target] using hx)
  simpa only [positiveParametrization_apply] using h

@[simp]
theorem CuspPositive.time_positiveInclusion (s : ToricFan.Triangle)
    (r : CuspPositiveRetraction.Orthant) :
    ToricSpace.time (positiveInclusion s r : ToricSpace.Space) =
      (CuspPositiveRetraction.height r : ℂ) := by
  simp [positiveInclusion, ToricFan.Triangle.time, CuspPositiveRetraction.height,
    Fin.prod_univ_succ, mul_assoc]

@[simp]
theorem CuspPositive.norm_time_positiveInclusion (s : ToricFan.Triangle)
    (r : CuspPositiveRetraction.Orthant) :
    ‖ToricSpace.time (positiveInclusion s r : ToricSpace.Space)‖ =
      CuspPositiveRetraction.height r := by
  rw [time_positiveInclusion]
  exact Complex.norm_of_nonneg (CuspPositiveRetraction.height_nonneg r)

theorem CuspPositive.positiveInclusion_jointly_surjective (x : ToricSpace.PositivePart) :
    ∃ s r, positiveInclusion s r = x := by
  obtain ⟨s, z, hz⟩ := ToricSpace.inclusion_jointly_surjective (x : ToricSpace.Space)
  have hp : ToricSpace.inclusion s z ∈ ToricSpace.positivePart := hz.symm ▸ x.property
  obtain ⟨r, hr, he⟩ := (ToricSpace.inclusion_mem_positivePart_iff s z).mp hp
  refine ⟨s, ⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  change ToricSpace.inclusion s (fun i => (r i : ℂ)) = (x : ToricSpace.Space)
  rw [← he]
  exact hz

def CuspPositive.positiveOpenTube (ε : ℝ) : TopologicalSpace.Opens ToricSpace.PositivePart :=
  ⟨{x | ‖ToricSpace.time (x : ToricSpace.Space)‖ < ε},
    isOpen_lt (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val).norm
      continuous_const⟩

def CuspPositive.positiveTubeOpenHomeomorph (ε : ℝ) : PositiveTube ε ≃ₜ positiveOpenTube ε :=
  positiveTubeHomeomorph ε

theorem CuspPositive.positiveOpenTube_nonempty (ε : ℝ) (hε : 0 < ε) :
    Nonempty (positiveOpenTube ε) := by
  refine ⟨⟨positiveInclusion ToricSpace.referenceTriangle ⟨0, fun _ => le_rfl⟩, ?_⟩⟩
  change
    ‖ToricSpace.time
          (positiveInclusion ToricSpace.referenceTriangle ⟨0, fun _ => le_rfl⟩ :
            ToricSpace.Space)‖ <
      ε
  rw [norm_time_positiveInclusion]
  simpa [CuspPositiveRetraction.height] using hε

def CuspPositive.positiveTubeChart (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) :
    OpenPartialHomeomorph (PositiveTube ε) CuspPositiveRetraction.Orthant :=
  (positiveTubeOpenHomeomorph ε).toOpenPartialHomeomorph.trans
    ((positiveParametrization s).symm.subtypeRestr (positiveOpenTube_nonempty ε hε))

@[simp]
theorem CuspPositive.positiveTubeChart_apply (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    (x : PositiveTube ε) :
    positiveTubeChart ε hε s x = (positiveParametrization s).symm (positiveTubeToPositive ε x) :=
  rfl

theorem CuspPositive.positiveTubeChart_source (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) :
    (positiveTubeChart ε hε s).source =
      {x | positiveTubeToPositive ε x ∈ Set.range (positiveInclusion s)} := by
  unfold positiveTubeChart
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.subtypeRestr_source]
  ext x
  change (x ∈ Set.univ ∧ positiveTubeToPositive ε x ∈ (positiveParametrization s).target) ↔ _
  simp only [Set.mem_univ, true_and, positiveParametrization_target, Set.mem_ofPred_eq]

theorem CuspPositive.exists_positiveTubeChart_source (ε : ℝ) (hε : 0 < ε) (x : PositiveTube ε) :
    ∃ s : ToricFan.Triangle, x ∈ (positiveTubeChart ε hε s).source := by
  obtain ⟨s, r, hr⟩ := positiveInclusion_jointly_surjective (positiveTubeToPositive ε x)
  refine ⟨s, ?_⟩
  rw [positiveTubeChart_source]
  exact ⟨r, hr⟩

theorem CuspPositive.positiveTubeChart_symm_positive (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    {r : CuspPositiveRetraction.Orthant} (hr : r ∈ (positiveTubeChart ε hε s).target) :
    positiveTubeToPositive ε ((positiveTubeChart ε hε s).symm r) = positiveInclusion s r := by
  have hx := (positiveTubeChart ε hε s).map_target hr
  rw [positiveTubeChart_source] at hx
  have he := positiveInclusion_positiveParametrization_symm s hx
  have hinv := (positiveTubeChart ε hε s).right_inv hr
  rw [positiveTubeChart_apply] at hinv
  rw [hinv] at he
  exact he.symm

theorem CuspPositive.positiveTubeChart_height_symm (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    {r : CuspPositiveRetraction.Orthant} (hr : r ∈ (positiveTubeChart ε hε s).target) :
    ‖ToricSpace.time (((positiveTubeChart ε hε s).symm r).1 : ToricSpace.Space)‖ =
      CuspPositiveRetraction.height r := by
  have h :=
    congrArg (fun x : ToricSpace.PositivePart => ‖ToricSpace.time (x : ToricSpace.Space)‖)
      (positiveTubeChart_symm_positive ε hε s hr)
  exact h.trans (norm_time_positiveInclusion s r)

theorem CuspPositive.positiveTubeChart_height (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle)
    {x : PositiveTube ε} (hx : x ∈ (positiveTubeChart ε hε s).source) :
    ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ =
      CuspPositiveRetraction.height (positiveTubeChart ε hε s x) := by
  have h := positiveTubeChart_height_symm ε hε s ((positiveTubeChart ε hε s).map_source hx)
  rwa [(positiveTubeChart ε hε s).left_inv hx] at h

def CuspPositive.quotientChart (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (a : PositiveTube ε)
    (s : ToricFan.Triangle) :
    OpenPartialHomeomorph (QuotientSpace C₀ ε) CuspPositiveRetraction.Orthant :=
  letI := positiveAction C₀ ε
  CoveringOrthant.localChart (project_covering C₀ ε hε hε1 hR) (positiveTubeChart ε hε s) a

theorem CuspPositive.quotientChart_mem_source (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (a : PositiveTube ε)
    (s : ToricFan.Triangle) (ha : a ∈ (positiveTubeChart ε hε s).source) :
    project C₀ ε a ∈ (quotientChart C₀ ε hε hε1 hR a s).source := by
  let := positiveAction C₀ ε
  exact
    CoveringOrthant.self_mem_localChart_source (project_covering C₀ ε hε hε1 hR)
      (positiveTubeChart ε hε s) a ha

theorem CuspPositive.quotientChart_height_symm (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε)
    (a : PositiveTube ε) (s : ToricFan.Triangle) {r : CuspPositiveRetraction.Orthant}
    (hr : r ∈ (quotientChart C₀ ε hε hε1 hR a s).target) :
    height C₀ ε ((quotientChart C₀ ε hε hε1 hR a s).symm r) = CuspPositiveRetraction.height r := by
  let := positiveAction C₀ ε
  apply
    CoveringOrthant.localChart_coordinate_identity (project_covering C₀ ε hε hε1 hR)
      (positiveTubeChart ε hε s) a (height C₀ ε) CuspPositiveRetraction.height ?_ r hr
  intro x hx
  rw [height_project]
  exact positiveTubeChart_height ε hε s hx

theorem CuspPositive.exists_quotientChart (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (positiveTwist C₀) ε) (x : QuotientSpace C₀ ε) :
    ∃ e : OpenPartialHomeomorph (QuotientSpace C₀ ε) CuspPositiveRetraction.Orthant,
      x ∈ e.source ∧ ∀ r ∈ e.target, height C₀ ε (e.symm r) = CuspPositiveRetraction.height r := by
  obtain ⟨a, ha⟩ := project_surjective C₀ ε x
  obtain ⟨s, hs⟩ := exists_positiveTubeChart_source ε hε a
  refine ⟨quotientChart C₀ ε hε hε1 hR a s, ?_, ?_⟩
  · rw [← ha]
    exact quotientChart_mem_source C₀ ε hε hε1 hR a s hs
  · intro r hr
    exact quotientChart_height_symm C₀ ε hε hε1 hR a s hr

def ToricSpace.phaseShear (v : Fin 2 → ℤ) (u : CompactTorus) : CompactTorus :=
  ![u 0 * u 2 ^ v 0, u 1 * u 2 ^ v 1, u 2]

theorem ToricSpace.phaseShear_coe (v : Fin 2 → ℤ) (u : CompactTorus) :
    (fun j => (phaseShear v u j : ℂ)) =
      ToricCharts.monomial (ToricFan.Triangle.shear v) (fun j => (u j : ℂ)) := by
  funext i
  fin_cases i <;>
    simp [phaseShear, ToricCharts.monomial, ToricFan.Triangle.shear, Fin.prod_univ_succ]

theorem ToricSpace.factors_shift_phaseShear (s : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (u : CompactTorus) :
    factors (s.shift v) (compactTorusUnits (phaseShear v u)) = factors s (compactTorusUnits u) := by
  change
    ToricCharts.monomial (s.shift v).dual (fun j => (phaseShear v u j : ℂ)) =
      ToricCharts.monomial s.dual (fun j => (u j : ℂ))
  rw [ToricFan.Triangle.dual_shift, phaseShear_coe,
    ToricCharts.monomial_mul_on_torus _ _ (fun j => (u j).coe_ne_zero), Matrix.mul_assoc,
    ToricFan.Triangle.shear_add]
  simp

theorem ToricSpace.translate_compactTorusAction (v : Fin 2 → ℤ) (u : CompactTorus) (x : Space) :
    ToricSpace.translate v (compactTorusAction u x) =
      compactTorusAction (phaseShear v u) (ToricSpace.translate v x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [compactTorusAction, scale, factors_shift_phaseShear]

def CuspPositive.frozenPhaseCoordinate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) : Circle :=
  ⟨(ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ) /
      (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0 i : ℂ),
    by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, exponentialMultiplier_positiveTwist_norm]
    exact
      div_self
        (norm_ne_zero_iff.mpr (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i).ne_zero)⟩

@[simp]
theorem CuspPositive.frozenPhaseCoordinate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) :
    (frozenPhaseCoordinate C₀ v i : ℂ) =
      (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 i : ℂ) /
        (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0 i : ℂ) :=
  rfl

theorem CuspPositive.frozenPhaseCoordinate_eq_exp (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) :
    frozenPhaseCoordinate C₀ v i =
      Circle.exp (2 * Real.pi * ((C₀ *ᵥ (fun j => (v j : ℂ))) i).re) := by
  apply Circle.ext
  simp only [frozenPhaseCoordinate_coe, Circle.coe_exp, ToricSpace.exponentialMultiplier,
    Units.val_mk0, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;>
    simp [positiveTwist, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]

def CuspPositive.frozenPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    ToricSpace.CompactTorus :=
  ![frozenPhaseCoordinate C₀ v 0, frozenPhaseCoordinate C₀ v 1, 1]

theorem CuspPositive.compactTorusUnits_frozenPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    ToricSpace.compactTorusUnits (frozenPhase C₀ v) =
      ToricSpace.fibreMultiplier
        (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0 /
          ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0) := by
  funext i
  apply Units.ext
  fin_cases i <;> simp [frozenPhase, ToricSpace.fibreMultiplier]

theorem CuspPositive.frozenMultiplier_phase_positive (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0) =
      ToricSpace.compactTorusUnits (frozenPhase C₀ v) *
        ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (positiveTwist C₀) v 0) := by
  rw [compactTorusUnits_frozenPhase, ← ToricSpace.fibreMultiplier_mul, div_mul_cancel]

theorem CuspPositive.twistedTranslate_constant_eq (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (fun _ => C₀) v x =
      ToricSpace.torusAction
        (ToricSpace.fibreMultiplier (ToricSpace.exponentialMultiplier (fun _ => C₀) v 0))
        (ToricSpace.translate (ToricSpace.cuspVector v) x) :=
  rfl

def CuspPositive.phaseTransform (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (u : ToricSpace.CompactTorus) : ToricSpace.CompactTorus :=
  frozenPhase C₀ v * ToricSpace.phaseShear (ToricSpace.cuspVector v) u

theorem CuspPositive.twistedTranslate_constant_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : ToricSpace.CompactTorus) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (fun _ => C₀) v (ToricSpace.compactTorusAction u x) =
      ToricSpace.compactTorusAction (phaseTransform C₀ v u)
        (ToricSpace.twistedTranslate (positiveTwist C₀) v x) := by
  rw [twistedTranslate_constant_eq, ToricSpace.translate_compactTorusAction,
    twistedTranslate_positiveTwist_eq]
  simp only [phaseTransform, ToricSpace.compactTorusAction, map_mul, ToricSpace.torusAction_mul]
  rw [frozenMultiplier_phase_positive]
  congr 1
  ac_rfl

def CuspPositive.closedPositiveTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (v : Fin 2 → ℤ)
    (q : ToricSpace.ClosedPositiveTube η) : ToricSpace.ClosedPositiveTube η :=
  ⟨⟨ToricSpace.twistedTranslate (positiveTwist C₀) v q.1,
      twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by simpa only [ToricSpace.time_twistedTranslate] using q.2⟩

@[simp]
theorem CuspPositive.closedPositiveTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    ((closedPositiveTranslate C₀ η v q).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (positiveTwist C₀) v q.1 :=
  rfl

def CuspPositiveRetraction.quotientHeight (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    C(CuspPositive.QuotientSpace C₀ ε, ℝ) :=
  ⟨CuspPositive.height C₀ ε, CuspPositive.height_continuous C₀ ε⟩

theorem CuspPositiveRetraction.exists_positiveQuotient_collapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η : ℝ,
      0 < η ∧
        η < ε ∧
          ∃ A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε),
            {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet := by
  let := CuspPositive.quotient_t2Space C₀ ε hε hε1 hR
  have hhalf : 0 < ε / 2 := half_pos hε
  have hhalfε : ε / 2 < ε := half_lt_self hε
  obtain ⟨η, hη, hηhalf, A, hA⟩ :=
    exists_small_sublevel_collapse_of_orthant_charts (quotientHeight C₀ ε)
      (CuspPositive.height_nonneg C₀ ε) hhalf
      (CuspPositive.height_sublevel_isCompact C₀ ε hε hε1 hR hhalfε)
      (by
        intro x _hx
        obtain ⟨e, hx, he⟩ := CuspPositive.exists_quotientChart C₀ ε hε hε1 hR x
        refine ⟨e.symm, e x, e.map_source hx, e.left_inv hx, ?_⟩
        exact he)
  exact ⟨η, hη, hηhalf.trans_lt hhalfε, A, hA⟩

def CuspPositiveRetraction.closedPositiveSublevelHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) {η : ℝ} (hηε : η < ε) :
    ToricSpace.ClosedPositiveTube η ≃ₜ
      { x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η } := by
  let F :
    ToricSpace.ClosedPositiveTube η →
      { x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η } :=
    fun x =>
    by
    have hx : ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε
    exact ⟨⟨⟨(x.1 : ToricSpace.Space), hx⟩, x.1.2⟩, x.2⟩
  let G :
    { x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η } →
      ToricSpace.ClosedPositiveTube η :=
    fun x => ⟨⟨(x.1.1 : ToricSpace.Space), x.1.2⟩, x.2⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        Continuous.subtype_mk
          (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _) _
      continuous_invFun :=
        (((continuous_subtype_val.comp continuous_subtype_val).comp
                  continuous_subtype_val).subtype_mk
              _).subtype_mk
          _ }

@[simp]
theorem CuspPositiveRetraction.closedPositiveSublevelHomeomorph_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) {η : ℝ} (hηε : η < ε)
    (x : ToricSpace.ClosedPositiveTube η) :
    (((closedPositiveSublevelHomeomorph C₀ ε hηε x).1).1 : ToricSpace.Space) =
      (x.1 : ToricSpace.Space) :=
  rfl

theorem CuspPositiveRetraction.closedPositiveSublevelHomeomorph_translate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) {η : ℝ} (hηε : η < ε) (v : Fin 2 → ℤ)
    (x : ToricSpace.ClosedPositiveTube η) :
    (closedPositiveSublevelHomeomorph C₀ ε hηε
          (CuspPositive.closedPositiveTranslate C₀ η v x)).1 =
      CuspPositive.positiveTubeTranslate C₀ ε v (closedPositiveSublevelHomeomorph C₀ ε hηε x).1 :=
  rfl

theorem CuspPositiveRetraction.positiveCovering (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    IsCoveringMap (CuspPositive.project C₀ ε) := by
  let := CuspPositive.positiveAction C₀ ε
  exact (CuspPositive.project_covering C₀ ε hε hε1 hR).isCoveringMap

def CuspPositiveRetraction.positiveLift (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) :
    C(unitInterval × CuspPositive.PositiveTube ε, CuspPositive.PositiveTube ε) :=
  Covering.lift (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero

@[simp]
theorem CuspPositiveRetraction.positiveLift_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε))
    (x : CuspPositive.PositiveTube ε) : positiveLift C₀ ε hε hε1 hR A (0, x) = x :=
  Covering.lift_zero (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero x

theorem CuspPositiveRetraction.positiveLift_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) :
    CuspPositive.project C₀ ε (positiveLift C₀ ε hε hε1 hR A (s, x)) =
      A.homotopy (s, CuspPositive.project C₀ ε x) :=
  Covering.lift_projection (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero s x

theorem CuspPositiveRetraction.positiveLift_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (v : Fin 2 → ℤ)
    (s : unitInterval) (x : CuspPositive.PositiveTube ε) :
    positiveLift C₀ ε hε hε1 hR A (s, CuspPositive.positiveTubeTranslate C₀ ε v x) =
      CuspPositive.positiveTubeTranslate C₀ ε v (positiveLift C₀ ε hε hε1 hR A (s, x)) := by
  let := CuspPositive.positiveAction C₀ ε
  let := CuspPositive.positiveAction_continuous C₀ ε
  exact
    Covering.lift_equivariant (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
      (fun g x => CuspPositive.project_translate C₀ ε g.toAdd x) (Multiplicative.ofAdd v) s x

theorem CuspPositiveRetraction.positiveLift_fixed (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) (hx : ToricSpace.time (x.1 : ToricSpace.Space) = 0) :
    positiveLift C₀ ε hε hε1 hR A (s, x) = x := by
  apply Covering.lift_fixed (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero x
  intro t
  apply A.fixes_zero
  change ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = 0
  simp only [hx, norm_zero]

theorem CuspPositiveRetraction.positiveLift_nonincreasing (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) :
    ‖ToricSpace.time ((positiveLift C₀ ε hε hε1 hR A (s, x)).1 : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ :=
  Covering.lift_height_le (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
    (CuspPositive.height C₀ ε) A.nonincreasing s x

def CuspPositiveRetraction.positiveDeformation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε) :
    C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η) :=
  let e := closedPositiveSublevelHomeomorph C₀ ε hηε
  let L :=
    Covering.liftSublevel (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
      (CuspPositive.height C₀ ε) η A.nonincreasing
  ⟨fun p => e.symm (L (p.1, e p.2)),
    e.symm.continuous.comp
      (L.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩

theorem CuspPositiveRetraction.positiveDeformation_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ToricSpace.ClosedPositiveTube η) :
    ((positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)).1 : ToricSpace.Space) =
      ((positiveLift C₀ ε hε hε1 hR A (s, (closedPositiveSublevelHomeomorph C₀ ε hηε x).1)).1 :
        ToricSpace.Space) :=
  rfl

@[simp]
theorem CuspPositiveRetraction.positiveDeformation_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (x : ToricSpace.ClosedPositiveTube η) : positiveDeformation C₀ ε hε hε1 hR A hηε (0, x) = x :=
  by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe, positiveLift_zero]
  rfl

theorem CuspPositiveRetraction.positiveDeformation_fixed (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ToricSpace.ClosedPositiveTube η)
    (hx : ToricSpace.time (x.1 : ToricSpace.Space) = 0) :
    positiveDeformation C₀ ε hε hε1 hR A hηε (s, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe]
  have hy := (congrArg ToricSpace.time (closedPositiveSublevelHomeomorph_coe C₀ ε hηε x)).trans hx
  have he :=
    positiveLift_fixed C₀ ε hε hε1 hR A s (closedPositiveSublevelHomeomorph C₀ ε hηε x).1 hy
  exact
    (congrArg (fun y : CuspPositive.PositiveTube ε => (y.1 : ToricSpace.Space)) he).trans
      (closedPositiveSublevelHomeomorph_coe C₀ ε hηε x)

theorem CuspPositiveRetraction.positiveDeformation_nonincreasing (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ToricSpace.ClosedPositiveTube η) :
    ‖ToricSpace.time ((positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)).1 : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ :=
  positiveLift_nonincreasing C₀ ε hε hε1 hR A s (closedPositiveSublevelHomeomorph C₀ ε hηε x).1

theorem CuspPositiveRetraction.positiveDeformation_one_central (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (hA : {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet)
    (x : ToricSpace.ClosedPositiveTube η) :
    ToricSpace.time ((positiveDeformation C₀ ε hε hε1 hR A hηε (1, x)).1 : ToricSpace.Space) =
      0 := by
  apply norm_eq_zero.mp
  rw [positiveDeformation_coe]
  change
    CuspPositive.height C₀ ε
        (CuspPositive.project C₀ ε
          (positiveLift C₀ ε hε hε1 hR A (1, (closedPositiveSublevelHomeomorph C₀ ε hηε x).1))) =
      0
  rw [positiveLift_projection]
  exact A.map_one_zero _ (hA (closedPositiveSublevelHomeomorph C₀ ε hηε x).2)

theorem CuspPositiveRetraction.positiveDeformation_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε)) {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ToricSpace.ClosedPositiveTube η) :
    positiveDeformation C₀ ε hε hε1 hR A hηε (s, CuspPositive.closedPositiveTranslate C₀ η v x) =
      CuspPositive.closedPositiveTranslate C₀ η v
        (positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe, closedPositiveSublevelHomeomorph_translate,
    positiveLift_equivariant, CuspPositive.closedPositiveTranslate_coe, positiveDeformation_coe]
  rfl

theorem CuspPositiveRetraction.exists_positive_closed_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ η : ℝ,
            0 < η →
              η ≤ η₀ →
                ∃ P :
                  C(unitInterval × ToricSpace.ClosedPositiveTube η,
                    ToricSpace.ClosedPositiveTube η),
                  (∀ q, P (0, q) = q) ∧
                    (∀ s q,
                      ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) ∧
                      (∀ q, ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0) ∧
                        (∀ s v q,
                            P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
                              CuspPositive.closedPositiveTranslate C₀ η v (P (s, q))) ∧
                          (∀ s q,
                            ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
                              ‖ToricSpace.time (q.1 : ToricSpace.Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀ε, A, hA⟩ := exists_positiveQuotient_collapse C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η _hη hηη₀
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  have hAη : {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet := fun _ hx =>
    hA (hx.trans hηη₀)
  refine
    ⟨positiveDeformation C₀ ε hε hε1 hR A hηε, positiveDeformation_zero C₀ ε hε hε1 hR A hηε,
      positiveDeformation_fixed C₀ ε hε hε1 hR A hηε,
      positiveDeformation_one_central C₀ ε hε hε1 hR A hηε hAη,
      positiveDeformation_equivariant C₀ ε hε hε1 hR A hηε,
      positiveDeformation_nonincreasing C₀ ε hε hε1 hR A hηε⟩

def CuspRetraction.closedCompactAction (η : ℝ) (u : ToricSpace.CompactTorus) (x : ClosedTube η) :
    ClosedTube η :=
  ⟨ToricSpace.compactTorusAction u x,
    by
    rw [ToricSpace.norm_time_compactTorusAction]
    exact x.2⟩

theorem CuspRetraction.closedCompactAction_closedPolarMap (η : ℝ) (u v : ToricSpace.CompactTorus)
    (q : ToricSpace.ClosedPositiveTube η) :
    closedCompactAction η u (ToricSpace.closedPolarMap η (v, q)) =
      ToricSpace.closedPolarMap η (u * v, q) :=
  Subtype.ext (ToricSpace.compactTorusAction_mul u v q.1)

theorem CuspRetraction.positiveHomotopy_polar_compatible {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (u v : ToricSpace.CompactTorus) (q r : ToricSpace.ClosedPositiveTube η)
    (h : ToricSpace.closedPolarMap η (u, q) = ToricSpace.closedPolarMap η (v, r)) :
    ToricSpace.closedPolarMap η (u, P (s, q)) = ToricSpace.closedPolarMap η (v, P (s, r)) := by
  have hqr : q = r := by
    apply Subtype.ext
    apply Subtype.ext
    have hm :
      ToricSpace.modulus (ToricSpace.compactTorusAction u q.1) =
        ToricSpace.modulus (ToricSpace.compactTorusAction v r.1) :=
      congrArg (fun x : ClosedTube η => ToricSpace.modulus (x : ToricSpace.Space)) h
    rwa [ToricSpace.modulus_compactTorusAction, ToricSpace.modulus_compactTorusAction, q.1.2,
      r.1.2] at hm
  subst r
  by_cases hq : ToricSpace.time (q.1 : ToricSpace.Space) = 0
  · rw [hfix s q hq]
    exact h
  · have huv : u = v :=
      ToricSpace.compactTorusAction_injective_of_time_ne_zero hq (congrArg Subtype.val h)
    rw [huv]

private def CuspRetraction.polarRepresentative_mo1973_10806 (η : ℝ) (x : ClosedTube η) :
    ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η :=
  (ToricSpace.closedPolarMap_surjective η x).choose

private theorem CuspRetraction.polarRepresentative_spec_mo1973_10807 (η : ℝ) (x : ClosedTube η) :
    ToricSpace.closedPolarMap η (polarRepresentative_mo1973_10806 η x) = x :=
  (ToricSpace.closedPolarMap_surjective η x).choose_spec

def CuspRetraction.polarSpread {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (s : unitInterval) (x : ClosedTube η) : ClosedTube η :=
  let p := polarRepresentative_mo1973_10806 η x
  ToricSpace.closedPolarMap η (p.1, P (s, p.2))

theorem CuspRetraction.polarSpread_closedPolarMap {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (p : ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η) :
    polarSpread P s (ToricSpace.closedPolarMap η p) =
      ToricSpace.closedPolarMap η (p.1, P (s, p.2)) := by
  change
    ToricSpace.closedPolarMap η
        ((polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).1,
          P (s, (polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).2)) =
      _
  exact
    positiveHomotopy_polar_compatible P hfix s
      (polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).1 p.1
      (polarRepresentative_mo1973_10806 η (ToricSpace.closedPolarMap η p)).2 p.2
      (polarRepresentative_spec_mo1973_10807 η (ToricSpace.closedPolarMap η p))

theorem CuspRetraction.polarSpread_continuous {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) :
    Continuous (fun p : unitInterval × ClosedTube η => polarSpread P p.1 p.2) := by
  apply (ToricSpace.closedPolarMap_isQuotientMap η).continuous_lift_prod_right
  have h :
    Continuous
      (fun p : unitInterval × (ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η) =>
        ToricSpace.closedPolarMap η (p.2.1, P (p.1, p.2.2))) :=
    (ToricSpace.closedPolarMap_continuous η).comp
      ((continuous_fst.comp continuous_snd).prodMk
        (P.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  simpa only [polarSpread_closedPolarMap P hfix] using h

theorem CuspRetraction.polarSpread_compactTorus_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (u : ToricSpace.CompactTorus) (x : ClosedTube η) :
    polarSpread P s (closedCompactAction η u x) = closedCompactAction η u (polarSpread P s x) := by
  obtain ⟨⟨v, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [closedCompactAction_closedPolarMap, polarSpread_closedPolarMap P hfix,
    polarSpread_closedPolarMap P hfix, closedCompactAction_closedPolarMap]

theorem CuspRetraction.polarSpread_zero {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hzero : ∀ q : ToricSpace.ClosedPositiveTube η, P (0, q) = q) (x : ClosedTube η) :
    polarSpread P 0 x = x := by
  obtain ⟨p, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix, hzero]

theorem CuspRetraction.polarSpread_fixed {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (x : ClosedTube η) (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    polarSpread P s x = x := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  have hq : ToricSpace.time (q.1 : ToricSpace.Space) = 0 := by
    have hn := congrArg Norm.norm hx
    change ‖ToricSpace.time (ToricSpace.compactTorusAction u q.1)‖ = ‖(0 : ℂ)‖ at hn
    rw [ToricSpace.norm_time_compactTorusAction, norm_zero] at hn
    exact norm_eq_zero.mp hn
  rw [polarSpread_closedPolarMap P hfix, hfix s q hq]

theorem CuspRetraction.polarSpread_one_central {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (x : ClosedTube η) : ToricSpace.time (polarSpread P 1 x : ToricSpace.Space) = 0 := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix]
  change ToricSpace.time (ToricSpace.compactTorusAction u ((P (1, q)).1 : ToricSpace.Space)) = 0
  simp only [ToricSpace.compactTorusAction, ToricSpace.time_torusAction, hone q,
    MulZeroClass.mul_zero]

abbrev CuspRetraction.CentralFibre :=
  { x : ToricSpace.Space // ToricSpace.time x = 0 }

def CuspRetraction.centralIntoClosedTube (η : ℝ) (hη : 0 ≤ η) : C(CentralFibre, ClosedTube η)
    where
  toFun x := ⟨x, by rw [x.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem CuspPositive.closedTranslate_closedPolarMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (u : ToricSpace.CompactTorus) (q : ToricSpace.ClosedPositiveTube η) :
    CuspRetraction.closedTranslate (fun _ => C₀) η v (ToricSpace.closedPolarMap η (u, q)) =
      ToricSpace.closedPolarMap η (phaseTransform C₀ v u, closedPositiveTranslate C₀ η v q) :=
  Subtype.ext (twistedTranslate_constant_polar C₀ v u q.1)

theorem CuspRetraction.polarSpread_frozen_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η),
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η) :
    polarSpread P s (closedTranslate (fun _ => C₀) η v x) =
      closedTranslate (fun _ => C₀) η v (polarSpread P s x) := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [CuspPositive.closedTranslate_closedPolarMap, polarSpread_closedPolarMap P hfix,
    polarSpread_closedPolarMap P hfix, CuspPositive.closedTranslate_closedPolarMap, hequiv]

theorem CuspRetraction.polarSpread_norm_time_le {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hmono :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (q.1 : ToricSpace.Space)‖)
    (s : unitInterval) (x : ClosedTube η) :
    ‖ToricSpace.time (polarSpread P s x : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x : ToricSpace.Space)‖ := by
  obtain ⟨⟨u, q⟩, rfl⟩ := ToricSpace.closedPolarMap_surjective η x
  rw [polarSpread_closedPolarMap P hfix]
  simpa only [ToricSpace.closedPolarMap_coe, ToricSpace.norm_time_compactTorusAction] using
    hmono s q

def CuspRetraction.compactFibrePhase (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) :
    ToricSpace.CompactTorus :=
  ![⟨(u 0 : ℂ), mem_sphere_zero_iff_norm.mpr (hu 0)⟩,
    ⟨(u 1 : ℂ), mem_sphere_zero_iff_norm.mpr (hu 1)⟩, 1]

@[simp]
theorem CuspRetraction.compactTorusUnits_compactFibrePhase (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) :
    ToricSpace.compactTorusUnits (compactFibrePhase u hu) = ToricSpace.fibreMultiplier u := by
  funext i
  apply Units.ext
  fin_cases i <;> simp [compactFibrePhase, ToricSpace.fibreMultiplier]

@[simp]
theorem CuspRetraction.closedCompactAction_compactFibrePhase (η : ℝ) (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedCompactAction η (compactFibrePhase u hu) x = closedFibreAction η u x := by
  apply Subtype.ext
  change
    ToricSpace.torusAction (ToricSpace.compactTorusUnits (compactFibrePhase u hu)) x =
      ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x
  rw [compactTorusUnits_compactFibrePhase]

theorem CuspRetraction.polarSpread_fibre_torus_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    polarSpread P s (closedFibreAction η u x) = closedFibreAction η u (polarSpread P s x) := by
  simpa only [closedCompactAction_compactFibrePhase] using
    polarSpread_compactTorus_equivariant P hfix s (compactFibrePhase u hu) x

theorem CuspPositiveRetraction.exists_frozen_closed_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ η : ℝ,
            0 < η →
              η ≤ η₀ →
                ∃ H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η),
                  (∀ x, H (0, x) = x) ∧
                    (∀ s (x : CuspRetraction.ClosedTube η),
                        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                      (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                        (∀ s v x,
                            H (s, CuspRetraction.closedTranslate (fun _ => C₀) η v x) =
                              CuspRetraction.closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
                          (∀ s u x,
                              H (s, CuspRetraction.closedCompactAction η u x) =
                                CuspRetraction.closedCompactAction η u (H (s, x))) ∧
                            (∀ s (u : Fin 2 → ℂˣ),
                                (∀ i, ‖(u i : ℂ)‖ = 1) →
                                  ∀ x,
                                    H (s, CuspRetraction.closedFibreAction η u x) =
                                      CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                              (∀ s x,
                                ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                  ‖ToricSpace.time (x : ToricSpace.Space)‖) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ := exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono⟩ := hP η hη hηη₀
  let H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η) :=
    ⟨fun p => CuspRetraction.polarSpread P p.1 p.2, CuspRetraction.polarSpread_continuous P hfix⟩
  exact
    ⟨H, CuspRetraction.polarSpread_zero P hfix hzero, CuspRetraction.polarSpread_fixed P hfix,
      CuspRetraction.polarSpread_one_central P hfix hone,
      CuspRetraction.polarSpread_frozen_equivariant C₀ P hfix hequiv,
      CuspRetraction.polarSpread_compactTorus_equivariant P hfix,
      CuspRetraction.polarSpread_fibre_torus_equivariant P hfix,
      CuspRetraction.polarSpread_norm_time_le P hfix hmono⟩

def CuspPositiveRetraction.closedFrozenStraightening (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) : CuspRetraction.ClosedTube η ≃ₜ CuspRetraction.ClosedTube η :=
  CuspRetraction.closedTubeHomeomorph C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε

theorem CuspPositiveRetraction.closedFrozenStraightening_base (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x : ToricSpace.Space) =
      ToricSpace.time (x : ToricSpace.Space) :=
  CuspRetraction.closedTubeHomeomorph_base C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε x

theorem CuspPositiveRetraction.closedFrozenStraightening_symm_base
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time
        (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x : ToricSpace.Space) =
      ToricSpace.time (x : ToricSpace.Space) := by
  have h :=
    closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε
      (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x)
  rw [((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply] at h
  exact h.symm

theorem CuspPositiveRetraction.closedFrozenStraightening_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η)
    (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x = x :=
  CuspRetraction.closedTubeHomeomorph_fixes_central C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε x hx

theorem CuspPositiveRetraction.closedFrozenStraightening_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η) :
    (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) (CuspRetraction.closedTranslate C η v x) =
      CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v
        ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) :=
  CuspRetraction.closedTubeHomeomorph_equivariant C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε v x

theorem CuspPositiveRetraction.closedFrozenStraightening_symm_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η) :
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
        (CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v x) =
      CuspRetraction.closedTranslate C η v
        (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x) := by
  apply ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).injective
  rw [((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply,
    closedFrozenStraightening_equivariant,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply]

theorem CuspPositiveRetraction.closedFrozenStraightening_fibre_torus
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : CuspRetraction.ClosedTube η) :
    (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) (CuspRetraction.closedFibreAction η u x) =
      CuspRetraction.closedFibreAction η u
        ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) :=
  CuspRetraction.closedTubeHomeomorph_fibre_torus C (CuspRetraction.frozen C) hε hε1 hC
    (fun _ _ => continuousOn_const) rfl hRC hRD hηε u hu x

theorem CuspPositiveRetraction.closedFrozenStraightening_symm_fibre_torus
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : CuspRetraction.ClosedTube η) :
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
        (CuspRetraction.closedFibreAction η u x) =
      CuspRetraction.closedFibreAction η u
        (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm x) := by
  apply ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).injective
  rw [((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply,
    closedFrozenStraightening_fibre_torus C hε hε1 hC hRC hRD hηε u hu,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).apply_symm_apply]

def CuspPositiveRetraction.straightenedHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε)
    (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η)) :
    C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η)
    where
  toFun
    p :=
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
      (H (p.1, (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) p.2))
  continuous_toFun :=
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm.continuous.comp
      (H.continuous.comp
        (continuous_fst.prodMk
          (((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).continuous.comp continuous_snd)))

@[simp]
theorem CuspPositiveRetraction.straightenedHomotopy_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (s : unitInterval) (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) =
      ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm
        (H (s, (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x)) :=
  rfl

theorem CuspPositiveRetraction.straightenedHomotopy_time (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (s : unitInterval) (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) : ToricSpace.Space) =
      ToricSpace.time
        (H (s, (closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) : ToricSpace.Space) :=
  closedFrozenStraightening_symm_base C hε hε1 hC hRC hRD hηε _

theorem CuspPositiveRetraction.straightenedHomotopy_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hzero : ∀ x : CuspRetraction.ClosedTube η, H (0, x) = x) (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (0, x) = x := by
  rw [straightenedHomotopy_apply, hzero,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm_apply_apply]

theorem CuspPositiveRetraction.straightenedHomotopy_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hfixed :
      ∀ (s : unitInterval) (x : CuspRetraction.ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (s : unitInterval) (x : CuspRetraction.ClosedTube η)
    (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) = x := by
  have hGx :
    ToricSpace.time ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x : ToricSpace.Space) =
      0 :=
    (closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε x).trans hx
  rw [straightenedHomotopy_apply,
    hfixed s ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x) hGx,
    ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε)).symm_apply_apply]

theorem CuspPositiveRetraction.straightenedHomotopy_one_central (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hone : ∀ x : CuspRetraction.ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0)
    (x : CuspRetraction.ClosedTube η) :
    ToricSpace.time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (1, x) : ToricSpace.Space) =
      0 := by
  rw [straightenedHomotopy_time]
  exact hone ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x)

theorem CuspPositiveRetraction.straightenedHomotopy_norm_time_le
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hnorm :
      ∀ (s : unitInterval) (x : CuspRetraction.ClosedTube η),
        ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (x : ToricSpace.Space)‖)
    (s : unitInterval) (x : CuspRetraction.ClosedTube η) :
    ‖ToricSpace.time (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x) : ToricSpace.Space)‖ ≤
      ‖ToricSpace.time (x : ToricSpace.Space)‖ := by
  rw [straightenedHomotopy_time]
  exact
    (hnorm s ((closedFrozenStraightening C hε hε1 hC hRC hRD hηε) x)).trans_eq
      (congrArg Norm.norm (closedFrozenStraightening_base C hε hε1 hC hRC hRD hηε x))

theorem CuspPositiveRetraction.straightenedHomotopy_equivariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η),
        H (s, CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v x) =
          CuspRetraction.closedTranslate (CuspRetraction.frozen C) η v (H (s, x)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, CuspRetraction.closedTranslate C η v x) =
      CuspRetraction.closedTranslate C η v
        (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x)) := by
  simp only [straightenedHomotopy_apply, closedFrozenStraightening_equivariant, hequiv,
    closedFrozenStraightening_symm_equivariant]

theorem CuspPositiveRetraction.straightenedHomotopy_fibre_torus_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hequiv :
      ∀ (s : unitInterval) (u : Fin 2 → ℂˣ),
        (∀ i, ‖(u i : ℂ)‖ = 1) →
          ∀ x : CuspRetraction.ClosedTube η,
            H (s, CuspRetraction.closedFibreAction η u x) =
              CuspRetraction.closedFibreAction η u (H (s, x)))
    (s : unitInterval) (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1)
    (x : CuspRetraction.ClosedTube η) :
    straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, CuspRetraction.closedFibreAction η u x) =
      CuspRetraction.closedFibreAction η u
        (straightenedHomotopy C hε hε1 hC hRC hRD hηε H (s, x)) := by
  simp only [straightenedHomotopy_apply,
    closedFrozenStraightening_fibre_torus C hε hε1 hC hRC hRD hηε u hu, hequiv s u hu,
    closedFrozenStraightening_symm_fibre_torus C hε hε1 hC hRC hRD hηε u hu]

private noncomputable def CuspRetraction.descentRepresentative_mo1973_10849
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε) (q : ClosedQuotient C ε η) :
    ClosedTube η :=
  (closedQuotientMap_surjective C hηε q).choose

private theorem CuspRetraction.descentRepresentative_spec_mo1973_10850
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε) (q : ClosedQuotient C ε η) :
    closedQuotientMap C hηε (descentRepresentative_mo1973_10849 C hηε q) = q :=
  (closedQuotientMap_surjective C hηε q).choose_spec

noncomputable def CuspRetraction.closedHomotopyDescent (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η)) (s : unitInterval)
    (q : ClosedQuotient C ε η) : ClosedQuotient C ε η :=
  closedQuotientMap C hηε (H (s, descentRepresentative_mo1973_10849 C hηε q))

theorem CuspRetraction.closedHomotopyDescent_compatible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (s : unitInterval) (x y : ClosedTube η)
    (hxy : closedQuotientMap C hηε x = closedQuotientMap C hηε y) :
    closedQuotientMap C hηε (H (s, x)) = closedQuotientMap C hηε (H (s, y)) := by
  obtain ⟨v, hv⟩ := (closedQuotientMap_eq_iff C hηε x y).mp hxy
  have hv' : closedTranslate C η v y = x := Subtype.ext hv
  apply (closedQuotientMap_eq_iff C hηε _ _).mpr
  refine ⟨v, ?_⟩
  have he := hH s v y
  rw [hv'] at he
  exact (congrArg Subtype.val he).symm

theorem CuspRetraction.closedHomotopyDescent_closedQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (s : unitInterval) (x : ClosedTube η) :
    closedHomotopyDescent C hηε H s (closedQuotientMap C hηε x) =
      closedQuotientMap C hηε (H (s, x)) :=
  closedHomotopyDescent_compatible C hηε H hH s _ _
    (descentRepresentative_spec_mo1973_10850 C hηε (closedQuotientMap C hηε x))

theorem CuspRetraction.closedHomotopyDescent_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Continuous
      (fun p : unitInterval × ClosedQuotient C ε η => closedHomotopyDescent C hηε H p.1 p.2) := by
  have hq := closedQuotientMap_isOpenQuotientMap C hηε hC
  have hprod :
    IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) (closedQuotientMap C hηε)) :=
    IsOpenQuotientMap.id.prodMap hq
  apply hprod.continuous_comp_iff.mp
  change
    Continuous
      (fun p : unitInterval × ClosedTube η =>
        closedHomotopyDescent C hηε H p.1 (closedQuotientMap C hηε p.2))
  simpa only [closedHomotopyDescent_closedQuotientMap C hηε H hH, Prod.mk.eta,
    Function.comp_def] using hq.continuous.comp H.continuous

theorem CuspRetraction.closedHomotopyDescent_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hzero : ∀ x : ClosedTube η, H (0, x) = x) (q : ClosedQuotient C ε η) :
    closedHomotopyDescent C hηε H 0 q = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, hzero]

theorem CuspRetraction.closedHomotopyDescent_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hfix :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (s : unitInterval) (q : ClosedQuotient C ε η) (hq : CuspQuotient.projection C ε q = 0) :
    closedHomotopyDescent C hηε H s q = q := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, hfix s x hq]

theorem CuspRetraction.closedHomotopyDescent_one_central (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0)
    (q : ClosedQuotient C ε η) :
    CuspQuotient.projection C ε (closedHomotopyDescent C hηε H 1 q) = 0 := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, closedQuotientMap_projection, hone]

theorem CuspRetraction.closedHomotopyDescent_norm_nonincrease (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hmono :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (x : ToricSpace.Space)‖)
    (s : unitInterval) (q : ClosedQuotient C ε η) :
    ‖CuspQuotient.projection C ε (closedHomotopyDescent C hηε H s q)‖ ≤
      ‖CuspQuotient.projection C ε q‖ := by
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηε q
  rw [closedHomotopyDescent_closedQuotientMap C hηε H hH, closedQuotientMap_projection,
    closedQuotientMap_projection]
  exact hmono s x

abbrev CuspRetraction.QuotientCentralFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  { q : CuspQuotient.QuotientSpace C ε // CuspQuotient.projection C ε q = 0 }

def CuspRetraction.quotientCentralIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ)
    (hη : 0 ≤ η) : C(QuotientCentralFibre C ε, ClosedQuotient C ε η)
    where
  toFun q := ⟨q, by rw [q.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

noncomputable def CuspRetraction.closedHomotopyDescentRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) :
    C(ClosedQuotient C ε η, QuotientCentralFibre C ε)
    where
  toFun
    q := ⟨closedHomotopyDescent C hηε H 1 q, closedHomotopyDescent_one_central C hηε H hH hone q⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((closedHomotopyDescent_continuous C hηε H hH hC).comp
            (continuous_const.prodMk continuous_id))).subtype_mk
      _

theorem CuspRetraction.closedHomotopyDescentRetraction_comp_inclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hfix :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) (hη : 0 ≤ η) :
    (closedHomotopyDescentRetraction C hηε H hH hC hone).comp
        (quotientCentralIntoClosed C ε η hη) =
      ContinuousMap.id (QuotientCentralFibre C ε) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change
    (closedHomotopyDescent C hηε H 1 (quotientCentralIntoClosed C ε η hη q) :
        CuspQuotient.QuotientSpace C ε) =
      (q : CuspQuotient.QuotientSpace C ε)
  exact
    congrArg Subtype.val
      (closedHomotopyDescent_fixed C hηε H hH hfix 1 (quotientCentralIntoClosed C ε η hη q) q.2)

noncomputable def CuspRetraction.closedHomotopyDescentHomotopyRel
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
        H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hzero : ∀ x : ClosedTube η, H (0, x) = x)
    (hfix :
      ∀ (s : unitInterval) (x : ClosedTube η),
        ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x)
    (hone : ∀ x : ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) (hη : 0 ≤ η) :
    (ContinuousMap.id (ClosedQuotient C ε η)).HomotopyRel
      ((quotientCentralIntoClosed C ε η hη).comp
        (closedHomotopyDescentRetraction C hηε H hH hC hone))
      {q : ClosedQuotient C ε η | CuspQuotient.projection C ε q = 0}
    where
  toFun p := closedHomotopyDescent C hηε H p.1 p.2
  continuous_toFun := closedHomotopyDescent_continuous C hηε H hH hC
  map_zero_left := closedHomotopyDescent_zero C hηε H hH hzero
  map_one_left _ := rfl
  prop' s q hq := closedHomotopyDescent_fixed C hηε H hH hfix s q hq

theorem CuspPositiveRetraction.exists_closed_tube_deformation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r : ℝ} (hr : 0 < r) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ η : ℝ,
              0 < η →
                η ≤ η₀ →
                  ∃ H :
                    C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η),
                    (∀ x, H (0, x) = x) ∧
                      (∀ s (x : CuspRetraction.ClosedTube η),
                          ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                        (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                          (∀ s v x,
                              H (s, CuspRetraction.closedTranslate C η v x) =
                                CuspRetraction.closedTranslate C η v (H (s, x))) ∧
                            (∀ s (u : Fin 2 → ℂˣ),
                                (∀ i, ‖(u i : ℂ)‖ = 1) →
                                  ∀ x,
                                    H (s, CuspRetraction.closedFibreAction η u x) =
                                      CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                              (∀ s x,
                                ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                  ‖ToricSpace.time (x : ToricSpace.Space)‖) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := CuspRetraction.exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) := fun i j =>
    (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hRP : ToricSpace.SmallDrift (CuspPositive.positiveTwist (C 0)) ε :=
    CuspPositive.smallDrift_positiveTwist (C 0) hRD
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ := exists_frozen_closed_deformation_below (C 0) ε hε hε1 hRP
  refine ⟨η₀, hη₀, hη₀ε.trans hεr, hη₀ε.trans hε1, ?_⟩
  intro η hη hηη₀
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  obtain ⟨H, hzero, hfix, hone, hequiv, _hcompact, hfibre, hmono⟩ := hH η hη hηη₀
  refine
    ⟨straightenedHomotopy C hε hε1 hCε hRC hRD hηε H,
      straightenedHomotopy_zero C hε hε1 hCε hRC hRD hηε H hzero,
      straightenedHomotopy_fixed C hε hε1 hCε hRC hRD hηε H hfix,
      straightenedHomotopy_one_central C hε hε1 hCε hRC hRD hηε H hone,
      straightenedHomotopy_equivariant C hε hε1 hCε hRC hRD hηε H hequiv,
      straightenedHomotopy_fibre_torus_equivariant C hε hε1 hCε hRC hRD hηε H hfibre,
      straightenedHomotopy_norm_time_le C hε hε1 hCε hRC hRD hηε H hmono⟩

theorem CuspPositiveRetraction.exists_closed_quotient_strongDeformationRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∃ R :
                  C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r),
                  R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                      ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                    ∃ H :
                      (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                        ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                        {q : CuspRetraction.ClosedQuotient C r η |
                          CuspQuotient.projection C r q = 0},
                      ∀ s q,
                        ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                          ‖CuspQuotient.projection C r q‖ := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hH⟩ :=
    exists_closed_tube_deformation C hr (fun i j => (hC i j).continuousOn)
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀
  have hηr : η < r := hηη₀.trans_lt hη₀r
  obtain ⟨H, hzero, hfix, hone, hequiv, _hfibre, hmono⟩ := hH η hη hηη₀
  refine
    ⟨CuspRetraction.closedHomotopyDescentRetraction C hηr H hequiv hC hone,
      CuspRetraction.closedHomotopyDescentRetraction_comp_inclusion C hηr H hequiv hC hfix hone
        hη.le,
      CuspRetraction.closedHomotopyDescentHomotopyRel C hηr H hequiv hC hzero hfix hone hη.le, ?_⟩
  exact CuspRetraction.closedHomotopyDescent_norm_nonincrease C hηr H hequiv hmono

def CuspCentralHomology.centralIntoOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδ : 0 < δ) : C(CuspRetraction.QuotientCentralFibre C r, OpenQuotient C r δ)
    where
  toFun
    q :=
    ⟨q.1, by
      rw [q.2, norm_zero]
      exact hδ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

def CuspCentralHomology.openIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδη : δ ≤ η) : C(OpenQuotient C r δ, CuspRetraction.ClosedQuotient C r η)
    where
  toFun q := ⟨q, q.2.le.trans hδη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def CuspCentralHomology.restrictClosedRetraction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r)) :
    C(OpenQuotient C r δ, CuspRetraction.QuotientCentralFibre C r) :=
  R.comp (openIntoClosed C r δ η hδη)

theorem CuspCentralHomology.restrictClosedRetraction_comp_inclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ) (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hR :
      R.comp (CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r)) :
    (restrictClosedRetraction C r δ η hδη R).comp (centralIntoOpen C r δ hδ) =
      ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) := by
  apply ContinuousMap.ext
  intro q
  exact ContinuousMap.congr_fun hR q

def CuspCentralHomology.restrictClosedHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
        ((CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
        {q : CuspRetraction.ClosedQuotient C r η | CuspQuotient.projection C r q = 0})
    (hmono : ∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤ ‖CuspQuotient.projection C r q‖) :
    (ContinuousMap.id (OpenQuotient C r δ)).HomotopyRel
      ((centralIntoOpen C r δ hδ).comp (restrictClosedRetraction C r δ η hδη R))
      {q : OpenQuotient C r δ | CuspQuotient.projection C r q = 0}
    where
  toFun
    p :=
    ⟨H (p.1, openIntoClosed C r δ η hδη p.2),
      (hmono p.1 (openIntoClosed C r δ η hδη p.2)).trans_lt p.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_subtype_val.comp
        (H.continuous.comp
          (continuous_fst.prodMk ((openIntoClosed C r δ η hδη).continuous.comp continuous_snd)))
  map_zero_left
    q := by
    apply Subtype.ext
    exact
      congrArg
        (fun x : CuspRetraction.ClosedQuotient C r η => (x : CuspQuotient.QuotientSpace C r))
        (H.map_zero_left (openIntoClosed C r δ η hδη q))
  map_one_left
    q := by
    apply Subtype.ext
    exact
      congrArg
        (fun x : CuspRetraction.ClosedQuotient C r η => (x : CuspQuotient.QuotientSpace C r))
        (H.map_one_left (openIntoClosed C r δ η hδη q))
  prop' s q
    hq := by
    apply Subtype.ext
    exact
      congrArg
        (fun x : CuspRetraction.ClosedQuotient C r η => (x : CuspQuotient.QuotientSpace C r))
        (H.eq_fst s (show CuspQuotient.projection C r (openIntoClosed C r δ η hδη q) = 0 from hq))

def CuspCentralHomology.openCentralHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ η : ℝ)
    (hδ : 0 < δ) (hδη : δ ≤ η)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hR :
      R.comp (CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)) =
        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
        ((CuspRetraction.quotientCentralIntoClosed C r η (hδ.le.trans hδη)).comp R)
        {q : CuspRetraction.ClosedQuotient C r η | CuspQuotient.projection C r q = 0})
    (hmono : ∀ s q, ‖CuspQuotient.projection C r (H (s, q))‖ ≤ ‖CuspQuotient.projection C r q‖) :
    CuspRetraction.QuotientCentralFibre C r ≃ₕ OpenQuotient C r δ
    where
  toFun := centralIntoOpen C r δ hδ
  invFun := restrictClosedRetraction C r δ η hδη R
  left_inv := by rw [restrictClosedRetraction_comp_inclusion C r δ η hδ hδη R hR]
  right_inv := ⟨(restrictClosedHomotopy C r δ η hδ hδη R H hmono).toHomotopy.symm⟩

def CuspCentralHomology.centralIntoSmallerQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδ : 0 < δ) (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    C(CuspRetraction.QuotientCentralFibre C r, CuspQuotient.QuotientSpace C δ) :=
  ((openQuotientRadiusHomeomorph C hδr hC).symm :
        C(OpenQuotient C r δ, CuspQuotient.QuotientSpace C δ)).comp
    (centralIntoOpen C r δ hδ)

theorem CuspCentralHomology.exists_centralHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ δ₀ : ℝ,
      0 < δ₀ ∧
        δ₀ < r ∧
          δ₀ < 1 ∧
            ∀ (δ : ℝ) (hδ : 0 < δ),
              δ ≤ δ₀ →
                ∀ hδr : δ ≤ r,
                  ∃ e : CuspRetraction.QuotientCentralFibre C r ≃ₕ CuspQuotient.QuotientSpace C δ,
                    e.toFun = centralIntoSmallerQuotient C r δ hδ hδr hC := by
  obtain ⟨δ₀, hδ₀, hδ₀r, hδ₀1, hex⟩ :=
    CuspPositiveRetraction.exists_closed_quotient_strongDeformationRetraction C hr hC
  refine ⟨δ₀, hδ₀, hδ₀r, hδ₀1, ?_⟩
  intro δ hδ hδδ₀ hδr
  obtain ⟨R, hR, H, hmono⟩ := hex δ₀ hδ₀ le_rfl
  let e := openCentralHomotopyEquiv C r δ δ₀ hδ hδδ₀ R hR H hmono
  refine ⟨e.trans (openQuotientRadiusHomeomorph C hδr hC).symm.toHomotopyEquiv, rfl⟩

def ThreefoldHomologyFinitenessCusp.positivePuncturedHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D) ≃ₜ
      CuspUniformization.PuncturedQuotient D.correction D.radius
    where
  toFun
    x :=
    ⟨x.val,
      norm_pos_iff.mp
        (show 0 < ‖CuspQuotient.projection D.correction D.radius x.val‖ from x.property)⟩
  invFun x := ⟨x.val, norm_pos_iff.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def ThreefoldHomologyFinitenessCusp.positiveHeightCutoff (D : SpecialPeriods.CuspFamily.Data)
    (H : ℝ) :
    C(unitInterval × ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D),
      ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D))
    where
  toFun
    p :=
    (positivePuncturedHomeomorph D).symm
      (puncturedHeightCutoff D H (p.1, positivePuncturedHomeomorph D p.2))
  continuous_toFun :=
    (positivePuncturedHomeomorph D).symm.continuous.comp
      ((puncturedHeightCutoff D H).continuous.comp
        (continuous_fst.prodMk ((positivePuncturedHomeomorph D).continuous.comp continuous_snd)))

@[simp]
theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_zero
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D)) :
    positiveHeightCutoff D H (0, x) = x := by
  change
    (positivePuncturedHomeomorph D).symm
        (puncturedHeightCutoff D H (0, positivePuncturedHomeomorph D x)) =
      x
  rw [puncturedHeightCutoff_zero, Homeomorph.symm_apply_apply]

theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_norm_nonincrease
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D)) :
    parameterNorm D (positiveHeightCutoff D H (t, x)).val ≤ parameterNorm D x.val :=
  puncturedHeightCutoff_norm_nonincrease D H t (positivePuncturedHomeomorph D x)

theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_one_norm_le
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D)) :
    parameterNorm D (positiveHeightCutoff D H (1, x)).val ≤ cutoffRadius H :=
  puncturedHeightCutoff_one_norm_le D H (positivePuncturedHomeomorph D x)

theorem ThreefoldHomologyFinitenessCusp.positiveHeightCutoff_fixed
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : ThreefoldHomologyFinitenessRetraction.Positive (parameterNorm D))
    (hx : parameterNorm D x.val < cutoffRadius H) : positiveHeightCutoff D H (t, x) = x := by
  change
    (positivePuncturedHomeomorph D).symm
        (puncturedHeightCutoff D H (t, positivePuncturedHomeomorph D x)) =
      x
  rw [puncturedHeightCutoff_fixed D H t _ hx, Homeomorph.symm_apply_apply]

def ThreefoldHomologyFinitenessCusp.fullSublevelHomotopyEquiv (D : SpecialPeriods.CuspFamily.Data)
    (δ : ℝ) (hδ : 0 < δ) :
    FullSpace D ≃ₕ CuspCentralHomology.OpenQuotient D.correction D.radius δ :=
  ThreefoldHomologyFinitenessRetraction.sublevelHomotopyEquiv (parameterNorm D)
    (positiveHeightCutoff D (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1))
    (cutoffRadius (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1)) (cutoffRadius_pos _)
    (positiveHeightCutoff_fixed D _) (positiveHeightCutoff_zero D _)
    (positiveHeightCutoff_norm_nonincrease D _) δ (cutoffRadius_threshold_lt hδ).le
    (fun x => (positiveHeightCutoff_one_norm_le D _ x).trans_lt (cutoffRadius_threshold_lt hδ))

def ThreefoldHomologyFinitenessCusp.fullCentralInclusion (D : SpecialPeriods.CuspFamily.Data) :
    C(CuspRetraction.QuotientCentralFibre D.correction D.radius, FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem ThreefoldHomologyFinitenessCusp.exists_fullCentralHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) :
    ∃ e : CuspRetraction.QuotientCentralFibre D.correction D.radius ≃ₕ FullSpace D,
      e.toFun = fullCentralInclusion D := by
  obtain ⟨δ, hδ, hδr, _hδ1, he⟩ :=
    CuspCentralHomology.exists_centralHomotopyEquiv D.correction D.radius D.radius_pos
      D.holomorphic
  obtain ⟨e, he⟩ := he δ hδ le_rfl hδr.le
  let eR := CuspCentralHomology.openQuotientRadiusHomeomorph D.correction hδr.le D.holomorphic
  let eF := fullSublevelHomotopyEquiv D δ hδ
  refine ⟨(e.trans eR.toHomotopyEquiv).trans eF.symm, ?_⟩
  apply ContinuousMap.ext
  intro x
  change (eR (e x)).val = x.val
  have hx := ContinuousMap.congr_fun he x
  change e x = eR.symm (CuspCentralHomology.centralIntoOpen D.correction D.radius δ hδ x) at hx
  rw [hx, Homeomorph.apply_symm_apply]
  rfl

def ThreefoldHomologyFinitenessCusp.fullCentralHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) :
    CuspRetraction.QuotientCentralFibre D.correction D.radius ≃ₕ FullSpace D :=
  Classical.choose (exists_fullCentralHomotopyEquiv D)

@[simp]
theorem ThreefoldHomologyFinitenessCusp.fullCentralHomotopyEquiv_toFun
    (D : SpecialPeriods.CuspFamily.Data) :
    (fullCentralHomotopyEquiv D).toFun = fullCentralInclusion D :=
  Classical.choose_spec (exists_fullCentralHomotopyEquiv D)

abbrev CuspHoneycombTiling.Plane :=
  Fin 2 → ℝ

abbrev CuspHoneycombTiling.Lattice :=
  Fin 2 → ℤ

def CuspHoneycombTiling.latticePoint (v : CuspHoneycombTiling.Lattice) : Plane := fun i =>
  (v i : ℝ)

@[simp]
theorem CuspHoneycombTiling.latticePoint_apply (v : CuspHoneycombTiling.Lattice) (i : Fin 2) :
    latticePoint v i = (v i : ℝ) :=
  rfl

@[simp]
theorem CuspHoneycombTiling.latticePoint_zero : latticePoint 0 = 0 := by
  funext i
  simp [latticePoint]

@[simp]
theorem CuspHoneycombTiling.latticePoint_add (v w : CuspHoneycombTiling.Lattice) :
    latticePoint (v + w) = latticePoint v + latticePoint w := by
  funext i
  simp [latticePoint]

@[simp]
theorem CuspHoneycombTiling.latticePoint_neg (v : CuspHoneycombTiling.Lattice) :
    latticePoint (-v) = -latticePoint v := by
  funext i
  simp [latticePoint]

def CuspHoneycombTiling.baseCell : Set Plane :=
  {x | |2 * x 0 + x 1| ≤ 1 ∧ |x 0 - x 1| ≤ 1 ∧ |x 0 + 2 * x 1| ≤ 1}

def CuspHoneycombTiling.cell (v : CuspHoneycombTiling.Lattice) : Set Plane :=
  {x | x - latticePoint v ∈ baseCell}

@[simp]
theorem CuspHoneycombTiling.mem_baseCell (x : Plane) :
    x ∈ baseCell ↔ |2 * x 0 + x 1| ≤ 1 ∧ |x 0 - x 1| ≤ 1 ∧ |x 0 + 2 * x 1| ≤ 1 :=
  Iff.rfl

@[simp]
theorem CuspHoneycombTiling.mem_cell (v : CuspHoneycombTiling.Lattice) (x : Plane) :
    x ∈ cell v ↔ x - latticePoint v ∈ baseCell :=
  Iff.rfl

@[simp]
theorem CuspHoneycombTiling.cell_zero : cell 0 = baseCell := by
  ext x
  simp only [mem_cell, latticePoint_zero, sub_zero]

theorem CuspHoneycombTiling.baseCell_coordinate_bound_sharp {x : Plane} (hx : x ∈ baseCell)
    (i : Fin 2) : |x i| ≤ (2 / 3 : ℝ) := by
  obtain ⟨h0, h1, h2⟩ := hx
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  fin_cases i
  · change |x 0| ≤ (2 / 3 : ℝ)
    exact abs_le.mpr ⟨by linarith [h0'.1, h1'.1], by linarith [h0'.2, h1'.2]⟩
  · change |x 1| ≤ (2 / 3 : ℝ)
    exact abs_le.mpr ⟨by linarith [h2'.1, h1'.2], by linarith [h2'.2, h1'.1]⟩

theorem CuspHoneycombTiling.baseCell_coordinate_bound {x : Plane} (hx : x ∈ baseCell)
    (i : Fin 2) : |x i| ≤ 1 :=
  (baseCell_coordinate_bound_sharp hx i).trans (by norm_num)

theorem CuspHoneycombTiling.cell_coordinate_bound {v : CuspHoneycombTiling.Lattice} {x : Plane}
    (hx : x ∈ cell v) (i : Fin 2) : |x i - (v i : ℝ)| ≤ 1 :=
  baseCell_coordinate_bound hx i

theorem CuspHoneycombTiling.add_latticePoint_mem_cell_iff (v w : CuspHoneycombTiling.Lattice)
    (x : Plane) : x + latticePoint w ∈ cell (v + w) ↔ x ∈ cell v := by
  simp only [mem_cell, latticePoint_add, add_sub_add_right_eq_sub]

def CuspHoneycombTiling.squareCenter (p q : ℝ) : CuspHoneycombTiling.Lattice :=
  if q ≤ p then if 2 * p + q ≤ 1 then 0 else if 2 ≤ p + 2 * q then 1 else ![1, 0]
  else if p + 2 * q ≤ 1 then 0 else if 2 ≤ 2 * p + q then 1 else ![0, 1]

theorem CuspHoneycombTiling.mem_cell_squareCenter (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : (![p, q] : Plane) ∈ cell (squareCenter p q) := by
  unfold squareCenter
  split_ifs
  all_goals
    simp only [mem_cell, mem_baseCell, Pi.sub_apply, latticePoint_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply, Pi.one_apply, Int.cast_zero,
      Int.cast_one, sub_zero, abs_le]
  all_goals repeat' apply And.intro
  all_goals linarith

def CuspHoneycombTiling.floorCenter (x : Plane) : CuspHoneycombTiling.Lattice := fun i =>
  ⌊x i⌋ + squareCenter (Int.fract (x 0)) (Int.fract (x 1)) i

theorem CuspHoneycombTiling.sub_latticePoint_floorCenter (x : Plane) :
    x - latticePoint (floorCenter x) =
      (![Int.fract (x 0), Int.fract (x 1)] : Plane) -
        latticePoint (squareCenter (Int.fract (x 0)) (Int.fract (x 1))) := by
  funext i
  simp only [Pi.sub_apply, latticePoint, floorCenter, Int.cast_add, sub_add_eq_sub_sub]
  rw [Int.self_sub_floor]
  fin_cases i <;> rfl

theorem CuspHoneycombTiling.mem_cell_floorCenter (x : Plane) : x ∈ cell (floorCenter x) := by
  change x - latticePoint (floorCenter x) ∈ baseCell
  rw [sub_latticePoint_floorCenter]
  exact
    mem_cell_squareCenter _ _ (Int.fract_nonneg _) (Int.fract_lt_one _).le (Int.fract_nonneg _)
      (Int.fract_lt_one _).le

theorem CuspHoneycombTiling.exists_mem_cell (x : Plane) :
    ∃ v : CuspHoneycombTiling.Lattice, x ∈ cell v :=
  ⟨floorCenter x, mem_cell_floorCenter x⟩

theorem CuspHoneycombTiling.iUnion_cell :
    (⋃ v : CuspHoneycombTiling.Lattice, cell v) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_cell x

theorem CuspHoneycombTiling.baseCell_isClosed : IsClosed baseCell := by
  have h0 : IsClosed {x : Plane | |2 * x 0 + x 1| ≤ 1} :=
    isClosed_le ((continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)).abs
      continuous_const
  have h1 : IsClosed {x : Plane | |x 0 - x 1| ≤ 1} :=
    isClosed_le ((continuous_apply 0).sub (continuous_apply 1)).abs continuous_const
  have h2 : IsClosed {x : Plane | |x 0 + 2 * x 1| ≤ 1} :=
    isClosed_le ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).abs
      continuous_const
  exact h0.inter (h1.inter h2)

theorem CuspHoneycombTiling.baseCell_isCompact : IsCompact baseCell := by
  apply
    (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (-1 : Plane) 1)).of_isClosed_subset
      baseCell_isClosed
  intro x hx
  exact
    ⟨fun i => (abs_le.mp (baseCell_coordinate_bound hx i)).1, fun i =>
      (abs_le.mp (baseCell_coordinate_bound hx i)).2⟩

theorem CuspHoneycombTiling.cell_isClosed (v : CuspHoneycombTiling.Lattice) : IsClosed (cell v) :=
  baseCell_isClosed.preimage (continuous_id.sub continuous_const)

theorem CuspHoneycombTiling.cell_finite_inter_ball (x : Plane) :
    {v : CuspHoneycombTiling.Lattice | (cell v ∩ Metric.ball x 1).Nonempty}.Finite := by
  have hbox : {v : CuspHoneycombTiling.Lattice | ∀ i, v i ∈ Set.Icc ⌈x i - 2⌉ ⌊x i + 2⌋}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc ⌈x i - 2⌉ ⌊x i + 2⌋)
  apply hbox.subset
  rintro v ⟨y, hyv, hyx⟩ i
  have hcoord := abs_le.mp (cell_coordinate_bound hyv i)
  have hdist : |y i - x i| < 1 := by
    simpa only [Real.dist_eq] using (dist_le_pi_dist y x i).trans_lt (Metric.mem_ball.mp hyx)
  have hnear := abs_lt.mp hdist
  constructor
  · apply Int.ceil_le.mpr
    linarith [hcoord.2, hnear.1]
  · apply Int.le_floor.mpr
    linarith [hcoord.1, hnear.2]

theorem CuspHoneycombTiling.cell_locallyFinite : LocallyFinite cell := by
  intro x
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), cell_finite_inter_ball x⟩

theorem CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff (v : CuspHoneycombTiling.Lattice) :
    (baseCell ∩ cell v).Nonempty ↔
      v = 0 ∨
        v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, -1] ∨ v = ![-1, 0] ∨ v = ![0, -1] ∨ v = ![-1, 1] := by
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hcoord (i : Fin 2) : -1 ≤ v i ∧ v i ≤ 1 := by
      have hbase := abs_le.mp (baseCell_coordinate_bound_sharp hx i)
      have hshift := abs_le.mp (baseCell_coordinate_bound_sharp hxv i)
      change -(2 / 3 : ℝ) ≤ x i - (v i : ℝ) ∧ x i - (v i : ℝ) ≤ 2 / 3 at hshift
      have hlo : (-2 : ℝ) < (v i : ℝ) := by linarith [hbase.1, hshift.2]
      have hhi : (v i : ℝ) < (2 : ℝ) := by linarith [hbase.2, hshift.1]
      have hlo' : (-2 : ℤ) < v i := by exact_mod_cast hlo
      have hhi' : v i < (2 : ℤ) := by exact_mod_cast hhi
      omega
    have hbase := abs_le.mp hx.1
    have hshift := abs_le.mp hxv.1
    change
      (-1 : ℝ) ≤ 2 * (x 0 - (v 0 : ℝ)) + (x 1 - (v 1 : ℝ)) ∧
        2 * (x 0 - (v 0 : ℝ)) + (x 1 - (v 1 : ℝ)) ≤ 1 at hshift
    have hlinear : (-2 : ℝ) ≤ 2 * (v 0 : ℝ) + (v 1 : ℝ) ∧ 2 * (v 0 : ℝ) + (v 1 : ℝ) ≤ 2 := by
      constructor <;> linarith [hbase.1, hbase.2, hshift.1, hshift.2]
    have hlinear' : (-2 : ℤ) ≤ 2 * v 0 + v 1 ∧ 2 * v 0 + v 1 ≤ 2 := by exact_mod_cast hlinear
    have h0 := hcoord 0
    have h1 := hcoord 1
    simp only [funext_iff, Fin.forall_fin_two, Pi.zero_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    omega
  · intro hv
    refine ⟨fun i => (v i : ℝ) / 2, ?_, ?_⟩
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [baseCell]
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [cell, baseCell, latticePoint]

theorem CuspHoneycombTiling.cell_inter_cell_nonempty_iff_baseCell
    (v w : CuspHoneycombTiling.Lattice) :
    (cell v ∩ cell w).Nonempty ↔ (baseCell ∩ cell (w - v)).Nonempty := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    refine ⟨x - latticePoint v, hxv, ?_⟩
    apply (add_latticePoint_mem_cell_iff (w - v) v (x - latticePoint v)).mp
    simpa only [sub_add_cancel] using hxw
  · rintro ⟨x, hx, hxwv⟩
    refine ⟨x + latticePoint v, ?_, ?_⟩
    · have h := (add_latticePoint_mem_cell_iff 0 v x).mpr (by simpa only [cell_zero] using hx)
      simpa only [zero_add] using h
    · simpa only [sub_add_cancel] using (add_latticePoint_mem_cell_iff (w - v) v x).mpr hxwv

abbrev CuspHoneycombHexagon.Plane :=
  Fin 2 → ℝ

abbrev CuspHoneycombHexagon.Square :=
  { p : Plane // ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 }

theorem CuspHoneycombHexagon.square_isCompact :
    IsCompact {p : Plane | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1} :=
  isCompact_pi_infinite (fun _ => CompactIccSpace.isCompact_Icc)

instance CuspHoneycombHexagon.square_compactSpace : CompactSpace Square :=
  isCompact_iff_compactSpace.mp square_isCompact

def CuspHoneycombHexagon.SquareRel (i j : Fin 6) (p q : Square) : Prop :=
  (i = j ∧ p = q) ∨
    (j = i + 1 ∧ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1) ∨
      (i = j + 1 ∧ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = p.1 0) ∨ ((∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1))

theorem CuspHoneycombHexagon.square_eq_of_all_one (p q : Square) (hp : ∀ k, p.1 k = 1)
    (hq : ∀ k, q.1 k = 1) : p = q := by
  apply Subtype.ext
  funext k
  exact (hp k).trans (hq k).symm

@[simp]
theorem CuspHoneycombHexagon.squareRel_self (i : Fin 6) (p q : Square) :
    SquareRel i i p q ↔ p = q := by
  have hne : i ≠ i + 1 := (show ∀ i : Fin 6, i ≠ i + 1 by decide) i
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨hp, hq⟩)
    · exact h
    · exact (hne h).elim
    · exact (hne h).elim
    · exact square_eq_of_all_one p q hp hq
  · exact fun h => Or.inl ⟨rfl, h⟩

@[simp]
theorem CuspHoneycombHexagon.squareRel_next (i : Fin 6) (p q : Square) :
    SquareRel i (i + 1) p q ↔ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1 := by
  have hne : i ≠ i + 1 := (show ∀ i : Fin 6, i ≠ i + 1 by decide) i
  have hne₂ : i ≠ (i + 1) + 1 := (show ∀ i : Fin 6, i ≠ (i + 1) + 1 by decide) i
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨hp, hq⟩)
    · exact (hne h).elim
    · exact h
    · exact (hne₂ h).elim
    · exact ⟨hp 0, hq 1, (hq 0).trans (hp 1).symm⟩
  · exact fun h => Or.inr (Or.inl ⟨rfl, h⟩)

@[simp]
theorem CuspHoneycombHexagon.squareRel_prev (i : Fin 6) (p q : Square) :
    SquareRel i (i + 5) p q ↔ p.1 1 = 1 ∧ q.1 0 = 1 ∧ q.1 1 = p.1 0 := by
  have hne : i ≠ i + 5 := (show ∀ i : Fin 6, i ≠ i + 5 by decide) i
  have hnext : i + 5 ≠ i + 1 := (show ∀ i : Fin 6, i + 5 ≠ i + 1 by decide) i
  have hprev : i = (i + 5) + 1 := (show ∀ i : Fin 6, i = (i + 5) + 1 by decide) i
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨hp, hq⟩)
    · exact (hne h).elim
    · exact (hnext h).elim
    · exact h
    · exact ⟨hp 1, hq 0, (hq 1).trans (hp 0).symm⟩
  · exact fun h => Or.inr (Or.inr (Or.inl ⟨hprev, h⟩))

theorem CuspHoneycombHexagon.squareRel_nonadjacent (i j : Fin 6) (p q : Square) (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    SquareRel i j p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) := by
  simp only [SquareRel, hij, hnext, hprev, false_and, false_or]

@[simp]
theorem CuspHoneycombHexagon.squareRel_add_two (i : Fin 6) (p q : Square) :
    SquareRel i (i + 2) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 2) p q ((show ∀ i : Fin 6, i ≠ i + 2 by decide) i)
    ((show ∀ i : Fin 6, i + 2 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 2) + 1 by decide) i)

@[simp]
theorem CuspHoneycombHexagon.squareRel_add_three (i : Fin 6) (p q : Square) :
    SquareRel i (i + 3) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 3) p q ((show ∀ i : Fin 6, i ≠ i + 3 by decide) i)
    ((show ∀ i : Fin 6, i + 3 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 3) + 1 by decide) i)

@[simp]
theorem CuspHoneycombHexagon.squareRel_add_four (i : Fin 6) (p q : Square) :
    SquareRel i (i + 4) p q ↔ (∀ k, p.1 k = 1) ∧ (∀ k, q.1 k = 1) :=
  squareRel_nonadjacent i (i + 4) p q ((show ∀ i : Fin 6, i ≠ i + 4 by decide) i)
    ((show ∀ i : Fin 6, i + 4 ≠ i + 1 by decide) i)
    ((show ∀ i : Fin 6, i ≠ (i + 4) + 1 by decide) i)

def ToricCharts.zeroCount (z : CoordinateSpace 3) : ℕ :=
  Nat.card { j : Fin 3 // z j = 0 }

def ToricCharts.vanishingIndices (z : CoordinateSpace 3) : Finset (Fin 3) := by
  classical exact Finset.univ.filter (fun j => z j = 0)

@[simp]
theorem ToricCharts.mem_vanishingIndices (z : CoordinateSpace 3) (j : Fin 3) :
    j ∈ vanishingIndices z ↔ z j = 0 := by classical simp [vanishingIndices]

theorem ToricCharts.vanishingIndices_card (z : CoordinateSpace 3) :
    (vanishingIndices z).card = zeroCount z := by
  classical
  rw [zeroCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem ToricCharts.vanishingIndices_nonempty (z : CoordinateSpace 3) :
    (vanishingIndices z).Nonempty ↔ ToricFan.Triangle.time z = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    have hp : ∏ k, z k = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) ((mem_vanishingIndices z j).mp hj)
    simpa [ToricFan.Triangle.time, Fin.prod_univ_succ, mul_assoc] using hp
  · intro hz
    obtain h | h | h := (ToricFan.Triangle.central_fibre z).mp hz
    · exact ⟨0, (mem_vanishingIndices z 0).mpr h⟩
    · exact ⟨1, (mem_vanishingIndices z 1).mpr h⟩
    · exact ⟨2, (mem_vanishingIndices z 2).mpr h⟩

theorem ToricCharts.zeroCount_pos_iff (z : CoordinateSpace 3) :
    0 < zeroCount z ↔ ToricFan.Triangle.time z = 0 := by
  rw [← vanishingIndices_card, Finset.card_pos, vanishingIndices_nonempty]

@[simp]
theorem ToricCharts.zeroCount_zero : zeroCount (0 : CoordinateSpace 3) = 3 := by
  classical simp [zeroCount, Nat.card_eq_fintype_card]

theorem ToricCharts.equal_columns_of_left_inverse {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hBA : B * A = 1) {j k : Fin 3} (hcol : ∀ i, A i j = A i k) : j = k := by
  have he : (B * A) j j = (B * A) j k := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun c => B j i * c) (hcol i))
  rw [hBA] at he
  by_contra hne
  simp [hne] at he

theorem ToricCharts.zeroCount_le_monomial {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hBA : B * A = 1) {z : CoordinateSpace 3} (hz : z ∈ domain A) :
    zeroCount z ≤ zeroCount (monomial A z) := by
  have hcol (j : { j : Fin 3 // z j = 0 }) : ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 :=
    column_single_of_zero hA hz j.2
  choose f hf using hcol
  let g : { j : Fin 3 // z j = 0 } → { k : Fin 3 // monomial A z k = 0 } := fun j =>
    ⟨f j, monomial_zero_of_column_single j.2 (hf j)⟩
  apply Nat.card_le_card_of_injective g
  intro j k h
  have hfk : f j = f k := congrArg Subtype.val h
  apply Subtype.ext
  apply equal_columns_of_left_inverse hBA
  intro i
  rw [hf j i, hf k i, hfk]

theorem ToricCharts.zeroCount_monomial {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hB : HeightOne B) (hAB : A * B = 1) (hBA : B * A = 1) {z : CoordinateSpace 3}
    (hz : z ∈ domain A) : zeroCount (monomial A z) = zeroCount z := by
  have hw := inverse_mapsTo_domain hA hBA hz
  have he : monomial B (monomial A z) = z := monomial_inverse_on_overlap A B hBA ⟨hz, hw⟩
  have hle := zeroCount_le_monomial hB hAB hw
  rw [he] at hle
  exact le_antisymm hle (zeroCount_le_monomial hA hBA hz)

theorem ToricCharts.zeroCount_mul (u z : CoordinateSpace 3) (hu : ∀ j, u j ≠ 0) :
    zeroCount (u * z) = zeroCount z := by
  apply Nat.card_congr
  exact
    Equiv.subtypeEquivRight (fun j => by simp only [Pi.mul_apply, mul_eq_zero, hu j, false_or])

theorem ToricFan.Triangle.zeroCount_chartChange (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange s t).source) :
    ToricCharts.zeroCount (chartChange s t z) = ToricCharts.zeroCount z := by
  apply
    ToricCharts.zeroCount_monomial (transition_heightOne s t) (transition_heightOne t s)
      (by rw [transition_mul, transition_self]) (by rw [transition_mul, transition_self])
  simpa only [chartChange_source] using hz

theorem ToricFan.Triangle.origin_mem_chartChange_source (s t : ToricFan.Triangle) :
    (0 : ToricCharts.CoordinateSpace 3) ∈ (chartChange s t).source ↔ s = t := by
  constructor
  · intro hz
    rw [chartChange_source] at hz
    have hn (i j : Fin 3) : 0 ≤ transition s t i j := by
      by_contra h
      exact hz i j (lt_of_not_ge h) rfl
    have h00 := hn 0 0
    have h01 := hn 0 1
    have h02 := hn 0 2
    have h10 := hn 1 0
    have h11 := hn 1 1
    have h12 := hn 1 2
    have h20 := hn 2 0
    have h21 := hn 2 1
    have h22 := hn 2 2
    cases hs : s.upper <;> cases ht : t.upper
    all_goals
      simp [transition, dual, rays, hs, ht, Matrix.mul_apply,
        Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    all_goals
      first
      | omega
      | apply ToricFan.Triangle.ext
        · omega
        · omega
        · simp [hs, ht]
  · rintro rfl
    rw [chartChange_self_source]
    exact Set.mem_univ _

def ToricSpace.branchCount (x : Space) : ℕ :=
  ToricCharts.zeroCount ((parametrization (preferredTriangle x)).symm x)

theorem ToricSpace.branchCount_inclusion (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    branchCount (ToricSpace.inclusion s z) = ToricCharts.zeroCount z := by
  have he :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  unfold branchCount
  rw [he.2]
  exact ToricFan.Triangle.zeroCount_chartChange s _ he.1

theorem ToricSpace.branchCount_pos_iff (x : Space) : 0 < branchCount x ↔ time x = 0 := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [branchCount_inclusion, ToricCharts.zeroCount_pos_iff, time_inclusion]

theorem ToricSpace.inclusion_origin_injective (s t : ToricFan.Triangle) :
    ToricSpace.inclusion s 0 = ToricSpace.inclusion t 0 ↔ s = t := by
  constructor
  · intro he
    exact
      (ToricFan.Triangle.origin_mem_chartChange_source s t).mp
        ((inclusion_eq_iff s t 0 0).mp he).1
  · rintro rfl
    rfl

theorem ToricSpace.twistedTranslate_origin (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (s : ToricFan.Triangle) :
    twistedTranslate C v (ToricSpace.inclusion s 0) =
      ToricSpace.inclusion (s.shift (cuspVector v)) 0 := by
  simp [twistedTranslate, translate_inclusion, variableMultiplier, scale]

@[simp]
theorem ToricSpace.branchCount_translate (v : Fin 2 → ℤ) (x : Space) :
    branchCount (ToricSpace.translate v x) = branchCount x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, branchCount_inclusion, branchCount_inclusion]

@[simp]
theorem ToricSpace.branchCount_torusAction (u : ActingTorus) (x : Space) :
    branchCount (torusAction u x) = branchCount x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, branchCount_inclusion, branchCount_inclusion]
  exact ToricCharts.zeroCount_mul (factors s u) z (factors_nonzero s u)

@[simp]
theorem ToricSpace.branchCount_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : Space) : branchCount (twistedTranslate C v x) = branchCount x := by
  simp [twistedTranslate, variableMultiplier]

def ToricFan.Triangle.vertex (s : ToricFan.Triangle) (j : Fin 3) : Fin 2 → ℤ := fun i =>
  s.rays i.castSucc j

theorem ToricFan.Triangle.vertex_eq_iff (s t : ToricFan.Triangle) (j k : Fin 3) :
    s.vertex j = t.vertex k ↔ ∀ i, s.rays i j = t.rays i k := by
  constructor
  · intro h i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · simp
  · intro h
    funext i
    exact h i.castSucc

theorem ToricFan.Triangle.vertex_injective (s : ToricFan.Triangle) :
    Function.Injective s.vertex := by
  intro j k h
  exact ToricCharts.equal_columns_of_left_inverse s.dual_rays ((vertex_eq_iff s s j k).mp h)

theorem ToricFan.Triangle.transition_column_iff_vertex (s t : ToricFan.Triangle) (j k : Fin 3) :
    (∀ i, transition s t i j = if i = k then 1 else 0) ↔ s.vertex j = t.vertex k := by
  rw [vertex_eq_iff]
  constructor
  · intro h i
    have hc := congrFun (congrFun (transition_covariance s t) i) j
    simpa only [Matrix.mul_apply, h, mul_ite, mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using hc.symm
  · intro h i
    have hc := congrFun (congrFun t.dual_rays i) k
    simpa only [transition, Matrix.mul_apply, h, Matrix.one_apply] using hc

@[simp]
theorem ToricFan.Triangle.vertex_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) (j : Fin 3) :
    (s.shift v).vertex j = s.vertex j + v := by
  ext i
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;> simp [vertex, shift, rays, hs] <;> ring

def ToricFan.Triangle.chartBranches (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    Set (Fin 2 → ℤ) :=
  s.vertex '' {j | z j = 0}

theorem ToricFan.Triangle.chartBranches_finite (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : (chartBranches s z).Finite :=
  (Set.toFinite _).image _

theorem ToricFan.Triangle.chartBranches_ncard (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : (chartBranches s z).ncard = ToricCharts.zeroCount z := by
  rw [chartBranches, Set.ncard_image_of_injective _ (vertex_injective s)]
  rfl

theorem ToricFan.Triangle.chartBranches_subset_change (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange s t).source) :
    chartBranches s z ⊆ chartBranches t (chartChange s t z) := by
  rintro v ⟨j, hj, rfl⟩
  obtain ⟨k, hk⟩ :=
    ToricCharts.column_single_of_zero (transition_heightOne s t)
      (by simpa only [chartChange_source] using hz) hj
  refine ⟨k, ToricCharts.monomial_zero_of_column_single hj hk, ?_⟩
  exact ((transition_column_iff_vertex s t j k).mp hk).symm

theorem ToricFan.Triangle.chartBranches_change (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange s t).source) :
    chartBranches t (chartChange s t z) = chartBranches s z := by
  apply subset_antisymm
  · have h := chartBranches_subset_change t s ((chartChange s t).map_source hz)
    have hi : chartChange t s (chartChange s t z) = z := (chartChange s t).left_inv hz
    rwa [hi] at h
  · exact chartBranches_subset_change s t hz

theorem ToricFan.Triangle.chartBranches_mul (s : ToricFan.Triangle)
    (u z : ToricCharts.CoordinateSpace 3) (hu : ∀ j, u j ≠ 0) :
    chartBranches s (u * z) = chartBranches s z := by
  unfold chartBranches
  congr 1
  ext j
  simp [hu]

theorem ToricFan.Triangle.chartBranches_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (z : ToricCharts.CoordinateSpace 3) :
    chartBranches (s.shift v) z = (fun w => w + v) '' chartBranches s z := by
  simp only [chartBranches, Set.image_image, vertex_shift]

def ToricSpace.branchVertices : Space → Set (Fin 2 → ℤ) :=
  descend ToricFan.Triangle.chartBranches

@[simp]
theorem ToricSpace.branchVertices_inclusion (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    branchVertices (ToricSpace.inclusion s z) = ToricFan.Triangle.chartBranches s z :=
  descend_inclusion ToricFan.Triangle.chartBranches
    (fun s t _ hz => ToricFan.Triangle.chartBranches_change s t hz) s z

theorem ToricSpace.branchVertices_finite (x : Space) : (branchVertices x).Finite :=
  ToricFan.Triangle.chartBranches_finite _ _

theorem ToricSpace.branchVertices_ncard (x : Space) : (branchVertices x).ncard = branchCount x :=
  ToricFan.Triangle.chartBranches_ncard _ _

theorem ToricSpace.branchVertices_nonempty (x : Space) :
    (branchVertices x).Nonempty ↔ time x = 0 := by
  rw [← Set.ncard_pos (branchVertices_finite x), branchVertices_ncard, branchCount_pos_iff]

def ToricSpace.rayDivisor (v : Fin 2 → ℤ) : Set Space :=
  {x | v ∈ branchVertices x}

theorem ToricSpace.mem_rayDivisor_inclusion (v : Fin 2 → ℤ) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z ∈ rayDivisor v ↔ ∃ j, z j = 0 ∧ s.vertex j = v := by
  change v ∈ branchVertices (ToricSpace.inclusion s z) ↔ _
  rw [branchVertices_inclusion]
  rfl

theorem ToricSpace.mem_rayDivisor_vertex (s : ToricFan.Triangle) (j : Fin 3)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z ∈ rayDivisor (s.vertex j) ↔ z j = 0 := by
  rw [mem_rayDivisor_inclusion]
  constructor
  · rintro ⟨k, hk, he⟩
    rwa [(ToricFan.Triangle.vertex_injective s) he] at hk
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem ToricSpace.preimage_rayDivisor (v : Fin 2 → ℤ) (s : ToricFan.Triangle) :
    ToricSpace.inclusion s ⁻¹' rayDivisor v = ⋃ j : Fin 3, {z | z j = 0 ∧ s.vertex j = v} := by
  ext z
  simp only [Set.mem_preimage, mem_rayDivisor_inclusion, Set.mem_iUnion, Set.mem_ofPred_eq]

theorem ToricSpace.rayDivisor_isClosed (v : Fin 2 → ℤ) : IsClosed (rayDivisor v) := by
  rw [← isOpen_compl_iff, gluing.isOpen_iff]
  change ∀ s : ToricFan.Triangle, IsOpen (ToricSpace.inclusion s ⁻¹' (rayDivisor v)ᶜ)
  intro s
  rw [Set.preimage_compl, isOpen_compl_iff, preimage_rayDivisor]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_eq (continuous_apply j) continuous_const).inter isClosed_const

theorem ToricSpace.time_eq_zero_of_mem_rayDivisor {v : Fin 2 → ℤ} {x : Space}
    (hx : x ∈ rayDivisor v) : time x = 0 :=
  (branchVertices_nonempty x).mp ⟨v, hx⟩

theorem ToricSpace.central_fibre_eq_rayDivisors : time ⁻¹' {0} = ⋃ v : Fin 2 → ℤ, rayDivisor v := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, rayDivisor,
    Set.mem_ofPred_eq, ← branchVertices_nonempty, Set.nonempty_def]

theorem ToricSpace.branchVertices_translate (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (ToricSpace.translate v x) = (fun w => w + v) '' branchVertices x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, branchVertices_inclusion, branchVertices_inclusion,
    ToricFan.Triangle.chartBranches_shift]

theorem ToricSpace.branchVertices_torusAction (u : ActingTorus) (x : Space) :
    branchVertices (torusAction u x) = branchVertices x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, branchVertices_inclusion, branchVertices_inclusion]
  exact ToricFan.Triangle.chartBranches_mul s (factors s u) z (factors_nonzero s u)

theorem ToricSpace.branchVertices_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (twistedTranslate C v x) = (fun w => w + cuspVector v) '' branchVertices x := by
  simp only [twistedTranslate, variableMultiplier, branchVertices_torusAction,
    branchVertices_translate]

theorem ToricSpace.twistedTranslate_mem_rayDivisor (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (x : Space) :
    twistedTranslate C v x ∈ rayDivisor w ↔ x ∈ rayDivisor (w - cuspVector v) := by
  change w ∈ branchVertices (twistedTranslate C v x) ↔ _
  rw [branchVertices_twistedTranslate]
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = w - cuspVector v := eq_sub_iff_add_eq.mpr he
    rwa [← this]
  · intro hx
    exact ⟨w - cuspVector v, hx, sub_add_cancel _ _⟩

def ToricComponent.insertZero (j : Fin 3) (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.CoordinateSpace 3 :=
  Fin.insertNth j 0 z

def ToricComponent.removeCoordinate (j : Fin 3) (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.CoordinateSpace 2 :=
  Fin.removeNth j z

@[simp]
theorem ToricComponent.insertZero_at (j : Fin 3) (z : ToricCharts.CoordinateSpace 2) :
    insertZero j z j = 0 :=
  Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℂ) j 0 z

@[simp]
theorem ToricComponent.removeCoordinate_insertZero (j : Fin 3)
    (z : ToricCharts.CoordinateSpace 2) : removeCoordinate j (insertZero j z) = z :=
  Fin.removeNth_insertNth (α := fun _ : Fin 3 => ℂ) j 0 z

theorem ToricComponent.insertZero_removeCoordinate (j : Fin 3) (z : ToricCharts.CoordinateSpace 3)
    (hz : z j = 0) : insertZero j (removeCoordinate j z) = z :=
  Fin.insertNth_eq_iff.mpr ⟨hz.symm, rfl⟩

theorem ToricComponent.insertZero_holomorphic (j : Fin 3) : ContDiff ℂ ω (insertZero j) := by
  apply contDiff_pi.mpr
  intro k
  obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simpa only [insertZero_at] using
      (contDiff_const : ContDiff ℂ ω (fun _ : ToricCharts.CoordinateSpace 2 => (0 : ℂ)))
  · simpa only [insertZero, Fin.insertNth_apply_succAbove] using (contDiff_apply ℂ ℂ l)

theorem ToricComponent.removeCoordinate_holomorphic (j : Fin 3) :
    ContDiff ℂ ω (removeCoordinate j) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_apply ℂ ℂ (j.succAbove i)

structure ToricComponent.ChartIndex (v : Fin 2 → ℤ) where
  triangle : ToricFan.Triangle
  coordinate : Fin 3
  vertex_eq : triangle.vertex coordinate = v

theorem ToricComponent.insertZero_mem {v : Fin 2 → ℤ} (c : ChartIndex v)
    (z : ToricCharts.CoordinateSpace 2) :
    ToricSpace.inclusion c.triangle (insertZero c.coordinate z) ∈ ToricSpace.rayDivisor v := by
  have h :=
    (ToricSpace.mem_rayDivisor_vertex c.triangle c.coordinate (insertZero c.coordinate z)).mpr
      (insertZero_at c.coordinate z)
  simpa only [c.vertex_eq] using h

def ToricComponent.planeHomeomorph {v : Fin 2 → ℤ} (c : ChartIndex v) :
    ToricCharts.CoordinateSpace 2 ≃ₜ
      ToricSpace.inclusion c.triangle ⁻¹' ToricSpace.rayDivisor v := by
  refine
    { toFun := fun z => ⟨insertZero c.coordinate z, insertZero_mem c z⟩
      invFun := fun w => removeCoordinate c.coordinate w
      left_inv := fun z => removeCoordinate_insertZero c.coordinate z
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro w
    apply Subtype.ext
    apply insertZero_removeCoordinate
    have hw :
      ToricSpace.inclusion c.triangle (w : ToricCharts.CoordinateSpace 3) ∈
        ToricSpace.rayDivisor v :=
      w.2
    exact
      (ToricSpace.mem_rayDivisor_vertex c.triangle c.coordinate w).mp
        (by simpa only [c.vertex_eq] using hw)
  · exact (insertZero_holomorphic c.coordinate).continuous.subtype_mk _
  · exact (removeCoordinate_holomorphic c.coordinate).continuous.comp continuous_subtype_val

def ToricComponent.affineInclusion {v : Fin 2 → ℤ} (c : ChartIndex v)
    (z : ToricCharts.CoordinateSpace 2) : ToricSpace.rayDivisor v :=
  ⟨ToricSpace.inclusion c.triangle (insertZero c.coordinate z), insertZero_mem c z⟩

theorem ToricComponent.affineInclusion_openEmbedding {v : Fin 2 → ℤ} (c : ChartIndex v) :
    Topology.IsOpenEmbedding (affineInclusion c) :=
  ((ToricSpace.inclusion_openEmbedding c.triangle).restrictPreimage
        (ToricSpace.rayDivisor v)).comp
    (planeHomeomorph c).isOpenEmbedding

theorem ToricComponent.affineInclusion_jointly_surjective {v : Fin 2 → ℤ}
    (x : ToricSpace.rayDivisor v) :
    ∃ c : ChartIndex v, ∃ z : ToricCharts.CoordinateSpace 2, affineInclusion c z = x := by
  obtain ⟨s, z, hz⟩ := ToricSpace.inclusion_jointly_surjective (x : ToricSpace.Space)
  have hx : ToricSpace.inclusion s z ∈ ToricSpace.rayDivisor v := by rw [hz]; exact x.2
  obtain ⟨j, hj, hv⟩ := (ToricSpace.mem_rayDivisor_inclusion v s z).mp hx
  refine ⟨⟨s, j, hv⟩, removeCoordinate j z, ?_⟩
  apply Subtype.ext
  change ToricSpace.inclusion s (insertZero j (removeCoordinate j z)) = (x : ToricSpace.Space)
  rw [insertZero_removeCoordinate j z hj]
  exact hz

def CuspQuotient.branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : QuotientSpace C ε → ℕ :=
  Quotient.lift
    (fun x : ToricSpace.Tube (disc ε) => ToricSpace.branchCount (x : ToricSpace.Space))
    (by
      let := ToricSpace.tubeAction C (disc ε)
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact ToricSpace.branchCount_twistedTranslate C g.toAdd y)

theorem CuspQuotient.centralChartMap_origin_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s t : ToricFan.Triangle) :
    centralChartMap C ε hε s centralOrigin = centralChartMap C ε hε t centralOrigin ↔
      s.upper = t.upper := by
  let := ToricSpace.tubeAction C (disc ε)
  constructor
  · intro he
    have horb := Quotient.exact he
    change
      centralLift ε hε s centralOrigin ∈
        MulAction.orbit LatticeGroup (centralLift ε hε t centralOrigin) at horb
    obtain ⟨g, hg⟩ := horb
    have he' :
      ToricSpace.twistedTranslate C g.toAdd (ToricSpace.inclusion t 0) =
        ToricSpace.inclusion s 0 :=
      congrArg Subtype.val hg
    rw [ToricSpace.twistedTranslate_origin] at he'
    have hst := (ToricSpace.inclusion_origin_injective _ _).mp he'
    exact (congrArg ToricFan.Triangle.upper hst).symm
  · intro hst
    rw [centralChartMap_origin_reference C ε hε s, centralChartMap_origin_reference C ε hε t, hst]

@[simp]
theorem ToricSpace.cuspVector_neg (v : Fin 2 → ℤ) : cuspVector (-v) = -cuspVector v := by
  ext i
  fin_cases i <;> simp [cuspVector]

@[simp]
theorem ToricSpace.cuspVector_cuspVector (v : Fin 2 → ℤ) : cuspVector (cuspVector v) = -v := by
  ext i
  fin_cases i <;> simp [cuspVector]

theorem ToricSpace.cuspVector_injective : Function.Injective cuspVector := by
  intro v w h
  have h' := congrArg cuspVector h
  simpa only [cuspVector_cuspVector, neg_inj] using h'

def CuspQuotient.componentLift (ε : ℝ) (hε : 0 < ε) (x : ToricSpace.rayDivisor 0) :
    ToricSpace.Tube (disc ε) :=
  ⟨x, by
    change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
    rw [ToricSpace.time_eq_zero_of_mem_rayDivisor x.2]
    simpa using hε⟩

theorem ToricSpace.rayDivisors_locallyFinite : LocallyFinite rayDivisor := by
  intro x
  let s := preferredTriangle x
  refine
    ⟨Set.range (ToricSpace.inclusion s),
      (inclusion_openEmbedding s).isOpen_range.mem_nhds (preferred_mem x), ?_⟩
  apply (Set.finite_range s.vertex).subset
  rintro v ⟨y, hy, ⟨z, rfl⟩⟩
  obtain ⟨j, _, hj⟩ := (mem_rayDivisor_inclusion v s z).mp hy
  exact ⟨j, hj⟩

def ToricSpace.centralTranslationHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    Space ≃ₜ Space :=
  (translationHomeomorph (cuspVector v)).trans
    (torusHomeomorph (fibreMultiplier (exponentialMultiplier C v 0)))

def ToricComponent.zeroTriangle : Fin 6 → ToricFan.Triangle :=
  ![⟨0, 0, Bool.false⟩, ⟨-1, 0, Bool.true⟩, ⟨-1, 0, Bool.false⟩, ⟨-1, -1, Bool.true⟩,
    ⟨0, -1, Bool.false⟩, ⟨0, -1, Bool.true⟩]

def ToricComponent.zeroCoordinate : Fin 6 → Fin 3 :=
  ![0, 0, 1, 2, 2, 1]

theorem ToricComponent.zeroTriangle_vertex (i : Fin 6) :
    (zeroTriangle i).vertex (zeroCoordinate i) = 0 := by fin_cases i <;> decide

def ToricComponent.zeroChart (i : Fin 6) : ChartIndex 0 :=
  ⟨zeroTriangle i, zeroCoordinate i, zeroTriangle_vertex i⟩

theorem ToricComponent.zeroChart_surjective : Function.Surjective zeroChart := by
  rintro ⟨⟨a, b, u⟩, j, hj⟩
  have h0 := congrFun hj 0
  have h1 := congrFun hj 1
  cases u <;> fin_cases j
  · change a = 0 at h0
    change b = 0 at h1
    subst a b
    exact ⟨0, rfl⟩
  · change a + 1 = 0 at h0
    change b = 0 at h1
    have ha : a = -1 := by omega
    subst a b
    exact ⟨2, rfl⟩
  · change a = 0 at h0
    change b + 1 = 0 at h1
    have hb : b = -1 := by omega
    subst a b
    exact ⟨4, rfl⟩
  · change a + 1 = 0 at h0
    change b = 0 at h1
    have ha : a = -1 := by omega
    subst a b
    exact ⟨1, rfl⟩
  · change a = 0 at h0
    change b + 1 = 0 at h1
    have hb : b = -1 := by omega
    subst a b
    exact ⟨5, rfl⟩
  · change a + 1 = 0 at h0
    change b + 1 = 0 at h1
    have ha : a = -1 := by omega
    have hb : b = -1 := by omega
    subst a b
    exact ⟨3, rfl⟩

def ToricComponent.hexagonRay : Fin 6 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![-1, 1], ![-1, 0], ![0, -1], ![1, -1] ]

theorem ToricComponent.hexagonRay_injective : Function.Injective hexagonRay := by decide

theorem ToricComponent.hexagonRay_ne_zero (i : Fin 6) : hexagonRay i ≠ 0 := by
  fin_cases i <;> decide

theorem ToricComponent.hexagonRay_opposite (i : Fin 6) : hexagonRay (i + 3) = -hexagonRay i := by
  fin_cases i <;> decide

def CuspHoneycombHexagon.vertex (i : Fin 6) : Plane := fun k =>
  (ToricComponent.hexagonRay i k : ℝ)

def CuspHoneycombHexagon.midpoint (i : Fin 6) : Plane :=
  (1 / 2 : ℝ) • (vertex (i - 1) + vertex i)

def CuspHoneycombHexagon.Hexagon : Set Plane :=
  {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 0 + x 1| ≤ 1}

def CuspHoneycombHexagon.sideFunctional (k : Fin 6) (x : Plane) : ℝ :=
  ![x 0, x 0 + x 1, x 1, -x 0, -x 0 - x 1, -x 1] k

def CuspHoneycombHexagon.side (k : Fin 6) : Set Plane :=
  {x | x ∈ Hexagon ∧ sideFunctional k x = 1}

@[simp]
theorem CuspHoneycombHexagon.sideFunctional_zero (x : Plane) : sideFunctional 0 x = x 0 :=
  rfl

@[simp]
theorem CuspHoneycombHexagon.sideFunctional_one (x : Plane) : sideFunctional 1 x = x 0 + x 1 :=
  rfl

@[simp]
theorem CuspHoneycombHexagon.sideFunctional_two (x : Plane) : sideFunctional 2 x = x 1 :=
  rfl

@[simp]
theorem CuspHoneycombHexagon.sideFunctional_three (x : Plane) : sideFunctional 3 x = -x 0 :=
  rfl

@[simp]
theorem CuspHoneycombHexagon.sideFunctional_four (x : Plane) : sideFunctional 4 x = -x 0 - x 1 :=
  rfl

@[simp]
theorem CuspHoneycombHexagon.sideFunctional_five (x : Plane) : sideFunctional 5 x = -x 1 :=
  rfl

def CuspHoneycombHexagon.cornerZero : Square :=
  ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩

def CuspHoneycombHexagon.cornerOne : Square :=
  ⟨fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩⟩

def CuspHoneycombHexagon.tile (i : Fin 6) (p : Square) : Plane :=
  (1 - Max.max (p.1 0) (p.1 1)) • vertex i +
      Max.max (p.1 1 - p.1 0) 0 • CuspHoneycombHexagon.midpoint i +
    Max.max (p.1 0 - p.1 1) 0 • CuspHoneycombHexagon.midpoint (i + 1)

theorem CuspHoneycombHexagon.tile_continuous (i : Fin 6) : Continuous (tile i) := by
  have h0 : Continuous (fun p : Square => p.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun p : Square => p.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact
    (((continuous_const.sub (h0.max h1)).smul continuous_const).add
          (((h1.sub h0).max continuous_const).smul continuous_const)).add
      (((h0.sub h1).max continuous_const).smul continuous_const)

theorem CuspHoneycombHexagon.tile_of_le (i : Fin 6) (p : Square) (hp : p.1 0 ≤ p.1 1) :
    tile i p = (1 - p.1 1) • vertex i + (p.1 1 - p.1 0) • CuspHoneycombHexagon.midpoint i := by
  simp only [tile, max_eq_right hp, max_eq_left (sub_nonneg.mpr hp),
    max_eq_right (sub_nonpos.mpr hp), zero_smul, add_zero]

theorem CuspHoneycombHexagon.tile_of_ge (i : Fin 6) (p : Square) (hp : p.1 1 ≤ p.1 0) :
    tile i p = (1 - p.1 0) • vertex i + (p.1 0 - p.1 1) • CuspHoneycombHexagon.midpoint (i + 1) :=
  by
  simp only [tile, max_eq_left hp, max_eq_right (sub_nonpos.mpr hp),
    max_eq_left (sub_nonneg.mpr hp), zero_smul, add_zero]

theorem CuspHoneycombHexagon.tile_fst_one (i : Fin 6) (p : Square) (hp : p.1 0 = 1) :
    tile i p = (1 - p.1 1) • CuspHoneycombHexagon.midpoint (i + 1) := by
  rw [tile_of_ge i p (by simpa only [hp] using (p.2 1).2)]
  simp only [hp, sub_self, zero_smul, zero_add]

theorem CuspHoneycombHexagon.tile_fst_zero (i : Fin 6) (p : Square) (hp : p.1 0 = 0) :
    tile i p = (1 - p.1 1) • vertex i + p.1 1 • CuspHoneycombHexagon.midpoint i := by
  rw [tile_of_le i p (by simpa only [hp] using (p.2 1).1)]
  simp only [hp, sub_zero]

@[simp]
theorem CuspHoneycombHexagon.tile_cornerZero (i : Fin 6) : tile i cornerZero = vertex i := by
  rw [tile_fst_zero i cornerZero rfl]
  simp only [cornerZero, sub_zero, one_smul, zero_smul, add_zero]

@[simp]
theorem CuspHoneycombHexagon.tile_cornerOne (i : Fin 6) : tile i cornerOne = 0 := by
  rw [tile_fst_one i cornerOne rfl]
  simp only [cornerOne, sub_self, zero_smul]

@[simp]
theorem CuspHoneycombHexagon.vertex_zero : vertex 0 = ![1, 0] := by
  funext k
  fin_cases k
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((0 : ℤ) : ℝ) = 0
    norm_num

@[simp]
theorem CuspHoneycombHexagon.vertex_one : vertex 1 = ![0, 1] := by
  funext k
  fin_cases k
  · change ((0 : ℤ) : ℝ) = 0
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num

@[simp]
theorem CuspHoneycombHexagon.vertex_two : vertex 2 = ![-1, 1] := by
  funext k
  fin_cases k
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num

@[simp]
theorem CuspHoneycombHexagon.vertex_three : vertex 3 = ![-1, 0] := by
  funext k
  fin_cases k
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num
  · change ((0 : ℤ) : ℝ) = 0
    norm_num

@[simp]
theorem CuspHoneycombHexagon.vertex_four : vertex 4 = ![0, -1] := by
  funext k
  fin_cases k
  · change ((0 : ℤ) : ℝ) = 0
    norm_num
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num

@[simp]
theorem CuspHoneycombHexagon.vertex_five : vertex 5 = ![1, -1] := by
  funext k
  fin_cases k
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num

def CuspHoneycombHexagon.rotate : Plane ≃ₗ[ℝ] Plane
    where
  toFun x := ![-x 1, x 0 + x 1]
  invFun x := ![x 0 + x 1, -x 0]
  left_inv
    x := by
    funext k
    fin_cases k <;> simp
  right_inv
    x := by
    funext k
    fin_cases k <;> simp
  map_add' x
    y := by
    funext k
    fin_cases k <;> simp <;> ring
  map_smul' r
    x := by
    funext k
    fin_cases k <;> simp; ring

@[simp]
theorem CuspHoneycombHexagon.rotate_vertex (i : Fin 6) : rotate (vertex i) = vertex (i + 1) := by
  have hr :
    ∀ i : Fin 6,
      ToricComponent.hexagonRay (i + 1) 0 = -ToricComponent.hexagonRay i 1 ∧
        ToricComponent.hexagonRay (i + 1) 1 =
          ToricComponent.hexagonRay i 0 + ToricComponent.hexagonRay i 1 := by decide
  funext k
  fin_cases k
  · change -(ToricComponent.hexagonRay i 1 : ℝ) = (ToricComponent.hexagonRay (i + 1) 0 : ℝ)
    rw [(hr i).1, Int.cast_neg]
  · change
      (ToricComponent.hexagonRay i 0 : ℝ) + (ToricComponent.hexagonRay i 1 : ℝ) =
        (ToricComponent.hexagonRay (i + 1) 1 : ℝ)
    rw [(hr i).2, Int.cast_add]

@[simp]
theorem CuspHoneycombHexagon.rotate_midpoint (i : Fin 6) :
    rotate (CuspHoneycombHexagon.midpoint i) = CuspHoneycombHexagon.midpoint (i + 1) := by
  simp only [CuspHoneycombHexagon.midpoint, map_smul, map_add, rotate_vertex, sub_add_cancel,
    add_sub_cancel_right]

@[simp]
theorem CuspHoneycombHexagon.rotate_tile (i : Fin 6) (p : Square) :
    rotate (tile i p) = tile (i + 1) p := by
  simp only [tile, map_add, map_smul, rotate_vertex, rotate_midpoint]

theorem CuspHoneycombHexagon.sector_formula_0 (α β : ℝ) :
    α • vertex 0 + β • vertex (0 + 1) = ![α, β] := by
  ext k
  fin_cases k
  · change α * ((1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = α
    norm_num [sub_eq_add_neg]
  · change α * ((0 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = β
    norm_num [sub_eq_add_neg]

theorem CuspHoneycombHexagon.sector_formula_1 (α β : ℝ) :
    α • vertex 1 + β • vertex (1 + 1) = ![-β, α + β] := by
  ext k
  fin_cases k
  · change α * ((0 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -β
    norm_num [sub_eq_add_neg]
  · change α * ((1 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = α + β
    norm_num [sub_eq_add_neg]

theorem CuspHoneycombHexagon.sector_formula_2 (α β : ℝ) :
    α • vertex 2 + β • vertex (2 + 1) = ![-α - β, α] := by
  ext k
  fin_cases k
  · change α * ((-1 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -α - β
    norm_num [sub_eq_add_neg]
  · change α * ((1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = α
    norm_num [sub_eq_add_neg]

theorem CuspHoneycombHexagon.sector_formula_3 (α β : ℝ) :
    α • vertex 3 + β • vertex (3 + 1) = ![-α, -β] := by
  ext k
  fin_cases k
  · change α * ((-1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = -α
    norm_num [sub_eq_add_neg]
  · change α * ((0 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -β
    norm_num [sub_eq_add_neg]

theorem CuspHoneycombHexagon.sector_formula_4 (α β : ℝ) :
    α • vertex 4 + β • vertex (4 + 1) = ![β, -α - β] := by
  ext k
  fin_cases k
  · change α * ((0 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = β
    norm_num [sub_eq_add_neg]
  · change α * ((-1 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -α - β
    norm_num [sub_eq_add_neg]

theorem CuspHoneycombHexagon.sector_formula_5 (α β : ℝ) :
    α • vertex 5 + β • vertex (5 + 1) = ![α + β, -α] := by
  ext k
  fin_cases k
  · change α * ((1 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = α + β
    norm_num [sub_eq_add_neg]
  · change α * ((-1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = -α
    norm_num [sub_eq_add_neg]

theorem CuspHoneycombHexagon.sector_decomposition {x : Plane} (hx : x ∈ Hexagon) :
    ∃ i : Fin 6, ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1 ∧ x = α • vertex i + β • vertex (i + 1) := by
  obtain ⟨h0, h1, h01⟩ := hx
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h01l, h01u⟩ := abs_le.mp h01
  by_cases ha : 0 ≤ x 0
  · by_cases hb : 0 ≤ x 1
    · refine ⟨0, x 0, x 1, ha, hb, h01u, ?_⟩
      rw [sector_formula_0]
      exact funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
    · by_cases hab : 0 ≤ x 0 + x 1
      · refine ⟨5, -x 1, x 0 + x 1, ?_, hab, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_5]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
            ring
      · refine ⟨4, -(x 0 + x 1), x 0, ?_, ha, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_4]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one];
          ring
  · by_cases hb : 0 ≤ x 1
    · by_cases hab : 0 ≤ x 0 + x 1
      · refine ⟨1, x 0 + x 1, -x 0, hab, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_1]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
            ring
      · refine ⟨2, x 1, -(x 0 + x 1), hb, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_2]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one];
          ring
    · refine ⟨3, -x 0, -x 1, ?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · rw [sector_formula_3]
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
          ring

theorem CuspHoneycombHexagon.sector_mem_hexagon (i : Fin 6) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β ≤ 1) : α • vertex i + β • vertex (i + 1) ∈ Hexagon := by
  fin_cases i
  · change α • vertex 0 + β • vertex (0 + 1) ∈ Hexagon
    rw [sector_formula_0]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 1 + β • vertex (1 + 1) ∈ Hexagon
    rw [sector_formula_1]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 2 + β • vertex (2 + 1) ∈ Hexagon
    rw [sector_formula_2]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 3 + β • vertex (3 + 1) ∈ Hexagon
    rw [sector_formula_3]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 4 + β • vertex (4 + 1) ∈ Hexagon
    rw [sector_formula_4]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 5 + β • vertex (5 + 1) ∈ Hexagon
    rw [sector_formula_5]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem CuspHoneycombHexagon.tile_zero_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 0 p = ![1 - p.1 0, (p.1 0 - p.1 1) / 2] := by
  rw [tile_of_le 0 p h]
  have hindex : (0 : Fin 6) - 1 = 5 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_five, vertex_zero]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_zero_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 0 p = ![1 - (p.1 0 + p.1 1) / 2, (p.1 0 - p.1 1) / 2] := by
  rw [tile_of_ge 0 p h]
  have hadd : (0 : Fin 6) + 1 = 1 := by decide
  have hindex : (1 : Fin 6) - 1 = 0 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_zero, vertex_one]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem CuspHoneycombHexagon.tile_one_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 1 p = ![(p.1 1 - p.1 0) / 2, 1 - (p.1 0 + p.1 1) / 2] := by
  rw [tile_of_le 1 p h]
  have hindex : (1 : Fin 6) - 1 = 0 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_zero, vertex_one]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem CuspHoneycombHexagon.tile_one_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 1 p = ![(p.1 1 - p.1 0) / 2, 1 - p.1 1] := by
  rw [tile_of_ge 1 p h]
  have hadd : (1 : Fin 6) + 1 = 2 := by decide
  have hindex : (2 : Fin 6) - 1 = 1 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_one, vertex_two]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_two_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 2 p = ![(p.1 0 + p.1 1) / 2 - 1, 1 - p.1 0] := by
  rw [tile_of_le 2 p h]
  have hindex : (2 : Fin 6) - 1 = 1 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_one, vertex_two]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_two_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 2 p = ![p.1 1 - 1, 1 - (p.1 0 + p.1 1) / 2] := by
  rw [tile_of_ge 2 p h]
  have hadd : (2 : Fin 6) + 1 = 3 := by decide
  have hindex : (3 : Fin 6) - 1 = 2 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_two, vertex_three]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_three_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 3 p = ![p.1 0 - 1, (p.1 1 - p.1 0) / 2] := by
  rw [tile_of_le 3 p h]
  have hindex : (3 : Fin 6) - 1 = 2 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_two, vertex_three]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_three_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 3 p = ![(p.1 0 + p.1 1) / 2 - 1, (p.1 1 - p.1 0) / 2] := by
  rw [tile_of_ge 3 p h]
  have hadd : (3 : Fin 6) + 1 = 4 := by decide
  have hindex : (4 : Fin 6) - 1 = 3 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_three, vertex_four]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem CuspHoneycombHexagon.tile_four_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 4 p = ![(p.1 0 - p.1 1) / 2, (p.1 0 + p.1 1) / 2 - 1] := by
  rw [tile_of_le 4 p h]
  have hindex : (4 : Fin 6) - 1 = 3 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_three, vertex_four]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem CuspHoneycombHexagon.tile_four_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 4 p = ![(p.1 0 - p.1 1) / 2, p.1 1 - 1] := by
  rw [tile_of_ge 4 p h]
  have hadd : (4 : Fin 6) + 1 = 5 := by decide
  have hindex : (5 : Fin 6) - 1 = 4 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_four, vertex_five]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_five_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 5 p = ![1 - (p.1 0 + p.1 1) / 2, p.1 0 - 1] := by
  rw [tile_of_le 5 p h]
  have hindex : (5 : Fin 6) - 1 = 4 := by decide
  rw [CuspHoneycombHexagon.midpoint, hindex, vertex_four, vertex_five]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.tile_five_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 5 p = ![1 - p.1 1, (p.1 0 + p.1 1) / 2 - 1] := by
  rw [tile_of_ge 5 p h]
  have hadd : (5 : Fin 6) + 1 = 0 := by decide
  have hindex : (0 : Fin 6) - 1 = 5 := by decide
  rw [hadd, CuspHoneycombHexagon.midpoint, hindex, vertex_five, vertex_zero]
  ext k
  fin_cases k <;> norm_num; ring

theorem CuspHoneycombHexagon.eq_cornerOne_iff (p : Square) :
    p = cornerOne ↔ p.1 0 = 1 ∧ p.1 1 = 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    apply Subtype.ext
    ext k
    fin_cases k <;> assumption

theorem CuspHoneycombHexagon.tile_zero_eq_one_iff (p q : Square) :
    tile 0 p = tile 1 q ↔ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1 := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_one_le q hq] at h
      | rw [tile_one_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨?_, ?_, ?_⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨hp, hq, hqp⟩
    have hp' : p.1 1 ≤ p.1 0 := by simpa only [hp] using (p.property 1).2
    have hq' : q.1 0 ≤ q.1 1 := by simpa only [hq] using (q.property 0).2
    rw [tile_zero_ge p hp', tile_one_le q hq']
    ext k
    fin_cases k <;> simp [hp, hq, hqp] <;> ring

theorem CuspHoneycombHexagon.tile_zero_eq_five_iff (p q : Square) :
    tile 0 p = tile 5 q ↔ p.1 1 = 1 ∧ q.1 0 = 1 ∧ p.1 0 = q.1 1 := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_five_le q hq] at h
      | rw [tile_five_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨?_, ?_, ?_⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨hp, hq, hpq⟩
    have hp' : p.1 0 ≤ p.1 1 := by simpa only [hp] using (p.property 0).2
    have hq' : q.1 1 ≤ q.1 0 := by simpa only [hq] using (q.property 1).2
    rw [tile_zero_le p hp', tile_five_ge q hq']
    ext k
    fin_cases k <;> simp [hp, hq, hpq]; ring

theorem CuspHoneycombHexagon.tile_zero_eq_two_iff (p q : Square) :
    tile 0 p = tile 2 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_two_le q hq] at h
      | rw [tile_two_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.tile_zero_eq_three_iff (p q : Square) :
    tile 0 p = tile 3 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_three_le q hq] at h
      | rw [tile_three_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.tile_zero_eq_four_iff (p q : Square) :
    tile 0 p = tile 4 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first
      | rw [tile_zero_le p hp] at h
      | rw [tile_zero_ge p hp] at h
      first
      | rw [tile_four_le q hq] at h
      | rw [tile_four_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.tile_zero_injective : Function.Injective (tile 0) := by
  intro p q h
  apply Subtype.ext
  rcases le_total (p.1 0) (p.1 1) with hp | hp <;> rcases le_total (q.1 0) (q.1 1) with hq | hq
  all_goals
    first
    | rw [tile_zero_le p hp] at h
    | rw [tile_zero_ge p hp] at h
    first
    | rw [tile_zero_le q hq] at h
    | rw [tile_zero_ge q hq] at h
    have hx := congrFun h 0
    have hy := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    ext k
    fin_cases k
    · change p.1 0 = q.1 0
      linarith only [hp, hq, hx, hy]
    · change p.1 1 = q.1 1
      linarith only [hp, hq, hx, hy]

theorem CuspHoneycombHexagon.rotate_iterate_tile (n : ℕ) (i : Fin 6) (p : Square) :
    (rotate : Plane → Plane)^[n] (tile i p) = tile (i + (n : Fin 6)) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, rotate_tile]
    congr 1
    simp only [Nat.cast_succ, add_assoc]

theorem CuspHoneycombHexagon.tile_eq_iff_sub (i j : Fin 6) (p q : Square) :
    tile i p = tile j q ↔ tile 0 p = tile (j - i) q := by
  have hp : (rotate : Plane → Plane)^[i.val] (tile 0 p) = tile i p := by
    rw [rotate_iterate_tile]
    simp only [Fin.cast_val_eq_self, zero_add]
  have hq : (rotate : Plane → Plane)^[i.val] (tile (j - i) q) = tile j q := by
    rw [rotate_iterate_tile]
    simp only [Fin.cast_val_eq_self, sub_add_cancel]
  rw [← hp, ← hq]
  exact (rotate.injective.iterate i.val).eq_iff

theorem CuspHoneycombHexagon.squareRel_sub (i j : Fin 6) (p q : Square) :
    SquareRel 0 (j - i) p q ↔ SquareRel i j p q := by
  have h0 : (0 : Fin 6) = j - i ↔ i = j := by rw [eq_sub_iff_add_eq, zero_add]
  have h1 : j - i = (0 : Fin 6) + 1 ↔ j = i + 1 := by
    rw [zero_add, sub_eq_iff_eq_add, add_comm (1 : Fin 6) i]
  have h2 : (0 : Fin 6) = (j - i) + 1 ↔ i = j + 1 := by
    have he : j - i + 1 = (j + 1) - i := by abel
    rw [he, eq_sub_iff_add_eq, zero_add]
  simp only [SquareRel, h0, h1, h2]

theorem CuspHoneycombHexagon.eq_cornerOne_iff_all (p : Square) : p = cornerOne ↔ ∀ k, p.1 k = 1 :=
  by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro hp
    exact square_eq_of_all_one p cornerOne hp (fun _ => rfl)

theorem CuspHoneycombHexagon.tile_zero_eq_iff (j : Fin 6) (p q : Square) :
    tile 0 p = tile j q ↔ SquareRel 0 j p q := by
  fin_cases j
  · change tile 0 p = tile 0 q ↔ SquareRel 0 0 p q
    rw [squareRel_self]
    exact tile_zero_injective.eq_iff
  · change tile 0 p = tile 1 q ↔ SquareRel 0 (0 + 1) p q
    rw [squareRel_next]
    exact tile_zero_eq_one_iff p q
  · change tile 0 p = tile 2 q ↔ SquareRel 0 (0 + 2) p q
    rw [squareRel_add_two, tile_zero_eq_two_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 3 q ↔ SquareRel 0 (0 + 3) p q
    rw [squareRel_add_three, tile_zero_eq_three_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 4 q ↔ SquareRel 0 (0 + 4) p q
    rw [squareRel_add_four, tile_zero_eq_four_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 5 q ↔ SquareRel 0 (0 + 5) p q
    rw [squareRel_prev, tile_zero_eq_five_iff]
    constructor <;> rintro ⟨h0, h1, h2⟩
    · exact ⟨h0, h1, h2.symm⟩
    · exact ⟨h0, h1, h2.symm⟩

theorem CuspHoneycombHexagon.tile_eq_iff (i j : Fin 6) (p q : Square) :
    tile i p = tile j q ↔ SquareRel i j p q :=
  (tile_eq_iff_sub i j p q).trans ((tile_zero_eq_iff (j - i) p q).trans (squareRel_sub i j p q))

theorem CuspHoneycombHexagon.tile_sector_of_le (i : Fin 6) (p : Square) (hp : p.1 0 ≤ p.1 1) :
    tile i p =
      ((p.1 1 - p.1 0) / 2) • vertex (i - 1) + (1 - (p.1 0 + p.1 1) / 2) • vertex ((i - 1) + 1) :=
  by
  rw [tile_of_le i p hp, CuspHoneycombHexagon.midpoint, sub_add_cancel]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem CuspHoneycombHexagon.tile_sector_of_ge (i : Fin 6) (p : Square) (hp : p.1 1 ≤ p.1 0) :
    tile i p = (1 - (p.1 0 + p.1 1) / 2) • vertex i + ((p.1 0 - p.1 1) / 2) • vertex (i + 1) := by
  rw [tile_of_ge i p hp, CuspHoneycombHexagon.midpoint, add_sub_cancel_right]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem CuspHoneycombHexagon.tile_mem_hexagon (i : Fin 6) (p : Square) : tile i p ∈ Hexagon := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_sector_of_le i p hp]
    apply sector_mem_hexagon (i - 1) <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · rw [tile_sector_of_ge i p hp]
    apply sector_mem_hexagon i <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]

theorem CuspHoneycombHexagon.exists_tile_of_sector (i : Fin 6) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β ≤ 1) : ∃ j : Fin 6, ∃ p : Square, tile j p = α • vertex i + β • vertex (i + 1) :=
  by
  rcases le_total β α with h | h
  · let p : Square :=
      ⟨![1 - α + β, 1 - α - β], by
        intro k
        fin_cases k
        · change 0 ≤ 1 - α + β ∧ 1 - α + β ≤ 1
          constructor <;> linarith
        · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
          constructor <;> linarith⟩
    have hp : p.1 1 ≤ p.1 0 := by
      change 1 - α - β ≤ 1 - α + β
      linarith
    refine ⟨i, p, ?_⟩
    rw [tile_sector_of_ge i p hp]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · let p : Square :=
      ⟨![1 - α - β, 1 + α - β], by
        intro k
        fin_cases k
        · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
          constructor <;> linarith
        · change 0 ≤ 1 + α - β ∧ 1 + α - β ≤ 1
          constructor <;> linarith⟩
    have hp : p.1 0 ≤ p.1 1 := by
      change 1 - α - β ≤ 1 + α - β
      linarith
    refine ⟨i + 1, p, ?_⟩
    rw [tile_sector_of_le (i + 1) p hp, add_sub_cancel_right]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

theorem CuspHoneycombHexagon.tile_jointly_surjective (x : Hexagon) :
    ∃ i : Fin 6, ∃ p : Square, tile i p = x.val := by
  obtain ⟨i, α, β, hα, hβ, hαβ, hx⟩ := sector_decomposition x.2
  obtain ⟨j, p, hp⟩ := exists_tile_of_sector i α β hα hβ hαβ
  exact ⟨j, p, hp.trans hx.symm⟩

theorem CuspHoneycombHexagon.tile_zero_side_zero_eq_one_iff (p : Square) :
    sideFunctional 0 (tile 0 p) = 1 ↔ p.1 0 = 0 := by
  rw [sideFunctional_zero]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]

theorem CuspHoneycombHexagon.tile_zero_side_one_eq_one_iff (p : Square) :
    sideFunctional 1 (tile 0 p) = 1 ↔ p.1 1 = 0 := by
  rw [sideFunctional_one]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]

theorem CuspHoneycombHexagon.tile_zero_side_two_lt_one (p : Square) :
    sideFunctional 2 (tile 0 p) < 1 := by
  rw [sideFunctional_two]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]

theorem CuspHoneycombHexagon.tile_zero_side_three_lt_one (p : Square) :
    sideFunctional 3 (tile 0 p) < 1 := by
  rw [sideFunctional_three]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero]
    linarith only [hp0, hp1]

theorem CuspHoneycombHexagon.tile_zero_side_four_lt_one (p : Square) :
    sideFunctional 4 (tile 0 p) < 1 := by
  rw [sideFunctional_four]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hp0, hp1]

theorem CuspHoneycombHexagon.tile_zero_side_five_lt_one (p : Square) :
    sideFunctional 5 (tile 0 p) < 1 := by
  rw [sideFunctional_five]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]

theorem CuspHoneycombHexagon.tile_zero_side_eq_one_iff (p : Square) (k : Fin 6) :
    sideFunctional k (tile 0 p) = 1 ↔ (k = 0 ∧ p.1 0 = 0) ∨ (k = 1 ∧ p.1 1 = 0) := by
  fin_cases k
  · simpa only [Fin.zero_eta, true_and, or_false,
      show (0 : Fin 6) = 0 ↔ True from iff_true_intro rfl,
      show (0 : Fin 6) = 1 ↔ False from iff_false_intro (by decide), false_and] using
      tile_zero_side_zero_eq_one_iff p
  · simpa only [Fin.mk_one, false_and, false_or, true_and,
      show (1 : Fin 6) = 0 ↔ False from iff_false_intro (by decide),
      show (1 : Fin 6) = 1 ↔ True from iff_true_intro rfl] using tile_zero_side_one_eq_one_iff p
  · constructor
    · intro h
      exact ((tile_zero_side_two_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (2 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (2 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_three_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (3 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (3 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_four_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (4 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (4 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_five_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (5 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (5 : Fin 6) ≠ 1 by decide) h).elim

theorem CuspHoneycombHexagon.sideFunctional_rotate (k : Fin 6) (x : Plane) :
    sideFunctional (k + 1) (rotate x) = sideFunctional k x := by
  fin_cases k
  · change -x 1 + (x 0 + x 1) = x 0
    ring
  · change x 0 + x 1 = x 0 + x 1
    rfl
  · change -(-x 1) = x 1
    ring
  · change -(-x 1) - (x 0 + x 1) = -x 0
    ring
  · change -(x 0 + x 1) = -x 0 - x 1
    ring
  · change -x 1 = -x 1
    rfl

theorem CuspHoneycombHexagon.sideFunctional_iterate (n : ℕ) (k : Fin 6) (x : Plane) :
    sideFunctional (k + (n : Fin 6)) ((rotate : Plane → Plane)^[n] x) = sideFunctional k x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Function.iterate_succ_apply', sideFunctional_rotate, ih]

theorem CuspHoneycombHexagon.sideFunctional_tile_sub (i k : Fin 6) (p : Square) :
    sideFunctional k (tile i p) = sideFunctional (k - i) (tile 0 p) := by
  have h := sideFunctional_iterate i.val (k - i) (tile 0 p)
  simpa only [rotate_iterate_tile, Fin.cast_val_eq_self, sub_add_cancel, zero_add] using h

theorem CuspHoneycombHexagon.tile_mem_side_iff (i k : Fin 6) (p : Square) :
    tile i p ∈ side k ↔ (k = i ∧ p.1 0 = 0) ∨ (k = i + 1 ∧ p.1 1 = 0) := by
  have h1 : k - i = (1 : Fin 6) ↔ k = i + 1 := by rw [sub_eq_iff_eq_add, add_comm (1 : Fin 6) i]
  change (tile i p ∈ Hexagon ∧ sideFunctional k (tile i p) = 1) ↔ _
  rw [sideFunctional_tile_sub]
  simp only [tile_mem_hexagon i p, true_and, tile_zero_side_eq_one_iff, sub_eq_zero, h1]

def CuspHoneycombTiling.dualStandardLinearEquiv : Plane ≃ₗ[ℝ] Plane
    where
  toFun x := ![2 * x 0 + x 1, x 1 - x 0]
  invFun y := ![(y 0 - y 1) / 3, (y 0 + 2 * y 1) / 3]
  left_inv
    x := by
    funext i
    fin_cases i
    · change ((2 * x 0 + x 1) - (x 1 - x 0)) / 3 = x 0
      ring
    · change ((2 * x 0 + x 1) + 2 * (x 1 - x 0)) / 3 = x 1
      ring
  right_inv
    y := by
    funext i
    fin_cases i
    · change 2 * ((y 0 - y 1) / 3) + (y 0 + 2 * y 1) / 3 = y 0
      ring
    · change (y 0 + 2 * y 1) / 3 - (y 0 - y 1) / 3 = y 1
      ring
  map_add' x
    y := by
    funext i
    fin_cases i
    · change 2 * (x 0 + y 0) + (x 1 + y 1) = (2 * x 0 + x 1) + (2 * y 0 + y 1)
      ring
    · change (x 1 + y 1) - (x 0 + y 0) = (x 1 - x 0) + (y 1 - y 0)
      ring
  map_smul' a
    x := by
    funext i
    fin_cases i
    · change 2 * (a * x 0) + a * x 1 = a * (2 * x 0 + x 1)
      ring
    · change a * x 1 - a * x 0 = a * (x 1 - x 0)
      ring

def CuspHoneycombTiling.dualStandardPlaneHomeomorph : Plane ≃ₜ Plane
    where
  toEquiv := dualStandardLinearEquiv.toEquiv
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)
    · exact (continuous_apply 1).sub (continuous_apply 0)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((continuous_apply 0).sub (continuous_apply 1)).div_const 3
    · exact ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).div_const 3

@[simp]
theorem CuspHoneycombTiling.dualStandardPlaneHomeomorph_apply (x : Plane) :
    dualStandardPlaneHomeomorph x = ![2 * x 0 + x 1, x 1 - x 0] :=
  rfl

theorem CuspHoneycombTiling.dualStandardPlaneHomeomorph_mem_hexagon (x : Plane) :
    dualStandardPlaneHomeomorph x ∈ CuspHoneycombHexagon.Hexagon ↔ x ∈ baseCell := by
  change (|2 * x 0 + x 1| ≤ 1 ∧ |x 1 - x 0| ≤ 1 ∧ |2 * x 0 + x 1 + (x 1 - x 0)| ≤ 1) ↔ _
  have he : 2 * x 0 + x 1 + (x 1 - x 0) = x 0 + 2 * x 1 := by ring
  rw [he, abs_sub_comm (x 1) (x 0)]
  rfl

theorem CuspHoneycombTiling.dualStandardPlaneHomeomorph_symm_mem_baseCell (y : Plane) :
    dualStandardPlaneHomeomorph.symm y ∈ baseCell ↔ y ∈ CuspHoneycombHexagon.Hexagon := by
  simpa only [Homeomorph.apply_symm_apply] using
    (dualStandardPlaneHomeomorph_mem_hexagon (dualStandardPlaneHomeomorph.symm y)).symm

def CuspHoneycombTiling.standardHexagonDualHomeomorph : CuspHoneycombHexagon.Hexagon ≃ₜ baseCell
    where
  toFun
    y :=
    ⟨dualStandardPlaneHomeomorph.symm y,
      (dualStandardPlaneHomeomorph_symm_mem_baseCell y).mpr y.2⟩
  invFun x := ⟨dualStandardPlaneHomeomorph x, (dualStandardPlaneHomeomorph_mem_hexagon x).mpr x.2⟩
  left_inv y := Subtype.ext (dualStandardPlaneHomeomorph.apply_symm_apply y)
  right_inv x := Subtype.ext (dualStandardPlaneHomeomorph.symm_apply_apply x)
  continuous_toFun :=
    (dualStandardPlaneHomeomorph.symm.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (dualStandardPlaneHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem CuspHoneycombTiling.standardHexagonDualHomeomorph_coe (y : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonDualHomeomorph y : Plane) = dualStandardPlaneHomeomorph.symm y :=
  rfl

def CuspHoneycombTiling.triangleBarycenter (s : ToricFan.Triangle) : Plane := fun i =>
  ((s.vertex 0 i : ℝ) + (s.vertex 1 i : ℝ) + (s.vertex 2 i : ℝ)) / 3

theorem CuspHoneycombTiling.triangleBarycenter_zeroTriangle (i : Fin 6) :
    triangleBarycenter (ToricComponent.zeroTriangle i) = fun j =>
      ((ToricComponent.hexagonRay i j : ℝ) + (ToricComponent.hexagonRay (i + 1) j : ℝ)) / 3 := by
  have hs :
    (ToricComponent.zeroTriangle i).vertex 0 + (ToricComponent.zeroTriangle i).vertex 1 +
        (ToricComponent.zeroTriangle i).vertex 2 =
      ToricComponent.hexagonRay i + ToricComponent.hexagonRay (i + 1) := by fin_cases i <;> decide
  funext j
  have hj :
    (ToricComponent.zeroTriangle i).vertex 0 j + (ToricComponent.zeroTriangle i).vertex 1 j +
        (ToricComponent.zeroTriangle i).vertex 2 j =
      ToricComponent.hexagonRay i j + ToricComponent.hexagonRay (i + 1) j :=
    congrFun hs j
  have hreal :
    ((ToricComponent.zeroTriangle i).vertex 0 j : ℝ) +
          ((ToricComponent.zeroTriangle i).vertex 1 j : ℝ) +
        ((ToricComponent.zeroTriangle i).vertex 2 j : ℝ) =
      (ToricComponent.hexagonRay i j : ℝ) + (ToricComponent.hexagonRay (i + 1) j : ℝ) := by
    exact_mod_cast hj
  exact congrArg (fun r : ℝ => r / 3) hreal

theorem CuspHoneycombTiling.dual_standard_vertex (i : Fin 6) :
    dualStandardPlaneHomeomorph.symm (CuspHoneycombHexagon.vertex i) =
      triangleBarycenter (ToricComponent.zeroTriangle i) := by
  have hr :
    ∀ i : Fin 6,
      ToricComponent.hexagonRay (i + 1) 0 = -ToricComponent.hexagonRay i 1 ∧
        ToricComponent.hexagonRay (i + 1) 1 =
          ToricComponent.hexagonRay i 0 + ToricComponent.hexagonRay i 1 := by decide
  rw [triangleBarycenter_zeroTriangle]
  funext j
  fin_cases j
  · change
      ((ToricComponent.hexagonRay i 0 : ℝ) - (ToricComponent.hexagonRay i 1 : ℝ)) / 3 =
        ((ToricComponent.hexagonRay i 0 : ℝ) + (ToricComponent.hexagonRay (i + 1) 0 : ℝ)) / 3
    rw [(hr i).1, Int.cast_neg]
    ring
  · change
      ((ToricComponent.hexagonRay i 0 : ℝ) + 2 * (ToricComponent.hexagonRay i 1 : ℝ)) / 3 =
        ((ToricComponent.hexagonRay i 1 : ℝ) + (ToricComponent.hexagonRay (i + 1) 1 : ℝ)) / 3
    rw [(hr i).2, Int.cast_add]
    ring

theorem CuspHoneycombTiling.mem_neighbor_cell_iff_sideFunctional (k : Fin 6) (x : Plane)
    (hx : x ∈ baseCell) :
    x ∈ cell (ToricComponent.hexagonRay k) ↔
      CuspHoneycombHexagon.sideFunctional k (dualStandardPlaneHomeomorph x) = 1 := by
  have h0 := abs_le.mp hx.1
  have h1 := abs_le.mp hx.2.1
  have h2 := abs_le.mp hx.2.2
  fin_cases k <;>
    norm_num [cell, baseCell, latticePoint, ToricComponent.hexagonRay,
      CuspHoneycombHexagon.sideFunctional, dualStandardPlaneHomeomorph_apply, abs_le]
  all_goals
    constructor
    · intro h
      linarith
    · intro h
      repeat' apply And.intro
      all_goals linarith

theorem CuspHoneycombTiling.dual_image_side (k : Fin 6) :
    dualStandardPlaneHomeomorph.symm '' CuspHoneycombHexagon.side k =
      baseCell ∩ cell (ToricComponent.hexagonRay k) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hx : dualStandardPlaneHomeomorph.symm y ∈ baseCell :=
      (dualStandardPlaneHomeomorph_symm_mem_baseCell y).mpr hy.1
    refine ⟨hx, (mem_neighbor_cell_iff_sideFunctional k _ hx).mpr ?_⟩
    simpa only [Homeomorph.apply_symm_apply] using hy.2
  · intro hx
    refine ⟨dualStandardPlaneHomeomorph x, ?_, dualStandardPlaneHomeomorph.symm_apply_apply x⟩
    exact
      ⟨(dualStandardPlaneHomeomorph_mem_hexagon x).mpr hx.1,
        (mem_neighbor_cell_iff_sideFunctional k x hx.1).mp hx.2⟩

theorem CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side (k : Fin 6)
    (x : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonDualHomeomorph x : Plane) ∈ cell (ToricComponent.hexagonRay k) ↔
      (x : Plane) ∈ CuspHoneycombHexagon.side k := by
  have h :=
    mem_neighbor_cell_iff_sideFunctional k (standardHexagonDualHomeomorph x)
      (standardHexagonDualHomeomorph x).property
  simpa only [standardHexagonDualHomeomorph_coe, Homeomorph.apply_symm_apply,
    CuspHoneycombHexagon.side, Set.mem_ofPred_eq, x.property, true_and] using h

def CuspHoneycombHexagon.segmentIntervalHomeomorph {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] [T2Space E] (a b : E)
    (hab : a ≠ b) : unitInterval ≃ₜ segment ℝ a b :=
  ((Path.segment a b).continuous.isClosedEmbedding
        (Path.segment_injective_of_ne hab)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (Path.range_segment a b))

@[simp]
theorem CuspHoneycombHexagon.segmentIntervalHomeomorph_apply {E : Type*} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] [T2Space E] (a b : E)
    (hab : a ≠ b) (t : unitInterval) :
    (segmentIntervalHomeomorph a b hab t : E) = (1 - (t : ℝ)) • a + (t : ℝ) • b := by
  change AffineMap.lineMap a b (t : ℝ) = _
  exact AffineMap.lineMap_apply_module _ _ _

theorem CuspHoneycombHexagon.vertex_injective : Function.Injective vertex := by
  intro i j hij
  apply ToricComponent.hexagonRay_injective
  funext k
  have h := congrFun hij k
  change (ToricComponent.hexagonRay i k : ℝ) = (ToricComponent.hexagonRay j k : ℝ) at h
  exact_mod_cast h

theorem CuspHoneycombHexagon.vertex_prev_ne (k : Fin 6) : vertex (k - 1) ≠ vertex k := by
  intro h
  exact (show ∀ k : Fin 6, k - 1 ≠ k by decide) k (vertex_injective h)

theorem CuspHoneycombHexagon.side_eq_segment (k : Fin 6) :
    side k = segment ℝ (vertex (k - 1)) (vertex k) := by
  have hpred :
    ∀ k : Fin 6,
      k - 1 =
        ![⟨5, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
            ⟨4, by decide⟩]
          k := by decide
  rw [hpred k, segment_eq_image]
  ext x
  constructor
  · rintro ⟨⟨h0, h1, h01⟩, hk⟩
    obtain ⟨h0l, h0u⟩ := abs_le.mp h0
    obtain ⟨h1l, h1u⟩ := abs_le.mp h1
    obtain ⟨h01l, h01u⟩ := abs_le.mp h01
    refine ⟨![x 1 + 1, x 1, -x 0, 1 - x 1, -x 1, x 0] k, ?_, ?_⟩
    · fin_cases k <;> norm_num [sideFunctional] at hk ⊢ <;> constructor <;> linarith
    · funext j
      fin_cases k <;> fin_cases j <;>
          norm_num [sideFunctional, vertex, ToricComponent.hexagonRay, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul] at hk ⊢ <;>
        linarith
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    fin_cases k <;>
          norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay,
            Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_le] <;>
        (repeat' constructor) <;>
      linarith

def CuspHoneycombHexagon.sideIntervalHomeomorph (k : Fin 6) : unitInterval ≃ₜ side k :=
  (segmentIntervalHomeomorph (vertex (k - 1)) (vertex k) (vertex_prev_ne k)).trans
    (Homeomorph.setCongr (side_eq_segment k).symm)

@[simp]
theorem CuspHoneycombHexagon.sideIntervalHomeomorph_apply (k : Fin 6) (t : unitInterval) :
    (sideIntervalHomeomorph k t : Plane) = (1 - (t : ℝ)) • vertex (k - 1) + (t : ℝ) • vertex k := by
  change (segmentIntervalHomeomorph (vertex (k - 1)) (vertex k) (vertex_prev_ne k) t : Plane) = _
  exact segmentIntervalHomeomorph_apply _ _ _ _

@[simp]
theorem CuspHoneycombHexagon.sideIntervalHomeomorph_one (k : Fin 6) :
    (sideIntervalHomeomorph k 1 : Plane) = vertex k := by simp

theorem CuspHoneycombHexagon.eq_vertex_of_consecutive_sideFunctional (k : Fin 6) (x : Plane)
    (h0 : sideFunctional k x = 1) (h1 : sideFunctional (k + 1) x = 1) : x = vertex k := by
  fin_cases k <;> ext l <;> fin_cases l <;>
      norm_num [sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def, Matrix.cons_val,
        Matrix.vecHead, Matrix.vecTail] at h0 h1 ⊢ <;>
    linarith

theorem CuspHoneycombHexagon.vertex_mem_side_self (k : Fin 6) : vertex k ∈ side k := by
  fin_cases k <;>
    norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]

theorem CuspHoneycombHexagon.vertex_mem_side_next (k : Fin 6) : vertex k ∈ side (k + 1) := by
  fin_cases k <;>
    norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]

theorem CuspHoneycombHexagon.side_inter_next (k : Fin 6) : side k ∩ side (k + 1) = {vertex k} := by
  ext x
  constructor
  · intro hx
    exact eq_vertex_of_consecutive_sideFunctional k x hx.1.2 hx.2.2
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨vertex_mem_side_self k, vertex_mem_side_next k⟩

theorem CuspHoneycombHexagon.side_disjoint_add_two (k : Fin 6) :
    Disjoint (side k) (side (k + 2)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨h0l, h0u⟩ := abs_le.mp hx.1.1
  obtain ⟨h1l, h1u⟩ := abs_le.mp hx.1.2.1
  obtain ⟨h01l, h01u⟩ := abs_le.mp hx.1.2.2
  have h0 := hx.2
  have h2 := hy.2
  fin_cases k <;>
      norm_num [sideFunctional, Fin.add_def, Matrix.cons_val, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h0 h2 <;>
    linarith only [h0, h2, h0l, h0u, h1l, h1u, h01l, h01u]

theorem CuspHoneycombHexagon.side_disjoint_add_three (k : Fin 6) :
    Disjoint (side k) (side (k + 3)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h0 := hx.2
  have h3 := hy.2
  fin_cases k <;>
      norm_num [sideFunctional, Fin.add_def, Matrix.cons_val, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] at h0 h3 <;>
    linarith only [h0, h3]

theorem CuspHoneycombHexagon.side_disjoint_add_four (k : Fin 6) :
    Disjoint (side k) (side (k + 4)) := by
  have hi : (k + 4) + 2 = k := by
    rw [add_assoc]
    change k + 0 = k
    exact add_zero k
  simpa only [hi] using (side_disjoint_add_two (k + 4)).symm

theorem CuspHoneycombHexagon.side_disjoint_nonadjacent {i j : Fin 6} (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) : Disjoint (side i) (side j) := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, j = i + k := ⟨j - i, by rw [add_comm i (j - i), sub_add_cancel]⟩
  fin_cases k
  · exact (hij (by change i = i + 0; simp)).elim
  · exact (hnext rfl).elim
  · change Disjoint (side i) (side (i + 2))
    exact side_disjoint_add_two i
  · change Disjoint (side i) (side (i + 3))
    exact side_disjoint_add_three i
  · change Disjoint (side i) (side (i + 4))
    exact side_disjoint_add_four i
  · apply False.elim
    apply hprev
    change i = (i + 5) + 1
    rw [add_assoc]
    change i = i + 0
    exact (add_zero i).symm

theorem CuspHoneycombTiling.standard_vertex_opposite (k : Fin 6) :
    CuspHoneycombHexagon.vertex (k + 3) = -CuspHoneycombHexagon.vertex k := by
  funext i
  change (ToricComponent.hexagonRay (k + 3) i : ℝ) = -(ToricComponent.hexagonRay k i : ℝ)
  rw [ToricComponent.hexagonRay_opposite]
  simp only [Pi.neg_apply, Int.cast_neg]

theorem CuspHoneycombTiling.dual_latticePoint_ray (k : Fin 6) :
    dualStandardLinearEquiv (latticePoint (ToricComponent.hexagonRay k)) =
      CuspHoneycombHexagon.vertex (k - 1) + CuspHoneycombHexagon.vertex k := by
  have h :
    ∀ k : Fin 6,
      ToricComponent.hexagonRay (k - 1) 0 + ToricComponent.hexagonRay k 0 =
          2 * ToricComponent.hexagonRay k 0 + ToricComponent.hexagonRay k 1 ∧
        ToricComponent.hexagonRay (k - 1) 1 + ToricComponent.hexagonRay k 1 =
          ToricComponent.hexagonRay k 1 - ToricComponent.hexagonRay k 0 := by decide
  funext i
  fin_cases i
  · change
      2 * (ToricComponent.hexagonRay k 0 : ℝ) + (ToricComponent.hexagonRay k 1 : ℝ) =
        (ToricComponent.hexagonRay (k - 1) 0 : ℝ) + (ToricComponent.hexagonRay k 0 : ℝ)
    exact_mod_cast (h k).1.symm
  · change
      (ToricComponent.hexagonRay k 1 : ℝ) - (ToricComponent.hexagonRay k 0 : ℝ) =
        (ToricComponent.hexagonRay (k - 1) 1 : ℝ) + (ToricComponent.hexagonRay k 1 : ℝ)
    exact_mod_cast (h k).2.symm

theorem CuspHoneycombTiling.dual_sideInterval_opposite (k : Fin 6) (t : unitInterval) :
    dualStandardPlaneHomeomorph.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
      dualStandardPlaneHomeomorph.symm (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) -
        latticePoint (ToricComponent.hexagonRay k) := by
  change
    dualStandardLinearEquiv.symm
        (CuspHoneycombHexagon.sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
      dualStandardLinearEquiv.symm (CuspHoneycombHexagon.sideIntervalHomeomorph k t : Plane) -
        latticePoint (ToricComponent.hexagonRay k)
  apply dualStandardLinearEquiv.injective
  simp only [map_sub, LinearEquiv.apply_symm_apply, dual_latticePoint_ray]
  have hidx : ∀ k : Fin 6, k + 3 - 1 = (k - 1) + 3 := by decide
  simp only [CuspHoneycombHexagon.sideIntervalHomeomorph_apply, unitInterval.coe_symm_eq, hidx,
    standard_vertex_opposite]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem CuspHoneycombTiling.sub_latticePoint_mem_cell_iff (v w : CuspHoneycombTiling.Lattice)
    (x : Plane) : x - latticePoint v ∈ cell w ↔ x ∈ cell (v + w) := by
  simp only [mem_cell, latticePoint_add, sub_sub]

def CuspHoneycombTiling.cellTranslationHomeomorph (v : CuspHoneycombTiling.Lattice) :
    baseCell ≃ₜ cell v
    where
  toFun
    x := ⟨(x : Plane) + latticePoint v, by simpa only [mem_cell, add_sub_cancel_right] using x.2⟩
  invFun y := ⟨(y : Plane) - latticePoint v, y.2⟩
  left_inv x := Subtype.ext (add_sub_cancel_right (x : Plane) (latticePoint v))
  right_inv y := Subtype.ext (sub_add_cancel (y : Plane) (latticePoint v))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

def CuspHoneycombTiling.cellShiftHomeomorph (v w : CuspHoneycombTiling.Lattice) :
    cell v ≃ₜ cell (v + w)
    where
  toFun x := ⟨(x : Plane) + latticePoint w, (add_latticePoint_mem_cell_iff v w x).mpr x.2⟩
  invFun
    y :=
    ⟨(y : Plane) - latticePoint w,
      (sub_latticePoint_mem_cell_iff w v y).mpr (by simpa only [add_comm w v] using y.2)⟩
  left_inv x := Subtype.ext (add_sub_cancel_right (x : Plane) (latticePoint w))
  right_inv y := Subtype.ext (sub_add_cancel (y : Plane) (latticePoint w))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

@[simp]
theorem CuspHoneycombTiling.cellShiftHomeomorph_coe (v w : CuspHoneycombTiling.Lattice)
    (x : cell v) : (cellShiftHomeomorph v w x : Plane) = (x : Plane) + latticePoint w :=
  rfl

theorem CuspHoneycombTiling.triangleBarycenter_shift (s : ToricFan.Triangle)
    (v : CuspHoneycombTiling.Lattice) :
    triangleBarycenter (s.shift v) = triangleBarycenter s + latticePoint v := by
  funext i
  simp only [triangleBarycenter, ToricFan.Triangle.vertex_shift, Pi.add_apply, Int.cast_add,
    latticePoint_apply]
  ring

abbrev ToricSpace.CompactFibreTorus :=
  Fin 2 → Circle

def ToricSpace.compactFibreUnits : CompactFibreTorus →* (Fin 2 → ℂˣ)
    where
  toFun u i := Circle.toUnits (u i)
  map_one' := by
    funext i
    exact Circle.toUnits.map_one
  map_mul' u
    v := by
    funext i
    exact Circle.toUnits.map_mul (u i) (v i)

def ToricSpace.compactFibrePhase (u : CompactFibreTorus) : CompactTorus :=
  ![u 0, u 1, 1]

theorem ToricSpace.compactFibrePhase_continuous : Continuous compactFibrePhase := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

theorem ToricSpace.compactTorusUnits_compactFibrePhase (u : CompactFibreTorus) :
    compactTorusUnits (compactFibrePhase u) = fibreMultiplier (compactFibreUnits u) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact Circle.toUnits.map_one

def ToricSpace.compactFibreAction (u : CompactFibreTorus) (x : Space) : Space :=
  torusAction (fibreMultiplier (compactFibreUnits u)) x

theorem ToricSpace.compactFibreAction_eq_compact (u : CompactFibreTorus) (x : Space) :
    compactFibreAction u x = compactTorusAction (compactFibrePhase u) x := by
  rw [compactTorusAction, compactTorusUnits_compactFibrePhase]
  rfl

@[simp]
theorem ToricSpace.compactFibreAction_one (x : Space) : compactFibreAction 1 x = x := by
  simp only [compactFibreAction, map_one, fibreMultiplier_one, torusAction_one]

theorem ToricSpace.compactFibreAction_mul (u v : CompactFibreTorus) (x : Space) :
    compactFibreAction u (compactFibreAction v x) = compactFibreAction (u * v) x := by
  simp only [compactFibreAction, map_mul, fibreMultiplier_mul, torusAction_mul]

instance ToricSpace.compactFibreMulAction : MulAction CompactFibreTorus Space
    where
  smul := compactFibreAction
  one_smul := compactFibreAction_one
  mul_smul u v x := (compactFibreAction_mul u v x).symm

theorem ToricSpace.compactFibreAction_continuous :
    Continuous (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) := by
  have h :=
    compactTorusAction_continuous.comp
      ((compactFibrePhase_continuous.comp continuous_fst).prodMk continuous_snd)
  exact h.congr (fun _ => (compactFibreAction_eq_compact _ _).symm)

instance ToricSpace.compactFibreContinuousSMul : ContinuousSMul CompactFibreTorus Space :=
  ⟨compactFibreAction_continuous⟩

@[simp]
theorem ToricSpace.time_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    time (compactFibreAction u x) = time x :=
  time_fibreMultiplier _ x

@[simp]
theorem ToricSpace.modulus_compactFibreAction (u : CompactFibreTorus) (x : Space) :
    modulus (compactFibreAction u x) = modulus x := by
  rw [compactFibreAction_eq_compact, modulus_compactTorusAction]

def ToricSpace.compactFibreActionShear : CompactFibreTorus × Space ≃ₜ CompactFibreTorus × Space
    where
  toFun p := (p.1, p.1 • p.2)
  invFun p := (p.1, p.1⁻¹ • p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk ContinuousSMul.continuous_smul
  continuous_invFun := continuous_fst.prodMk (continuous_fst.inv.smul continuous_snd)

theorem ToricSpace.compactFibreAction_isProperMap :
    IsProperMap (fun p : CompactFibreTorus × Space => compactFibreAction p.1 p.2) :=
  isProperMap_snd_of_compactSpace.comp compactFibreActionShear.isProperMap

theorem ToricSpace.torusAction_inclusion_eq_self_iff (u : ActingTorus) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    torusAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∀ i, z i ≠ 0 → factors s u i = 1 := by
  rw [torusAction_inclusion, (inclusion_openEmbedding s).injective.eq_iff]
  constructor
  · intro h i hi
    apply mul_right_cancel₀ hi
    simpa only [scale, Pi.mul_apply, one_mul] using congrFun h i
  · intro h
    funext i
    change factors s u i * z i = z i
    by_cases hi : z i = 0
    · simp only [hi, MulZeroClass.mul_zero]
    · rw [h i hi, one_mul]

theorem ToricSpace.compactTorusAction_inclusion_eq_self_iff (u : CompactTorus)
    (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    compactTorusAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∀ i, z i ≠ 0 → factors s (compactTorusUnits u) i = 1 :=
  torusAction_inclusion_eq_self_iff (compactTorusUnits u) s z

def ToricSpace.rayCompactPhase (v : Fin 2 → ℤ) (a : Circle) : CompactTorus :=
  ![a ^ v 0, a ^ v 1, a]

@[simp]
theorem ToricSpace.rayCompactPhase_two (v : Fin 2 → ℤ) (a : Circle) : rayCompactPhase v a 2 = a :=
  rfl

theorem ToricSpace.rayCompactPhase_vertex_coe (s : ToricFan.Triangle) (j : Fin 3) (a : Circle) :
    (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = fun i => (a : ℂ) ^ s.rays i j := by
  funext i
  fin_cases i <;> simp [rayCompactPhase, ToricFan.Triangle.vertex]

theorem ToricSpace.monomial_single_coordinate_phase (A : Matrix (Fin 3) (Fin 3) ℤ) (j : Fin 3)
    (a : ℂ) : ToricCharts.monomial A (fun k => if k = j then a else 1) = fun i => a ^ A i j := by
  funext i
  change (∏ k, (if k = j then a else 1) ^ A i k) = _
  calc
    (∏ k, (if k = j then a else 1) ^ A i k) = ∏ k, if k = j then a ^ A i k else 1 := by
      apply Finset.prod_congr rfl
      intro k _
      split_ifs <;> simp
    _ = a ^ A i j := by simp

theorem ToricSpace.factors_rayCompactPhase_vertex (s : ToricFan.Triangle) (j : Fin 3)
    (a : Circle) :
    factors s (compactTorusUnits (rayCompactPhase (s.vertex j) a)) = fun i =>
      if i = j then (a : ℂ) else 1 := by
  let w : ToricCharts.CoordinateSpace 3 := fun i => if i = j then (a : ℂ) else 1
  have hw : w ∈ ToricCharts.torus := by
    intro i
    dsimp [w]
    split_ifs
    · exact a.coe_ne_zero
    · exact one_ne_zero
  have hv : (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = ToricCharts.monomial s.rays w := by
    rw [rayCompactPhase_vertex_coe]
    exact (monomial_single_coordinate_phase s.rays j a).symm
  change ToricCharts.monomial s.dual (fun i => (rayCompactPhase (s.vertex j) a i : ℂ)) = _
  rw [hv, ToricCharts.monomial_mul_on_torus _ _ hw, ToricFan.Triangle.dual_rays,
    ToricCharts.monomial_one]

theorem ToricSpace.rayCompactPhase_fixes_of_mem_rayDivisor (v : Fin 2 → ℤ) (a : Circle)
    {x : Space} (hx : x ∈ rayDivisor v) : compactTorusAction (rayCompactPhase v a) x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨j, hj, rfl⟩ := (mem_rayDivisor_inclusion v s z).mp hx
  apply (compactTorusAction_inclusion_eq_self_iff _ s z).mpr
  intro i hi
  have hij : i ≠ j := by
    intro h
    subst i
    exact hi hj
  rw [factors_rayCompactPhase_vertex]
  exact if_neg hij

abbrev CuspPositiveRetraction.PositiveCentralFibre :=
  { q : ToricSpace.PositivePart // ToricSpace.time (q : ToricSpace.Space) = 0 }

def CuspPositiveRetraction.positiveCentralInclusion (η : ℝ) (hη : 0 ≤ η) :
    C(PositiveCentralFibre, ToricSpace.ClosedPositiveTube η)
    where
  toFun q := ⟨q.1, by rw [q.2, norm_zero]; exact hη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem CuspCollapse.exists_compactFibreAction_modulus {x : ToricSpace.Space}
    (hx : ToricSpace.time x = 0) :
    ∃ u : ToricSpace.CompactFibreTorus,
      ToricSpace.compactFibreAction u (ToricSpace.modulus x) = x := by
  obtain ⟨u, hu⟩ := ToricSpace.exists_compactTorusAction_modulus x
  have hzero : ToricSpace.time (ToricSpace.modulus x) = 0 := by
    simp only [ToricSpace.time_modulus, hx, norm_zero, Complex.ofReal_zero]
  obtain ⟨v, hv⟩ := (ToricSpace.branchVertices_nonempty (ToricSpace.modulus x)).mpr hzero
  let w : ToricSpace.CompactTorus := u * ToricSpace.rayCompactPhase v (u 2)⁻¹
  have hw : w 2 = 1 := by
    simp only [w, Pi.mul_apply, ToricSpace.rayCompactPhase_two, mul_inv_cancel]
  let uf : ToricSpace.CompactFibreTorus := ![w 0, w 1]
  have hf : ToricSpace.compactFibrePhase uf = w := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hw.symm
  refine ⟨uf, ?_⟩
  rw [ToricSpace.compactFibreAction_eq_compact, hf]
  change
    ToricSpace.compactTorusAction (u * ToricSpace.rayCompactPhase v (u 2)⁻¹)
        (ToricSpace.modulus x) =
      x
  rw [← ToricSpace.compactTorusAction_mul,
    ToricSpace.rayCompactPhase_fixes_of_mem_rayDivisor v (u 2)⁻¹ hv]
  exact hu

theorem CuspCollapse.positiveCentral_isClosed :
    IsClosed {q : ToricSpace.PositivePart | ToricSpace.time (q : ToricSpace.Space) = 0} :=
  isClosed_eq (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val)
    continuous_const

theorem CuspCollapse.positiveCentralVal_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (fun q : CuspPositiveRetraction.PositiveCentralFibre => (q.1 : ToricSpace.Space)) :=
  ToricSpace.positivePart_isClosed.isClosedEmbedding_subtypeVal.comp
    positiveCentral_isClosed.isClosedEmbedding_subtypeVal

def CuspCollapse.centralPolarMap
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    CuspRetraction.CentralFibre :=
  ⟨ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space), by
    rw [ToricSpace.time_compactFibreAction, p.2.2]⟩

@[simp]
theorem CuspCollapse.centralPolarMap_coe
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    (centralPolarMap p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space) :=
  rfl

theorem CuspCollapse.centralPolarMap_continuous : Continuous centralPolarMap :=
  (ToricSpace.compactFibreAction_continuous.comp
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))).subtype_mk
    _

@[simp]
theorem CuspCollapse.modulus_centralPolarMap
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    ToricSpace.modulus (centralPolarMap p : ToricSpace.Space) = (p.2.1 : ToricSpace.Space) := by
  rw [centralPolarMap_coe, ToricSpace.modulus_compactFibreAction]
  exact p.2.1.2

def CuspCollapse.centralModulus (x : CuspRetraction.CentralFibre) :
    CuspPositiveRetraction.PositiveCentralFibre :=
  ⟨ToricSpace.modulusRetraction x, by
    simp only [ToricSpace.modulusRetraction_coe, ToricSpace.time_modulus, x.2, norm_zero,
      Complex.ofReal_zero]⟩

@[simp]
theorem CuspCollapse.centralModulus_centralPolarMap
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    centralModulus (centralPolarMap p) = p.2 :=
  Subtype.ext (Subtype.ext (modulus_centralPolarMap p))

theorem CuspCollapse.centralPolarMap_surjective : Function.Surjective centralPolarMap := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactFibreAction_modulus x.2
  exact ⟨(u, centralModulus x), Subtype.ext hu⟩

theorem CuspCollapse.centralPolarMap_isProperMap : IsProperMap centralPolarMap := by
  have hinc :
    IsProperMap
      (fun p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre =>
        (p.1, (p.2.1 : ToricSpace.Space))) :=
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).isClosedEmbedding.prodMap
        positiveCentralVal_isClosedEmbedding).isProperMap
  have hcomp :
    IsProperMap
      ((Subtype.val : CuspRetraction.CentralFibre → ToricSpace.Space) ∘ centralPolarMap) :=
    ToricSpace.compactFibreAction_isProperMap.comp hinc
  exact
    isProperMap_of_comp_of_inj centralPolarMap_continuous continuous_subtype_val hcomp
      Subtype.val_injective

theorem CuspCollapse.centralPolarMap_isClosedMap : IsClosedMap centralPolarMap :=
  centralPolarMap_isProperMap.isClosedMap

theorem CuspCollapse.centralPolarMap_isQuotientMap : Topology.IsQuotientMap centralPolarMap :=
  centralPolarMap_isClosedMap.isQuotientMap centralPolarMap_continuous centralPolarMap_surjective

theorem CuspCollapse.centralPolarMap_eq_iff
    (p q : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    centralPolarMap p = centralPolarMap q ↔
      p.2 = q.2 ∧
        p.1⁻¹ * q.1 ∈
          MulAction.stabilizer ToricSpace.CompactFibreTorus (p.2.1 : ToricSpace.Space) := by
  rcases p with ⟨u, x⟩
  rcases q with ⟨v, y⟩
  constructor
  · intro h
    have hxy : x = y := by
      simpa only [centralModulus_centralPolarMap] using congrArg centralModulus h
    subst y
    refine ⟨rfl, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    have he : u • (x.1 : ToricSpace.Space) = v • (x.1 : ToricSpace.Space) :=
      congrArg Subtype.val h
    rw [SemigroupAction.mul_smul, ← he, inv_smul_smul]
  · rintro ⟨hxy, h⟩
    change x = y at hxy
    subst y
    have hs := congrArg (fun z : ToricSpace.Space => u • z) (MulAction.mem_stabilizer_iff.mp h)
    apply Subtype.ext
    change u • (x.1 : ToricSpace.Space) = v • (x.1 : ToricSpace.Space)
    simpa only [smul_smul, mul_inv_cancel_left] using hs.symm

def CuspCollapse.deckFibrePhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    ToricSpace.CompactFibreTorus := fun i => CuspPositive.frozenPhaseCoordinate C₀ v i

@[simp]
theorem CuspCollapse.deckFibrePhase_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    deckFibrePhase C₀ 0 = 1 := by
  funext i
  apply Circle.ext
  simp only [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_coe,
    ToricSpace.exponentialMultiplier_zero, Pi.one_apply, Units.val_one, one_div, inv_one,
    Circle.coe_one]

theorem CuspCollapse.deckFibrePhase_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ) :
    deckFibrePhase C₀ (v + w) = deckFibrePhase C₀ v * deckFibrePhase C₀ w := by
  funext i
  apply Circle.ext
  simp only [deckFibrePhase, CuspPositive.frozenPhaseCoordinate_coe, Pi.mul_apply, Circle.coe_mul]
  rw [ToricSpace.exponentialMultiplier_add, ToricSpace.exponentialMultiplier_add]
  simp only [Pi.mul_apply, Units.val_mul, div_mul_div_comm]

theorem CuspCollapse.phaseTransform_compactFibrePhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : ToricSpace.CompactFibreTorus) :
    CuspPositive.phaseTransform C₀ v (ToricSpace.compactFibrePhase u) =
      ToricSpace.compactFibrePhase (deckFibrePhase C₀ v * u) := by
  funext i
  fin_cases i <;>
    simp [CuspPositive.phaseTransform, CuspPositive.frozenPhase, ToricSpace.phaseShear,
      ToricSpace.compactFibrePhase, deckFibrePhase]

def CuspCollapse.positiveCentralTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) :
    CuspPositiveRetraction.PositiveCentralFibre :=
  ⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space),
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by rw [ToricSpace.time_twistedTranslate, q.2]⟩

@[simp]
theorem CuspCollapse.positiveCentralTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) :
    ((positiveCentralTranslate C₀ v q).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space) :=
  rfl

@[simp]
theorem CuspCollapse.positiveCentralTranslate_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) : positiveCentralTranslate C₀ 0 q = q :=
  Subtype.ext (Subtype.ext (ToricSpace.twistedTranslate_zero (CuspPositive.positiveTwist C₀) q.1))

theorem CuspCollapse.positiveCentralTranslate_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (q : CuspPositiveRetraction.PositiveCentralFibre) :
    positiveCentralTranslate C₀ v (positiveCentralTranslate C₀ w q) =
      positiveCentralTranslate C₀ (v + w) q :=
  Subtype.ext
    (Subtype.ext (ToricSpace.twistedTranslate_add (CuspPositive.positiveTwist C₀) v w q.1))

theorem CuspCollapse.positiveCentralTranslate_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : Continuous (positiveCentralTranslate C₀ v) :=
  (((ToricSpace.centralTranslationHomeomorph (CuspPositive.positiveTwist C₀) v).continuous.comp
            (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
        _).subtype_mk
    _

def CuspCollapse.positiveCentralHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    CuspPositiveRetraction.PositiveCentralFibre ≃ₜ CuspPositiveRetraction.PositiveCentralFibre
    where
  toFun := positiveCentralTranslate C₀ v
  invFun := positiveCentralTranslate C₀ (-v)
  left_inv
    q := by rw [positiveCentralTranslate_add, neg_add_cancel, positiveCentralTranslate_zero]
  right_inv
    q := by rw [positiveCentralTranslate_add, add_neg_cancel, positiveCentralTranslate_zero]
  continuous_toFun := positiveCentralTranslate_continuous C₀ v
  continuous_invFun := positiveCentralTranslate_continuous C₀ (-v)

def CuspCollapse.phaseDeckMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre :=
  (deckFibrePhase C₀ v * p.1, positiveCentralTranslate C₀ v p.2)

theorem CuspCollapse.twistedTranslate_central_eq_constant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) :
    ToricSpace.twistedTranslate C v x = ToricSpace.twistedTranslate (fun _ => C 0) v x := by
  simp only [ToricSpace.twistedTranslate, ToricSpace.variableMultiplier,
    ToricSpace.time_translate, hx]
  rfl

theorem CuspCollapse.centralPolarMap_phaseDeckMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ)
    (p : ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    (centralPolarMap (phaseDeckMap (C 0) v p) : ToricSpace.Space) =
      ToricSpace.twistedTranslate C v (centralPolarMap p : ToricSpace.Space) := by
  rw [twistedTranslate_central_eq_constant C v (centralPolarMap p).2]
  change
    ToricSpace.compactFibreAction (deckFibrePhase (C 0) v * p.1)
        ((positiveCentralTranslate (C 0) v p.2).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C 0) v
        (ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space))
  rw [ToricSpace.compactFibreAction_eq_compact, ToricSpace.compactFibreAction_eq_compact,
    CuspPositive.twistedTranslate_constant_polar, phaseTransform_compactFibrePhase]
  rfl

def CuspHoneycombHexagon.positiveComponentSet (v : Fin 2 → ℤ) : Set (ToricSpace.rayDivisor v) :=
  Subtype.val ⁻¹' ToricSpace.positivePart

abbrev CuspHoneycombHexagon.PositiveComponent (v : Fin 2 → ℤ) :=
  positiveComponentSet v

abbrev CuspHoneycombHexagon.PositiveE0 :=
  PositiveComponent 0

theorem CuspHoneycombHexagon.coordinateModulus_insertZero (j : Fin 3)
    (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.coordinateModulus (ToricComponent.insertZero j z) =
      ToricComponent.insertZero j (ToricCharts.coordinateModulus z) := by
  funext k
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simp [ToricCharts.coordinateModulus]
  · simp [ToricCharts.coordinateModulus, ToricComponent.insertZero, Fin.insertNth_apply_succAbove]

theorem CuspHoneycombHexagon.affineInclusion_mem_positive_iff {v : Fin 2 → ℤ}
    (c : ToricComponent.ChartIndex v) (z : ToricCharts.CoordinateSpace 2) :
    ToricComponent.affineInclusion c z ∈ positiveComponentSet v ↔
      z ∈ ToricCharts.nonnegativeCoordinates := by
  change
    ToricSpace.modulus
          (ToricSpace.inclusion c.triangle (ToricComponent.insertZero c.coordinate z)) =
        ToricSpace.inclusion c.triangle (ToricComponent.insertZero c.coordinate z) ↔
      _
  rw [ToricSpace.modulus_inclusion, coordinateModulus_insertZero,
    (ToricSpace.inclusion_openEmbedding c.triangle).injective.eq_iff, ←
    ToricCharts.coordinateModulus_eq_self_iff]
  constructor
  · intro h
    simpa only [ToricComponent.removeCoordinate_insertZero] using
      congrArg (ToricComponent.removeCoordinate c.coordinate) h
  · intro h
    exact congrArg (ToricComponent.insertZero c.coordinate) h

abbrev CuspHoneycombHexagon.PositiveQuadrant :=
  { r : Fin 2 → ℝ // ∀ i, 0 ≤ r i }

def CuspHoneycombHexagon.positiveAffineInclusion {v : Fin 2 → ℤ} (c : ToricComponent.ChartIndex v)
    (r : PositiveQuadrant) : PositiveComponent v :=
  ⟨ToricComponent.affineInclusion c (fun i => (r.1 i : ℂ)),
    (affineInclusion_mem_positive_iff c _).mpr ⟨r.1, r.2, rfl⟩⟩

theorem CuspHoneycombHexagon.twistedTranslate_zero_correction (v : Fin 2 → ℤ)
    (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate (fun _ => 0) v x =
      ToricSpace.translate (ToricSpace.cuspVector v) x := by
  have he : ToricSpace.exponentialMultiplier (fun _ => 0) v = fun _ => 1 := by
    funext t
    ext i
    simp [ToricSpace.exponentialMultiplier]
  simp [ToricSpace.twistedTranslate, he]

theorem CuspHoneycombHexagon.zeroComponent_bounded_chart (x : ToricSpace.rayDivisor 0) :
    ∃ (i : Fin 6) (z : ToricCharts.CoordinateSpace 2),
      ‖z‖ ≤ 1 ∧ ToricComponent.affineInclusion (ToricComponent.zeroChart i) z = x := by
  let C : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 0
  have hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 (1 : ℝ)) := fun _ _ =>
    contDiffOn_const
  obtain ⟨ε, hε, _, hε1, hR, hCε⟩ := CuspQuotient.exists_admissible_radius C (by norm_num) hC
  let a : ToricSpace.Tube (CuspQuotient.disc ε) := CuspQuotient.componentLift ε hε x
  have ha0 : ToricSpace.time (a : ToricSpace.Space) = 0 :=
    ToricSpace.time_eq_zero_of_mem_rayDivisor x.2
  have hrep :=
    CuspQuotient.mem_quotientRepresentatives C ε hε hε1 hCε hR (half_pos hε) (half_lt_self hε)
      (x := a)
      (by
        rw [ha0, norm_zero]
        exact (half_pos hε).le)
  obtain ⟨b, hb, hba⟩ := hrep
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  have horb := Quotient.exact hba
  change b ∈ MulAction.orbit CuspQuotient.LatticeGroup a at horb
  obtain ⟨g, hg⟩ := horb
  have hgb :
    ToricSpace.translate (ToricSpace.cuspVector g.toAdd) (x : ToricSpace.Space) =
      (b : ToricSpace.Space) := by
    have h := congrArg Subtype.val hg
    change
      ToricSpace.twistedTranslate C g.toAdd (x : ToricSpace.Space) = (b : ToricSpace.Space) at h
    rwa [show C = (fun _ => 0) from rfl, twistedTranslate_zero_correction] at h
  change (b : ToricSpace.Space) ∈ CuspQuotient.compactRepresentatives (ε / 2) at hb
  obtain ⟨s, _hs, z, hz, hzb⟩ := Set.mem_iUnion₂.mp hb
  have hx :
    ToricSpace.inclusion (s.shift (-ToricSpace.cuspVector g.toAdd)) z = (x : ToricSpace.Space) := by
    rw [← ToricSpace.translate_inclusion, hzb, ← hgb, ToricSpace.translate_add]
    simp
  obtain ⟨j, hj, hv⟩ := (ToricSpace.mem_rayDivisor_inclusion 0 _ z).mp (hx.symm ▸ x.2)
  let c : ToricComponent.ChartIndex 0 := ⟨s.shift (-ToricSpace.cuspVector g.toAdd), j, hv⟩
  obtain ⟨i, hi⟩ := ToricComponent.zeroChart_surjective c
  refine ⟨i, ToricComponent.removeCoordinate j z, ?_, ?_⟩
  · have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro k
    exact (norm_le_pi_norm z (j.succAbove k)).trans hz1
  · rw [hi]
    apply Subtype.ext
    change
      ToricSpace.inclusion (s.shift (-ToricSpace.cuspVector g.toAdd))
          (ToricComponent.insertZero j (ToricComponent.removeCoordinate j z)) =
        (x : ToricSpace.Space)
    rw [ToricComponent.insertZero_removeCoordinate j z hj]
    exact hx

theorem CuspHoneycombHexagon.positiveE0_bounded_chart (x : PositiveE0) :
    ∃ (i : Fin 6) (r : PositiveQuadrant),
      (∀ k, r.1 k ≤ 1) ∧ positiveAffineInclusion (ToricComponent.zeroChart i) r = x := by
  obtain ⟨i, z, hz, he⟩ := zeroComponent_bounded_chart x.1
  have hp :
    ToricComponent.affineInclusion (ToricComponent.zeroChart i) z ∈ positiveComponentSet 0 :=
    he.symm ▸ x.2
  obtain ⟨r, hr, hzr⟩ := (affineInclusion_mem_positive_iff (ToricComponent.zeroChart i) z).mp hp
  refine ⟨i, ⟨r, hr⟩, ?_, Subtype.ext ?_⟩
  · intro k
    have hk := (norm_le_pi_norm z k).trans hz
    rwa [hzr, Complex.norm_of_nonneg (hr k)] at hk
  · change ToricComponent.affineInclusion (ToricComponent.zeroChart i) (fun k => (r k : ℂ)) = x.1
    rw [← hzr]
    exact he

def ToricFan.edgeDirection : Fin 3 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![1, -1] ]

def ToricFan.AreAdjacent (v w : Fin 2 → ℤ) : Prop :=
  ∃ i : Fin 3, w - v = edgeDirection i ∨ w - v = -edgeDirection i

theorem ToricFan.Triangle.vertices_adjacent (s : ToricFan.Triangle) {j k : Fin 3} (hjk : j ≠ k) :
    ToricFan.AreAdjacent (s.vertex j) (s.vertex k) := by
  cases hs : s.upper <;> fin_cases j <;> fin_cases k <;>
    simp_all [ToricFan.AreAdjacent, vertex, rays, ToricFan.edgeDirection, funext_iff,
      Fin.exists_fin_succ, Fin.forall_fin_succ]

theorem ToricFan.Triangle.triangle_for_edge (v : Fin 2 → ℤ) (i : Fin 3) :
    ∃ s : ToricFan.Triangle,
      ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = v + ToricFan.edgeDirection i := by
  fin_cases i
  · refine ⟨⟨v 0, v 1, Bool.false⟩, 0, 1, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, ToricFan.edgeDirection]
  · refine ⟨⟨v 0, v 1, Bool.false⟩, 0, 2, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, ToricFan.edgeDirection]
  · refine ⟨⟨v 0, v 1 - 1, Bool.false⟩, 2, 1, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, ToricFan.edgeDirection, sub_eq_add_neg]

theorem ToricFan.Triangle.exists_triangle_of_adjacent {v w : Fin 2 → ℤ}
    (h : ToricFan.AreAdjacent v w) :
    ∃ s : ToricFan.Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = w := by
  obtain ⟨i, hi | hi⟩ := h
  · have hw : w = v + ToricFan.edgeDirection i := by
      exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
    obtain ⟨s, j, k, hj, hk⟩ := triangle_for_edge v i
    exact ⟨s, j, k, hj, hk.trans hw.symm⟩
  · have hv : v = w + ToricFan.edgeDirection i := by
      ext a
      have h := congrFun hi a
      change w a - v a = -ToricFan.edgeDirection i a at h
      change v a = w a + ToricFan.edgeDirection i a
      omega
    obtain ⟨s, j, k, hj, hk⟩ := triangle_for_edge w i
    exact ⟨s, k, j, hk.trans hv.symm, hj⟩

theorem ToricSpace.rayDivisor_inter_nonempty_iff_vertices (v w : Fin 2 → ℤ) :
    (rayDivisor v ∩ rayDivisor w).Nonempty ↔
      ∃ s : ToricFan.Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = w := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    obtain ⟨j, _, hj⟩ := (mem_rayDivisor_inclusion v s z).mp hxv
    obtain ⟨k, _, hk⟩ := (mem_rayDivisor_inclusion w s z).mp hxw
    exact ⟨s, j, k, hj, hk⟩
  · rintro ⟨s, j, k, rfl, rfl⟩
    exact
      ⟨ToricSpace.inclusion s 0, (mem_rayDivisor_vertex s j 0).mpr rfl,
        (mem_rayDivisor_vertex s k 0).mpr rfl⟩

theorem ToricSpace.rayDivisor_inter_nonempty_iff (v w : Fin 2 → ℤ) (hvw : v ≠ w) :
    (rayDivisor v ∩ rayDivisor w).Nonempty ↔ ToricFan.AreAdjacent v w := by
  rw [rayDivisor_inter_nonempty_iff_vertices]
  constructor
  · rintro ⟨s, j, k, rfl, rfl⟩
    exact ToricFan.Triangle.vertices_adjacent s (fun h => hvw (congrArg s.vertex h))
  · exact ToricFan.Triangle.exists_triangle_of_adjacent

def CuspHoneycombPositive.positiveCell (v : Fin 2 → ℤ) :
    Set CuspPositiveRetraction.PositiveCentralFibre :=
  {q | (q.1 : ToricSpace.Space) ∈ ToricSpace.rayDivisor v}

theorem CuspHoneycombPositive.positiveCell_isClosed (v : Fin 2 → ℤ) : IsClosed (positiveCell v) :=
  (ToricSpace.rayDivisor_isClosed v).preimage (continuous_subtype_val.comp continuous_subtype_val)

theorem CuspHoneycombPositive.positiveCells_locallyFinite : LocallyFinite positiveCell :=
  ToricSpace.rayDivisors_locallyFinite.preimage_continuous
    (continuous_subtype_val.comp continuous_subtype_val)

theorem CuspHoneycombPositive.iUnion_positiveCell :
    (⋃ v : Fin 2 → ℤ, positiveCell v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : (q.1 : ToricSpace.Space) ∈ ToricSpace.time ⁻¹' {0} := q.2
  rw [ToricSpace.central_fibre_eq_rayDivisors] at hq
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨v, hv⟩

def CuspHoneycombPositive.positiveCellComponentHomeomorph (v : Fin 2 → ℤ) :
    positiveCell v ≃ₜ CuspHoneycombHexagon.PositiveComponent v
    where
  toFun q := ⟨⟨q.1.1.1, q.2⟩, q.1.1.2⟩
  invFun x := ⟨⟨⟨x.1.1, x.2⟩, ToricSpace.time_eq_zero_of_mem_rayDivisor x.1.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

abbrev CuspHoneycombPositive.positiveCellZeroHomeomorph :
    positiveCell 0 ≃ₜ CuspHoneycombHexagon.PositiveE0 :=
  positiveCellComponentHomeomorph 0

theorem CuspHoneycombPositive.positiveCentralTranslate_mem_positiveCell
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℤ)
    (q : CuspPositiveRetraction.PositiveCentralFibre) :
    CuspCollapse.positiveCentralTranslate C₀ u q ∈ positiveCell v ↔
      q ∈ positiveCell (v - ToricSpace.cuspVector u) :=
  ToricSpace.twistedTranslate_mem_rayDivisor (CuspPositive.positiveTwist C₀) u v
    (q.1 : ToricSpace.Space)

def CuspHoneycombPositive.positiveE0CellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) : CuspHoneycombHexagon.PositiveE0 ≃ₜ positiveCell v :=
  positiveCellZeroHomeomorph.symm.trans
    ((CuspCollapse.positiveCentralHomeomorph C₀ (-ToricSpace.cuspVector v)).subtype
      (fun q =>
        by
        change
          q ∈ positiveCell 0 ↔
            CuspCollapse.positiveCentralTranslate C₀ (-ToricSpace.cuspVector v) q ∈ positiveCell v
        rw [positiveCentralTranslate_mem_positiveCell, ToricSpace.cuspVector_neg,
          ToricSpace.cuspVector_cuspVector, neg_neg, sub_self]))

def CuspHoneycombHexagon.orientedCoordinates (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.CoordinateSpace 2 :=
  if i = 1 ∨ i = 2 ∨ i = 3 then ![z 1, z 0] else z

@[simp]
theorem CuspHoneycombHexagon.orientedCoordinates_involutive (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) : orientedCoordinates i (orientedCoordinates i z) = z := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext j
    fin_cases j <;> simp [orientedCoordinates, hi]
  · simp [orientedCoordinates, hi]

theorem CuspHoneycombHexagon.orientedCoordinates_continuous (i : Fin 6) :
    Continuous (orientedCoordinates i) := by
  unfold orientedCoordinates
  split_ifs
  · apply continuous_pi
    intro j
    fin_cases j
    · exact continuous_apply 1
    · exact continuous_apply 0
  · exact continuous_id

def CuspHoneycombHexagon.orientedHomeomorph (i : Fin 6) :
    ToricCharts.CoordinateSpace 2 ≃ₜ ToricCharts.CoordinateSpace 2
    where
  toFun := orientedCoordinates i
  invFun := orientedCoordinates i
  left_inv := orientedCoordinates_involutive i
  right_inv := orientedCoordinates_involutive i
  continuous_toFun := orientedCoordinates_continuous i
  continuous_invFun := orientedCoordinates_continuous i

def CuspHoneycombHexagon.firstCoordinate : Fin 6 → Fin 3 :=
  ![1, 2, 2, 1, 0, 0]

def CuspHoneycombHexagon.secondCoordinate : Fin 6 → Fin 3 :=
  ![2, 1, 0, 0, 1, 2]

theorem CuspHoneycombHexagon.firstCoordinate_vertex (i : Fin 6) :
    (ToricComponent.zeroTriangle i).vertex (firstCoordinate i) = ToricComponent.hexagonRay i := by
  fin_cases i <;> decide

theorem CuspHoneycombHexagon.secondCoordinate_vertex (i : Fin 6) :
    (ToricComponent.zeroTriangle i).vertex (secondCoordinate i) =
      ToricComponent.hexagonRay (i + 1) := by fin_cases i <;> decide

theorem CuspHoneycombHexagon.coordinates_exhaustive (i : Fin 6) (j : Fin 3) :
    j = ToricComponent.zeroCoordinate i ∨ j = firstCoordinate i ∨ j = secondCoordinate i := by
  fin_cases i <;> fin_cases j <;> decide

def CuspHoneycombHexagon.liftCoordinates (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    ToricCharts.CoordinateSpace 3 :=
  ToricComponent.insertZero (ToricComponent.zeroCoordinate i) (orientedCoordinates i z)

@[simp]
theorem CuspHoneycombHexagon.liftCoordinates_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) :
    liftCoordinates i z (ToricComponent.zeroCoordinate i) = 0 :=
  ToricComponent.insertZero_at _ _

@[simp]
theorem CuspHoneycombHexagon.liftCoordinates_first (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) : liftCoordinates i z (firstCoordinate i) = z 0 := by
  fin_cases i <;> rfl

@[simp]
theorem CuspHoneycombHexagon.liftCoordinates_second (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) : liftCoordinates i z (secondCoordinate i) = z 1 := by
  fin_cases i <;> rfl

theorem CuspHoneycombHexagon.liftCoordinates_table (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) :
    liftCoordinates i z =
      ![![0, z 0, z 1], ![0, z 1, z 0], ![z 1, 0, z 0], ![z 1, z 0, 0], ![z 0, z 1, 0],
          ![z 0, 0, z 1] ]
        i := by fin_cases i <;> ext j <;> fin_cases j <;> rfl

theorem CuspHoneycombHexagon.liftCoordinates_vector (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] =
      ![![0, a, b], ![0, b, a], ![b, 0, a], ![b, a, 0], ![a, b, 0], ![a, 0, b] ] i :=
  liftCoordinates_table i ![a, b]

def CuspHoneycombHexagon.chartPoint (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    ToricSpace.rayDivisor 0 :=
  ToricComponent.affineInclusion (ToricComponent.zeroChart i) (orientedCoordinates i z)

@[simp]
theorem CuspHoneycombHexagon.chartPoint_coe (i : Fin 6) (z : ToricCharts.CoordinateSpace 2) :
    (chartPoint i z : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) (liftCoordinates i z) :=
  rfl

theorem CuspHoneycombHexagon.chartPoint_openEmbedding (i : Fin 6) :
    Topology.IsOpenEmbedding (chartPoint i) :=
  (ToricComponent.affineInclusion_openEmbedding (ToricComponent.zeroChart i)).comp
    (orientedHomeomorph i).isOpenEmbedding

theorem CuspHoneycombHexagon.chartPoint_injective (i : Fin 6) :
    Function.Injective (chartPoint i) :=
  (chartPoint_openEmbedding i).injective

theorem CuspHoneycombHexagon.chartPoint_continuous (i : Fin 6) : Continuous (chartPoint i) :=
  (chartPoint_openEmbedding i).continuous

theorem CuspHoneycombHexagon.chartPoint_jointly_surjective (x : ToricSpace.rayDivisor 0) :
    ∃ i z, chartPoint i z = x := by
  obtain ⟨c, z, hz⟩ := ToricComponent.affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := ToricComponent.zeroChart_surjective c
  refine ⟨i, orientedCoordinates i z, ?_⟩
  change
    ToricComponent.affineInclusion (ToricComponent.zeroChart i)
        (orientedCoordinates i (orientedCoordinates i z)) =
      x
  rw [orientedCoordinates_involutive]
  exact hz

theorem CuspHoneycombHexagon.chartPoint_eq_iff (i j : Fin 6)
    (z w : ToricCharts.CoordinateSpace 2) :
    chartPoint i z = chartPoint j w ↔
      liftCoordinates i z ∈
          (ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
              (ToricComponent.zeroTriangle j)).source ∧
        ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
            (ToricComponent.zeroTriangle j) (liftCoordinates i z) =
          liftCoordinates j w := by
  rw [Subtype.ext_iff, chartPoint_coe, chartPoint_coe, ToricSpace.inclusion_eq_iff]

theorem CuspHoneycombHexagon.chartPoint_mem_rayDivisor_iff (i k : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) :
    (chartPoint i z : ToricSpace.Space) ∈ ToricSpace.rayDivisor (ToricComponent.hexagonRay k) ↔
      (k = i ∧ z 0 = 0) ∨ (k = i + 1 ∧ z 1 = 0) := by
  rw [chartPoint_coe, ToricSpace.mem_rayDivisor_inclusion]
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases coordinates_exhaustive i j with rfl | rfl | rfl
    · exact
        (ToricComponent.hexagonRay_ne_zero k
            ((ToricComponent.zeroTriangle_vertex i).symm.trans hv).symm).elim
    · exact
        Or.inl
          ⟨(ToricComponent.hexagonRay_injective ((firstCoordinate_vertex i).symm.trans hv)).symm,
            by simpa only [liftCoordinates_first] using hj⟩
    · exact
        Or.inr
          ⟨(ToricComponent.hexagonRay_injective ((secondCoordinate_vertex i).symm.trans hv)).symm,
            by simpa only [liftCoordinates_second] using hj⟩
  · rintro (⟨hki, hz⟩ | ⟨hki, hz⟩)
    · subst k
      exact ⟨firstCoordinate i, (liftCoordinates_first i z).trans hz, firstCoordinate_vertex i⟩
    · subst k
      exact ⟨secondCoordinate i, (liftCoordinates_second i z).trans hz, secondCoordinate_vertex i⟩

def CuspHoneycombHexagon.nextTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![1, 1, 0; 0, -1, 0; 0, 1, 1], !![0, 0, -1; 1, 0, 1; 0, 1, 1],
    !![0, 0, -1; 1, 0, 1; 0, 1, 1], !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0], !![1, 1, 0; 1, 0, 1; -1, 0, 0] ]

theorem CuspHoneycombHexagon.transition_next (i : Fin 6) :
    ToricFan.Triangle.transition (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 1)) =
      nextTransitionMatrix i := by fin_cases i <;> decide

theorem CuspHoneycombHexagon.next_source_iff (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] ∈
        (ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
            (ToricComponent.zeroTriangle (i + 1))).source ↔
      a ≠ 0 := by
  rw [ToricFan.Triangle.chartChange_source, transition_next, liftCoordinates_vector]
  fin_cases i <;>
    norm_num [ToricCharts.domain, nextTransitionMatrix, Fin.forall_fin_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem CuspHoneycombHexagon.next_transition (i : Fin 6) (a b : ℂ) :
    ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 1)) (liftCoordinates i ![a, b]) =
      liftCoordinates (i + 1) ![a * b, a⁻¹] := by
  change ToricCharts.monomial (ToricFan.Triangle.transition _ _) _ = _
  rw [transition_next, liftCoordinates_vector, liftCoordinates_vector]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [ToricCharts.monomial, nextTransitionMatrix, Fin.prod_univ_succ, Fin.add_def,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
      Matrix.vecTail, mul_comm]

theorem CuspHoneycombHexagon.chartPoint_next (i : Fin 6) (a b : ℂ) (ha : a ≠ 0) :
    chartPoint (i + 1) ![a * b, a⁻¹] = chartPoint i ![a, b] := by
  symm
  exact
    (chartPoint_eq_iff i (i + 1) ![a, b] ![a * b, a⁻¹]).mpr
      ⟨(next_source_iff i a b).mpr ha, next_transition i a b⟩

theorem CuspHoneycombHexagon.chartPoint_eq_next_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 1) ![c, d] ↔ a ≠ 0 ∧ c = a * b ∧ d = a⁻¹ := by
  constructor
  · intro he
    have ha := (next_source_iff i a b).mp ((chartPoint_eq_iff i (i + 1) _ _).mp he).1
    have hw : ![c, d] = ![a * b, a⁻¹] :=
      chartPoint_injective (i + 1) (he.symm.trans (chartPoint_next i a b ha).symm)
    exact ⟨ha, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, rfl, rfl⟩
    exact (chartPoint_next i a b ha).symm

theorem CuspHoneycombHexagon.chartPoint_eq_nonadjacent_nonzero {i j : Fin 6}
    {z w : ToricCharts.CoordinateSpace 2} (hji : j ≠ i) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1)
    (he : chartPoint i z = chartPoint j w) : z 0 ≠ 0 ∧ z 1 ≠ 0 := by
  have hcoe : (chartPoint i z : ToricSpace.Space) = (chartPoint j w : ToricSpace.Space) :=
    congrArg Subtype.val he
  constructor
  · intro hz
    have hm :
      (chartPoint j w : ToricSpace.Space) ∈ ToricSpace.rayDivisor (ToricComponent.hexagonRay i) :=
      by
      rw [← hcoe]
      exact (chartPoint_mem_rayDivisor_iff i i z).mpr (Or.inl ⟨rfl, hz⟩)
    rcases (chartPoint_mem_rayDivisor_iff j i w).mp hm with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hji hi.symm
    · exact hprev hi
  · intro hz
    have hm :
      (chartPoint j w : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay (i + 1)) := by
      rw [← hcoe]
      exact (chartPoint_mem_rayDivisor_iff i (i + 1) z).mpr (Or.inr ⟨rfl, hz⟩)
    rcases (chartPoint_mem_rayDivisor_iff j (i + 1) w).mp hm with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact hnext hi.symm
    · exact hji (add_right_cancel hi).symm

def CuspHoneycombHexagon.previousTransitionMatrix : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![0, 0, -1; 1, 0, 1; 0, 1, 1], !![1, 1, 0; 0, -1, 0; 0, 1, 1],
    !![1, 1, 0; 1, 0, 1; -1, 0, 0], !![1, 1, 0; 1, 0, 1; -1, 0, 0],
    !![1, 1, 0; 0, -1, 0; 0, 1, 1], !![0, 0, -1; 1, 0, 1; 0, 1, 1] ]

theorem CuspHoneycombHexagon.transition_previous (i : Fin 6) :
    ToricFan.Triangle.transition (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 5)) =
      previousTransitionMatrix i := by fin_cases i <;> decide

theorem CuspHoneycombHexagon.previous_source_iff (i : Fin 6) (a b : ℂ) :
    liftCoordinates i ![a, b] ∈
        (ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
            (ToricComponent.zeroTriangle (i + 5))).source ↔
      b ≠ 0 := by
  rw [ToricFan.Triangle.chartChange_source, transition_previous, liftCoordinates_vector]
  fin_cases i <;>
    norm_num [ToricCharts.domain, previousTransitionMatrix, Fin.forall_fin_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
      Matrix.vecTail]

theorem CuspHoneycombHexagon.previous_transition (i : Fin 6) (a b : ℂ) :
    ToricFan.Triangle.chartChange (ToricComponent.zeroTriangle i)
        (ToricComponent.zeroTriangle (i + 5)) (liftCoordinates i ![a, b]) =
      liftCoordinates (i + 5) ![b⁻¹, a * b] := by
  change ToricCharts.monomial (ToricFan.Triangle.transition _ _) _ = _
  rw [transition_previous, liftCoordinates_vector, liftCoordinates_vector]
  fin_cases i <;> ext j <;> fin_cases j <;>
      norm_num [ToricCharts.monomial, previousTransitionMatrix, Fin.prod_univ_succ, Fin.add_def,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
        Matrix.vecTail, mul_comm] <;>
    rfl

theorem CuspHoneycombHexagon.chartPoint_previous (i : Fin 6) (a b : ℂ) (hb : b ≠ 0) :
    chartPoint (i + 5) ![b⁻¹, a * b] = chartPoint i ![a, b] := by
  symm
  exact
    (chartPoint_eq_iff i (i + 5) ![a, b] ![b⁻¹, a * b]).mpr
      ⟨(previous_source_iff i a b).mpr hb, previous_transition i a b⟩

theorem CuspHoneycombHexagon.chartPoint_eq_previous_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 5) ![c, d] ↔ b ≠ 0 ∧ c = b⁻¹ ∧ d = a * b := by
  constructor
  · intro he
    have hb := (previous_source_iff i a b).mp ((chartPoint_eq_iff i (i + 5) _ _).mp he).1
    have hw : ![c, d] = ![b⁻¹, a * b] :=
      chartPoint_injective (i + 5) (he.symm.trans (chartPoint_previous i a b hb).symm)
    exact ⟨hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨hb, rfl, rfl⟩
    exact (chartPoint_previous i a b hb).symm

theorem CuspHoneycombHexagon.chartPoint_offset_two (i : Fin 6) (a b : ℂ) (ha : a ≠ 0)
    (hb : b ≠ 0) : chartPoint (i + 2) ![b, (a * b)⁻¹] = chartPoint i ![a, b] := by
  have hi : (i + 1) + 1 = i + 2 := by rw [add_assoc]; rfl
  have hm : a * b * a⁻¹ = b := by rw [mul_right_comm, mul_inv_cancel₀ ha, one_mul]
  simpa only [hi, hm] using
    (chartPoint_next (i + 1) (a * b) a⁻¹ (mul_ne_zero ha hb)).trans (chartPoint_next i a b ha)

theorem CuspHoneycombHexagon.chartPoint_offset_three (i : Fin 6) (a b : ℂ) (ha : a ≠ 0)
    (hb : b ≠ 0) : chartPoint (i + 3) ![a⁻¹, b⁻¹] = chartPoint i ![a, b] := by
  have hi : (i + 2) + 1 = i + 3 := by rw [add_assoc]; rfl
  have hm : b * (a * b)⁻¹ = a⁻¹ := by simp [mul_inv_rev, hb]
  simpa only [hi, hm] using
    (chartPoint_next (i + 2) b (a * b)⁻¹ hb).trans (chartPoint_offset_two i a b ha hb)

theorem CuspHoneycombHexagon.chartPoint_offset_four (i : Fin 6) (a b : ℂ) (ha : a ≠ 0)
    (hb : b ≠ 0) : chartPoint (i + 4) ![(a * b)⁻¹, a] = chartPoint i ![a, b] := by
  have hi : (i + 3) + 1 = i + 4 := by rw [add_assoc]; rfl
  have hm : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by simp [mul_inv_rev, mul_comm]
  simpa only [hi, hm, inv_inv] using
    (chartPoint_next (i + 3) a⁻¹ b⁻¹ (inv_ne_zero ha)).trans (chartPoint_offset_three i a b ha hb)

theorem CuspHoneycombHexagon.chartPoint_eq_offset_two_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 2) ![c, d] ↔ a ≠ 0 ∧ b ≠ 0 ∧ c = b ∧ d = (a * b)⁻¹ := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ :=
      chartPoint_eq_nonadjacent_nonzero (by fin_cases i <;> decide : i + 2 ≠ i)
        (by fin_cases i <;> decide : i + 2 ≠ i + 1) (by fin_cases i <;> decide : i ≠ (i + 2) + 1)
        he
    have hw : ![c, d] = ![b, (a * b)⁻¹] :=
      chartPoint_injective (i + 2) (he.symm.trans (chartPoint_offset_two i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_two i a b ha hb).symm

theorem CuspHoneycombHexagon.chartPoint_eq_offset_three_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 3) ![c, d] ↔ a ≠ 0 ∧ b ≠ 0 ∧ c = a⁻¹ ∧ d = b⁻¹ := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ :=
      chartPoint_eq_nonadjacent_nonzero (by fin_cases i <;> decide : i + 3 ≠ i)
        (by fin_cases i <;> decide : i + 3 ≠ i + 1) (by fin_cases i <;> decide : i ≠ (i + 3) + 1)
        he
    have hw : ![c, d] = ![a⁻¹, b⁻¹] :=
      chartPoint_injective (i + 3) (he.symm.trans (chartPoint_offset_three i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_three i a b ha hb).symm

theorem CuspHoneycombHexagon.chartPoint_eq_offset_four_iff (i : Fin 6) (a b c d : ℂ) :
    chartPoint i ![a, b] = chartPoint (i + 4) ![c, d] ↔ a ≠ 0 ∧ b ≠ 0 ∧ c = (a * b)⁻¹ ∧ d = a := by
  constructor
  · intro he
    obtain ⟨ha, hb⟩ :=
      chartPoint_eq_nonadjacent_nonzero (by fin_cases i <;> decide : i + 4 ≠ i)
        (by fin_cases i <;> decide : i + 4 ≠ i + 1) (by fin_cases i <;> decide : i ≠ (i + 4) + 1)
        he
    have hw : ![c, d] = ![(a * b)⁻¹, a] :=
      chartPoint_injective (i + 4) (he.symm.trans (chartPoint_offset_four i a b ha hb).symm)
    exact ⟨ha, hb, congrFun hw 0, congrFun hw 1⟩
  · rintro ⟨ha, hb, hc, hd⟩
    subst c d
    exact (chartPoint_offset_four i a b ha hb).symm

theorem CuspHoneycombHexagon.unitSquare_mul_eq_one_iff {a b : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have hab : a * b ≤ a := mul_le_of_le_one_right ha.1 hb.2
    have hba : a * b ≤ b := mul_le_of_le_one_left hb.1 ha.2
    rw [h] at hab hba
    exact ⟨le_antisymm ha.2 hab, le_antisymm hb.2 hba⟩
  · rintro ⟨rfl, rfl⟩
    exact one_mul 1

theorem CuspHoneycombHexagon.unitSquare_inv_iff {a b : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) : ((a : ℂ) ≠ 0 ∧ (b : ℂ) = (a : ℂ)⁻¹) ↔ a = 1 ∧ b = 1 := by
  constructor
  · rintro ⟨ha0, hbInv⟩
    have hC : (a : ℂ) * (b : ℂ) = 1 := by rw [hbInv, mul_inv_cancel₀ ha0]
    apply (unitSquare_mul_eq_one_iff ha hb).mp
    exact_mod_cast hC
  · rintro ⟨rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.unitSquare_inv_mul_iff {a b c : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹) ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv⟩
    have hab : a * b ∈ Set.Icc 0 1 :=
      ⟨mul_nonneg ha.1 hb.1, (mul_le_of_le_one_right ha.1 hb.2).trans ha.2⟩
    have hmul : a * b = 1 ∧ c = 1 :=
      (unitSquare_inv_iff hab hc).mp
        ⟨by simpa only [Complex.ofReal_mul] using mul_ne_zero ha0 hb0, by
          simpa only [Complex.ofReal_mul] using hcInv⟩
    obtain ⟨ha1, hb1⟩ := (unitSquare_mul_eq_one_iff ha hb).mp hmul.1
    exact ⟨ha1, hb1, hmul.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.unitSquare_transition_one_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hd : d ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (c : ℂ) = (a : ℂ) * (b : ℂ) ∧ (d : ℂ) = (a : ℂ)⁻¹) ↔ a = 1 ∧ c = b ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hc, hdInv⟩
    obtain ⟨ha1, hd1⟩ := (unitSquare_inv_iff ha hd).mp ⟨ha0, hdInv⟩
    refine ⟨ha1, ?_, hd1⟩
    exact_mod_cast (show (c : ℂ) = (b : ℂ) by simpa [ha1] using hc)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.unitSquare_transition_two_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = (b : ℂ) ∧ (d : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hc, hdInv⟩
    obtain ⟨ha1, hb1, hd1⟩ := (unitSquare_inv_mul_iff ha hb hd).mp ⟨ha0, hb0, hdInv⟩
    refine ⟨ha1, hb1, ?_, hd1⟩
    exact_mod_cast (show (c : ℂ) = 1 by simpa [hb1] using hc)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.unitSquare_transition_three_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = (a : ℂ)⁻¹ ∧ (d : ℂ) = (b : ℂ)⁻¹) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv, hdInv⟩
    obtain ⟨ha1, hc1⟩ := (unitSquare_inv_iff ha hc).mp ⟨ha0, hcInv⟩
    obtain ⟨hb1, hd1⟩ := (unitSquare_inv_iff hb hd).mp ⟨hb0, hdInv⟩
    exact ⟨ha1, hb1, hc1, hd1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.unitSquare_transition_four_iff {a b c d : ℝ} (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    ((a : ℂ) ≠ 0 ∧ (b : ℂ) ≠ 0 ∧ (c : ℂ) = ((a : ℂ) * (b : ℂ))⁻¹ ∧ (d : ℂ) = (a : ℂ)) ↔
      a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 := by
  constructor
  · rintro ⟨ha0, hb0, hcInv, hd⟩
    obtain ⟨ha1, hb1, hc1⟩ := (unitSquare_inv_mul_iff ha hb hc).mp ⟨ha0, hb0, hcInv⟩
    refine ⟨ha1, hb1, hc1, ?_⟩
    exact_mod_cast (show (d : ℂ) = 1 by simpa [ha1] using hd)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.unitSquare_transition_five_iff {a b c d : ℝ} (hb : b ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) :
    ((b : ℂ) ≠ 0 ∧ (c : ℂ) = (b : ℂ)⁻¹ ∧ (d : ℂ) = (a : ℂ) * (b : ℂ)) ↔ b = 1 ∧ c = 1 ∧ d = a := by
  constructor
  · rintro ⟨hb0, hcInv, hd⟩
    obtain ⟨hb1, hc1⟩ := (unitSquare_inv_iff hb hc).mp ⟨hb0, hcInv⟩
    refine ⟨hb1, hc1, ?_⟩
    exact_mod_cast (show (d : ℂ) = (a : ℂ) by simpa [hb1] using hd)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem CuspHoneycombHexagon.squareComplexCoordinates_vector (p : Square) :
    (fun k : Fin 2 => (p.1 k : ℂ)) = ![(p.1 0 : ℂ), (p.1 1 : ℂ)] := by
  ext k
  fin_cases k <;> rfl

theorem CuspHoneycombHexagon.squareComplexCoordinates_injective :
    Function.Injective (fun p : Square => fun k : Fin 2 => (p.1 k : ℂ)) := by
  intro p q h
  apply Subtype.ext
  funext k
  exact Complex.ofReal_injective (congrFun h k)

theorem CuspHoneycombHexagon.chartPoint_square_eq_iff (i j : Fin 6) (p q : Square) :
    chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint j (fun k => (q.1 k : ℂ)) ↔
      SquareRel i j p q := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, j = i + k := ⟨j - i, by rw [add_comm i (j - i), sub_add_cancel]⟩
  fin_cases k
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 0) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 0) p q
    rw [add_zero, squareRel_self]
    exact ((chartPoint_injective i).comp squareComplexCoordinates_injective).eq_iff
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 1) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 1) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_next_iff, squareRel_next]
    simpa only [and_assoc, and_comm, and_left_comm] using
      (unitSquare_transition_one_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (q.2 1))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 2) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 2) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_two_iff, squareRel_add_two]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_two_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (p.2 1) (q.2 1))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 3) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 3) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_three_iff, squareRel_add_three]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_three_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (p.2 1) (q.2 0) (q.2 1))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 4) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 4) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_offset_four_iff, squareRel_add_four]
    simpa only [Fin.forall_fin_two, and_assoc] using
      (unitSquare_transition_four_iff (a := p.1 0) (b := p.1 1) (c := q.1 0) (d := q.1 1) (p.2 0)
        (p.2 1) (q.2 0))
  · change
      chartPoint i (fun k => (p.1 k : ℂ)) = chartPoint (i + 5) (fun k => (q.1 k : ℂ)) ↔
        SquareRel i (i + 5) p q
    rw [squareComplexCoordinates_vector p, squareComplexCoordinates_vector q,
      chartPoint_eq_previous_iff, squareRel_prev]
    exact unitSquare_transition_five_iff (p.2 1) (q.2 0)

def CuspQuotient.componentBoundary (v : Fin 2 → ℤ) : Set (ToricSpace.rayDivisor 0) :=
  {x | (x : ToricSpace.Space) ∈ ToricSpace.rayDivisor v}

def CuspHoneycombHexagon.orientedSquare (i : Fin 6) (p : Square) : Square :=
  if i = 1 ∨ i = 2 ∨ i = 3 then ⟨![p.1 1, p.1 0], by intro k; fin_cases k <;> exact p.2 _⟩ else p

@[simp]
theorem CuspHoneycombHexagon.orientedSquare_involutive (i : Fin 6) (p : Square) :
    orientedSquare i (orientedSquare i p) = p := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · apply Subtype.ext
    funext k
    fin_cases k <;> simp [orientedSquare, hi]
  · simp [orientedSquare, hi]

theorem CuspHoneycombHexagon.orientedCoordinates_square (i : Fin 6) (p : Square) :
    orientedCoordinates i (fun k => (p.1 k : ℂ)) = fun k => ((orientedSquare i p).1 k : ℂ) := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext k
    fin_cases k <;> simp [orientedSquare, orientedCoordinates, hi]
  · simp [orientedSquare, orientedCoordinates, hi]

def CuspHoneycombHexagon.squarePoint (i : Fin 6) (p : Square) : PositiveE0 :=
  ⟨chartPoint i (fun k => (p.1 k : ℂ)),
    by
    apply (affineInclusion_mem_positive_iff (ToricComponent.zeroChart i) _).mpr
    rw [orientedCoordinates_square]
    exact ⟨(orientedSquare i p).1, fun k => ((orientedSquare i p).2 k).1, rfl⟩⟩

@[simp]
theorem CuspHoneycombHexagon.squarePoint_coe (i : Fin 6) (p : Square) :
    (squarePoint i p : ToricSpace.rayDivisor 0) = chartPoint i (fun k => (p.1 k : ℂ)) :=
  rfl

theorem CuspHoneycombHexagon.squarePoint_continuous (i : Fin 6) : Continuous (squarePoint i) := by
  have h : Continuous (fun p : Square => fun k => (p.1 k : ℂ)) :=
    continuous_pi fun k =>
      Complex.continuous_ofReal.comp ((continuous_apply k).comp continuous_subtype_val)
  exact ((chartPoint_continuous i).comp h).subtype_mk _

theorem CuspHoneycombHexagon.squarePoint_eq_iff (i j : Fin 6) (p q : Square) :
    squarePoint i p = squarePoint j q ↔ SquareRel i j p q := by
  rw [← chartPoint_square_eq_iff]
  exact Subtype.ext_iff

theorem CuspHoneycombHexagon.squarePoint_jointly_surjective (x : PositiveE0) :
    ∃ (i : Fin 6) (p : Square), squarePoint i p = x := by
  obtain ⟨i, r, hr, he⟩ := positiveE0_bounded_chart x
  let p : Square := ⟨r.1, fun k => ⟨r.2 k, hr k⟩⟩
  refine ⟨i, orientedSquare i p, Subtype.ext ?_⟩
  change
    ToricComponent.affineInclusion (ToricComponent.zeroChart i)
        (orientedCoordinates i (fun k => ((orientedSquare i p).1 k : ℂ))) =
      x.1
  rw [orientedCoordinates_square, orientedSquare_involutive]
  exact congrArg Subtype.val he

abbrev CuspHoneycombHexagon.TileSpace :=
  Fin 6 × Square

def CuspHoneycombHexagon.squareProjection (p : TileSpace) : PositiveE0 :=
  squarePoint p.1 p.2

theorem CuspHoneycombHexagon.squareProjection_continuous : Continuous squareProjection :=
  continuous_prod_of_discrete_left.mpr squarePoint_continuous

theorem CuspHoneycombHexagon.squareProjection_surjective : Function.Surjective squareProjection :=
  by
  intro x
  obtain ⟨i, p, hp⟩ := squarePoint_jointly_surjective x
  exact ⟨(i, p), hp⟩

def CuspHoneycombHexagon.positiveBoundary (k : Fin 6) : Set PositiveE0 :=
  Subtype.val ⁻¹' CuspQuotient.componentBoundary (ToricComponent.hexagonRay k)

theorem CuspHoneycombHexagon.squarePoint_mem_positiveBoundary_iff (i k : Fin 6) (p : Square) :
    squarePoint i p ∈ positiveBoundary k ↔ (k = i ∧ p.1 0 = 0) ∨ (k = i + 1 ∧ p.1 1 = 0) := by
  change
    (chartPoint i (fun j => (p.1 j : ℂ)) : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay k) ↔
      _
  rw [chartPoint_mem_rayDivisor_iff]
  simp

def CuspHoneycombHexagon.polygonProjection (p : TileSpace) : Hexagon :=
  ⟨tile p.1 p.2, tile_mem_hexagon p.1 p.2⟩

theorem CuspHoneycombHexagon.polygonProjection_continuous : Continuous polygonProjection :=
  (continuous_prod_of_discrete_left.mpr tile_continuous).subtype_mk _

theorem CuspHoneycombHexagon.polygonProjection_surjective :
    Function.Surjective polygonProjection := by
  intro x
  obtain ⟨i, p, hp⟩ := tile_jointly_surjective x
  exact ⟨(i, p), Subtype.ext hp⟩

theorem CuspHoneycombHexagon.squareProjection_eq_iff_polygonProjection_eq (a b : TileSpace) :
    squareProjection a = squareProjection b ↔ polygonProjection a = polygonProjection b := by
  change squarePoint a.1 a.2 = squarePoint b.1 b.2 ↔ _
  rw [squarePoint_eq_iff, Subtype.ext_iff]
  exact (tile_eq_iff a.1 b.1 a.2 b.2).symm

def CuspHoneycombHexagon.positiveE0HexagonHomeomorph : PositiveE0 ≃ₜ Hexagon :=
  CommonFibres.homeomorph squareProjection polygonProjection squareProjection_surjective
    squareProjection_continuous polygonProjection_continuous polygonProjection_surjective
    squareProjection_eq_iff_polygonProjection_eq

@[simp]
theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_squarePoint (i : Fin 6) (p : Square) :
    (positiveE0HexagonHomeomorph (squarePoint i p) : Plane) = tile i p := by
  exact
    congrArg Subtype.val
      (CommonFibres.homeomorph_apply squareProjection polygonProjection
        squareProjection_surjective squareProjection_continuous polygonProjection_continuous
        polygonProjection_surjective squareProjection_eq_iff_polygonProjection_eq (i, p))

@[simp]
theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_cornerZero (i : Fin 6) :
    (positiveE0HexagonHomeomorph (squarePoint i cornerZero) : Plane) = vertex i := by simp

@[simp]
theorem CuspHoneycombHexagon.squarePoint_cornerZero_coe (i : Fin 6) :
    ((squarePoint i cornerZero : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  rw [squarePoint_coe, chartPoint_coe]
  congr 1
  ext k
  rcases coordinates_exhaustive i k with rfl | rfl | rfl <;> simp [cornerZero]

theorem CuspHoneycombHexagon.squarePoint_cornerZero_mem_positiveBoundary_iff (i k : Fin 6) :
    squarePoint i cornerZero ∈ positiveBoundary k ↔ k = i ∨ k = i + 1 := by
  rw [squarePoint_mem_positiveBoundary_iff]
  simp [cornerZero]

theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_mem_side_iff (x : PositiveE0)
    (k : Fin 6) : (positiveE0HexagonHomeomorph x : Plane) ∈ side k ↔ x ∈ positiveBoundary k := by
  obtain ⟨i, p, rfl⟩ := squarePoint_jointly_surjective x
  rw [positiveE0HexagonHomeomorph_squarePoint, tile_mem_side_iff,
    squarePoint_mem_positiveBoundary_iff]

theorem CuspHoneycombHexagon.positiveE0HexagonHomeomorph_mem_boundary_iff (x : PositiveE0) :
    (positiveE0HexagonHomeomorph x : Plane) ∈ ⋃ k, side k ↔ x ∈ ⋃ k, positiveBoundary k := by
  simp only [Set.mem_iUnion]
  exact exists_congr (fun k => positiveE0HexagonHomeomorph_mem_side_iff x k)

def CuspHoneycombHexagon.positiveBoundaryHexagonHomeomorph (k : Fin 6) :
    positiveBoundary k ≃ₜ side k
    where
  toFun
    x :=
    ⟨(positiveE0HexagonHomeomorph x.1 : Plane),
      (positiveE0HexagonHomeomorph_mem_side_iff x.1 k).mpr x.2⟩
  invFun
    y :=
    ⟨positiveE0HexagonHomeomorph.symm ⟨y.1, y.2.1⟩,
      by
      apply (positiveE0HexagonHomeomorph_mem_side_iff _ k).mp
      simpa only [Homeomorph.apply_symm_apply] using y.2⟩
  left_inv x := Subtype.ext (positiveE0HexagonHomeomorph.symm_apply_apply x.1)
  right_inv
    y := by
    apply Subtype.ext
    change
      (positiveE0HexagonHomeomorph (positiveE0HexagonHomeomorph.symm ⟨y.1, y.2.1⟩) : Plane) = y.1
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun :=
    (continuous_subtype_val.comp
          (positiveE0HexagonHomeomorph.continuous.comp continuous_subtype_val)).subtype_mk
      _
  continuous_invFun :=
    (positiveE0HexagonHomeomorph.symm.continuous.comp
          (continuous_subtype_val.subtype_mk _)).subtype_mk
      _

theorem CuspHoneycombHexagon.sideFunctional_continuous (k : Fin 6) :
    Continuous (sideFunctional k) := by fin_cases k <;> unfold sideFunctional <;> fun_prop

theorem CuspHoneycombHexagon.sideFunctional_add (k : Fin 6) (x y : Plane) :
    sideFunctional k (x + y) = sideFunctional k x + sideFunctional k y := by
  fin_cases k <;> simp [sideFunctional] <;> ring

theorem CuspHoneycombHexagon.sideFunctional_smul (k : Fin 6) (a : ℝ) (x : Plane) :
    sideFunctional k (a • x) = a * sideFunctional k x := by
  fin_cases k <;> simp [sideFunctional] <;> ring

theorem CuspHoneycombHexagon.mem_hexagon_iff_sideFunctional_le (x : Plane) :
    x ∈ Hexagon ↔ ∀ k : Fin 6, sideFunctional k x ≤ 1 := by
  constructor
  · rintro ⟨hx, hy, hxy⟩ k
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    have hxy' := abs_le.mp hxy
    fin_cases k
    · exact hx'.2
    · exact hxy'.2
    · exact hy'.2
    · change -x 0 ≤ 1
      linarith [hx'.1]
    · change -x 0 - x 1 ≤ 1
      linarith [hxy'.1]
    · change -x 1 ≤ 1
      linarith [hy'.1]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    simp only [sideFunctional_zero, sideFunctional_one, sideFunctional_two, sideFunctional_three,
      sideFunctional_four, sideFunctional_five] at h0 h1 h2 h3 h4 h5
    exact
      ⟨abs_le.mpr ⟨by linarith, h0⟩, abs_le.mpr ⟨by linarith, h2⟩, abs_le.mpr ⟨by linarith, h1⟩⟩

theorem CuspHoneycombHexagon.hexagon_convex : Convex ℝ Hexagon := by
  intro x hx y hy a b ha hb hab
  apply (mem_hexagon_iff_sideFunctional_le _).mpr
  intro k
  rw [sideFunctional_add, sideFunctional_smul, sideFunctional_smul]
  calc
    a * sideFunctional k x + b * sideFunctional k y ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left ((mem_hexagon_iff_sideFunctional_le x).mp hx k) ha)
        (mul_le_mul_of_nonneg_left ((mem_hexagon_iff_sideFunctional_le y).mp hy k) hb)
    _ = 1 := by simpa only [mul_one] using hab

theorem CuspHoneycombHexagon.hexagon_isClosed : IsClosed Hexagon := by
  have he : Hexagon = ⋂ k : Fin 6, {x | sideFunctional k x ≤ 1} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_hexagon_iff_sideFunctional_le]
  rw [he]
  exact isClosed_iInter fun k => isClosed_le (sideFunctional_continuous k) continuous_const

theorem CuspHoneycombHexagon.hexagon_subset_closedBall :
    Hexagon ⊆ Metric.closedBall (0 : Plane) 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  intro i
  fin_cases i
  · exact hx.1
  · exact hx.2.1

theorem CuspHoneycombHexagon.hexagon_isCompact : IsCompact Hexagon :=
  (ProperSpace.isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hexagon_isClosed
    hexagon_subset_closedBall

theorem CuspHoneycombHexagon.hexagon_isBounded : Bornology.IsBounded Hexagon :=
  hexagon_isCompact.isBounded

theorem CuspHoneycombHexagon.ball_half_subset_hexagon :
    Metric.ball (0 : Plane) (1 / 2) ⊆ Hexagon := by
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have h0 : |x 0| ≤ ‖x‖ := norm_le_pi_norm x 0
  have h1 : |x 1| ≤ ‖x‖ := norm_le_pi_norm x 1
  have hsum := abs_add_le (x 0) (x 1)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem CuspHoneycombHexagon.hexagon_mem_nhds_zero : Hexagon ∈ 𝓝 (0 : Plane) :=
  Filter.mem_of_superset (Metric.ball_mem_nhds _ (by norm_num)) ball_half_subset_hexagon

theorem CuspHoneycombHexagon.zero_mem_interior_hexagon : (0 : Plane) ∈ interior Hexagon :=
  mem_interior_iff_mem_nhds.mpr hexagon_mem_nhds_zero

theorem CuspHoneycombHexagon.hexagon_interior_nonempty : (interior Hexagon).Nonempty :=
  ⟨0, zero_mem_interior_hexagon⟩

theorem CuspHoneycombHexagon.mem_interior_hexagon_iff (x : Plane) :
    x ∈ interior Hexagon ↔ ∀ k : Fin 6, sideFunctional k x < 1 := by
  constructor
  · intro hx k
    have hle := (mem_hexagon_iff_sideFunctional_le x).mp (interior_subset hx) k
    apply lt_of_le_of_ne hle
    intro heq
    have hopen : IsOpen ((fun a : ℝ => a • x) ⁻¹' interior Hexagon) :=
      isOpen_interior.preimage (continuous_id.smul continuous_const)
    have hone : (1 : ℝ) ∈ (fun a : ℝ => a • x) ⁻¹' interior Hexagon := by
      simpa only [Set.mem_preimage, one_smul] using hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    have ha : (1 + δ / 2) • x ∈ interior Hexagon :=
      hball
        (by
          change Dist.dist (1 + δ / 2) (1 : ℝ) < δ
          rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
          exact half_lt_self hδ)
    have hb := (mem_hexagon_iff_sideFunctional_le _).mp (interior_subset ha) k
    rw [sideFunctional_smul, heq, mul_one] at hb
    linarith
  · intro hx
    let U : Set Plane := ⋂ k : Fin 6, {y | sideFunctional k y < 1}
    have hU : IsOpen U :=
      isOpen_iInter_of_finite fun k => isOpen_lt (sideFunctional_continuous k) continuous_const
    have hxU : x ∈ U := Set.mem_iInter.mpr hx
    have hUK : U ⊆ Hexagon := by
      intro y hy
      apply (mem_hexagon_iff_sideFunctional_le y).mpr
      intro k
      exact (Set.mem_iInter.mp hy k).le
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hU.mem_nhds hxU) hUK)

theorem CuspHoneycombHexagon.frontier_hexagon : frontier Hexagon = ⋃ k : Fin 6, side k := by
  ext x
  rw [frontier, hexagon_isClosed.closure_eq, Set.mem_sdiff, mem_interior_hexagon_iff,
    Set.mem_iUnion]
  constructor
  · rintro ⟨hx, hn⟩
    push Not at hn
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, hx, le_antisymm ((mem_hexagon_iff_sideFunctional_le x).mp hx k) hk⟩
  · rintro ⟨k, hx, hk⟩
    exact ⟨hx, fun h => (h k).ne hk⟩

abbrev CuspHoneycombRadial.UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  Metric.sphere (0 : E) (1 : ℝ)

@[simp]
theorem CuspHoneycombRadial.unitSphere_norm {E : Type*} [NormedAddCommGroup E]
    (x : UnitSphere E) : ‖(x : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

theorem CuspHoneycombRadial.unitSphere_ne_zero {E : Type*} [NormedAddCommGroup E]
    (x : UnitSphere E) : (x : E) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [unitSphere_norm]; exact one_ne_zero)

def CuspHoneycombRadial.direction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : { x : E // x ≠ 0 }) : UnitSphere E :=
  ⟨NormedSpace.normalize x.1, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize x.2)⟩

theorem CuspHoneycombRadial.direction_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (direction (E := E)) := by
  apply Continuous.subtype_mk
  exact
    (continuous_subtype_val.norm.inv₀
          (fun x : { x : E // x ≠ 0 } => norm_ne_zero_iff.mpr x.2)).smul
      continuous_subtype_val

theorem CuspHoneycombRadial.norm_smul_direction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : { x : E // x ≠ 0 }) : ‖x.1‖ • (direction x : E) = x.1 :=
  NormedSpace.norm_smul_normalize x.1

theorem CuspHoneycombRadial.direction_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : UnitSphere E) (hx : (x : E) ≠ 0) : direction ⟨(x : E), hx⟩ = x :=
  Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (unitSphere_norm x))

private def CuspHoneycombRadial.radialOffZero_mo1973_11510 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : { x : E // x ≠ 0 }) : E :=
  ‖x.1‖ • (e (direction x) : E)

private theorem CuspHoneycombRadial.radialOffZero_continuous_mo1973_11511 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) :
    Continuous (radialOffZero_mo1973_11510 e) :=
  continuous_subtype_val.norm.smul
    (continuous_subtype_val.comp (e.continuous.comp direction_continuous))

def CuspHoneycombRadial.radialMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : E := by
  classical exact if hx : x = 0 then 0 else radialOffZero_mo1973_11510 e ⟨x, hx⟩

@[simp]
theorem CuspHoneycombRadial.radialMap_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) : radialMap e (0 : E) = 0 := by simp [radialMap]

theorem CuspHoneycombRadial.radialMap_apply_of_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) {x : E} (hx : x ≠ 0) :
    radialMap e x = ‖x‖ • (e (direction ⟨x, hx⟩) : E) := by
  simp only [radialMap, dif_neg hx, radialOffZero_mo1973_11510]

@[simp]
theorem CuspHoneycombRadial.radialMap_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : ‖radialMap e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp only [hx, radialMap_zero]
  · rw [radialMap_apply_of_ne_zero e hx, norm_smul, norm_norm, unitSphere_norm, mul_one]

@[simp]
theorem CuspHoneycombRadial.radialMap_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : radialMap e x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← radialMap_norm e x, h, norm_zero]
  · rintro rfl
    exact radialMap_zero e

theorem CuspHoneycombRadial.radialMap_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) {x : E} (hx : x ≠ 0) : radialMap e x ≠ 0 := fun h =>
  hx ((radialMap_eq_zero_iff e x).mp h)

theorem CuspHoneycombRadial.direction_radialMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) {x : E} (hx : x ≠ 0) :
    direction ⟨radialMap e x, radialMap_ne_zero e hx⟩ = e (direction ⟨x, hx⟩) := by
  apply Subtype.ext
  change ‖radialMap e x‖⁻¹ • radialMap e x = (e (direction ⟨x, hx⟩) : E)
  rw [radialMap_norm, radialMap_apply_of_ne_zero e hx, smul_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem CuspHoneycombRadial.radialMap_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : UnitSphere E) : radialMap e (x : E) = (e x : E) := by
  rw [radialMap_apply_of_ne_zero e (unitSphere_ne_zero x), unitSphere_norm, direction_sphere,
    one_smul]

theorem CuspHoneycombRadial.radialMap_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : radialMap e.symm (radialMap e x) = x := by
  by_cases hx : x = 0
  · simp only [hx, radialMap_zero]
  · rw [radialMap_apply_of_ne_zero e.symm (radialMap_ne_zero e hx), radialMap_norm,
      direction_radialMap e hx, e.symm_apply_apply]
    exact norm_smul_direction ⟨x, hx⟩

theorem CuspHoneycombRadial.radialMap_continuousAt_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) : ContinuousAt (radialMap e) (0 : E) := by
  change Filter.Tendsto (radialMap e) (𝓝 (0 : E)) (𝓝 (radialMap e 0))
  rw [radialMap_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h : Filter.Tendsto (fun x : E => ‖x‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : E))
  simpa only [radialMap_norm] using h

theorem CuspHoneycombRadial.radialMap_continuousOn_nonzero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) :
    ContinuousOn (radialMap e) {x : E | x ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact
    (radialOffZero_continuous_mo1973_11511 e).congr
      (fun x : { x : E // x ≠ 0 } => (radialMap_apply_of_ne_zero e x.2).symm)

theorem CuspHoneycombRadial.radialMap_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) : Continuous (radialMap e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact radialMap_continuousAt_zero e
  · exact
      (radialMap_continuousOn_nonzero e).continuousAt
        ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)

def CuspHoneycombRadial.radialHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : UnitSphere E ≃ₜ UnitSphere E) : E ≃ₜ E
    where
  toFun := radialMap e
  invFun := radialMap e.symm
  left_inv := radialMap_symm e
  right_inv := radialMap_symm e.symm
  continuous_toFun := radialMap_continuous e
  continuous_invFun := radialMap_continuous e.symm

@[simp]
theorem CuspHoneycombRadial.radialHomeomorph_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : E) : ‖radialHomeomorph e x‖ = ‖x‖ :=
  radialMap_norm e x

theorem CuspHoneycombRadial.radialHomeomorph_sphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : UnitSphere E ≃ₜ UnitSphere E) (x : UnitSphere E) :
    radialHomeomorph e (x : E) = (e x : E) :=
  radialMap_sphere e x

private theorem CuspHoneycombRadial.homeomorph_mem_image_iff_mo1973_11532 {E : Type*}
    [NormedAddCommGroup E] (H : E ≃ₜ E) {S T : Set E} (hST : H '' S = T) (x : E) :
    x ∈ S ↔ H x ∈ T := by
  rw [← hST]
  exact H.injective.mem_set_image.symm

private theorem CuspHoneycombRadial.homeomorph_image_eq_of_mem_iff_mo1973_11533 {E : Type*}
    [NormedAddCommGroup E] (F : E ≃ₜ E) {K : Set E} (hmem : ∀ x, F x ∈ K ↔ x ∈ K) : F '' K = K := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro y hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    apply (hmem (F.symm y)).mp
    rwa [F.apply_symm_apply]

theorem CuspHoneycombRadial.exists_homeomorph_extending_frontier {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K)
    (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) :
    ∃ F : E ≃ₜ E, F '' K = K ∧ ∀ x : frontier K, F (x : E) = (e x : E) := by
  obtain ⟨H, _hinterior, hclosure, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbounded
  have hK : H '' K = Metric.closedBall (0 : E) 1 := by
    simpa only [hclosed.closure_eq] using hclosure
  let HB : frontier K ≃ₜ UnitSphere E :=
    H.subtype (homeomorph_mem_image_iff_mo1973_11532 H hfrontier)
  let eS : UnitSphere E ≃ₜ UnitSphere E := HB.symm.trans (e.trans HB)
  let F : E ≃ₜ E := H.trans ((radialHomeomorph eS).trans H.symm)
  have hmemF (x : E) : F x ∈ K ↔ x ∈ K := by
    rw [homeomorph_mem_image_iff_mo1973_11532 H hK (F x),
      homeomorph_mem_image_iff_mo1973_11532 H hK x]
    change
      H (H.symm (radialHomeomorph eS (H x))) ∈ Metric.closedBall (0 : E) 1 ↔
        H x ∈ Metric.closedBall (0 : E) 1
    rw [H.apply_symm_apply]
    simp only [Metric.mem_closedBall, dist_zero_right, radialHomeomorph_norm]
  refine ⟨F, homeomorph_image_eq_of_mem_iff_mo1973_11533 F hmemF, ?_⟩
  intro x
  change H.symm (radialHomeomorph eS (HB x : E)) = (e x : E)
  rw [radialHomeomorph_sphere]
  change H.symm (HB (e (HB.symm (HB x))) : E) = (e x : E)
  rw [HB.symm_apply_apply]
  exact H.symm_apply_apply (e x : E)

def CuspHoneycombRadial.boundaryExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K)
    (hne : (interior K).Nonempty) (e : frontier K ≃ₜ frontier K) : E ≃ₜ E :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose

theorem CuspHoneycombRadial.boundaryExtension_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) : boundaryExtension hconv hclosed hbounded hne e '' K = K :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose_spec.1

theorem CuspHoneycombRadial.boundaryExtension_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) (x : frontier K) :
    boundaryExtension hconv hclosed hbounded hne e (x : E) = (e x : E) :=
  (exists_homeomorph_extending_frontier hconv hclosed hbounded hne e).choose_spec.2 x

def CuspHoneycombRadial.boundarySetExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbounded : Bornology.IsBounded K)
    (hne : (interior K).Nonempty) (e : frontier K ≃ₜ frontier K) : K ≃ₜ K :=
  (boundaryExtension hconv hclosed hbounded hne e).subtype
    (homeomorph_mem_image_iff_mo1973_11532 _
      (boundaryExtension_image hconv hclosed hbounded hne e))

theorem CuspHoneycombRadial.boundarySetExtension_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hconv : Convex ℝ K) (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) (hne : (interior K).Nonempty)
    (e : frontier K ≃ₜ frontier K) (x : frontier K) :
    (boundarySetExtension hconv hclosed hbounded hne e ⟨(x : E), hclosed.frontier_subset x.2⟩ :
        E) =
      (e x : E) :=
  boundaryExtension_frontier hconv hclosed hbounded hne e x

abbrev CuspHoneycombHexagon.PositiveE0Boundary :=
  (⋃ k : Fin 6, positiveBoundary k)

def CuspHoneycombHexagon.positiveE0BoundaryHexagonHomeomorph :
    PositiveE0Boundary ≃ₜ frontier Hexagon
    where
  toFun
    x :=
    ⟨(positiveE0HexagonHomeomorph x.1 : Plane),
      by
      rw [frontier_hexagon]
      exact (positiveE0HexagonHomeomorph_mem_boundary_iff x.1).mpr x.2⟩
  invFun
    y :=
    ⟨positiveE0HexagonHomeomorph.symm ⟨y.1, hexagon_isClosed.frontier_subset y.2⟩,
      by
      apply (positiveE0HexagonHomeomorph_mem_boundary_iff _).mp
      simpa only [Homeomorph.apply_symm_apply, ← frontier_hexagon] using y.2⟩
  left_inv x := Subtype.ext (positiveE0HexagonHomeomorph.symm_apply_apply x.1)
  right_inv
    y := by
    apply Subtype.ext
    change
      (positiveE0HexagonHomeomorph
            (positiveE0HexagonHomeomorph.symm ⟨y.1, hexagon_isClosed.frontier_subset y.2⟩) :
          Plane) =
        y.1
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      continuous_subtype_val.comp
        (positiveE0HexagonHomeomorph.continuous.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact positiveE0HexagonHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)

@[simp]
theorem CuspHoneycombHexagon.positiveE0BoundaryHexagonHomeomorph_coe (x : PositiveE0Boundary) :
    (positiveE0BoundaryHexagonHomeomorph x : Plane) = (positiveE0HexagonHomeomorph x.1 : Plane) :=
  rfl

def CuspHoneycombHexagon.polygonBoundaryConjugate (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) :
    frontier Hexagon ≃ₜ frontier Hexagon :=
  positiveE0BoundaryHexagonHomeomorph.symm.trans (b.trans positiveE0BoundaryHexagonHomeomorph)

@[simp]
theorem CuspHoneycombHexagon.polygonBoundaryConjugate_apply
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) (x : PositiveE0Boundary) :
    polygonBoundaryConjugate b (positiveE0BoundaryHexagonHomeomorph x) =
      positiveE0BoundaryHexagonHomeomorph (b x) := by
  change
    positiveE0BoundaryHexagonHomeomorph
        (b (positiveE0BoundaryHexagonHomeomorph.symm (positiveE0BoundaryHexagonHomeomorph x))) =
      _
  rw [Homeomorph.symm_apply_apply]

def CuspHoneycombHexagon.positiveE0BoundaryExtension
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) : PositiveE0 ≃ₜ PositiveE0 :=
  positiveE0HexagonHomeomorph.trans
    ((CuspHoneycombRadial.boundarySetExtension hexagon_convex hexagon_isClosed hexagon_isBounded
          hexagon_interior_nonempty (polygonBoundaryConjugate b)).trans
      positiveE0HexagonHomeomorph.symm)

theorem CuspHoneycombHexagon.positiveE0BoundaryExtension_boundary
    (b : PositiveE0Boundary ≃ₜ PositiveE0Boundary) (x : PositiveE0Boundary) :
    positiveE0BoundaryExtension b (x : PositiveE0) = (b x : PositiveE0) := by
  apply positiveE0HexagonHomeomorph.injective
  change
    positiveE0HexagonHomeomorph
        (positiveE0HexagonHomeomorph.symm
          (CuspHoneycombRadial.boundarySetExtension hexagon_convex hexagon_isClosed
            hexagon_isBounded hexagon_interior_nonempty (polygonBoundaryConjugate b)
            (positiveE0HexagonHomeomorph x.1))) =
      _
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  have h :=
    CuspHoneycombRadial.boundarySetExtension_frontier hexagon_convex hexagon_isClosed
      hexagon_isBounded hexagon_interior_nonempty (polygonBoundaryConjugate b)
      (positiveE0BoundaryHexagonHomeomorph x)
  simpa only [polygonBoundaryConjugate_apply, positiveE0BoundaryHexagonHomeomorph_coe] using h

def CuspHoneycombHexagon.positiveBoundaryArc (k : Fin 6) : unitInterval ≃ₜ positiveBoundary k :=
  (sideIntervalHomeomorph k).trans (positiveBoundaryHexagonHomeomorph k).symm

@[simp]
theorem CuspHoneycombHexagon.positiveBoundaryArc_hexagon (k : Fin 6) (t : unitInterval) :
    (positiveE0HexagonHomeomorph (positiveBoundaryArc k t).1 : Plane) =
      (1 - (t : ℝ)) • vertex (k - 1) + (t : ℝ) • vertex k := by
  change
    (positiveBoundaryHexagonHomeomorph k
          ((positiveBoundaryHexagonHomeomorph k).symm (sideIntervalHomeomorph k t)) :
        Plane) =
      _
  rw [Homeomorph.apply_symm_apply]
  exact sideIntervalHomeomorph_apply k t

@[simp]
theorem CuspHoneycombHexagon.positiveBoundaryArc_zero (k : Fin 6) :
    (positiveBoundaryArc k 0).1 = squarePoint (k - 1) cornerZero := by
  apply positiveE0HexagonHomeomorph.injective
  apply Subtype.ext
  rw [positiveBoundaryArc_hexagon, positiveE0HexagonHomeomorph_cornerZero]
  simp

@[simp]
theorem CuspHoneycombHexagon.positiveBoundaryArc_one (k : Fin 6) :
    (positiveBoundaryArc k 1).1 = squarePoint k cornerZero := by
  apply positiveE0HexagonHomeomorph.injective
  apply Subtype.ext
  rw [positiveBoundaryArc_hexagon, positiveE0HexagonHomeomorph_cornerZero]
  simp

@[simp]
theorem CuspHoneycombHexagon.positiveBoundaryArc_zero_coe (k : Fin 6) :
    (((positiveBoundaryArc k 0).1 : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0 := by
  rw [positiveBoundaryArc_zero, squarePoint_cornerZero_coe]

@[simp]
theorem CuspHoneycombHexagon.positiveBoundaryArc_one_coe (k : Fin 6) :
    (((positiveBoundaryArc k 1).1 : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 := by
  rw [positiveBoundaryArc_one, squarePoint_cornerZero_coe]

theorem CuspHoneycombHexagon.positiveBoundaryArc_next_endpoint (k : Fin 6) :
    (positiveBoundaryArc k 1).1 = (positiveBoundaryArc (k + 1) 0).1 := by
  rw [positiveBoundaryArc_one, positiveBoundaryArc_zero, add_sub_cancel_right]

theorem CuspHoneycombHexagon.positiveBoundary_inter_next (k : Fin 6) :
    positiveBoundary k ∩ positiveBoundary (k + 1) = {squarePoint k cornerZero} := by
  ext x
  constructor
  · intro hx
    have hy : (positiveE0HexagonHomeomorph x : Plane) ∈ side k ∩ side (k + 1) :=
      ⟨(positiveE0HexagonHomeomorph_mem_side_iff x k).mpr hx.1,
        (positiveE0HexagonHomeomorph_mem_side_iff x (k + 1)).mpr hx.2⟩
    rw [side_inter_next, Set.mem_singleton_iff] at hy
    change x = squarePoint k cornerZero
    apply positiveE0HexagonHomeomorph.injective
    apply Subtype.ext
    exact hy.trans (positiveE0HexagonHomeomorph_cornerZero k).symm
  · intro hx
    have hx' : x = squarePoint k cornerZero := hx
    subst x
    exact
      ⟨(squarePoint_cornerZero_mem_positiveBoundary_iff k k).mpr (Or.inl rfl),
        (squarePoint_cornerZero_mem_positiveBoundary_iff k (k + 1)).mpr (Or.inr rfl)⟩

theorem CuspHoneycombHexagon.positiveBoundary_disjoint_nonadjacent {i j : Fin 6} (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    Disjoint (positiveBoundary i) (positiveBoundary j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact
    Set.disjoint_left.mp (side_disjoint_nonadjacent hij hnext hprev)
      ((positiveE0HexagonHomeomorph_mem_side_iff x i).mpr hx)
      ((positiveE0HexagonHomeomorph_mem_side_iff x j).mpr hy)

def CuspHoneycombHexagon.boundaryArcInclusion (k : Fin 6) (x : positiveBoundary k) :
    (⋃ j : Fin 6, positiveBoundary j) :=
  ⟨x.1, Set.mem_iUnion.mpr ⟨k, x.2⟩⟩

theorem CuspHoneycombHexagon.boundaryArcInclusion_continuous (k : Fin 6) :
    Continuous (boundaryArcInclusion k) :=
  continuous_subtype_val.subtype_mk _

def CuspHoneycombHexagon.boundaryArcProjection
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) (p : Fin 6 × unitInterval) :
    (⋃ j : Fin 6, positiveBoundary j) :=
  boundaryArcInclusion p.1 (P p.1 p.2)

theorem CuspHoneycombHexagon.boundaryArcProjection_continuous
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    Continuous (boundaryArcProjection P) :=
  continuous_prod_of_discrete_left.mpr
    (fun k => (boundaryArcInclusion_continuous k).comp (P k).continuous)

theorem CuspHoneycombHexagon.boundaryArcProjection_surjective
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) :
    Function.Surjective (boundaryArcProjection P) := by
  intro x
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp x.2
  obtain ⟨t, ht⟩ := (P k).surjective ⟨x.1, hk⟩
  refine ⟨(k, t), ?_⟩
  apply Subtype.ext
  change (P k t).1 = x.1
  exact congrArg (fun y : positiveBoundary k => y.1) ht

theorem CuspHoneycombHexagon.boundaryArcFamily_eq_self_iff
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) (i : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P i u).1 ↔ t = u := by
  constructor
  · intro h
    exact (P i).injective (Subtype.ext h)
  · rintro rfl
    rfl

theorem CuspHoneycombHexagon.boundaryArcFamily_eq_next_iff
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1) (i : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P (i + 1) u).1 ↔ t = 1 ∧ u = 0 := by
  constructor
  · intro h
    have hm : (P i t).1 ∈ positiveBoundary i ∩ positiveBoundary (i + 1) := by
      refine ⟨(P i t).2, ?_⟩
      rw [h]
      exact (P (i + 1) u).2
    have hx : (P i t).1 = squarePoint i cornerZero := by
      simpa only [positiveBoundary_inter_next, Set.mem_singleton_iff] using hm
    constructor
    · apply (P i).injective
      apply Subtype.ext
      rw [hP1 i, positiveBoundaryArc_one]
      exact hx
    · apply (P (i + 1)).injective
      apply Subtype.ext
      rw [hP0 (i + 1), positiveBoundaryArc_zero, add_sub_cancel_right]
      exact h.symm.trans hx
  · rintro ⟨rfl, rfl⟩
    rw [hP1 i, hP0 (i + 1)]
    exact positiveBoundaryArc_next_endpoint i

theorem CuspHoneycombHexagon.boundaryArcFamily_ne_nonadjacent
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k) {i j : Fin 6} (hij : i ≠ j)
    (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) (t u : unitInterval) : (P i t).1 ≠ (P j u).1 := by
  intro h
  apply Set.disjoint_left.mp (positiveBoundary_disjoint_nonadjacent hij hnext hprev) (P i t).2
  rw [h]
  exact (P j u).2

theorem CuspHoneycombHexagon.boundaryArcFamilies_sameFibres
    (P Q : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (hQ0 : ∀ k, (Q k 0).1 = (positiveBoundaryArc k 0).1)
    (hQ1 : ∀ k, (Q k 1).1 = (positiveBoundaryArc k 1).1) (i j : Fin 6) (t u : unitInterval) :
    (P i t).1 = (P j u).1 ↔ (Q i t).1 = (Q j u).1 := by
  by_cases hij : i = j
  · subst j
    rw [boundaryArcFamily_eq_self_iff, boundaryArcFamily_eq_self_iff]
  by_cases hnext : j = i + 1
  · subst j
    rw [boundaryArcFamily_eq_next_iff P hP0 hP1, boundaryArcFamily_eq_next_iff Q hQ0 hQ1]
  by_cases hprev : i = j + 1
  · subst i
    rw [eq_comm (a := (P (j + 1) t).1), eq_comm (a := (Q (j + 1) t).1),
      boundaryArcFamily_eq_next_iff P hP0 hP1, boundaryArcFamily_eq_next_iff Q hQ0 hQ1]
  exact
    iff_of_false (boundaryArcFamily_ne_nonadjacent P hij hnext hprev t u)
      (boundaryArcFamily_ne_nonadjacent Q hij hnext hprev t u)

theorem CuspHoneycombHexagon.boundaryArcProjection_sameFibres
    (P Q : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1)
    (hQ0 : ∀ k, (Q k 0).1 = (positiveBoundaryArc k 0).1)
    (hQ1 : ∀ k, (Q k 1).1 = (positiveBoundaryArc k 1).1) (a b : Fin 6 × unitInterval) :
    boundaryArcProjection P a = boundaryArcProjection P b ↔
      boundaryArcProjection Q a = boundaryArcProjection Q b := by
  have h := boundaryArcFamilies_sameFibres P Q hP0 hP1 hQ0 hQ1 a.1 b.1 a.2 b.2
  constructor
  · intro hab
    apply Subtype.ext
    exact h.mp (congrArg Subtype.val hab)
  · intro hab
    apply Subtype.ext
    exact h.mpr (congrArg Subtype.val hab)

def CuspHoneycombHexagon.boundaryGluingHomeomorph
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1) :
    (⋃ k : Fin 6, positiveBoundary k) ≃ₜ (⋃ k : Fin 6, positiveBoundary k) :=
  CommonFibres.homeomorph (boundaryArcProjection positiveBoundaryArc) (boundaryArcProjection P)
    (boundaryArcProjection_surjective positiveBoundaryArc)
    (boundaryArcProjection_continuous positiveBoundaryArc) (boundaryArcProjection_continuous P)
    (boundaryArcProjection_surjective P)
    (boundaryArcProjection_sameFibres positiveBoundaryArc P (fun _ => rfl) (fun _ => rfl) hP0 hP1)

@[simp]
theorem CuspHoneycombHexagon.boundaryGluingHomeomorph_apply
    (P : ∀ k : Fin 6, unitInterval ≃ₜ positiveBoundary k)
    (hP0 : ∀ k, (P k 0).1 = (positiveBoundaryArc k 0).1)
    (hP1 : ∀ k, (P k 1).1 = (positiveBoundaryArc k 1).1) (k : Fin 6) (t : unitInterval) :
    boundaryGluingHomeomorph P hP0 hP1 (boundaryArcInclusion k (positiveBoundaryArc k t)) =
      boundaryArcInclusion k (P k t) :=
  CommonFibres.homeomorph_apply (boundaryArcProjection positiveBoundaryArc)
    (boundaryArcProjection P) (boundaryArcProjection_surjective positiveBoundaryArc)
    (boundaryArcProjection_continuous positiveBoundaryArc) (boundaryArcProjection_continuous P)
    (boundaryArcProjection_surjective P)
    (boundaryArcProjection_sameFibres positiveBoundaryArc P (fun _ => rfl) (fun _ => rfl) hP0 hP1)
    (k, t)

noncomputable def CuspHoneycombHexagon.oppositePositiveBoundaryMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (x : positiveBoundary k) : positiveBoundary (k + 3) :=
  ⟨⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space),
        by
        rw [ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_cuspVector]
        simp only [zero_sub, neg_neg]
        exact x.2⟩,
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) x.1.2⟩,
    by
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay (k + 3))
    rw [ToricComponent.hexagonRay_opposite, ToricSpace.twistedTranslate_mem_rayDivisor,
      ToricSpace.cuspVector_cuspVector, sub_self]
    exact x.1.1.2⟩

private noncomputable def CuspHoneycombHexagon.oppositePositiveBoundaryInv_mo1973_11577
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (y : positiveBoundary (k + 3)) :
    positiveBoundary k :=
  ⟨⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (y.1.1 : ToricSpace.Space),
        by
        rw [ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_neg,
          ToricSpace.cuspVector_cuspVector, neg_neg, zero_sub, ←
          ToricComponent.hexagonRay_opposite]
        exact y.2⟩,
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀
        (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) y.1.2⟩,
    by
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (y.1.1 : ToricSpace.Space) ∈
        ToricSpace.rayDivisor (ToricComponent.hexagonRay k)
    rw [ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_neg,
      ToricSpace.cuspVector_cuspVector, neg_neg, sub_self]
    exact y.1.1.2⟩

noncomputable def CuspHoneycombHexagon.oppositePositiveBoundaryHomeomorph
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) : positiveBoundary k ≃ₜ positiveBoundary (k + 3)
    where
  toFun := oppositePositiveBoundaryMap C₀ k
  invFun := oppositePositiveBoundaryInv_mo1973_11577 C₀ k
  left_inv
    x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (-ToricSpace.cuspVector (ToricComponent.hexagonRay k))
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
            (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space)) =
        (x.1.1 : ToricSpace.Space)
    rw [ToricSpace.twistedTranslate_add, neg_add_cancel, ToricSpace.twistedTranslate_zero]
  right_inv
    y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
          (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
            (-ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (y.1.1 : ToricSpace.Space)) =
        (y.1.1 : ToricSpace.Space)
    rw [ToricSpace.twistedTranslate_add, add_neg_cancel, ToricSpace.twistedTranslate_zero]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (ToricSpace.centralTranslationHomeomorph (CuspPositive.positiveTwist C₀)
            (ToricSpace.cuspVector (ToricComponent.hexagonRay k))).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact
      (ToricSpace.centralTranslationHomeomorph (CuspPositive.positiveTwist C₀)
            (-ToricSpace.cuspVector (ToricComponent.hexagonRay k))).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem CuspHoneycombHexagon.oppositePositiveBoundaryHomeomorph_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ k x).1.1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (x.1.1 : ToricSpace.Space) :=
  rfl

theorem CuspHoneycombHexagon.zeroTriangle_shift_opposite_previous (k : Fin 6) :
    (ToricComponent.zeroTriangle (k - 1)).shift (-ToricComponent.hexagonRay k) =
      ToricComponent.zeroTriangle (k + 3) := by fin_cases k <;> decide

theorem CuspHoneycombHexagon.zeroTriangle_shift_opposite_current (k : Fin 6) :
    (ToricComponent.zeroTriangle k).shift (-ToricComponent.hexagonRay k) =
      ToricComponent.zeroTriangle (k + 2) := by fin_cases k <;> decide

theorem CuspHoneycombHexagon.opposite_twistedTranslate_origin_previous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    ToricSpace.twistedTranslate C (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        (ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k + 3)) 0 := by
  rw [ToricSpace.twistedTranslate_origin, ToricSpace.cuspVector_cuspVector,
    zeroTriangle_shift_opposite_previous]

theorem CuspHoneycombHexagon.opposite_twistedTranslate_origin_current
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    ToricSpace.twistedTranslate C (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        (ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k + 2)) 0 := by
  rw [ToricSpace.twistedTranslate_origin, ToricSpace.cuspVector_cuspVector,
    zeroTriangle_shift_opposite_current]

noncomputable def CuspHoneycombHexagon.reversedOppositeBoundaryArc (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : unitInterval ≃ₜ positiveBoundary (k + 3) :=
  unitInterval.symmHomeomorph.trans
    ((positiveBoundaryArc k).trans (oppositePositiveBoundaryHomeomorph C₀ k))

theorem CuspHoneycombHexagon.reversedOppositeBoundaryArc_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : reversedOppositeBoundaryArc C₀ k 0 = positiveBoundaryArc (k + 3) 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change
    ((oppositePositiveBoundaryHomeomorph C₀ k (positiveBoundaryArc k (unitInterval.symm 0))).1.1 :
        ToricSpace.Space) =
      ((positiveBoundaryArc (k + 3) 0).1.1 : ToricSpace.Space)
  rw [unitInterval.symm_zero, oppositePositiveBoundaryHomeomorph_coe, positiveBoundaryArc_one_coe,
    opposite_twistedTranslate_origin_current, positiveBoundaryArc_zero_coe]
  have hi : (k + 3) - 1 = k + 2 := by fin_cases k <;> decide
  rw [hi]

theorem CuspHoneycombHexagon.reversedOppositeBoundaryArc_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : reversedOppositeBoundaryArc C₀ k 1 = positiveBoundaryArc (k + 3) 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change
    ((oppositePositiveBoundaryHomeomorph C₀ k (positiveBoundaryArc k (unitInterval.symm 1))).1.1 :
        ToricSpace.Space) =
      ((positiveBoundaryArc (k + 3) 1).1.1 : ToricSpace.Space)
  rw [unitInterval.symm_one, oppositePositiveBoundaryHomeomorph_coe, positiveBoundaryArc_zero_coe,
    opposite_twistedTranslate_origin_previous, positiveBoundaryArc_one_coe]

noncomputable def CuspHoneycombHexagon.compatibleBoundaryArc (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    (k : Fin 6) → unitInterval ≃ₜ positiveBoundary k :=
  Fin.cases (positiveBoundaryArc 0)
    (Fin.cases (positiveBoundaryArc 1)
      (Fin.cases (positiveBoundaryArc 2)
        (Fin.cases (reversedOppositeBoundaryArc C₀ 0)
          (Fin.cases (reversedOppositeBoundaryArc C₀ 1)
            (Fin.cases (reversedOppositeBoundaryArc C₀ 2) (fun i => Fin.elim0 i))))))

theorem CuspHoneycombHexagon.compatibleBoundaryArc_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : compatibleBoundaryArc C₀ k 0 = positiveBoundaryArc k 0 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact reversedOppositeBoundaryArc_zero C₀ 0
  · exact reversedOppositeBoundaryArc_zero C₀ 1
  · exact reversedOppositeBoundaryArc_zero C₀ 2

theorem CuspHoneycombHexagon.compatibleBoundaryArc_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : compatibleBoundaryArc C₀ k 1 = positiveBoundaryArc k 1 := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact reversedOppositeBoundaryArc_one C₀ 0
  · exact reversedOppositeBoundaryArc_one C₀ 1
  · exact reversedOppositeBoundaryArc_one C₀ 2

theorem CuspHoneycombHexagon.compatibleBoundaryArc_zero_point (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : (compatibleBoundaryArc C₀ k 0).1 = squarePoint (k - 1) cornerZero := by
  rw [compatibleBoundaryArc_zero, positiveBoundaryArc_zero]

theorem CuspHoneycombHexagon.compatibleBoundaryArc_one_point (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : (compatibleBoundaryArc C₀ k 1).1 = squarePoint k cornerZero := by
  rw [compatibleBoundaryArc_one, positiveBoundaryArc_one]

theorem CuspHoneycombHexagon.oppositePositiveBoundaryHomeomorph_twice_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ (k + 3)
              (oppositePositiveBoundaryHomeomorph C₀ k x)).1.1 :
        ToricSpace.Space) =
      (x.1.1 : ToricSpace.Space) := by
  rw [oppositePositiveBoundaryHomeomorph_coe, oppositePositiveBoundaryHomeomorph_coe,
    ToricComponent.hexagonRay_opposite, ToricSpace.cuspVector_neg,
    ToricSpace.twistedTranslate_add, neg_add_cancel, ToricSpace.twistedTranslate_zero]

theorem CuspHoneycombHexagon.compatibleBoundaryArc_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleBoundaryArc C₀ (k + 3) (unitInterval.symm t) =
      oppositePositiveBoundaryHomeomorph C₀ k (compatibleBoundaryArc C₀ k t) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  fin_cases k
  · change
      ((oppositePositiveBoundaryHomeomorph C₀ 0
                (positiveBoundaryArc 0 (unitInterval.symm (unitInterval.symm t)))).1.1 :
          ToricSpace.Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 0 (positiveBoundaryArc 0 t)).1.1 :
          ToricSpace.Space)
    rw [unitInterval.symm_symm]
  · change
      ((oppositePositiveBoundaryHomeomorph C₀ 1
                (positiveBoundaryArc 1 (unitInterval.symm (unitInterval.symm t)))).1.1 :
          ToricSpace.Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 1 (positiveBoundaryArc 1 t)).1.1 :
          ToricSpace.Space)
    rw [unitInterval.symm_symm]
  · change
      ((oppositePositiveBoundaryHomeomorph C₀ 2
                (positiveBoundaryArc 2 (unitInterval.symm (unitInterval.symm t)))).1.1 :
          ToricSpace.Space) =
        ((oppositePositiveBoundaryHomeomorph C₀ 2 (positiveBoundaryArc 2 t)).1.1 :
          ToricSpace.Space)
    rw [unitInterval.symm_symm]
  · exact
      (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 0
          (positiveBoundaryArc 0 (unitInterval.symm t))).symm
  · exact
      (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 1
          (positiveBoundaryArc 1 (unitInterval.symm t))).symm
  · exact
      (oppositePositiveBoundaryHomeomorph_twice_coe C₀ 2
          (positiveBoundaryArc 2 (unitInterval.symm t))).symm

theorem CuspHoneycombHexagon.compatibleBoundaryArc_opposite_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    ((compatibleBoundaryArc C₀ (k + 3) (unitInterval.symm t)).1.1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        ((compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) := by
  rw [compatibleBoundaryArc_opposite, oppositePositiveBoundaryHomeomorph_coe]

def CuspHoneycombHexagon.compatibleBoundaryHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PositiveE0Boundary ≃ₜ PositiveE0Boundary :=
  boundaryGluingHomeomorph (compatibleBoundaryArc C₀)
    (fun k => congrArg Subtype.val (compatibleBoundaryArc_zero C₀ k))
    (fun k => congrArg Subtype.val (compatibleBoundaryArc_one C₀ k))

theorem CuspHoneycombHexagon.compatibleBoundaryHomeomorph_arc (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleBoundaryHomeomorph C₀ (boundaryArcInclusion k (positiveBoundaryArc k t)) =
      boundaryArcInclusion k (compatibleBoundaryArc C₀ k t) :=
  boundaryGluingHomeomorph_apply _ _ _ k t

def CuspHoneycombHexagon.compatibleComponentHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PositiveE0 ≃ₜ PositiveE0 :=
  positiveE0BoundaryExtension (compatibleBoundaryHomeomorph C₀)

theorem CuspHoneycombHexagon.compatibleComponentHomeomorph_arc (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleComponentHomeomorph C₀ (positiveBoundaryArc k t).1 =
      (compatibleBoundaryArc C₀ k t).1 := by
  exact
    (positiveE0BoundaryExtension_boundary (compatibleBoundaryHomeomorph C₀)
          (boundaryArcInclusion k (positiveBoundaryArc k t))).trans
      (congrArg Subtype.val (compatibleBoundaryHomeomorph_arc C₀ k t))

theorem CuspHoneycombHexagon.compatibleComponentHomeomorph_mem_boundary_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : PositiveE0) (k : Fin 6) :
    compatibleComponentHomeomorph C₀ x ∈ positiveBoundary k ↔ x ∈ positiveBoundary k := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ :=
      (compatibleBoundaryArc C₀ k).surjective ⟨compatibleComponentHomeomorph C₀ x, hx⟩
    have he : (positiveBoundaryArc k t).1 = x := by
      apply (compatibleComponentHomeomorph C₀).injective
      rw [compatibleComponentHomeomorph_arc]
      exact congrArg Subtype.val ht
    rw [← he]
    exact (positiveBoundaryArc k t).2
  · intro hx
    obtain ⟨t, ht⟩ := (positiveBoundaryArc k).surjective ⟨x, hx⟩
    have he : (positiveBoundaryArc k t).1 = x := congrArg Subtype.val ht
    rw [← he, compatibleComponentHomeomorph_arc]
    exact (compatibleBoundaryArc C₀ k t).2

def CuspHoneycombHexagon.compatibleHexagonHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Hexagon ≃ₜ PositiveE0 :=
  positiveE0HexagonHomeomorph.symm.trans (compatibleComponentHomeomorph C₀)

theorem CuspHoneycombHexagon.compatibleHexagonHomeomorph_sideInterval
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (t : unitInterval) :
    compatibleHexagonHomeomorph C₀
        ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ =
      (compatibleBoundaryArc C₀ k t).1 :=
  compatibleComponentHomeomorph_arc C₀ k t

theorem CuspHoneycombHexagon.compatibleHexagonHomeomorph_mem_boundary_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : Hexagon) (k : Fin 6) :
    compatibleHexagonHomeomorph C₀ x ∈ positiveBoundary k ↔ (x : Plane) ∈ side k := by
  change
    compatibleComponentHomeomorph C₀ (positiveE0HexagonHomeomorph.symm x) ∈ positiveBoundary k ↔ _
  rw [compatibleComponentHomeomorph_mem_boundary_iff]
  exact
    (positiveE0HexagonHomeomorph_mem_side_iff (positiveE0HexagonHomeomorph.symm x) k).symm.trans
      (by rw [Homeomorph.apply_symm_apply])

def CuspHoneycombHexagon.compatibleCellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycombTiling.baseCell ≃ₜ PositiveE0 :=
  CuspHoneycombTiling.standardHexagonDualHomeomorph.symm.trans (compatibleHexagonHomeomorph C₀)

theorem CuspHoneycombHexagon.compatibleCellHomeomorph_sideInterval (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    compatibleCellHomeomorph C₀
        (CuspHoneycombTiling.standardHexagonDualHomeomorph
          ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩) =
      (compatibleBoundaryArc C₀ k t).1 := by
  change
    compatibleHexagonHomeomorph C₀
        (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm
          (CuspHoneycombTiling.standardHexagonDualHomeomorph _)) =
      _
  rw [Homeomorph.symm_apply_apply]
  exact compatibleHexagonHomeomorph_sideInterval C₀ k t

theorem CuspHoneycombHexagon.compatibleCellHomeomorph_mem_boundary_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : CuspHoneycombTiling.baseCell) (k : Fin 6) :
    compatibleCellHomeomorph C₀ x ∈ positiveBoundary k ↔
      (x : Plane) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k) := by
  change
    compatibleHexagonHomeomorph C₀ (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x) ∈
        positiveBoundary k ↔
      _
  rw [compatibleHexagonHomeomorph_mem_boundary_iff]
  have h :=
    CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side k
      (CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

theorem ToricFan.areAdjacent_iff_hexagonRay (v w : Fin 2 → ℤ) :
    AreAdjacent v w ↔ ∃ k : Fin 6, w - v = ToricComponent.hexagonRay k := by
  have hedges : ∀ i : Fin 3, ∃ k : Fin 6, edgeDirection i = ToricComponent.hexagonRay k := by
    intro i
    fin_cases i <;> decide
  have hrays :
    ∀ k : Fin 6,
      ∃ i : Fin 3,
        ToricComponent.hexagonRay k = edgeDirection i ∨
          ToricComponent.hexagonRay k = -edgeDirection i := by
    intro k
    fin_cases k <;> decide
  constructor
  · rintro ⟨i, hi | hi⟩
    · obtain ⟨k, hk⟩ := hedges i
      exact ⟨k, hi.trans hk⟩
    · obtain ⟨k, hk⟩ := hedges i
      refine ⟨k + 3, hi.trans ?_⟩
      rw [hk, ToricComponent.hexagonRay_opposite]
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi | hi⟩ := hrays k
    · exact ⟨i, Or.inl (hk.trans hi)⟩
    · exact ⟨i, Or.inr (hk.trans hi)⟩

theorem CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff_hexagonRay
    (v : CuspHoneycombTiling.Lattice) :
    (baseCell ∩ cell v).Nonempty ↔ v = 0 ∨ ∃ k : Fin 6, v = ToricComponent.hexagonRay k := by
  rw [baseCell_inter_cell_nonempty_iff]
  simp [ToricComponent.hexagonRay, Fin.exists_fin_succ, or_assoc, or_left_comm, or_comm]

theorem CuspHoneycombTiling.cell_inter_cell_nonempty_iff_adjacent
    (v w : CuspHoneycombTiling.Lattice) :
    (cell v ∩ cell w).Nonempty ↔ v = w ∨ ToricFan.AreAdjacent v w := by
  rw [cell_inter_cell_nonempty_iff_baseCell, baseCell_inter_cell_nonempty_iff_hexagonRay, ←
    ToricFan.areAdjacent_iff_hexagonRay, sub_eq_zero]
  exact or_congr eq_comm Iff.rfl

theorem CuspHoneycombHexagon.compatibleCellHomeomorph_mem_rayDivisor_iff
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (x : CuspHoneycombTiling.baseCell) (v : Fin 2 → ℤ) :
    ((compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space) ∈ ToricSpace.rayDivisor v ↔
      (x : Plane) ∈ CuspHoneycombTiling.cell v := by
  by_cases hv : v = 0
  · subst v
    exact
      iff_of_true (compatibleCellHomeomorph C₀ x).1.2
        (by simpa only [CuspHoneycombTiling.cell_zero] using x.2)
  constructor
  · intro hx
    have hmeet : (ToricSpace.rayDivisor 0 ∩ ToricSpace.rayDivisor v).Nonempty :=
      ⟨((compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space),
        (compatibleCellHomeomorph C₀ x).1.2, hx⟩
    have hadj : ToricFan.AreAdjacent 0 v :=
      (ToricSpace.rayDivisor_inter_nonempty_iff 0 v (fun h => hv h.symm)).mp hmeet
    obtain ⟨k, hk⟩ := (ToricFan.areAdjacent_iff_hexagonRay 0 v).mp hadj
    have hvk : v = ToricComponent.hexagonRay k := by simpa only [sub_zero] using hk
    subst v
    change compatibleCellHomeomorph C₀ x ∈ positiveBoundary k at hx
    exact (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mp hx
  · intro hx
    have hmeet : (CuspHoneycombTiling.baseCell ∩ CuspHoneycombTiling.cell v).Nonempty :=
      ⟨(x : Plane), x.2, hx⟩
    rcases (CuspHoneycombTiling.baseCell_inter_cell_nonempty_iff_hexagonRay v).mp hmeet with
      hzero | ⟨k, hk⟩
    · exact (hv hzero).elim
    · subst v
      exact (compatibleCellHomeomorph_mem_boundary_iff C₀ x k).mpr hx

theorem CuspHoneycombHexagon.compatibleCellHomeomorph_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (x : CuspHoneycombTiling.baseCell)
    (hx : (x : Plane) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k)) :
    ((compatibleCellHomeomorph C₀
            ⟨(x : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k),
              hx⟩).1 :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀)
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
        ((compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space) := by
  let y : Hexagon := CuspHoneycombTiling.standardHexagonDualHomeomorph.symm x
  have hy : (y : Plane) ∈ side k := by
    apply (CuspHoneycombTiling.standardHexagonDualHomeomorph_mem_cell_iff_side k y).mp
    simpa only [y, Homeomorph.apply_symm_apply] using hx
  obtain ⟨t, ht⟩ := (sideIntervalHomeomorph k).surjective ⟨y, hy⟩
  have hxt :
    CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ =
      x := by
    have hyt :
      (⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ : Hexagon) = y :=
      Subtype.ext (congrArg (fun z : side k => (z : Plane)) ht)
    rw [hyt]
    exact CuspHoneycombTiling.standardHexagonDualHomeomorph.apply_symm_apply x
  have hshift :
    CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane),
          (sideIntervalHomeomorph (k + 3) (unitInterval.symm t)).2.1⟩ =
      ⟨(x : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k), hx⟩ := by
    apply Subtype.ext
    change
      CuspHoneycombTiling.dualStandardPlaneHomeomorph.symm
          (sideIntervalHomeomorph (k + 3) (unitInterval.symm t) : Plane) =
        (x : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k)
    rw [CuspHoneycombTiling.dual_sideInterval_opposite]
    exact
      congrArg
        (fun z : CuspHoneycombTiling.baseCell =>
          (z : Plane) - CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k))
        hxt
  rw [← hshift, compatibleCellHomeomorph_sideInterval, ← hxt,
    compatibleCellHomeomorph_sideInterval]
  exact compatibleBoundaryArc_opposite_coe C₀ k t

def CuspHoneycomb.cellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) :
    CuspHoneycombTiling.cell v ≃ₜ CuspHoneycombPositive.positiveCell v :=
  (CuspHoneycombTiling.cellTranslationHomeomorph v).symm.trans
    ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀).trans
      (CuspHoneycombPositive.positiveE0CellHomeomorph C₀ v))

@[simp]
theorem CuspHoneycomb.cellHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    ((cellHomeomorph C₀ v x).1.1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
              ((CuspHoneycombTiling.cellTranslationHomeomorph v).symm x)).1 :
          ToricSpace.Space) :=
  rfl

theorem CuspHoneycomb.cellHomeomorph_mem_positiveCell_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) ∈
        CuspHoneycombPositive.positiveCell w ↔
      (x : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell w := by
  change ((cellHomeomorph C₀ v x).1.1 : ToricSpace.Space) ∈ ToricSpace.rayDivisor w ↔ _
  rw [cellHomeomorph_coe, ToricSpace.twistedTranslate_mem_rayDivisor, ToricSpace.cuspVector_neg,
    ToricSpace.cuspVector_cuspVector, neg_neg,
    CuspHoneycombHexagon.compatibleCellHomeomorph_mem_rayDivisor_iff]
  change
    (x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v ∈
        CuspHoneycombTiling.cell (w - v) ↔
      _
  rw [CuspHoneycombTiling.sub_latticePoint_mem_cell_iff]
  have he : v + (w - v) = w := by abel
  rw [he]

theorem CuspHoneycomb.cellHomeomorph_compatible (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v)
    (y : CuspHoneycombTiling.cell w)
    (hxy : (x : (CuspHoneycombTiling.Plane)) = (y : (CuspHoneycombTiling.Plane))) :
    (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) =
      (cellHomeomorph C₀ w y : CuspPositiveRetraction.PositiveCentralFibre) := by
  have hxw : (x : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell w := by
    rw [hxy]
    exact y.2
  have hnonempty : (CuspHoneycombTiling.cell v ∩ CuspHoneycombTiling.cell w).Nonempty :=
    ⟨x, x.2, hxw⟩
  rcases (CuspHoneycombTiling.cell_inter_cell_nonempty_iff_adjacent v w).mp hnonempty with rfl |
    hadj
  · have he : x = y := Subtype.ext hxy
    rw [he]
  obtain ⟨k, hk⟩ := (ToricFan.areAdjacent_iff_hexagonRay v w).mp hadj
  have hw : w = v + ToricComponent.hexagonRay k := (sub_eq_iff_eq_add.mp hk).trans (add_comm _ _)
  let a : CuspHoneycombTiling.baseCell := (CuspHoneycombTiling.cellTranslationHomeomorph v).symm x
  let b : CuspHoneycombTiling.baseCell := (CuspHoneycombTiling.cellTranslationHomeomorph w).symm y
  have ha :
    (a : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell (ToricComponent.hexagonRay k) := by
    change
      (x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v ∈
        CuspHoneycombTiling.cell (ToricComponent.hexagonRay k)
    apply
      (CuspHoneycombTiling.sub_latticePoint_mem_cell_iff v (ToricComponent.hexagonRay k) x).mpr
    simpa only [← hw] using hxw
  have hb :
    b =
      ⟨(a : (CuspHoneycombTiling.Plane)) -
          CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k),
        ha⟩ := by
    apply Subtype.ext
    change
      (y : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint w =
        ((x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v) -
          CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k)
    rw [← hxy, hw, CuspHoneycombTiling.latticePoint_add]
    abel
  apply Subtype.ext
  apply Subtype.ext
  rw [cellHomeomorph_coe, cellHomeomorph_coe]
  change
    ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀ a).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector w)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀ b).1 : ToricSpace.Space)
  rw [hb, CuspHoneycombHexagon.compatibleCellHomeomorph_opposite C₀ k a ha,
    ToricSpace.twistedTranslate_add]
  have hu :
    -ToricSpace.cuspVector w + ToricSpace.cuspVector (ToricComponent.hexagonRay k) =
      -ToricSpace.cuspVector v := by
    rw [hw, ToricSpace.cuspVector_add]
    abel
  rw [hu]

theorem CuspHoneycomb.cellHomeomorph_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v w : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v)
    (y : CuspHoneycombTiling.cell w) :
    (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) =
        (cellHomeomorph C₀ w y : CuspPositiveRetraction.PositiveCentralFibre) ↔
      (x : (CuspHoneycombTiling.Plane)) = (y : (CuspHoneycombTiling.Plane)) := by
  constructor
  · intro h
    have hxw : (x : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell w :=
      (cellHomeomorph_mem_positiveCell_iff C₀ v w x).mp
        (by
          rw [h]
          exact (cellHomeomorph C₀ w y).2)
    have hcomp := cellHomeomorph_compatible C₀ v w x ⟨x, hxw⟩ rfl
    have he : cellHomeomorph C₀ w ⟨x, hxw⟩ = cellHomeomorph C₀ w y :=
      Subtype.ext (hcomp.symm.trans h)
    exact congrArg Subtype.val ((cellHomeomorph C₀ w).injective he)
  · exact cellHomeomorph_compatible C₀ v w x y

def CuspHoneycombClosedCover.projection {ι X : Type*} (A : ι → Set X) (p : Σ i, A i) : X :=
  p.2.1

theorem CuspHoneycombClosedCover.projection_continuous {ι X : Type*} [TopologicalSpace X]
    (A : ι → Set X) : Continuous (projection A) :=
  continuous_sigma_iff.mpr fun _ => continuous_subtype_val

theorem CuspHoneycombClosedCover.projection_surjective {ι X : Type*} {A : ι → Set X}
    (hcover : ⋃ i, A i = Set.univ) : Function.Surjective (projection A) := by
  intro x
  have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨i, x, hi⟩, rfl⟩

theorem CuspHoneycombClosedCover.projection_isClosedMap {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hclosed : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) :
    IsClosedMap (projection A) := by
  intro S hS
  let F : ι → Set X := fun i => (Subtype.val : A i → X) '' ((fun x : A i => Sigma.mk i x) ⁻¹' S)
  have hFclosed (i : ι) : IsClosed (F i) :=
    (hclosed i).isClosedMap_subtype_val _ (hS.preimage continuous_sigmaMk)
  have hFsub (i : ι) : F i ⊆ A i := by
    rintro x ⟨a, _, rfl⟩
    exact a.2
  have heq : projection A '' S = ⋃ i, F i := by
    ext x
    constructor
    · rintro ⟨⟨i, a⟩, ha, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩
    · intro hx
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i, a⟩, ha, rfl⟩
  rw [heq]
  exact (hloc.subset hFsub).isClosed_iUnion hFclosed

theorem CuspHoneycombClosedCover.projection_isQuotientMap {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hcover : ⋃ i, A i = Set.univ) (hclosed : ∀ i, IsClosed (A i))
    (hloc : LocallyFinite A) : Topology.IsQuotientMap (projection A) :=
  (projection_isClosedMap hclosed hloc).isQuotientMap (projection_continuous A)
    (projection_surjective hcover)

def CuspHoneycombClosedCover.quotientHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] (f : Z → X) (g : Z → Y)
    (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y
    where
  toFun := CuspHoneycombHexagon.CommonFibres.descend f g hf.surjective
  invFun := CuspHoneycombHexagon.CommonFibres.descend g f hg.surjective
  left_inv
    x := by
    obtain ⟨a, rfl⟩ := hf.surjective x
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective
        (fun a b => (hfg a b).mp),
      CuspHoneycombHexagon.CommonFibres.descend_apply g f hg.surjective
        (fun a b => (hfg a b).mpr)]
  right_inv
    y := by
    obtain ⟨a, rfl⟩ := hg.surjective y
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply g f hg.surjective
        (fun a b => (hfg a b).mpr),
      CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (hfg a b).mp)]
  continuous_toFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous f g hf.surjective hf hg.continuous
      (fun a b => (hfg a b).mp)
  continuous_invFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous g f hg.surjective hg hf.continuous
      (fun a b => (hfg a b).mpr)

theorem CuspHoneycombClosedCover.quotientHomeomorph_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Z : Type*} [TopologicalSpace Z] (f : Z → X) (g : Z → Y)
    (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) (a : Z) : quotientHomeomorph f g hf hg hfg (f a) = g a :=
  CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (hfg a b).mp) a

def CuspHoneycombClosedCover.sigmaHomeomorph {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i) :
    (Σ i, A i) ≃ₜ (Σ i, B i) where
  toFun p := ⟨p.1, e p.1 p.2⟩
  invFun p := ⟨p.1, (e p.1).symm p.2⟩
  left_inv := by rintro ⟨i, a⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp
  continuous_toFun := continuous_sigma_iff.mpr fun i => continuous_sigmaMk.comp (e i).continuous
  continuous_invFun :=
    continuous_sigma_iff.mpr fun i => continuous_sigmaMk.comp (e i).symm.continuous

def CuspHoneycombClosedCover.homeomorph {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i) (hAcov : ⋃ i, A i = Set.univ)
    (hAcl : ∀ i, IsClosed (A i)) (hAloc : LocallyFinite A) (hBcov : ⋃ i, B i = Set.univ)
    (hBcl : ∀ i, IsClosed (B i)) (hBloc : LocallyFinite B)
    (hglue : ∀ i j (x : A i) (y : A j), (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y)) : X ≃ₜ Y :=
  quotientHomeomorph (projection A) (projection B ∘ sigmaHomeomorph A B e)
    (projection_isQuotientMap hAcov hAcl hAloc)
    ((projection_isQuotientMap hBcov hBcl hBloc).comp (sigmaHomeomorph A B e).isQuotientMap)
    (fun a b => hglue a.1 b.1 a.2 b.2)

theorem CuspHoneycombClosedCover.homeomorph_apply {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y) (e : ∀ i, A i ≃ₜ B i)
    (hAcov : ⋃ i, A i = Set.univ) (hAcl : ∀ i, IsClosed (A i)) (hAloc : LocallyFinite A)
    (hBcov : ⋃ i, B i = Set.univ) (hBcl : ∀ i, IsClosed (B i)) (hBloc : LocallyFinite B)
    (hglue : ∀ i j (x : A i) (y : A j), (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y)) (i : ι)
    (x : A i) : homeomorph A B e hAcov hAcl hAloc hBcov hBcl hBloc hglue (x : X) = (e i x : Y) :=
  quotientHomeomorph_apply _ _ _ _ _ (⟨i, x⟩ : Σ i, A i)

def CuspHoneycomb.honeycombHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    (CuspHoneycombTiling.Plane) ≃ₜ CuspPositiveRetraction.PositiveCentralFibre :=
  CuspHoneycombClosedCover.homeomorph CuspHoneycombTiling.cell CuspHoneycombPositive.positiveCell
    (cellHomeomorph C₀) CuspHoneycombTiling.iUnion_cell CuspHoneycombTiling.cell_isClosed
    CuspHoneycombTiling.cell_locallyFinite CuspHoneycombPositive.iUnion_positiveCell
    CuspHoneycombPositive.positiveCell_isClosed CuspHoneycombPositive.positiveCells_locallyFinite
    (fun v w x y => (cellHomeomorph_eq_iff C₀ v w x y).symm)

theorem CuspHoneycomb.honeycombHomeomorph_cell (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    honeycombHomeomorph C₀ (x : (CuspHoneycombTiling.Plane)) =
      (cellHomeomorph C₀ v x : CuspPositiveRetraction.PositiveCentralFibre) :=
  CuspHoneycombClosedCover.homeomorph_apply CuspHoneycombTiling.cell
    CuspHoneycombPositive.positiveCell (cellHomeomorph C₀) CuspHoneycombTiling.iUnion_cell
    CuspHoneycombTiling.cell_isClosed CuspHoneycombTiling.cell_locallyFinite
    CuspHoneycombPositive.iUnion_positiveCell CuspHoneycombPositive.positiveCell_isClosed
    CuspHoneycombPositive.positiveCells_locallyFinite
    (fun v w x y => (cellHomeomorph_eq_iff C₀ v w x y).symm) v x

theorem CuspHoneycomb.honeycombHomeomorph_cell_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    ((honeycombHomeomorph C₀ (x : (CuspHoneycombTiling.Plane))).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) (-ToricSpace.cuspVector v)
        ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
              ((CuspHoneycombTiling.cellTranslationHomeomorph v).symm x)).1 :
          ToricSpace.Space) := by rw [honeycombHomeomorph_cell, cellHomeomorph_coe]

theorem CuspHoneycomb.honeycombHomeomorph_mem_positiveCell_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : (CuspHoneycombTiling.Plane)) :
    honeycombHomeomorph C₀ x ∈ CuspHoneycombPositive.positiveCell v ↔
      x ∈ CuspHoneycombTiling.cell v := by
  obtain ⟨w, hw⟩ := CuspHoneycombTiling.exists_mem_cell x
  rw [honeycombHomeomorph_cell C₀ w ⟨x, hw⟩]
  exact cellHomeomorph_mem_positiveCell_iff C₀ w v ⟨x, hw⟩

theorem CuspHoneycomb.cellHomeomorph_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : (CuspHoneycombTiling.Lattice)) (x : CuspHoneycombTiling.cell v) :
    (cellHomeomorph C₀ (v + ToricSpace.cuspVector u)
          (CuspHoneycombTiling.cellShiftHomeomorph v (ToricSpace.cuspVector u) x) :
        CuspPositiveRetraction.PositiveCentralFibre) =
      CuspCollapse.positiveCentralTranslate C₀ u (cellHomeomorph C₀ v x) := by
  have hnorm :
    (CuspHoneycombTiling.cellTranslationHomeomorph (v + ToricSpace.cuspVector u)).symm
        (CuspHoneycombTiling.cellShiftHomeomorph v (ToricSpace.cuspVector u) x) =
      (CuspHoneycombTiling.cellTranslationHomeomorph v).symm x := by
    apply Subtype.ext
    change
      ((x : (CuspHoneycombTiling.Plane)) +
            CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector u)) -
          CuspHoneycombTiling.latticePoint (v + ToricSpace.cuspVector u) =
        (x : (CuspHoneycombTiling.Plane)) - CuspHoneycombTiling.latticePoint v
    rw [CuspHoneycombTiling.latticePoint_add]
    abel
  have hu : -ToricSpace.cuspVector (v + ToricSpace.cuspVector u) = u + -ToricSpace.cuspVector v :=
    by
    rw [ToricSpace.cuspVector_add, ToricSpace.cuspVector_cuspVector]
    abel
  apply Subtype.ext
  apply Subtype.ext
  simp only [cellHomeomorph_coe, CuspCollapse.positiveCentralTranslate_coe, hnorm]
  rw [ToricSpace.twistedTranslate_add, hu]

theorem CuspHoneycomb.honeycombHomeomorph_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : (CuspHoneycombTiling.Lattice)) (x : (CuspHoneycombTiling.Plane)) :
    honeycombHomeomorph C₀ (x + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector u)) =
      CuspCollapse.positiveCentralTranslate C₀ u (honeycombHomeomorph C₀ x) := by
  obtain ⟨v, hx⟩ := CuspHoneycombTiling.exists_mem_cell x
  let a : CuspHoneycombTiling.cell v := ⟨x, hx⟩
  have ha : (a : (CuspHoneycombTiling.Plane)) = x := rfl
  have hshift :=
    honeycombHomeomorph_cell C₀ (v + ToricSpace.cuspVector u)
      (CuspHoneycombTiling.cellShiftHomeomorph v (ToricSpace.cuspVector u) a)
  have hbase :=
    congrArg (CuspCollapse.positiveCentralTranslate C₀ u) (honeycombHomeomorph_cell C₀ v a).symm
  simpa only [CuspHoneycombTiling.cellShiftHomeomorph_coe, ha] using
    hshift.trans ((cellHomeomorph_translate C₀ u v a).trans hbase)

theorem CuspHoneycomb.honeycombHomeomorph_add_latticePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (CuspHoneycombTiling.Lattice)) (x : (CuspHoneycombTiling.Plane)) :
    honeycombHomeomorph C₀ (x + CuspHoneycombTiling.latticePoint v) =
      CuspCollapse.positiveCentralTranslate C₀ (-ToricSpace.cuspVector v)
        (honeycombHomeomorph C₀ x) := by
  simpa only [ToricSpace.cuspVector_neg, ToricSpace.cuspVector_cuspVector, neg_neg] using
    honeycombHomeomorph_equivariant C₀ (-ToricSpace.cuspVector v) x

theorem CuspHoneycomb.honeycombHomeomorph_symm_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : (CuspHoneycombTiling.Lattice)) (q : CuspPositiveRetraction.PositiveCentralFibre) :
    (honeycombHomeomorph C₀).symm (CuspCollapse.positiveCentralTranslate C₀ u q) =
      (honeycombHomeomorph C₀).symm q +
        CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector u) := by
  apply (honeycombHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply, honeycombHomeomorph_equivariant, Homeomorph.apply_symm_apply]

theorem CuspHoneycomb.standardHexagonDualHomeomorph_vertex_coe (i : Fin 6) :
    (CuspHoneycombTiling.standardHexagonDualHomeomorph
          ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩ :
        (CuspHoneycombTiling.Plane)) =
      CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i) :=
  CuspHoneycombTiling.dual_standard_vertex i

theorem CuspHoneycomb.compatibleCellHomeomorph_vertex (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 6) :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀
        (CuspHoneycombTiling.standardHexagonDualHomeomorph
          ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩) =
      CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
  simpa only [CuspHoneycombHexagon.sideIntervalHomeomorph_one,
    CuspHoneycombHexagon.compatibleBoundaryArc_one_point] using
    CuspHoneycombHexagon.compatibleCellHomeomorph_sideInterval C₀ i 1

theorem CuspHoneycomb.triangleBarycenter_zeroTriangle_mem_baseCell (i : Fin 6) :
    CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i) ∈
      CuspHoneycombTiling.baseCell := by
  rw [← standardHexagonDualHomeomorph_vertex_coe i]
  exact
    (CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩).2

theorem CuspHoneycomb.compatibleCellHomeomorph_triangleBarycenter (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 6) :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀
        ⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
          triangleBarycenter_zeroTriangle_mem_baseCell i⟩ =
      CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
  have hi :
    (⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
          triangleBarycenter_zeroTriangle_mem_baseCell i⟩ :
        CuspHoneycombTiling.baseCell) =
      CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨CuspHoneycombHexagon.vertex i, (CuspHoneycombHexagon.vertex_mem_side_self i).1⟩ := by
    apply Subtype.ext
    exact (standardHexagonDualHomeomorph_vertex_coe i).symm
  rw [hi, compatibleCellHomeomorph_vertex]

theorem CuspHoneycomb.compatibleCellHomeomorph_triangleBarycenter_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀
            ⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
              triangleBarycenter_zeroTriangle_mem_baseCell i⟩).1 :
        ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  rw [compatibleCellHomeomorph_triangleBarycenter,
    CuspHoneycombHexagon.squarePoint_cornerZero_coe]

theorem CuspHoneycomb.honeycombHomeomorph_zeroTriangleBarycenter_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    ((honeycombHomeomorph C₀
            (CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i))).1 :
        ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  let a : CuspHoneycombTiling.baseCell :=
    ⟨CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i),
      triangleBarycenter_zeroTriangle_mem_baseCell i⟩
  let x : CuspHoneycombTiling.cell 0 := CuspHoneycombTiling.cellTranslationHomeomorph 0 a
  have hx :
    (x : (CuspHoneycombTiling.Plane)) =
      CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i) := by
    change
      (a : (CuspHoneycombTiling.Plane)) + CuspHoneycombTiling.latticePoint 0 =
        CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle i)
    rw [CuspHoneycombTiling.latticePoint_zero, add_zero]
  have hnorm : (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm x = a :=
    (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm_apply_apply a
  have h := honeycombHomeomorph_cell_coe C₀ 0 x
  rw [hx, hnorm, ToricSpace.cuspVector_zero, neg_zero, ToricSpace.twistedTranslate_zero] at h
  exact h.trans (compatibleCellHomeomorph_triangleBarycenter_coe C₀ i)

theorem CuspHoneycomb.triangle_eq_zeroTriangle_shift (s : ToricFan.Triangle) :
    ∃ i : Fin 6,
      ∃ v : (CuspHoneycombTiling.Lattice), s = (ToricComponent.zeroTriangle i).shift v := by
  rcases s with ⟨a, b, u⟩
  cases u
  · refine ⟨0, ![a, b], ?_⟩
    ext <;> simp [ToricComponent.zeroTriangle, ToricFan.Triangle.shift]
  · refine ⟨1, ![a + 1, b], ?_⟩
    ext <;> simp [ToricComponent.zeroTriangle, ToricFan.Triangle.shift]

theorem CuspHoneycomb.honeycombHomeomorph_triangleBarycenter_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : ToricFan.Triangle) :
    ((honeycombHomeomorph C₀ (CuspHoneycombTiling.triangleBarycenter s)).1 : ToricSpace.Space) =
      ToricSpace.inclusion s 0 := by
  obtain ⟨i, v, rfl⟩ := triangle_eq_zeroTriangle_shift s
  rw [CuspHoneycombTiling.triangleBarycenter_shift, honeycombHomeomorph_add_latticePoint,
    CuspCollapse.positiveCentralTranslate_coe, honeycombHomeomorph_zeroTriangleBarycenter_coe,
    ToricSpace.twistedTranslate_origin, ToricSpace.cuspVector_neg,
    ToricSpace.cuspVector_cuspVector, neg_neg]

noncomputable def CuspCollapse.centralClosedZeroHomeomorph :
    CuspRetraction.CentralFibre ≃ₜ CuspRetraction.ClosedTube 0 :=
  Homeomorph.setCongr
    (by
      ext x
      exact norm_le_zero_iff.symm)

noncomputable def CuspCollapse.quotientCentralClosedZeroHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    CuspRetraction.QuotientCentralFibre C ε ≃ₜ CuspRetraction.ClosedQuotient C ε 0 :=
  Homeomorph.setCongr
    (by
      ext q
      exact norm_le_zero_iff.symm)

noncomputable def CuspCollapse.centralProject (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (x : CuspRetraction.CentralFibre) : CuspRetraction.QuotientCentralFibre C ε :=
  ⟨CuspQuotient.quotientMap C ε
      ⟨x, by
        change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
        rw [x.2]
        simpa only [Metric.mem_ball, dist_self] using hε⟩,
    x.2⟩

theorem CuspCollapse.centralProject_eq_comp (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    centralProject C ε hε =
      (quotientCentralClosedZeroHomeomorph C ε).symm ∘
        (CuspRetraction.closedQuotientMap C hε ∘ centralClosedZeroHomeomorph) :=
  rfl

theorem CuspCollapse.centralProject_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (centralProject C ε hε) := by
  apply Continuous.subtype_mk
  exact (CuspQuotient.quotientMap_continuous C ε).comp (continuous_subtype_val.subtype_mk _)

theorem CuspCollapse.centralProject_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Surjective (centralProject C ε hε) := by
  rw [centralProject_eq_comp]
  exact
    (quotientCentralClosedZeroHomeomorph C ε).symm.surjective.comp
      ((CuspRetraction.closedQuotientMap_surjective C hε).comp
        centralClosedZeroHomeomorph.surjective)

theorem CuspCollapse.centralProject_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (centralProject C ε hε) := by
  rw [centralProject_eq_comp]
  exact
    (quotientCentralClosedZeroHomeomorph C ε).symm.isOpenQuotientMap.comp
      ((CuspRetraction.closedQuotientMap_isOpenQuotientMap C hε hC).comp
        centralClosedZeroHomeomorph.isOpenQuotientMap)

theorem CuspCollapse.centralProject_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Topology.IsQuotientMap (centralProject C ε hε) :=
  (centralProject_isOpenQuotientMap C ε hε hC).isQuotientMap

theorem CuspCollapse.centralProject_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (x y : CuspRetraction.CentralFibre) :
    centralProject C ε hε x = centralProject C ε hε y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.twistedTranslate C v (y : ToricSpace.Space) = (x : ToricSpace.Space) := by
  rw [← (quotientCentralClosedZeroHomeomorph C ε).injective.eq_iff]
  change
    CuspRetraction.closedQuotientMap C hε (centralClosedZeroHomeomorph x) =
        CuspRetraction.closedQuotientMap C hε (centralClosedZeroHomeomorph y) ↔
      _
  exact CuspRetraction.closedQuotientMap_eq_iff C hε _ _

abbrev CuspCollapse.PhasePositiveSpace :=
  ToricSpace.CompactFibreTorus × CuspPositiveRetraction.PositiveCentralFibre

def CuspCollapse.centralCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    PhasePositiveSpace → CuspRetraction.QuotientCentralFibre C ε :=
  centralProject C ε hε ∘ centralPolarMap

theorem CuspCollapse.centralCollapseMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (centralCollapseMap C ε hε) :=
  (centralProject_continuous C ε hε).comp centralPolarMap_continuous

theorem CuspCollapse.centralCollapseMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Surjective (centralCollapseMap C ε hε) :=
  (centralProject_surjective C ε hε).comp centralPolarMap_surjective

theorem CuspCollapse.centralCollapseMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Topology.IsQuotientMap (centralCollapseMap C ε hε) :=
  (centralProject_isQuotientMap C ε hε hC).comp centralPolarMap_isQuotientMap

def CuspCollapse.centralCollapseRelation (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : PhasePositiveSpace) : Prop :=
  ∃ v : Fin 2 → ℤ,
    p.2 = positiveCentralTranslate C₀ v q.2 ∧
      p.1⁻¹ * (deckFibrePhase C₀ v * q.1) ∈
        MulAction.stabilizer ToricSpace.CompactFibreTorus (p.2.1 : ToricSpace.Space)

theorem CuspCollapse.centralCollapseMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : PhasePositiveSpace) :
    centralCollapseMap C ε hε p = centralCollapseMap C ε hε q ↔
      centralCollapseRelation (C 0) p q := by
  change centralProject C ε hε (centralPolarMap p) = centralProject C ε hε (centralPolarMap q) ↔ _
  rw [centralProject_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hpq : centralPolarMap p = centralPolarMap (phaseDeckMap (C 0) v q) := by
      apply Subtype.ext
      exact ((centralPolarMap_phaseDeckMap C v q).trans hv).symm
    exact ⟨v, (centralPolarMap_eq_iff p (phaseDeckMap (C 0) v q)).mp hpq⟩
  · rintro ⟨v, hv⟩
    have hpq : centralPolarMap p = centralPolarMap (phaseDeckMap (C 0) v q) :=
      (centralPolarMap_eq_iff p (phaseDeckMap (C 0) v q)).mpr hv
    refine ⟨v, ?_⟩
    rw [← centralPolarMap_phaseDeckMap C v q]
    exact congrArg Subtype.val hpq.symm

def CuspCollapse.centralCollapseSetoid (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : Setoid PhasePositiveSpace
    where
  r := centralCollapseRelation C₀
  iseqv := by
    let f := centralCollapseMap (fun _ => C₀) 1 zero_lt_one
    have he (p q : PhasePositiveSpace) : f p = f q ↔ centralCollapseRelation C₀ p q :=
      centralCollapseMap_eq_iff (fun _ => C₀) 1 zero_lt_one p q
    exact
      { refl := fun p => (he p p).mp rfl
        symm := fun {p q} h => (he q p).mp ((he p q).mpr h).symm
        trans := fun {p q r} hpq hqr =>
          (he p r).mp (((he p q).mpr hpq).trans ((he q r).mpr hqr)) }

abbrev CuspCollapse.CentralCollapseModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :=
  Quotient (centralCollapseSetoid C₀)

def CuspCollapse.centralCollapseModelMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CentralCollapseModel (C 0) → CuspRetraction.QuotientCentralFibre C ε :=
  Quotient.lift (centralCollapseMap C ε hε)
    (fun p q h => (centralCollapseMap_eq_iff C ε hε p q).mpr h)

theorem CuspCollapse.centralCollapseModelMap_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Bijective (centralCollapseModelMap C ε hε) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro h
        exact Quotient.sound ((centralCollapseMap_eq_iff C ε hε p q).mp h)
  · intro x
    obtain ⟨p, hp⟩ := centralCollapseMap_surjective C ε hε x
    exact ⟨Quotient.mk (centralCollapseSetoid (C 0)) p, hp⟩

def CuspCollapse.centralCollapseEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CentralCollapseModel (C 0) ≃ CuspRetraction.QuotientCentralFibre C ε :=
  Equiv.ofBijective (centralCollapseModelMap C ε hε) (centralCollapseModelMap_bijective C ε hε)

@[simp]
theorem CuspCollapse.centralCollapseEquiv_symm_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : PhasePositiveSpace) :
    (centralCollapseEquiv C ε hε).symm (centralCollapseMap C ε hε p) =
      Quotient.mk (centralCollapseSetoid (C 0)) p := by
  apply (centralCollapseEquiv C ε hε).injective
  rw [Equiv.apply_symm_apply]
  rfl

abbrev CuspHoneycomb.PhasePlane :=
  ToricSpace.CompactFibreTorus × (CuspHoneycombTiling.Plane)

def CuspHoneycomb.phaseCoordinatesHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PhasePlane ≃ₜ CuspCollapse.PhasePositiveSpace :=
  (Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr (honeycombHomeomorph C₀)

def CuspHoneycomb.honeycombPolarMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    PhasePlane → CuspRetraction.CentralFibre :=
  CuspCollapse.centralPolarMap ∘ phaseCoordinatesHomeomorph C₀

theorem CuspHoneycomb.honeycombPolarMap_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (honeycombPolarMap C₀) :=
  CuspCollapse.centralPolarMap_surjective.comp (phaseCoordinatesHomeomorph C₀).surjective

def CuspHoneycomb.honeycombDeckMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : PhasePlane) : PhasePlane :=
  (CuspCollapse.deckFibrePhase C₀ v * p.1,
    p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))

def CuspHoneycomb.honeycombCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    PhasePlane → CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralCollapseMap C ε hε ∘ phaseCoordinatesHomeomorph (C 0)

theorem CuspHoneycomb.honeycombCollapseMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (honeycombCollapseMap C ε hε) :=
  (CuspCollapse.centralCollapseMap_continuous C ε hε).comp
    (phaseCoordinatesHomeomorph (C 0)).continuous

theorem CuspHoneycomb.honeycombCollapseMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Surjective (honeycombCollapseMap C ε hε) :=
  (CuspCollapse.centralCollapseMap_surjective C ε hε).comp
    (phaseCoordinatesHomeomorph (C 0)).surjective

theorem CuspHoneycomb.honeycombCollapseMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Topology.IsQuotientMap (honeycombCollapseMap C ε hε) :=
  (CuspCollapse.centralCollapseMap_isQuotientMap C ε hε hC).comp
    (phaseCoordinatesHomeomorph (C 0)).isQuotientMap

def CuspHoneycomb.honeycombCollapseRelation (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p q : PhasePlane) :
    Prop :=
  ∃ v : Fin 2 → ℤ,
    p.2 = q.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) ∧
      p.1⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * q.1) ∈
        MulAction.stabilizer ToricSpace.CompactFibreTorus
          ((honeycombHomeomorph C₀ p.2).1 : ToricSpace.Space)

theorem CuspHoneycomb.honeycombCollapseMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : PhasePlane) :
    honeycombCollapseMap C ε hε p = honeycombCollapseMap C ε hε q ↔
      honeycombCollapseRelation (C 0) p q := by
  change
    CuspCollapse.centralCollapseMap C ε hε (phaseCoordinatesHomeomorph (C 0) p) =
        CuspCollapse.centralCollapseMap C ε hε (phaseCoordinatesHomeomorph (C 0) q) ↔
      _
  rw [CuspCollapse.centralCollapseMap_eq_iff]
  unfold CuspCollapse.centralCollapseRelation honeycombCollapseRelation
  apply exists_congr
  intro v
  change
    honeycombHomeomorph (C 0) p.2 =
          CuspCollapse.positiveCentralTranslate (C 0) v (honeycombHomeomorph (C 0) q.2) ∧
        _ ↔
      _
  rw [← honeycombHomeomorph_equivariant, (honeycombHomeomorph (C 0)).injective.eq_iff]
  rfl

def ToricCharts.coordinateExp {d : ℕ} (z : CoordinateSpace d) : CoordinateSpace d := fun j =>
  Complex.exp (z j)

theorem ToricCharts.coordinateExp_continuous {d : ℕ} : Continuous (@coordinateExp d) :=
  continuous_pi fun j => Complex.continuous_exp.comp (continuous_apply j)

theorem ToricCharts.range_coordinateExp {d : ℕ} :
    Set.range (@coordinateExp d) = (torus : Set (CoordinateSpace d)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩ j
    exact Complex.exp_ne_zero (w j)
  · intro hz
    refine ⟨fun j => Complex.log (z j), ?_⟩
    funext j
    exact Complex.exp_log (hz j)

theorem CuspQuotient.affineTube_isOpen (ε : ℝ) : IsOpen (affineTube ε) :=
  isOpen_lt ToricFan.Triangle.time_holomorphic.continuous.norm continuous_const

theorem CuspQuotient.affineTube_isSimplyConnected {ε : ℝ} (hε : 0 < ε) :
    IsSimplyConnected (affineTube ε) := by
  let :=
    (affineTube_starConvex ε).contractibleSpace
      (show (affineTube ε).Nonempty from
        ⟨0, by simpa [affineTube, ToricFan.Triangle.time] using hε⟩)
  exact SimplyConnectedSpace.ofContractible _

def CuspQuotient.logarithmicTube (ε : ℝ) : Set (ToricCharts.CoordinateSpace 3) :=
  {z | (z 0 + z 1 + z 2).re < Real.log ε}

theorem CuspQuotient.logarithmicTube_convex (ε : ℝ) : Convex ℝ (logarithmicTube ε) := by
  apply convex_halfSpace_lt
  constructor
  · intro z w
    simp only [Pi.add_apply, Complex.add_re]
    ring
  · intro r z
    simp only [Pi.smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
    ring

theorem CuspQuotient.logarithmicTube_nonempty (ε : ℝ) : (logarithmicTube ε).Nonempty := by
  refine ⟨![((Real.log ε - 1 : ℝ) : ℂ), 0, 0], ?_⟩
  simp [logarithmicTube]

theorem CuspQuotient.norm_time_coordinateExp (z : ToricCharts.CoordinateSpace 3) :
    ‖ToricFan.Triangle.time (ToricCharts.coordinateExp z)‖ = Real.exp (z 0 + z 1 + z 2).re := by
  simp only [ToricFan.Triangle.time, ToricCharts.coordinateExp, ← Complex.exp_add,
    Complex.norm_exp]

theorem CuspQuotient.coordinateExp_mem_affineTube_iff {ε : ℝ} (hε : 0 < ε)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.coordinateExp z ∈ affineTube ε ↔ z ∈ logarithmicTube ε := by
  change
    ‖ToricFan.Triangle.time (ToricCharts.coordinateExp z)‖ < ε ↔ (z 0 + z 1 + z 2).re < Real.log ε
  rw [norm_time_coordinateExp]
  exact (Real.lt_log_iff_exp_lt hε).symm

theorem CuspQuotient.coordinateExp_image_logarithmicTube {ε : ℝ} (hε : 0 < ε) :
    ToricCharts.coordinateExp '' logarithmicTube ε = ToricCharts.torus ∩ affineTube ε := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun j => Complex.exp_ne_zero _, (coordinateExp_mem_affineTube_iff hε w).mpr hw⟩
  · rintro ⟨hzT, hz⟩
    obtain ⟨w, rfl⟩ := ToricCharts.range_coordinateExp.symm ▸ hzT
    exact ⟨w, (coordinateExp_mem_affineTube_iff hε w).mp hz, rfl⟩

theorem CuspQuotient.torus_inter_affineTube_isPathConnected {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (ToricCharts.torus ∩ affineTube ε) := by
  rw [← coordinateExp_image_logarithmicTube hε]
  exact
    ((logarithmicTube_convex ε).isPathConnected (logarithmicTube_nonempty ε)).image
      ToricCharts.coordinateExp_continuous

theorem CuspQuotient.domain_inter_affineTube_isPathConnected (A : Matrix (Fin 3) (Fin 3) ℤ)
    {ε : ℝ} (hε : 0 < ε) : IsPathConnected (ToricCharts.domain A ∩ affineTube ε) := by
  apply
    ((ToricCharts.domain_open A).inter (affineTube_isOpen ε)).isConnected_iff_isPathConnected.mp
  apply (torus_inter_affineTube_isPathConnected hε).isConnected.subset_closure
  · exact fun _ hz => ⟨ToricCharts.torus_subset_domain A hz.1, hz.2⟩
  · intro z hz
    simpa only [Set.inter_comm] using
      (ToricCharts.torus_dense.open_subset_closure_inter (affineTube_isOpen ε) hz.2)

theorem CuspQuotient.inclusion_affineTube_subset (s : ToricFan.Triangle) (ε : ℝ) :
    ToricSpace.inclusion s '' affineTube ε ⊆
      (ToricSpace.tubeOpen (disc ε) : Set ToricSpace.Space) := by
  rw [tube_eq_union]
  exact Set.subset_iUnion (fun t => ToricSpace.inclusion t '' affineTube ε) s

theorem CuspQuotient.inclusion_affineTube_isOpen (s : ToricFan.Triangle) (ε : ℝ) :
    IsOpen (ToricSpace.inclusion s '' affineTube ε) :=
  (ToricSpace.inclusion_openEmbedding s).isOpenMap _ (affineTube_isOpen ε)

theorem CuspQuotient.inclusion_affineTube_isSimplyConnected (s : ToricFan.Triangle) {ε : ℝ}
    (hε : 0 < ε) : IsSimplyConnected (ToricSpace.inclusion s '' affineTube ε) :=
  (ToricSpace.inclusion_openEmbedding s).isEmbedding.isSimplyConnected_image.mpr
    (affineTube_isSimplyConnected hε)

theorem CuspQuotient.inclusion_affineTubes_inter (s t : ToricFan.Triangle) (ε : ℝ) :
    (ToricSpace.inclusion s '' affineTube ε) ∩ (ToricSpace.inclusion t '' affineTube ε) =
      ToricSpace.inclusion s ''
        (ToricCharts.domain (ToricFan.Triangle.transition s t) ∩ affineTube ε) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨w, _, hw⟩⟩
    refine ⟨z, ⟨?_, hz⟩, rfl⟩
    simpa only [ToricFan.Triangle.chartChange_source] using
      ((ToricSpace.inclusion_eq_iff s t z w).mp hw.symm).1
  · rintro ⟨z, ⟨hzD, hz⟩, rfl⟩
    have hzS : z ∈ (ToricFan.Triangle.chartChange s t).source := by
      simpa only [ToricFan.Triangle.chartChange_source] using hzD
    refine ⟨⟨z, hz, rfl⟩, ToricFan.Triangle.chartChange s t z, ?_, ?_⟩
    · change ‖ToricFan.Triangle.time (ToricFan.Triangle.chartChange s t z)‖ < ε
      have he :
        ToricFan.Triangle.time (ToricFan.Triangle.chartChange s t z) = ToricFan.Triangle.time z :=
        ToricFan.Triangle.chartChange_preserves_time s t hzS
      rw [he]
      exact hz
    · exact ((ToricSpace.inclusion_eq_iff s t z _).mpr ⟨hzS, rfl⟩).symm

theorem CuspQuotient.inclusion_affineTubes_inter_isPathConnected (s t : ToricFan.Triangle) {ε : ℝ}
    (hε : 0 < ε) :
    IsPathConnected
      ((ToricSpace.inclusion s '' affineTube ε) ∩ (ToricSpace.inclusion t '' affineTube ε)) := by
  rw [inclusion_affineTubes_inter]
  exact
    (domain_inter_affineTube_isPathConnected (ToricFan.Triangle.transition s t) hε).image
      (ToricSpace.inclusion_openEmbedding s).continuous

def CuspQuotient.affineTubeChart (ε : ℝ) (s : ToricFan.Triangle) :
    Set (ToricSpace.Tube (disc ε)) :=
  Subtype.val ⁻¹' (ToricSpace.inclusion s '' affineTube ε)

theorem CuspQuotient.affineTubeChart_isOpen (ε : ℝ) (s : ToricFan.Triangle) :
    IsOpen (affineTubeChart ε s) :=
  (inclusion_affineTube_isOpen s ε).preimage continuous_subtype_val

theorem CuspQuotient.affineTubeChart_isSimplyConnected {ε : ℝ} (hε : 0 < ε)
    (s : ToricFan.Triangle) : IsSimplyConnected (affineTubeChart ε s) := by
  apply Topology.IsEmbedding.subtypeVal.isSimplyConnected_image.mp
  have he :
    (Subtype.val : ToricSpace.Tube (disc ε) → ToricSpace.Space) '' affineTubeChart ε s =
      ToricSpace.inclusion s '' affineTube ε := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, inclusion_affineTube_subset s ε hx⟩, hx, rfl⟩
  rw [he]
  exact inclusion_affineTube_isSimplyConnected s hε

theorem CuspQuotient.affineTubeCharts_inter_isPathConnected {ε : ℝ} (hε : 0 < ε)
    (s t : ToricFan.Triangle) : IsPathConnected (affineTubeChart ε s ∩ affineTubeChart ε t) := by
  change
    IsPathConnected
      ((Subtype.val : ToricSpace.Tube (disc ε) → ToricSpace.Space) ⁻¹'
        ((ToricSpace.inclusion s '' affineTube ε) ∩ (ToricSpace.inclusion t '' affineTube ε)))
  exact
    (inclusion_affineTubes_inter_isPathConnected s t hε).preimage_coe
      (Set.inter_subset_left.trans (inclusion_affineTube_subset s ε))

theorem CuspQuotient.affineTubeCharts_cover (ε : ℝ) :
    ⋃ s : ToricFan.Triangle, affineTubeChart ε s = Set.univ := by
  unfold affineTubeChart
  rw [← Set.preimage_iUnion, ← tube_eq_union]
  ext x
  simp

theorem CuspQuotient.tube_simplyConnected {ε : ℝ} (hε : 0 < ε) :
    SimplyConnectedSpace (ToricSpace.Tube (disc ε)) := by
  obtain ⟨x, hx⟩ := tube_charts_common_point hε
  have hxTube : x ∈ (ToricSpace.tubeOpen (disc ε) : Set ToricSpace.Space) :=
    inclusion_affineTube_subset ToricSpace.referenceTriangle ε
      (Set.mem_iInter.mp hx ToricSpace.referenceTriangle)
  exact
    simplyConnectedSpace_of_open_cover (affineTubeChart ε) (affineTubeChart_isOpen ε)
      (affineTubeCharts_cover ε) (affineTubeChart_isSimplyConnected hε) ⟨x, hxTube⟩
      (fun s => Set.mem_iInter.mp hx s) (affineTubeCharts_inter_isPathConnected hε)

theorem CuspQuotient.quotient_pathConnected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : PathConnectedSpace (QuotientSpace C ε) := by
  let : SimplyConnectedSpace (ToricSpace.Tube (disc ε)) := tube_simplyConnected hε
  have hq : Function.Surjective (quotientMap C ε) := Quotient.mk_surjective
  exact hq.pathConnectedSpace (quotientMap_continuous C ε)

abbrev FullPeriodMatrix.IntegerPeriods :=
  (Fin 2 → ℤ) × (Fin 2 → ℤ)

def FullPeriodMatrix.periodVector (p : FullPeriodMatrix) : IntegerPeriods →+ ComplexPlane₂
    where
  toFun c := (fun i => (c.1 i : ℂ)) + p.matrix *ᵥ (fun i => (c.2 i : ℂ))
  map_zero' := by ext i; fin_cases i <;> simp []
  map_add' c
    d := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring

theorem FullPeriodMatrix.periodVector_eq_periodLinear (p : FullPeriodMatrix)
    (c : IntegerPeriods) :
    p.periodVector c = p.periodLinear ((fun i => (c.1 i : ℝ)), (fun i => (c.2 i : ℝ))) := by
  ext i
  fin_cases i <;> simp [periodVector, periodLinear, Matrix.vecHead, Matrix.vecTail]

theorem FullPeriodMatrix.periodVector_injective (p : FullPeriodMatrix) :
    Function.Injective p.periodVector := by
  intro c d h
  rw [p.periodVector_eq_periodLinear, p.periodVector_eq_periodLinear] at h
  have he := p.periodLinear_bijective.1 h
  apply Prod.ext
  · ext i
    have hi : (c.1 i : ℝ) = (d.1 i : ℝ) := congrFun (congrArg Prod.fst he) i
    exact_mod_cast hi
  · ext i
    have hi : (c.2 i : ℝ) = (d.2 i : ℝ) := congrFun (congrArg Prod.snd he) i
    exact_mod_cast hi

theorem FullPeriodMatrix.periodVector_mem_lattice (p : FullPeriodMatrix) (c : IntegerPeriods) :
    p.periodVector c ∈ p.lattice :=
  (p.mem_lattice_iff _).mpr ⟨c.1, c.2, rfl⟩

def FullPeriodMatrix.periodLatticeMap (p : FullPeriodMatrix) : IntegerPeriods →+ p.lattice :=
  p.periodVector.codRestrict p.lattice.toAddSubgroup p.periodVector_mem_lattice

theorem FullPeriodMatrix.periodLatticeMap_bijective (p : FullPeriodMatrix) :
    Function.Bijective p.periodLatticeMap := by
  constructor
  · intro c d h
    exact p.periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨m, n, hmn⟩ := (p.mem_lattice_iff z).mp z.property
    exact ⟨(m, n), Subtype.ext hmn.symm⟩

def FullPeriodMatrix.periodLatticeEquiv (p : FullPeriodMatrix) : IntegerPeriods ≃+ p.lattice :=
  AddEquiv.ofBijective p.periodLatticeMap p.periodLatticeMap_bijective

def FullPeriodMatrix.latticeEquiv (p : FullPeriodMatrix) : p.lattice ≃+ IntegerPeriods :=
  p.periodLatticeEquiv.symm

theorem FullPeriodMatrix.periodVector_latticeEquiv (p : FullPeriodMatrix) (z : p.lattice) :
    p.periodVector (p.latticeEquiv z) = z :=
  congrArg Subtype.val (p.periodLatticeEquiv.apply_symm_apply z)

theorem FullPeriodMatrix.quotientCovering (p : FullPeriodMatrix) :
    IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
  apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (p.lattice : Set ComplexPlane₂)
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact DiscreteTopology.isDiscrete

def FullPeriodMatrix.zeroLift (p : FullPeriodMatrix) : p.lattice.mkQ ⁻¹' ({0} : Set p.Torus) :=
  ⟨0, by simp⟩

def FullPeriodMatrix.fundamentalGroupEquiv (p : FullPeriodMatrix) :
    FundamentalGroup p.Torus 0 ≃* Multiplicative IntegerPeriods :=
  ((p.quotientCovering.fundamentalGroupEquiv p.zeroLift).trans MulOpposite.opMulEquiv.symm).trans
    p.latticeEquiv.toMultiplicative

theorem FullPeriodMatrix.fundamentalGroupEquiv_monodromy (p : FullPeriodMatrix)
    (γ : FundamentalGroup p.Torus 0) :
    p.periodVector (p.fundamentalGroupEquiv γ).toAdd =
      (p.quotientCovering.isCoveringMap.monodromy γ p.zeroLift : ComplexPlane₂) := by
  have h := p.quotientCovering.unop_fundamentalGroupToMulOpposite_smul (e := p.zeroLift) (γ := γ)
  change
    p.periodVector
        (p.latticeEquiv
          (p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift γ).unop.toAdd) =
      _
  rw [p.periodVector_latticeEquiv]
  change
    ((p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift γ).unop.toAdd : ComplexPlane₂) +
        0 =
      _ at h
  simpa only [add_zero] using h

@[simp]
theorem FullPeriodMatrix.mkQ_periodVector (p : FullPeriodMatrix) (c : IntegerPeriods) :
    p.lattice.mkQ (p.periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr (p.periodVector_mem_lattice c)

def FullPeriodMatrix.periodLoop (p : FullPeriodMatrix) (c : IntegerPeriods) :
    Path (0 : p.Torus) 0 :=
  ((Path.segment (0 : ComplexPlane₂) (p.periodVector c)).map p.lattice.continuous_mkQ).cast
    (map_zero p.lattice.mkQ).symm (p.mkQ_periodVector c).symm

theorem FullPeriodMatrix.periodLoop_apply (p : FullPeriodMatrix) (c : IntegerPeriods)
    (t : unitInterval) : p.periodLoop c t = p.lattice.mkQ ((t : ℝ) • p.periodVector c) := by
  simp only [periodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    AffineMap.lineMap_apply_module, smul_zero, zero_add]

theorem FullPeriodMatrix.periodLoop_monodromy (p : FullPeriodMatrix) (c : IntegerPeriods) :
    p.quotientCovering.isCoveringMap.monodromy (FundamentalGroup.fromPath ⟦p.periodLoop c⟧)
        p.zeroLift =
      ⟨p.periodVector c, p.mkQ_periodVector c⟩ := by
  apply
    p.quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (Path.segment (0 : ComplexPlane₂) (p.periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

@[simp]
theorem FullPeriodMatrix.fundamentalGroupEquiv_periodLoop (p : FullPeriodMatrix)
    (c : IntegerPeriods) :
    p.fundamentalGroupEquiv (FundamentalGroup.fromPath ⟦p.periodLoop c⟧) =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply p.periodVector_injective
  rw [p.fundamentalGroupEquiv_monodromy, p.periodLoop_monodromy]
  rfl

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

def CuspQuotient.fundamentalGroupEquivAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (e : ToricSpace.Tube (disc ε)) :
    FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e) ≃* LatticeGroup := by
  let := ToricSpace.tubeAction C (disc ε)
  let := tube_simplyConnected hε
  let hq := quotientMap_covering C ε hε hε1 hC hR
  exact (hq.fundamentalGroupEquiv ⟨e, rfl⟩).trans MulOpposite.opMulEquiv.symm

def CuspQuotient.fundamentalGroupEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : QuotientSpace C ε) :
    FundamentalGroup (QuotientSpace C ε) x ≃* LatticeGroup := by
  let := ToricSpace.tubeAction C (disc ε)
  let := tube_simplyConnected hε
  let hq := quotientMap_covering C ε hε hε1 hC hR
  let e : quotientMap C ε ⁻¹' { x } := ⟨(hq.surjective x).choose, (hq.surjective x).choose_spec⟩
  exact (hq.fundamentalGroupEquiv e).trans MulOpposite.opMulEquiv.symm

theorem CuspQuotient.fundamentalGroupEquivAt_monodromy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (e : ToricSpace.Tube (disc ε))
    (γ : FundamentalGroup (QuotientSpace C ε) (quotientMap C ε e)) :
    letI := ToricSpace.tubeAction C (disc ε)
    ToricSpace.tubeTranslate C (disc ε) (fundamentalGroupEquivAt C ε hε hε1 hC hR e γ).toAdd e =
      ((quotientMap_covering C ε hε hε1 hC hR).isCoveringMap.monodromy γ ⟨e, rfl⟩ :
        ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  let := tube_simplyConnected hε
  exact (quotientMap_covering C ε hε hε1 hC hR).unop_fundamentalGroupToMulOpposite_smul

def CuspQuotient.singularH1Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : QuotientSpace C ε) :
    FirstHurewicz.SingularH1 (QuotientSpace C ε) ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  let := quotient_pathConnected C ε hε
  exact FirstHurewicz.singularH1EquivOfPi1 x (fundamentalGroupEquiv C ε hε hε1 hC hR x)

theorem CuspCentralHomology.central_pathConnectedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) : PathConnectedSpace (CuspRetraction.QuotientCentralFibre C r) := by
  exact
    (CuspHoneycomb.honeycombCollapseMap_surjective C r hr).pathConnectedSpace
      (CuspHoneycomb.honeycombCollapseMap_continuous C r hr)

def CuspCentralHomology.centralBasePoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    CuspRetraction.QuotientCentralFibre C r :=
  CuspHoneycomb.honeycombCollapseMap C r hr (1, 0)

def CuspCentralHomology.centralSingularH0Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 0 ≃ₗ[ℤ] ℤ := by
  let := central_pathConnectedSpace C r hr
  exact
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv (CuspRetraction.QuotientCentralFibre C r)

theorem CuspCentralHomology.centralSingularH0Equiv_natural (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (a : SingularMayerVietoris.SingularHomology X 0) :
    centralSingularH0Equiv C r hr (SingularMayerVietoris.singularHomologyMap f 0 a) =
      PeriodTorusHigherHomology.connectedHomologyZeroEquiv X a := by
  let := central_pathConnectedSpace C r hr
  exact PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural f a

structure CuspCentralHomology.SmallCentralModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < r
  radius_lt_one : radius < 1
  smallDrift : ToricSpace.SmallDrift C radius
  equivalence : CuspRetraction.QuotientCentralFibre C r ≃ₕ CuspQuotient.QuotientSpace C radius
  inclusion_eq :
    equivalence.toFun = centralIntoSmallerQuotient C r radius radius_pos radius_lt.le hC

theorem CuspCentralHomology.exists_smallCentralModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Nonempty (SmallCentralModel C r hC) := by
  obtain ⟨δ₀, hδ₀, hδ₀r, _hδ₀1, he⟩ := exists_centralHomotopyEquiv C r hr hC
  have hCδ₀ : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ₀) := fun i j =>
    (hC i j).mono (Metric.ball_subset_ball hδ₀r.le)
  obtain ⟨δ, hδ, hδδ₀, hδ1, hR, _hCδ⟩ := CuspQuotient.exists_admissible_radius C hδ₀ hCδ₀
  have hδr := hδδ₀.trans hδ₀r
  obtain ⟨e, he⟩ := he δ hδ hδδ₀.le hδr.le
  exact ⟨⟨δ, hδ, hδr, hδ1, hR, e, he⟩⟩

def CuspCentralHomology.smallCentralModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SmallCentralModel C r hC :=
  Classical.choice (exists_smallCentralModel C r hr hC)

theorem CuspCentralHomology.SmallCentralModel.holomorphic {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {r : ℝ} {hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)}
    (M : CuspCentralHomology.SmallCentralModel C r hC) :
    ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 M.radius) := fun i j =>
  (hC i j).mono (Metric.ball_subset_ball M.radius_lt.le)

def CuspCentralHomology.SmallCentralModel.singularH1Equiv {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {r : ℝ} {hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)}
    (M : CuspCentralHomology.SmallCentralModel C r hC)
    (q : CuspRetraction.QuotientCentralFibre C r) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv M.equivalence 1).trans
    (CuspQuotient.singularH1Equiv C M.radius M.radius_pos M.radius_lt_one M.holomorphic
      M.smallDrift (M.equivalence q))

def CuspCentralHomology.centralSingularH1Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (smallCentralModel C r hr hC).singularH1Equiv (centralBasePoint C r hr)

theorem CuspCentralHomology.centralSingularH1_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1) :=
  Module.Free.of_equiv (centralSingularH1Equiv C r hr hC).symm

theorem CuspCentralHomology.centralSingularH1_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1) :=
  Module.Finite.of_surjective (centralSingularH1Equiv C r hr hC).symm.toLinearMap
    (centralSingularH1Equiv C r hr hC).symm.surjective

theorem CuspCentralHomology.centralSingularH1_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1) =
      2 := by
  rw [(centralSingularH1Equiv C r hr hC).finrank_eq]
  simp

def ToricSpace.fibreCoordinatePhase (s : ToricFan.Triangle) (u : CompactFibreTorus) :
    CompactTorus := fun i =>
  ⟨factors s (compactTorusUnits (compactFibrePhase u)) i,
    mem_sphere_zero_iff_norm.mpr (norm_factors_compactTorusUnits s (compactFibrePhase u) i)⟩

@[simp]
theorem ToricSpace.fibreCoordinatePhase_coe (s : ToricFan.Triangle) (u : CompactFibreTorus)
    (i : Fin 3) :
    (fibreCoordinatePhase s u i : ℂ) = factors s (compactTorusUnits (compactFibrePhase u)) i :=
  rfl

theorem ToricSpace.fibreCoordinatePhase_prod (s : ToricFan.Triangle) (u : CompactFibreTorus) :
    ∏ i, fibreCoordinatePhase s u i = 1 := by
  apply Circle.ext
  change Circle.coeHom (∏ i, fibreCoordinatePhase s u i) = (1 : ℂ)
  rw [map_prod]
  change (∏ i, factors s (compactTorusUnits (compactFibrePhase u)) i) = 1
  simpa [compactFibrePhase, Fin.prod_univ_succ, ToricFan.Triangle.time, mul_assoc] using
    time_factors s (compactTorusUnits (compactFibrePhase u))

theorem ToricSpace.monomial_rays_fibreCoordinatePhase (s : ToricFan.Triangle)
    (u : CompactFibreTorus) :
    ToricCharts.monomial s.rays (fun i => (fibreCoordinatePhase s u i : ℂ)) = fun i =>
      (compactFibrePhase u i : ℂ) :=
  monomial_rays_factors s (compactTorusUnits (compactFibrePhase u))

theorem ToricSpace.compactFibreAction_inclusion_eq_self_iff_coordinatePhase
    (u : CompactFibreTorus) (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    compactFibreAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∀ i, z i ≠ 0 → fibreCoordinatePhase s u i = 1 := by
  rw [compactFibreAction_eq_compact, compactTorusAction_inclusion_eq_self_iff]
  simp only [← fibreCoordinatePhase_coe, Circle.coe_eq_one]

theorem ToricSpace.compactFibrePhase_vertexDifference (s : ToricFan.Triangle) (j k : Fin 3)
    (a : Circle) :
    compactFibrePhase (fun i => a ^ (s.vertex k i - s.vertex j i)) =
      rayCompactPhase (s.vertex j) a⁻¹ * rayCompactPhase (s.vertex k) a := by
  funext i
  fin_cases i <;> simp [compactFibrePhase, rayCompactPhase, zpow_sub, mul_comm]

theorem ToricSpace.factors_vertexDifferencePhase (s : ToricFan.Triangle) (j k : Fin 3)
    (a : Circle) :
    factors s (fibreMultiplier (compactFibreUnits (fun i => a ^ (s.vertex k i - s.vertex j i)))) =
      (fun i => if i = j then (a : ℂ)⁻¹ else 1) * (fun i => if i = k then (a : ℂ) else 1) := by
  rw [← compactTorusUnits_compactFibrePhase, compactFibrePhase_vertexDifference, map_mul,
    factors_mul, factors_rayCompactPhase_vertex, factors_rayCompactPhase_vertex]
  rfl

theorem ToricSpace.compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero
    (u : CompactFibreTorus) (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3)
    (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) :
    compactFibreAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔ u = 1 := by
  constructor
  · intro h
    have hf := (compactFibreAction_inclusion_eq_self_iff_coordinatePhase u s z).mp h
    have hrest (i : Fin 3) (hij : i ≠ j) : fibreCoordinatePhase s u i = 1 := hf i (hz i hij)
    have hp : (∏ i, fibreCoordinatePhase s u i) = fibreCoordinatePhase s u j :=
      Finset.prod_eq_single j (fun i _ hij => hrest i hij) (by simp)
    have hj : fibreCoordinatePhase s u j = 1 := hp.symm.trans (fibreCoordinatePhase_prod s u)
    have hall : fibreCoordinatePhase s u = 1 := by
      funext i
      by_cases hij : i = j
      · simpa only [hij, Pi.one_apply] using hj
      · exact hrest i hij
    have hr := monomial_rays_fibreCoordinatePhase s u
    have hc : (fun i => (fibreCoordinatePhase s u i : ℂ)) = 1 := by
      rw [hall]
      rfl
    rw [hc, ToricCharts.monomial_ones] at hr
    funext i
    apply Circle.ext
    have hi := congrFun hr i.castSucc
    fin_cases i <;> simpa [compactFibrePhase] using hi.symm
  · rintro rfl
    exact compactFibreAction_one _

theorem ToricSpace.compactFibreAction_inclusion_eq_self_iff_of_two_zero (u : CompactFibreTorus)
    (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k)
    (hzj : z j = 0) (hzk : z k = 0) (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    compactFibreAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s z ↔
      ∃ a : Circle, ∀ i : Fin 2, u i = a ^ (s.vertex k i - s.vertex j i) := by
  constructor
  · intro h
    have hf := (compactFibreAction_inclusion_eq_self_iff_coordinatePhase u s z).mp h
    have hrest (i : Fin 3) (hij : i ≠ j) (hik : i ≠ k) : fibreCoordinatePhase s u i = 1 :=
      hf i (hz i hij hik)
    have hp : fibreCoordinatePhase s u j * fibreCoordinatePhase s u k = 1 := by
      calc
        fibreCoordinatePhase s u j * fibreCoordinatePhase s u k =
            ∏ i ∈ ({ j, k } : Finset (Fin 3)), fibreCoordinatePhase s u i :=
          (Finset.prod_pair hjk).symm
        _ = ∏ i, fibreCoordinatePhase s u i := by
          apply Finset.prod_subset (Finset.subset_univ _)
          intro i _ hi
          have hi' : i ≠ j ∧ i ≠ k := by simpa using hi
          exact hrest i hi'.1 hi'.2
        _ = 1 := fibreCoordinatePhase_prod s u
    have hj : fibreCoordinatePhase s u j = (fibreCoordinatePhase s u k)⁻¹ :=
      eq_inv_iff_mul_eq_one.mpr hp
    let a := fibreCoordinatePhase s u k
    have hc :
      (fun i => (fibreCoordinatePhase s u i : ℂ)) =
        (fun i => if i = j then (a : ℂ)⁻¹ else 1) * (fun i => if i = k then (a : ℂ) else 1) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [hj, hjk, a]
      · by_cases hik : i = k
        · subst i
          simp [hjk.symm, a]
        · simp [hij, hik, hrest i hij hik]
    have hr := monomial_rays_fibreCoordinatePhase s u
    rw [hc, ToricCharts.monomial_mul, monomial_single_coordinate_phase,
      monomial_single_coordinate_phase] at hr
    refine ⟨a, ?_⟩
    intro i
    apply Circle.ext
    have hi := congrFun hr i.castSucc
    have hphase : compactFibrePhase u i.castSucc = u i := by fin_cases i <;> rfl
    rw [hphase] at hi
    change (u i : ℂ) = (a : ℂ) ^ (s.vertex k i - s.vertex j i)
    rw [ToricFan.Triangle.vertex, ToricFan.Triangle.vertex, zpow_sub₀ a.coe_ne_zero,
      div_eq_mul_inv]
    simpa only [Pi.mul_apply, inv_zpow, mul_comm] using hi.symm
  · rintro ⟨a, ha⟩
    have hu : u = fun i => a ^ (s.vertex k i - s.vertex j i) := funext ha
    rw [compactFibreAction, torusAction_inclusion_eq_self_iff, hu]
    intro i hi
    have hij : i ≠ j := fun hij => hi (hij ▸ hzj)
    have hik : i ≠ k := fun hik => hi (hik ▸ hzk)
    rw [factors_vertexDifferencePhase]
    simp [hij, hik]

@[simp]
theorem ToricSpace.compactFibreAction_inclusion_zero (u : CompactFibreTorus)
    (s : ToricFan.Triangle) :
    compactFibreAction u (ToricSpace.inclusion s 0) = ToricSpace.inclusion s 0 := by
  rw [compactFibreAction, torusAction_inclusion_eq_self_iff]
  intro i hi
  exact (hi rfl).elim

def ToricSpace.edgeCompactPhase (d : Fin 2 → ℤ) : Circle →* CompactFibreTorus
    where
  toFun a i := a ^ d i
  map_one' := by
    funext i
    exact one_zpow (d i)
  map_mul' a
    b := by
    funext i
    exact mul_zpow a b (d i)

def ToricSpace.edgeCircle (d : Fin 2 → ℤ) : Subgroup CompactFibreTorus :=
  (edgeCompactPhase d).range

theorem ToricSpace.mem_edgeCircle_iff (d : Fin 2 → ℤ) (u : CompactFibreTorus) :
    u ∈ edgeCircle d ↔ ∃ a : Circle, ∀ i : Fin 2, u i = a ^ d i := by
  change (∃ a : Circle, edgeCompactPhase d a = u) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i => (congrFun ha i).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun i => (ha i).symm⟩

theorem ToricSpace.edgeCompactPhase_continuous (d : Fin 2 → ℤ) :
    Continuous (edgeCompactPhase d) := by
  apply continuous_pi
  intro i
  exact continuous_id.zpow (d i)

theorem ToricSpace.compactFibre_stabilizer_eq_bot_of_at_most_one_zero (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (ToricSpace.inclusion s z) = ⊥ := by
  ext u
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  exact compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero u s z j hz

theorem ToricSpace.compactFibre_stabilizer_eq_edgeCircle_of_two_zero (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (j k : Fin 3) (hjk : j ≠ k) (hzj : z j = 0)
    (hzk : z k = 0) (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) :
    MulAction.stabilizer CompactFibreTorus (ToricSpace.inclusion s z) =
      edgeCircle (s.vertex k - s.vertex j) := by
  ext u
  rw [MulAction.mem_stabilizer_iff, mem_edgeCircle_iff]
  exact compactFibreAction_inclusion_eq_self_iff_of_two_zero u s z j k hjk hzj hzk hz

theorem ToricSpace.compactFibre_stabilizer_inclusion_zero (s : ToricFan.Triangle) :
    MulAction.stabilizer CompactFibreTorus (ToricSpace.inclusion s 0) = ⊤ := by
  ext u
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun _ => Subgroup.mem_top u, fun _ => compactFibreAction_inclusion_zero u s⟩

def CuspCentralHomology.edgeCharacter (n : Fin 2 → ℤ) : ToricSpace.CompactFibreTorus →* Circle
    where
  toFun u := u 0 ^ (-n 1) * u 1 ^ n 0
  map_one' := by simp
  map_mul' u
    v := by
    simp only [Pi.mul_apply, mul_zpow]
    ac_rfl

theorem CuspCentralHomology.edgeCharacter_continuous (n : Fin 2 → ℤ) :
    Continuous (edgeCharacter n) :=
  ((continuous_apply 0).zpow (-n 1)).mul ((continuous_apply 1).zpow (n 0))

theorem CuspCentralHomology.edgeCharacter_edgeCompactPhase (n m : Fin 2 → ℤ) (a : Circle) :
    edgeCharacter n (ToricSpace.edgeCompactPhase m a) = a ^ (n 0 * m 1 - n 1 * m 0) := by
  change (a ^ m 0) ^ (-n 1) * (a ^ m 1) ^ n 0 = _
  rw [← zpow_mul, ← zpow_mul, ← zpow_add]
  congr 1
  ring

@[simp]
theorem CuspCentralHomology.edgeCharacter_own_phase (n : Fin 2 → ℤ) (a : Circle) :
    edgeCharacter n (ToricSpace.edgeCompactPhase n a) = 1 := by
  rw [edgeCharacter_edgeCompactPhase]
  simp [mul_comm]

abbrev CuspCentralHomology.hexagonCharacter (k : Fin 6) :
    ToricSpace.CompactFibreTorus →* Circle :=
  edgeCharacter (ToricComponent.hexagonRay k)

def CuspCentralHomology.hexagonCharacterSection (k : Fin 6) :
    Circle →* ToricSpace.CompactFibreTorus :=
  ToricSpace.edgeCompactPhase (ToricComponent.hexagonRay (k + 1))

theorem CuspCentralHomology.hexagonCharacterSection_continuous (k : Fin 6) :
    Continuous (hexagonCharacterSection k) :=
  ToricSpace.edgeCompactPhase_continuous _

@[simp]
theorem CuspCentralHomology.hexagonCharacter_section (k : Fin 6) (a : Circle) :
    hexagonCharacter k (hexagonCharacterSection k a) = a := by
  rw [hexagonCharacterSection, edgeCharacter_edgeCompactPhase]
  have hd :
    ToricComponent.hexagonRay k 0 * ToricComponent.hexagonRay (k + 1) 1 -
        ToricComponent.hexagonRay k 1 * ToricComponent.hexagonRay (k + 1) 0 =
      1 := by fin_cases k <;> decide
  rw [hd, zpow_one]

theorem CuspCentralHomology.hexagonCharacter_decomposition (k : Fin 6)
    (u : ToricSpace.CompactFibreTorus) :
    ToricSpace.edgeCompactPhase (ToricComponent.hexagonRay k) ((hexagonCharacter (k + 1) u)⁻¹) *
        hexagonCharacterSection k (hexagonCharacter k u) =
      u := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [hexagonCharacter, edgeCharacter, hexagonCharacterSection, ToricSpace.edgeCompactPhase,
      ToricComponent.hexagonRay]

theorem CuspCentralHomology.ker_hexagonCharacter (k : Fin 6) :
    (hexagonCharacter k).ker = ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  ext u
  constructor
  · intro hu
    change hexagonCharacter k u = 1 at hu
    change ∃ a : Circle, ToricSpace.edgeCompactPhase (ToricComponent.hexagonRay k) a = u
    refine ⟨(hexagonCharacter (k + 1) u)⁻¹, ?_⟩
    simpa only [hu, map_one, mul_one] using hexagonCharacter_decomposition k u
  · rintro ⟨a, rfl⟩
    exact edgeCharacter_own_phase (ToricComponent.hexagonRay k) a

theorem CuspCentralHomology.hexagonCharacter_eq_iff (k : Fin 6)
    (u v : ToricSpace.CompactFibreTorus) :
    hexagonCharacter k u = hexagonCharacter k v ↔
      u⁻¹ * v ∈ ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  rw [← ker_hexagonCharacter, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

theorem CuspCentralHomology.chartPoint_stabilizer_fst_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay i) := by
  have hne : ToricComponent.zeroCoordinate i ≠ CuspHoneycombHexagon.firstCoordinate i := by
    intro h
    have hv := congrArg (ToricComponent.zeroTriangle i).vertex h
    rw [ToricComponent.zeroTriangle_vertex, CuspHoneycombHexagon.firstCoordinate_vertex] at hv
    exact ToricComponent.hexagonRay_ne_zero i hv.symm
  have hrest (j : Fin 3) (hj0 : j ≠ ToricComponent.zeroCoordinate i)
    (hj1 : j ≠ CuspHoneycombHexagon.firstCoordinate i) :
    CuspHoneycombHexagon.liftCoordinates i z j ≠ 0 := by
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with h | h | h
    · exact (hj0 h).elim
    · exact (hj1 h).elim
    · subst j
      simpa only [CuspHoneycombHexagon.liftCoordinates_second] using hz1
  rw [CuspHoneycombHexagon.chartPoint_coe]
  have h :=
    ToricSpace.compactFibre_stabilizer_eq_edgeCircle_of_two_zero (ToricComponent.zeroTriangle i)
      (CuspHoneycombHexagon.liftCoordinates i z) (ToricComponent.zeroCoordinate i)
      (CuspHoneycombHexagon.firstCoordinate i) hne (CuspHoneycombHexagon.liftCoordinates_zero i z)
      (by simpa only [CuspHoneycombHexagon.liftCoordinates_first] using hz0) hrest
  simpa only [CuspHoneycombHexagon.firstCoordinate_vertex, ToricComponent.zeroTriangle_vertex,
    sub_zero] using h

theorem CuspCentralHomology.chartPoint_stabilizer_snd_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 ≠ 0) (hz1 : z 1 = 0) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay (i + 1)) := by
  have hne : ToricComponent.zeroCoordinate i ≠ CuspHoneycombHexagon.secondCoordinate i := by
    intro h
    have hv := congrArg (ToricComponent.zeroTriangle i).vertex h
    rw [ToricComponent.zeroTriangle_vertex, CuspHoneycombHexagon.secondCoordinate_vertex] at hv
    exact ToricComponent.hexagonRay_ne_zero (i + 1) hv.symm
  have hrest (j : Fin 3) (hj0 : j ≠ ToricComponent.zeroCoordinate i)
    (hj1 : j ≠ CuspHoneycombHexagon.secondCoordinate i) :
    CuspHoneycombHexagon.liftCoordinates i z j ≠ 0 := by
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with h | h | h
    · exact (hj0 h).elim
    · subst j
      simpa only [CuspHoneycombHexagon.liftCoordinates_first] using hz0
    · exact (hj1 h).elim
  rw [CuspHoneycombHexagon.chartPoint_coe]
  have h :=
    ToricSpace.compactFibre_stabilizer_eq_edgeCircle_of_two_zero (ToricComponent.zeroTriangle i)
      (CuspHoneycombHexagon.liftCoordinates i z) (ToricComponent.zeroCoordinate i)
      (CuspHoneycombHexagon.secondCoordinate i) hne
      (CuspHoneycombHexagon.liftCoordinates_zero i z)
      (by simpa only [CuspHoneycombHexagon.liftCoordinates_second] using hz1) hrest
  simpa only [CuspHoneycombHexagon.secondCoordinate_vertex, ToricComponent.zeroTriangle_vertex,
    sub_zero] using h

theorem CuspCentralHomology.positiveBoundary_stabilizer_eq_edgeCircle (k : Fin 6)
    (q : CuspHoneycombHexagon.positiveBoundary k)
    (hprev : q.1 ≠ CuspHoneycombHexagon.squarePoint (k - 1) CuspHoneycombHexagon.cornerZero)
    (hcurr : q.1 ≠ CuspHoneycombHexagon.squarePoint k CuspHoneycombHexagon.cornerZero) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1.1 : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  obtain ⟨i, z, he⟩ := CuspHoneycombHexagon.chartPoint_jointly_surjective q.1.1
  have hqzero (hz0 : z 0 = 0) (hz1 : z 1 = 0) :
    q.1 = CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
    apply Subtype.ext
    change
      q.1.1 =
        CuspHoneycombHexagon.chartPoint i (fun j => (CuspHoneycombHexagon.cornerZero.1 j : ℂ))
    rw [← he]
    apply congrArg (CuspHoneycombHexagon.chartPoint i)
    funext j
    fin_cases j
    · change z 0 = 0
      exact hz0
    · change z 1 = 0
      exact hz1
  have hb :
    (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) ∈
      ToricSpace.rayDivisor (ToricComponent.hexagonRay k) := by
    rw [he]
    exact q.property
  rcases (CuspHoneycombHexagon.chartPoint_mem_rayDivisor_iff i k z).mp hb with ⟨rfl, hz0⟩ |
    ⟨rfl, hz1⟩
  · have hz1 : z 1 ≠ 0 := fun hz1 => hcurr (hqzero hz0 hz1)
    rw [← he]
    exact chartPoint_stabilizer_fst_zero k z hz0 hz1
  · have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hprev
      simpa only [add_sub_cancel_right] using hqzero hz0 hz1
    rw [← he]
    exact chartPoint_stabilizer_snd_zero i z hz0 hz1

theorem CuspCentralHomology.compatibleBoundaryArc_stabilizer (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  apply
    positiveBoundary_stabilizer_eq_edgeCircle k
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t)
  · intro h
    apply ht0
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_zero_point C₀ k).symm
  · intro h
    apply ht1
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_one_point C₀ k).symm

def CuspCollapse.centralPhaseOrbit (q : CuspPositiveRetraction.PositiveCentralFibre)
    (u : ToricSpace.CompactFibreTorus) : CuspRetraction.CentralFibre :=
  centralPolarMap (u, q)

@[simp]
theorem CuspCollapse.centralPhaseOrbit_apply (q : CuspPositiveRetraction.PositiveCentralFibre)
    (u : ToricSpace.CompactFibreTorus) : centralPhaseOrbit q u = centralPolarMap (u, q) :=
  rfl

abbrev CuspCollapse.CentralModulusFibre (q : CuspPositiveRetraction.PositiveCentralFibre) :=
  { x : CuspRetraction.CentralFibre // centralModulus x = q }

def CuspCollapse.centralPhaseOrbitToFibre (q : CuspPositiveRetraction.PositiveCentralFibre)
    (u : ToricSpace.CompactFibreTorus) : CentralModulusFibre q :=
  ⟨centralPhaseOrbit q u, centralModulus_centralPolarMap (u, q)⟩

theorem CuspCentralHomology.centralPhaseOrbit_eq_iff_character (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre)
    (hq :
      MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1 : ToricSpace.Space) =
        ToricSpace.edgeCircle (ToricComponent.hexagonRay k))
    (u v : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralPhaseOrbit q u = CuspCollapse.centralPhaseOrbit q v ↔
      hexagonCharacter k u = hexagonCharacter k v := by
  rw [CuspCollapse.centralPhaseOrbit_apply, CuspCollapse.centralPhaseOrbit_apply,
    CuspCollapse.centralPolarMap_eq_iff]
  simp only [true_and, hq]
  exact (hexagonCharacter_eq_iff k u v).symm

def CuspCentralHomology.characterCircleOrbit (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre) (a : Circle) :
    CuspCollapse.CentralModulusFibre q :=
  CuspCollapse.centralPhaseOrbitToFibre q (hexagonCharacterSection k a)

theorem CuspCentralHomology.characterCircleOrbit_character (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre)
    (hq :
      MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1 : ToricSpace.Space) =
        ToricSpace.edgeCircle (ToricComponent.hexagonRay k))
    (u : ToricSpace.CompactFibreTorus) :
    characterCircleOrbit k q (hexagonCharacter k u) = CuspCollapse.centralPhaseOrbitToFibre q u :=
  by
  apply Subtype.ext
  apply (centralPhaseOrbit_eq_iff_character k q hq _ _).mpr
  exact hexagonCharacter_section k _

theorem CuspCentralHomology.characterCircleOrbit_injective (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre)
    (hq :
      MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1 : ToricSpace.Space) =
        ToricSpace.edgeCircle (ToricComponent.hexagonRay k)) :
    Function.Injective (characterCircleOrbit k q) := by
  intro a b hab
  have he := (centralPhaseOrbit_eq_iff_character k q hq _ _).mp (congrArg Subtype.val hab)
  simpa only [hexagonCharacter_section] using he

def CuspCentralHomology.edgeArcPositive (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) : CuspPositiveRetraction.PositiveCentralFibre :=
  ⟨⟨(CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1,
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.2⟩,
    ToricSpace.time_eq_zero_of_mem_rayDivisor
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1.2⟩

@[simp]
theorem CuspCentralHomology.edgeArcPositive_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) :
    (edgeArcPositive C₀ k t).1.1 =
      ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) :=
  rfl

theorem CuspCentralHomology.edgeArcPositive_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : Continuous (edgeArcPositive C₀ k) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    continuous_subtype_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp
          (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).continuous))

theorem CuspCentralHomology.edgeArcPositive_injective (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : Function.Injective (edgeArcPositive C₀ k) := by
  intro s t h
  apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : CuspPositiveRetraction.PositiveCentralFibre => q.1.1) h

theorem CuspCentralHomology.edgeArcPositive_stabilizer (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay k) :=
  compatibleBoundaryArc_stabilizer C₀ k t ht0 ht1

def CuspCentralHomology.edgeCylinder (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) : CuspRetraction.CentralFibre :=
  CuspCollapse.centralPolarMap (hexagonCharacterSection k p.2, edgeArcPositive C₀ k p.1)

@[simp]
theorem CuspCentralHomology.edgeCylinder_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) :
    (edgeCylinder C₀ k p : ToricSpace.Space) =
      ToricSpace.compactFibreAction (hexagonCharacterSection k p.2)
        ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k p.1).1.1 : ToricSpace.Space) :=
  rfl

theorem CuspCentralHomology.edgeCylinder_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    Continuous (edgeCylinder C₀ k) :=
  CuspCollapse.centralPolarMap_continuous.comp
    (((hexagonCharacterSection_continuous k).comp continuous_snd).prodMk
      ((edgeArcPositive_continuous C₀ k).comp continuous_fst))

@[simp]
theorem CuspCentralHomology.edgeCylinder_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) :
    CuspCollapse.centralModulus (edgeCylinder C₀ k p) = edgeArcPositive C₀ k p.1 :=
  CuspCollapse.centralModulus_centralPolarMap _

theorem CuspCentralHomology.edgeCylinder_character (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (u : ToricSpace.CompactFibreTorus) :
    edgeCylinder C₀ k (t, hexagonCharacter k u) =
      CuspCollapse.centralPolarMap (u, edgeArcPositive C₀ k t) :=
  congrArg Subtype.val
    (characterCircleOrbit_character k (edgeArcPositive C₀ k t)
      (edgeArcPositive_stabilizer C₀ k t ht0 ht1) u)

theorem CuspCentralHomology.edgeCylinder_eq_iff_of_interior (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (a b : Circle) :
    edgeCylinder C₀ k (s, a) = edgeCylinder C₀ k (t, b) ↔ s = t ∧ a = b := by
  constructor
  · intro h
    have hst : s = t :=
      edgeArcPositive_injective C₀ k
        (by simpa only [edgeCylinder_modulus] using congrArg CuspCollapse.centralModulus h)
    subst t
    refine ⟨rfl, ?_⟩
    apply
      characterCircleOrbit_injective k (edgeArcPositive C₀ k s)
        (edgeArcPositive_stabilizer C₀ k s hs0 hs1)
    exact Subtype.ext h
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem CuspCentralHomology.edgeCylinder_zero_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (a : Circle) :
    (edgeCylinder C₀ k (0, a) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0 := by
  rw [edgeCylinder_coe, CuspHoneycombHexagon.compatibleBoundaryArc_zero,
    CuspHoneycombHexagon.positiveBoundaryArc_zero_coe,
    ToricSpace.compactFibreAction_inclusion_zero]

@[simp]
theorem CuspCentralHomology.edgeCylinder_one_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (a : Circle) :
    (edgeCylinder C₀ k (1, a) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 := by
  rw [edgeCylinder_coe, CuspHoneycombHexagon.compatibleBoundaryArc_one,
    CuspHoneycombHexagon.positiveBoundaryArc_one_coe,
    ToricSpace.compactFibreAction_inclusion_zero]

theorem CuspCentralHomology.edgeCylinder_character_all (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) (u : ToricSpace.CompactFibreTorus) :
    edgeCylinder C₀ k (t, hexagonCharacter k u) =
      CuspCollapse.centralPolarMap (u, edgeArcPositive C₀ k t) := by
  by_cases ht0 : t = 0
  · subst t
    apply Subtype.ext
    rw [edgeCylinder_zero_coe, CuspCollapse.centralPolarMap_coe, edgeArcPositive_coe,
      CuspHoneycombHexagon.compatibleBoundaryArc_zero,
      CuspHoneycombHexagon.positiveBoundaryArc_zero_coe,
      ToricSpace.compactFibreAction_inclusion_zero]
  by_cases ht1 : t = 1
  · subst t
    apply Subtype.ext
    rw [edgeCylinder_one_coe, CuspCollapse.centralPolarMap_coe, edgeArcPositive_coe,
      CuspHoneycombHexagon.compatibleBoundaryArc_one,
      CuspHoneycombHexagon.positiveBoundaryArc_one_coe,
      ToricSpace.compactFibreAction_inclusion_zero]
  exact edgeCylinder_character C₀ k t ht0 ht1 u

def CuspCentralHomology.cornerOrigin (k : Fin 6) : CuspRetraction.CentralFibre :=
  ⟨ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0, by simp [ToricFan.Triangle.time]⟩

@[simp]
theorem CuspCentralHomology.cornerOrigin_coe (k : Fin 6) :
    (cornerOrigin k : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 :=
  rfl

theorem CuspCentralHomology.zeroTriangle_upper_eq_iff_parity (k l : Fin 6) :
    (ToricComponent.zeroTriangle k).upper = (ToricComponent.zeroTriangle l).upper ↔
      k.val % 2 = l.val % 2 := by
  have h :
    ∀ k l : Fin 6,
      (ToricComponent.zeroTriangle k).upper = (ToricComponent.zeroTriangle l).upper ↔
        k.val % 2 = l.val % 2 := by decide
  exact h k l

def CuspCentralHomology.cornerPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (k : Fin 6) : CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralProject C ε hε (cornerOrigin k)

@[simp]
theorem CuspCentralHomology.cornerPoint_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) :
    (cornerPoint C ε hε k : CuspQuotient.QuotientSpace C ε) =
      CuspQuotient.centralChartMap C ε hε (ToricComponent.zeroTriangle k)
        CuspQuotient.centralOrigin :=
  rfl

theorem CuspCentralHomology.cornerPoint_eq_iff_parity (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k l : Fin 6) :
    cornerPoint C ε hε k = cornerPoint C ε hε l ↔ k.val % 2 = l.val % 2 := by
  rw [Subtype.ext_iff, cornerPoint_coe, cornerPoint_coe,
    CuspQuotient.centralChartMap_origin_eq_iff, zeroTriangle_upper_eq_iff_parity]

def CuspCentralHomology.evenPole (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CuspRetraction.QuotientCentralFibre C ε :=
  cornerPoint C ε hε 0

def CuspCentralHomology.oddPole (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CuspRetraction.QuotientCentralFibre C ε :=
  cornerPoint C ε hε 1

theorem CuspCentralHomology.cornerPoint_eq_evenPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) : cornerPoint C ε hε k = evenPole C ε hε ↔ k.val % 2 = 0 := by
  simpa only [evenPole, Fin.val_zero, Nat.zero_mod] using cornerPoint_eq_iff_parity C ε hε k 0

theorem CuspCentralHomology.cornerPoint_eq_oddPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) : cornerPoint C ε hε k = oddPole C ε hε ↔ k.val % 2 = 1 := by
  simpa [oddPole] using cornerPoint_eq_iff_parity C ε hε k 1

theorem CuspCentralHomology.pole_ne (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    evenPole C ε hε ≠ oddPole C ε hε := by
  intro h
  have hp := (cornerPoint_eq_iff_parity C ε hε 0 1).mp h
  norm_num at hp

abbrev CuspCentralHomology.ThreeCircles :=
  _root_.Circle ⊕ (_root_.Circle ⊕ _root_.Circle)

def CuspCentralHomology.unitCircleHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv _root_.Circle

def CuspCentralHomology.unitCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm 1).trans
    PeriodTorusHigherHomology.circleHomologyOneEquiv

theorem CuspCentralHomology.unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology _root_.Circle (n + 2)) := by
  let := PeriodTorusHigherHomology.circle_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
        (n + 2)).injective.subsingleton

def CuspCentralHomology.threeCirclesHomologySplit (n : ℕ) :
    SingularMayerVietoris.SingularHomology ThreeCircles n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology _root_.Circle n ×
        (SingularMayerVietoris.SingularHomology _root_.Circle n ×
          SingularMayerVietoris.SingularHomology _root_.Circle n)) :=
  ((PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle)
          n).toAddEquiv.trans
      ((AddEquiv.refl _).prodCongr
        (PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle _root_.Circle
            n).toAddEquiv)).toIntLinearEquiv

def CuspCentralHomology.integerTripleEquiv : (ℤ × (ℤ × ℤ)) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ({    toFun a := ![a.1, a.2.1, a.2.2]
        invFun a := (a 0, (a 1, a 2))
        left_inv _ := rfl
        right_inv a := by ext i; fin_cases i <;> rfl
        map_add' a b := by ext i; fin_cases i <;> rfl } :
      (ℤ × (ℤ × ℤ)) ≃+ (Fin 3 → ℤ)).toIntLinearEquiv

def CuspCentralHomology.threeCirclesHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircles 0 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((threeCirclesHomologySplit 0).toAddEquiv.trans
      ((unitCircleHomologyZeroEquiv.toAddEquiv.prodCongr
            (unitCircleHomologyZeroEquiv.toAddEquiv.prodCongr
              unitCircleHomologyZeroEquiv.toAddEquiv)).trans
        integerTripleEquiv.toAddEquiv)).toIntLinearEquiv

def CuspCentralHomology.threeCirclesHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircles 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((threeCirclesHomologySplit 1).toAddEquiv.trans
      ((unitCircleHomologyOneEquiv.toAddEquiv.prodCongr
            (unitCircleHomologyOneEquiv.toAddEquiv.prodCongr
              unitCircleHomologyOneEquiv.toAddEquiv)).trans
        integerTripleEquiv.toAddEquiv)).toIntLinearEquiv

theorem CuspCentralHomology.threeCircles_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology ThreeCircles (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (threeCirclesHomologySplit (n + 2)).injective.subsingleton

def CuspCentralHomology.sumCoordinates : (Fin 3 → ℤ) →ₗ[ℤ] ℤ
    where
  toFun a := ∑ i, a i
  map_add' a b := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r a := by simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]

@[simp]
theorem CuspCentralHomology.sumCoordinates_apply (a : Fin 3 → ℤ) :
    sumCoordinates a = a 0 + a 1 + a 2 := by
  simp only [sumCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_three]

private theorem CuspCentralHomology.sumHomology_map_mo1973_12039 {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X ⊕ Y, Z)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    SingularMayerVietoris.singularHomologyMap f n a =
      SingularMayerVietoris.singularHomologyMap (f.comp (PeriodTorusHigherHomology.sumInlMap X Y))
          n (PeriodTorusHigherHomology.sumHomologyEquiv X Y n a).1 +
        SingularMayerVietoris.singularHomologyMap
          (f.comp (PeriodTorusHigherHomology.sumInrMap X Y)) n
          (PeriodTorusHigherHomology.sumHomologyEquiv X Y n a).2 := by
  have hf :
    f =
      PeriodTorusHigherHomology.sumElimMap (f.comp (PeriodTorusHigherHomology.sumInlMap X Y))
        (f.comp (PeriodTorusHigherHomology.sumInrMap X Y)) := by
    ext x
    cases x <;> rfl
  conv_lhs => rw [hf]
  exact PeriodTorusHigherHomology.sumHomologyEquiv_sumElim _ _ n a

theorem CuspCentralHomology.threeCirclesHomologyZeroEquiv_map {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (f : C(ThreeCircles, Y))
    (a : SingularMayerVietoris.SingularHomology ThreeCircles 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (SingularMayerVietoris.singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesHomologyZeroEquiv a) := by
  rw [sumHomology_map_mo1973_12039 f, map_add]
  rw [sumHomology_map_mo1973_12039
      (f.comp
        (PeriodTorusHigherHomology.sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle))),
    map_add]
  rw [PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural,
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural,
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural, sumCoordinates_apply]
  exact (add_assoc _ _ _).symm

theorem CuspCentralHomology.threeCirclesHomologyZeroEquiv_map_homotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ ThreeCircles)
    (f : C(X, Y)) (a : SingularMayerVietoris.SingularHomology X 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (SingularMayerVietoris.singularHomologyMap f 0 a) =
      sumCoordinates
        (threeCirclesHomologyZeroEquiv
          (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0 a)) := by
  obtain ⟨b, rfl⟩ := (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0).symm.surjective a
  rw [LinearEquiv.apply_symm_apply,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply]
  change
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (((SingularMayerVietoris.singularHomologyMap f 0).comp
            (SingularMayerVietoris.singularHomologyMap e.invFun 0))
          b) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact threeCirclesHomologyZeroEquiv_map (f.comp e.invFun) b

def CuspCentralHomology.sumCoordinatesKernelEquiv :
    LinearMap.ker sumCoordinates ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({    toFun a := ![a.1 1, a.1 2]
        invFun
          a :=
          ⟨![-a 0 - a 1, a 0, a 1],
            by
            change sumCoordinates ![-a 0 - a 1, a 0, a 1] = 0
            rw [sumCoordinates_apply]
            change -a 0 - a 1 + a 0 + a 1 = 0
            ring⟩
        left_inv
          a := by
          apply Subtype.ext
          have ha : a.1 0 + a.1 1 + a.1 2 = 0 := by
            simpa only [LinearMap.mem_ker, sumCoordinates_apply] using a.2
          ext i
          fin_cases i
          · change -a.1 1 - a.1 2 = a.1 0
            omega
          · rfl
          · rfl
        right_inv a := by ext i; fin_cases i <;> rfl
        map_add' a b := by ext i; fin_cases i <;> rfl } :
      LinearMap.ker sumCoordinates ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

@[simp]
theorem CuspCentralHomology.centralProject_edgeCylinder_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (0, a)) =
      cornerPoint C ε hε (k - 1) :=
  congrArg (CuspCollapse.centralProject C ε hε) (Subtype.ext (edgeCylinder_zero_coe (C 0) k a))

@[simp]
theorem CuspCentralHomology.centralProject_edgeCylinder_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (1, a)) = cornerPoint C ε hε k :=
  congrArg (CuspCollapse.centralProject C ε hε) (Subtype.ext (edgeCylinder_one_coe (C 0) k a))

def CuspCentralHomology.doubleCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : unitInterval × ThreeCircles) : CuspRetraction.QuotientCentralFibre C ε :=
  match p.2 with
  | Sum.inl a => CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 0 (p.1, a))
  | Sum.inr (Sum.inl a) =>
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm p.1, a))
  | Sum.inr (Sum.inr a) => CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 2 (p.1, a))

@[simp]
theorem CuspCentralHomology.doubleCylinder_first (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inl a) =
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 0 (t, a)) :=
  rfl

@[simp]
theorem CuspCentralHomology.doubleCylinder_middle (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inr (Sum.inl a)) =
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm t, a)) :=
  rfl

@[simp]
theorem CuspCentralHomology.doubleCylinder_last (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inr (Sum.inr a)) =
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 2 (t, a)) :=
  rfl

theorem CuspCentralHomology.doubleCylinder_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (doubleCylinder C ε hε) := by
  have h0 :
    Continuous
      (fun p : unitInterval × Circle =>
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 0 p)) :=
    (CuspCollapse.centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) 0)
  have h1 :
    Continuous
      (fun p : unitInterval × Circle =>
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm p.1, p.2))) :=
    (CuspCollapse.centralProject_continuous C ε hε).comp
      ((edgeCylinder_continuous (C 0) 1).comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  have h2 :
    Continuous
      (fun p : unitInterval × Circle =>
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 2 p)) :=
    (CuspCollapse.centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) 2)
  let e0 :
    unitInterval × ThreeCircles ≃ₜ (unitInterval × Circle) ⊕ (unitInterval × (Circle ⊕ Circle)) :=
    Homeomorph.prodSumDistrib
  let e1 :
    unitInterval × (Circle ⊕ Circle) ≃ₜ (unitInterval × Circle) ⊕ (unitInterval × Circle) :=
    Homeomorph.prodSumDistrib
  have h := (h0.sumElim ((h1.sumElim h2).comp e1.continuous)).comp e0.continuous
  apply h.congr
  rintro ⟨t, a⟩
  rcases a with a | a | a <;> rfl

@[simp]
theorem CuspCentralHomology.doubleCylinder_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ThreeCircles) : doubleCylinder C ε hε (0, a) = oddPole C ε hε := by
  rcases a with a | a | a <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      unitInterval.symm_zero, centralProject_edgeCylinder_zero, centralProject_edgeCylinder_one]
  all_goals exact (cornerPoint_eq_oddPole_iff C ε hε _).mpr (by decide)

@[simp]
theorem CuspCentralHomology.doubleCylinder_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ThreeCircles) : doubleCylinder C ε hε (1, a) = evenPole C ε hε := by
  rcases a with a | a | a <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      unitInterval.symm_one, centralProject_edgeCylinder_zero, centralProject_edgeCylinder_one]
  all_goals exact (cornerPoint_eq_evenPole_iff C ε hε _).mpr (by decide)

theorem CuspCentralHomology.doubleCylinder_respects (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : unitInterval × ThreeCircles) (h : (suspensionSetoid ThreeCircles).r p q) :
    doubleCylinder C ε hε p = doubleCylinder C ε hε q := by
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  change s = t ∧ (s = 0 ∨ s = 1 ∨ a = b) at h
  rcases h with ⟨hst, hs⟩
  cases hst
  rcases hs with rfl | rfl | rfl <;> simp only [doubleCylinder_zero, doubleCylinder_one]

def CuspCentralHomology.doubleSuspensionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Suspension.topSus ThreeCircles → CuspRetraction.QuotientCentralFibre C ε :=
  Quotient.lift (doubleCylinder C ε hε) (doubleCylinder_respects C ε hε)

@[simp]
theorem CuspCentralHomology.doubleSuspensionMap_mk (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : ThreeCircles) :
    doubleSuspensionMap C ε hε (Suspension.topSus.mk t a) = doubleCylinder C ε hε (t, a) :=
  rfl

theorem CuspCentralHomology.doubleSuspensionMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (doubleSuspensionMap C ε hε) :=
  (Suspension.topSus.isQuotientMap_mk (X := ThreeCircles)).continuous_iff.mpr
    (doubleCylinder_continuous C ε hε)

theorem CuspCentralHomology.chartPoint_branchVertices_fst_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0) :
    ToricSpace.branchVertices (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay i} := by
  rw [CuspHoneycombHexagon.chartPoint_coe, ToricSpace.branchVertices_inclusion]
  ext v
  change
    (∃ j,
        CuspHoneycombHexagon.liftCoordinates i z j = 0 ∧
          (ToricComponent.zeroTriangle i).vertex j = v) ↔
      v = 0 ∨ v = ToricComponent.hexagonRay i
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with rfl | rfl | rfl
    · exact Or.inl (ToricComponent.zeroTriangle_vertex i)
    · exact Or.inr (CuspHoneycombHexagon.firstCoordinate_vertex i)
    · exact (hz1 (by simpa only [CuspHoneycombHexagon.liftCoordinates_second] using hj)).elim
  · rintro (rfl | rfl)
    · exact
        ⟨ToricComponent.zeroCoordinate i, CuspHoneycombHexagon.liftCoordinates_zero i z,
          ToricComponent.zeroTriangle_vertex i⟩
    · exact
        ⟨CuspHoneycombHexagon.firstCoordinate i,
          (CuspHoneycombHexagon.liftCoordinates_first i z).trans hz0,
          CuspHoneycombHexagon.firstCoordinate_vertex i⟩

theorem CuspCentralHomology.chartPoint_branchVertices_snd_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 ≠ 0) (hz1 : z 1 = 0) :
    ToricSpace.branchVertices (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay (i + 1)} := by
  rw [CuspHoneycombHexagon.chartPoint_coe, ToricSpace.branchVertices_inclusion]
  ext v
  change
    (∃ j,
        CuspHoneycombHexagon.liftCoordinates i z j = 0 ∧
          (ToricComponent.zeroTriangle i).vertex j = v) ↔
      v = 0 ∨ v = ToricComponent.hexagonRay (i + 1)
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with rfl | rfl | rfl
    · exact Or.inl (ToricComponent.zeroTriangle_vertex i)
    · exact (hz0 (by simpa only [CuspHoneycombHexagon.liftCoordinates_first] using hj)).elim
    · exact Or.inr (CuspHoneycombHexagon.secondCoordinate_vertex i)
  · rintro (rfl | rfl)
    · exact
        ⟨ToricComponent.zeroCoordinate i, CuspHoneycombHexagon.liftCoordinates_zero i z,
          ToricComponent.zeroTriangle_vertex i⟩
    · exact
        ⟨CuspHoneycombHexagon.secondCoordinate i,
          (CuspHoneycombHexagon.liftCoordinates_second i z).trans hz1,
          CuspHoneycombHexagon.secondCoordinate_vertex i⟩

theorem CuspCentralHomology.positiveBoundary_branchVertices (k : Fin 6)
    (q : CuspHoneycombHexagon.positiveBoundary k)
    (hprev : q.1 ≠ CuspHoneycombHexagon.squarePoint (k - 1) CuspHoneycombHexagon.cornerZero)
    (hcurr : q.1 ≠ CuspHoneycombHexagon.squarePoint k CuspHoneycombHexagon.cornerZero) :
    ToricSpace.branchVertices (q.1.1 : ToricSpace.Space) = {0, ToricComponent.hexagonRay k} := by
  obtain ⟨i, z, he⟩ := CuspHoneycombHexagon.chartPoint_jointly_surjective q.1.1
  have hqzero (hz0 : z 0 = 0) (hz1 : z 1 = 0) :
    q.1 = CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
    apply Subtype.ext
    change
      q.1.1 =
        CuspHoneycombHexagon.chartPoint i (fun j => (CuspHoneycombHexagon.cornerZero.1 j : ℂ))
    rw [← he]
    apply congrArg (CuspHoneycombHexagon.chartPoint i)
    funext j
    fin_cases j
    · change z 0 = 0
      exact hz0
    · change z 1 = 0
      exact hz1
  have hb :
    (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) ∈
      ToricSpace.rayDivisor (ToricComponent.hexagonRay k) := by
    rw [he]
    exact q.property
  rcases (CuspHoneycombHexagon.chartPoint_mem_rayDivisor_iff i k z).mp hb with ⟨rfl, hz0⟩ |
    ⟨rfl, hz1⟩
  · have hz1 : z 1 ≠ 0 := fun hz1 => hcurr (hqzero hz0 hz1)
    rw [← he]
    exact chartPoint_branchVertices_fst_zero k z hz0 hz1
  · have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hprev
      simpa only [add_sub_cancel_right] using hqzero hz0 hz1
    rw [← he]
    exact chartPoint_branchVertices_snd_zero i z hz0 hz1

theorem CuspCentralHomology.compatibleBoundaryArc_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ToricSpace.branchVertices
        ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay k} := by
  apply positiveBoundary_branchVertices k (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t)
  · intro h
    apply ht0
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_zero_point C₀ k).symm
  · intro h
    apply ht1
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_one_point C₀ k).symm

theorem CuspCentralHomology.edgeArcPositive_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ToricSpace.branchVertices ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay k} :=
  compatibleBoundaryArc_branchVertices C₀ k t ht0 ht1

theorem CuspCentralHomology.branchVertices_compactFibreAction (u : ToricSpace.CompactFibreTorus)
    (x : ToricSpace.Space) :
    ToricSpace.branchVertices (ToricSpace.compactFibreAction u x) = ToricSpace.branchVertices x :=
  ToricSpace.branchVertices_torusAction _ x

theorem CuspCentralHomology.edgeCylinder_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) (ht0 : p.1 ≠ 0) (ht1 : p.1 ≠ 1) :
    ToricSpace.branchVertices (edgeCylinder C₀ k p : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay k} := by
  rw [edgeCylinder_coe, branchVertices_compactFibreAction]
  exact compatibleBoundaryArc_branchVertices C₀ k p.1 ht0 ht1

theorem CuspCentralHomology.edgeArcPositive_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ToricSpace.branchCount ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) = 2 := by
  rw [← ToricSpace.branchVertices_ncard, edgeArcPositive_branchVertices C₀ k t ht0 ht1]
  exact Set.ncard_pair (ToricComponent.hexagonRay_ne_zero k).symm

theorem CuspCentralHomology.edgeCylinder_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) (ht0 : p.1 ≠ 0) (ht1 : p.1 ≠ 1) :
    ToricSpace.branchCount (edgeCylinder C₀ k p : ToricSpace.Space) = 2 := by
  rw [← ToricSpace.branchVertices_ncard, edgeCylinder_branchVertices C₀ k p ht0 ht1]
  exact Set.ncard_pair (ToricComponent.hexagonRay_ne_zero k).symm

@[simp]
theorem CuspCentralHomology.edgeArcPositive_zero_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : ToricSpace.branchCount ((edgeArcPositive C₀ k 0).1 : ToricSpace.Space) = 3 := by
  rw [edgeArcPositive_coe, CuspHoneycombHexagon.compatibleBoundaryArc_zero_point,
    CuspHoneycombHexagon.squarePoint_cornerZero_coe, ToricSpace.branchCount_inclusion,
    ToricCharts.zeroCount_zero]

@[simp]
theorem CuspCentralHomology.edgeArcPositive_one_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : ToricSpace.branchCount ((edgeArcPositive C₀ k 1).1 : ToricSpace.Space) = 3 := by
  rw [edgeArcPositive_coe, CuspHoneycombHexagon.compatibleBoundaryArc_one_point,
    CuspHoneycombHexagon.squarePoint_cornerZero_coe, ToricSpace.branchCount_inclusion,
    ToricCharts.zeroCount_zero]

theorem CuspCentralHomology.hexagonRay_first_half_ne_neg (k l : Fin 6) (hk : k.val < 3)
    (hl : l.val < 3) : ToricComponent.hexagonRay k ≠ -ToricComponent.hexagonRay l := by
  have h :
    ∀ k l : Fin 6,
      k.val < 3 → l.val < 3 → ToricComponent.hexagonRay k ≠ -ToricComponent.hexagonRay l := by
    decide
  exact h k l hk hl

theorem CuspCentralHomology.hexagonPair_image_add_eq (k l : Fin 6) (hk : k.val < 3)
    (hl : l.val < 3) (d : Fin 2 → ℤ)
    (h :
      ({0, ToricComponent.hexagonRay k} : Set (Fin 2 → ℤ)) =
        (fun w => w + d) '' {0, ToricComponent.hexagonRay l}) :
    k = l ∧ d = 0 := by
  simp only [Set.image_insert_eq, Set.image_singleton, zero_add, Set.pair_eq_pair_iff] at h
  rcases h with ⟨hd, hn⟩ | ⟨hd, hn⟩
  · subst d
    exact ⟨ToricComponent.hexagonRay_injective (by simpa only [add_zero] using hn), rfl⟩
  · have hneg : ToricComponent.hexagonRay k = -ToricComponent.hexagonRay l := by
      funext i
      have hd' := congrFun hd i
      have hn' := congrFun hn i
      change (0 : ℤ) = ToricComponent.hexagonRay l i + d i at hd'
      change ToricComponent.hexagonRay k i = d i at hn'
      change ToricComponent.hexagonRay k i = -ToricComponent.hexagonRay l i
      omega
    exact (hexagonRay_first_half_ne_neg k l hk hl hneg).elim

def CuspCentralHomology.projectedEdgeCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) (p : unitInterval × Circle) :
    CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k p)

theorem CuspCentralHomology.centralProject_branchCount_eq (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) {x y : CuspRetraction.CentralFibre}
    (h : CuspCollapse.centralProject C ε hε x = CuspCollapse.centralProject C ε hε y) :
    ToricSpace.branchCount (x : ToricSpace.Space) =
      ToricSpace.branchCount (y : ToricSpace.Space) := by
  obtain ⟨v, hv⟩ := (CuspCollapse.centralProject_eq_iff C ε hε x y).mp h
  rw [← hv, ToricSpace.branchCount_twistedTranslate]

theorem CuspCentralHomology.projectedEdgeCylinder_eq_iff_of_interior
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k l : Fin 6) (hk : k.val < 3)
    (hl : l.val < 3) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (a b : Circle) :
    projectedEdgeCylinder C ε hε k (s, a) = projectedEdgeCylinder C ε hε l (t, b) ↔
      k = l ∧ s = t ∧ a = b := by
  constructor
  · intro he
    obtain ⟨v, hv⟩ := (CuspCollapse.centralProject_eq_iff C ε hε _ _).mp he
    have hb := congrArg ToricSpace.branchVertices hv
    rw [ToricSpace.branchVertices_twistedTranslate,
      edgeCylinder_branchVertices (C 0) l (t, b) ht0 ht1,
      edgeCylinder_branchVertices (C 0) k (s, a) hs0 hs1] at hb
    obtain ⟨hkl, hv0⟩ := hexagonPair_image_add_eq k l hk hl (ToricSpace.cuspVector v) hb.symm
    have hzero : v = 0 :=
      ToricSpace.cuspVector_injective (hv0.trans ToricSpace.cuspVector_zero.symm)
    subst v
    subst l
    rw [ToricSpace.twistedTranslate_zero] at hv
    exact
      ⟨rfl, (edgeCylinder_eq_iff_of_interior (C 0) k s t hs0 hs1 a b).mp (Subtype.ext hv.symm)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem CuspCentralHomology.projectedEdgeCylinder_interior_ne_corner
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : Circle) (j : Fin 6) :
    projectedEdgeCylinder C ε hε k (t, a) ≠ cornerPoint C ε hε j := by
  intro he
  have hb := centralProject_branchCount_eq C ε hε he
  rw [edgeCylinder_branchCount (C 0) k (t, a) ht0 ht1, cornerOrigin_coe,
    ToricSpace.branchCount_inclusion, ToricCharts.zeroCount_zero] at hb
  omega

private def CuspCentralHomology.cylinderEdgeData_mo1973_12083 (t : unitInterval)
    (a : ThreeCircles) : Fin 6 × (unitInterval × Circle) :=
  match a with
  | Sum.inl a => (0, t, a)
  | Sum.inr (Sum.inl a) => (1, unitInterval.symm t, a)
  | Sum.inr (Sum.inr a) => (2, t, a)

private theorem CuspCentralHomology.cylinderEdgeData_index_lt_mo1973_12084 (t : unitInterval)
    (a : ThreeCircles) : (cylinderEdgeData_mo1973_12083 t a).1.val < 3 := by
  rcases a with a | a | a <;> norm_num [cylinderEdgeData_mo1973_12083]

private theorem CuspCentralHomology.cylinderEdgeData_time_ne_zero_mo1973_12085 (t : unitInterval)
    (a : ThreeCircles) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (cylinderEdgeData_mo1973_12083 t a).2.1 ≠ 0 := by
  rcases a with a | a | a
  · exact ht0
  · exact fun h => ht1 (unitInterval.symm_eq_zero.mp h)
  · exact ht0

private theorem CuspCentralHomology.cylinderEdgeData_time_ne_one_mo1973_12086 (t : unitInterval)
    (a : ThreeCircles) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (cylinderEdgeData_mo1973_12083 t a).2.1 ≠ 1 := by
  rcases a with a | a | a
  · exact ht1
  · exact fun h => ht0 (unitInterval.symm_eq_one.mp h)
  · exact ht1

private theorem CuspCentralHomology.cylinderEdgeData_eq_iff_mo1973_12087 (s t : unitInterval)
    (a b : ThreeCircles) :
    ((cylinderEdgeData_mo1973_12083 s a).1 = (cylinderEdgeData_mo1973_12083 t b).1 ∧
        (cylinderEdgeData_mo1973_12083 s a).2.1 = (cylinderEdgeData_mo1973_12083 t b).2.1 ∧
          (cylinderEdgeData_mo1973_12083 s a).2.2 = (cylinderEdgeData_mo1973_12083 t b).2.2) ↔
      s = t ∧ a = b := by
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp [cylinderEdgeData_mo1973_12083, unitInterval.symm_inj]

private theorem CuspCentralHomology.doubleCylinder_eq_projected_mo1973_12088
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (t : unitInterval)
    (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) =
      projectedEdgeCylinder C ε hε (cylinderEdgeData_mo1973_12083 t a).1
        (cylinderEdgeData_mo1973_12083 t a).2 := by rcases a with a | a | a <;> rfl

theorem CuspCentralHomology.doubleCylinder_eq_iff_of_interior (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (a b : ThreeCircles) :
    doubleCylinder C ε hε (s, a) = doubleCylinder C ε hε (t, b) ↔ s = t ∧ a = b := by
  simp only [doubleCylinder_eq_projected_mo1973_12088]
  exact
    (projectedEdgeCylinder_eq_iff_of_interior C ε hε _ _
          (cylinderEdgeData_index_lt_mo1973_12084 s a)
          (cylinderEdgeData_index_lt_mo1973_12084 t b) _ _
          (cylinderEdgeData_time_ne_zero_mo1973_12085 s a hs0 hs1)
          (cylinderEdgeData_time_ne_one_mo1973_12086 s a hs0 hs1)
          (cylinderEdgeData_time_ne_zero_mo1973_12085 t b ht0 ht1)
          (cylinderEdgeData_time_ne_one_mo1973_12086 t b ht0 ht1) _ _).trans
      (cylinderEdgeData_eq_iff_mo1973_12087 s t a b)

theorem CuspCentralHomology.doubleCylinder_interior_ne_corner (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : ThreeCircles)
    (j : Fin 6) : doubleCylinder C ε hε (t, a) ≠ cornerPoint C ε hε j := by
  rw [doubleCylinder_eq_projected_mo1973_12088]
  exact
    projectedEdgeCylinder_interior_ne_corner C ε hε _ _
      (cylinderEdgeData_time_ne_zero_mo1973_12085 t a ht0 ht1)
      (cylinderEdgeData_time_ne_one_mo1973_12086 t a ht0 ht1) _ j

theorem CuspCentralHomology.doubleCylinder_eq_oddPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) = oddPole C ε hε ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht0
    by_cases ht1 : t = 1
    · subst t
      exact pole_ne C ε hε (by simpa only [doubleCylinder_one] using h)
    · exact doubleCylinder_interior_ne_corner C ε hε t ht0 ht1 a 1 h
  · rintro rfl
    exact doubleCylinder_zero C ε hε a

theorem CuspCentralHomology.doubleCylinder_eq_evenPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) = evenPole C ε hε ↔ t = 1 := by
  constructor
  · intro h
    by_contra ht1
    by_cases ht0 : t = 0
    · subst t
      apply pole_ne C ε hε
      simpa only [doubleCylinder_zero] using h.symm
    · exact doubleCylinder_interior_ne_corner C ε hε t ht0 ht1 a 0 h
  · rintro rfl
    exact doubleCylinder_one C ε hε a

theorem CuspCentralHomology.doubleCylinder_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : unitInterval × ThreeCircles) :
    doubleCylinder C ε hε p = doubleCylinder C ε hε q ↔ (suspensionSetoid ThreeCircles).r p q := by
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  constructor
  · intro h
    change s = t ∧ (s = 0 ∨ s = 1 ∨ a = b)
    by_cases hs0 : s = 0
    · subst s
      have ht0 : t = 0 :=
        (doubleCylinder_eq_oddPole_iff C ε hε t b).mp
          (h.symm.trans (doubleCylinder_zero C ε hε a))
      exact ⟨ht0.symm, Or.inl rfl⟩
    by_cases hs1 : s = 1
    · subst s
      have ht1 : t = 1 :=
        (doubleCylinder_eq_evenPole_iff C ε hε t b).mp
          (h.symm.trans (doubleCylinder_one C ε hε a))
      exact ⟨ht1.symm, Or.inr (Or.inl rfl)⟩
    have ht0 : t ≠ 0 := by
      intro ht0
      subst t
      exact
        doubleCylinder_interior_ne_corner C ε hε s hs0 hs1 a 1
          (h.trans (doubleCylinder_zero C ε hε b))
    have ht1 : t ≠ 1 := by
      intro ht1
      subst t
      exact
        doubleCylinder_interior_ne_corner C ε hε s hs0 hs1 a 0
          (h.trans (doubleCylinder_one C ε hε b))
    obtain ⟨hst, hab⟩ := (doubleCylinder_eq_iff_of_interior C ε hε s t hs0 hs1 ht0 ht1 a b).mp h
    exact ⟨hst, Or.inr (Or.inr hab)⟩
  · exact doubleCylinder_respects C ε hε _ _

theorem CuspCentralHomology.doubleSuspensionMap_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Injective (doubleSuspensionMap C ε hε) := by
  intro x y h
  obtain ⟨⟨s, a⟩, rfl⟩ := Suspension.topSus.mk_surjective x
  obtain ⟨⟨t, b⟩, rfl⟩ := Suspension.topSus.mk_surjective y
  exact Quotient.sound ((doubleCylinder_eq_iff C ε hε (s, a) (t, b)).mp h)

theorem CuspCentralHomology.edgeArcPositive_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) :
    edgeArcPositive C₀ (k + 3) (unitInterval.symm t) =
      CuspCollapse.positiveCentralTranslate C₀
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (edgeArcPositive C₀ k t) := by
  apply Subtype.ext
  apply Subtype.ext
  exact CuspHoneycombHexagon.compatibleBoundaryArc_opposite_coe C₀ k t

theorem CuspCentralHomology.centralCollapseMap_phaseDeckMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (v : Fin 2 → ℤ) (p : CuspCollapse.PhasePositiveSpace) :
    CuspCollapse.centralCollapseMap C ε hε (CuspCollapse.phaseDeckMap (C 0) v p) =
      CuspCollapse.centralCollapseMap C ε hε p := by
  apply (CuspCollapse.centralProject_eq_iff C ε hε _ _).mpr
  exact ⟨v, (CuspCollapse.centralPolarMap_phaseDeckMap C v p).symm⟩

theorem CuspCentralHomology.centralCollapseMap_opposite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) (t : unitInterval) (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralCollapseMap C ε hε
        (u, edgeArcPositive (C 0) (k + 3) (unitInterval.symm t)) =
      CuspCollapse.centralCollapseMap C ε hε
        ((CuspCollapse.deckFibrePhase (C 0)
                (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
            u,
          edgeArcPositive (C 0) k t) := by
  have h :=
    centralCollapseMap_phaseDeckMap C ε hε (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
      ((CuspCollapse.deckFibrePhase (C 0)
              (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
          u,
        edgeArcPositive (C 0) k t)
  simpa only [CuspCollapse.phaseDeckMap, mul_inv_cancel_left, ← edgeArcPositive_opposite] using h

theorem CuspCentralHomology.centralProject_edgeCylinder_opposite
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (k + 3) (unitInterval.symm t, a)) =
      CuspCollapse.centralProject C ε hε
        (edgeCylinder (C 0) k
          (t,
            hexagonCharacter k
              ((CuspCollapse.deckFibrePhase (C 0)
                    (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
                hexagonCharacterSection (k + 3) a))) := by
  change
    CuspCollapse.centralCollapseMap C ε hε
        (hexagonCharacterSection (k + 3) a, edgeArcPositive (C 0) (k + 3) (unitInterval.symm t)) =
      _
  rw [centralCollapseMap_opposite]
  exact
    (congrArg (CuspCollapse.centralProject C ε hε)
        (edgeCylinder_character_all (C 0) k t
          ((CuspCollapse.deckFibrePhase (C 0)
                (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
            hexagonCharacterSection (k + 3) a))).symm

theorem CuspCentralHomology.centralProject_edgeCylinder_opposite_exists
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    ∃ b : Circle,
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (k + 3) (unitInterval.symm t, a)) =
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (t, b)) :=
  ⟨_, centralProject_edgeCylinder_opposite C ε hε k t a⟩

theorem CuspCentralHomology.edgeCylinder_mem_range_doubleCylinder
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (t, a)) ∈
      Set.range (doubleCylinder C ε hε) := by
  fin_cases k
  · exact ⟨(t, Sum.inl a), rfl⟩
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (1 : Fin 6) (t, a)) ∈ _
    refine ⟨(unitInterval.symm t, Sum.inr (Sum.inl a)), ?_⟩
    rw [doubleCylinder_middle, unitInterval.symm_symm]
  · exact ⟨(t, Sum.inr (Sum.inr a)), rfl⟩
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (3 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 0 (unitInterval.symm t) a
    refine ⟨(unitInterval.symm t, Sum.inl b), ?_⟩
    simpa only [show (0 + 3 : Fin 6) = 3 from by decide, doubleCylinder_first,
      unitInterval.symm_symm] using hb.symm
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (4 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 1 (unitInterval.symm t) a
    refine ⟨(t, Sum.inr (Sum.inl b)), ?_⟩
    simpa only [show (1 + 3 : Fin 6) = 4 from by decide, doubleCylinder_middle,
      unitInterval.symm_symm] using hb.symm
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (5 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 2 (unitInterval.symm t) a
    refine ⟨(unitInterval.symm t, Sum.inr (Sum.inr b)), ?_⟩
    simpa only [show (2 + 3 : Fin 6) = 5 from by decide, doubleCylinder_last,
      unitInterval.symm_symm] using hb.symm

theorem CuspCentralHomology.centralCollapseMap_edgeArc_mem_range_doubleCylinder
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) ∈
      Set.range (doubleCylinder C ε hε) := by
  have h := edgeCylinder_mem_range_doubleCylinder C ε hε k t (hexagonCharacter k u)
  change
    CuspCollapse.centralProject C ε hε
        (CuspCollapse.centralPolarMap (u, edgeArcPositive (C 0) k t)) ∈
      _
  rwa [edgeCylinder_character_all] at h

theorem CuspCentralHomology.range_doubleSuspensionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Set.range (doubleSuspensionMap C ε hε) = Set.range (doubleCylinder C ε hε) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨⟨t, z⟩, rfl⟩ := Suspension.topSus.mk_surjective p
    exact ⟨(t, z), rfl⟩
  · rintro ⟨⟨t, z⟩, rfl⟩
    exact ⟨Suspension.topSus.mk t z, rfl⟩

abbrev CuspCentralHomology.FundamentalCell :=
  ToricSpace.CompactFibreTorus × CuspHoneycombTiling.baseCell

instance CuspCentralHomology.fundamentalCell_compactSpace : CompactSpace FundamentalCell := by
  let : CompactSpace CuspHoneycombTiling.baseCell :=
    isCompact_iff_compactSpace.mp CuspHoneycombTiling.baseCell_isCompact
  infer_instance

def CuspCentralHomology.fundamentalCellInclusion (p : FundamentalCell) :
    CuspHoneycomb.PhasePlane :=
  (p.1, (p.2 : (CuspHoneycombTiling.Plane)))

theorem CuspCentralHomology.fundamentalCellInclusion_continuous :
    Continuous fundamentalCellInclusion :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

def CuspCentralHomology.fundamentalCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : FundamentalCell → CuspRetraction.QuotientCentralFibre C ε :=
  CuspHoneycomb.honeycombCollapseMap C ε hε ∘ fundamentalCellInclusion

theorem CuspCentralHomology.fundamentalCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (fundamentalCellMap C ε hε) :=
  (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp fundamentalCellInclusion_continuous

theorem CuspCentralHomology.honeycombCollapseMap_deck_invariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (v : (CuspHoneycombTiling.Lattice)) (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.honeycombCollapseMap C ε hε (CuspHoneycomb.honeycombDeckMap (C 0) v p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε p := by
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε _ _).mpr
  refine ⟨v, rfl, ?_⟩
  simp [CuspHoneycomb.honeycombDeckMap]

theorem CuspCentralHomology.fundamentalCellMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Surjective (fundamentalCellMap C ε hε) := by
  intro q
  obtain ⟨p, hp⟩ := CuspHoneycomb.honeycombCollapseMap_surjective C ε hε q
  obtain ⟨v, hv⟩ := CuspHoneycombTiling.exists_mem_cell p.2
  let y : CuspHoneycombTiling.baseCell := ⟨p.2 - CuspHoneycombTiling.latticePoint v, hv⟩
  refine ⟨(CuspCollapse.deckFibrePhase (C 0) (ToricSpace.cuspVector v) * p.1, y), ?_⟩
  change
    CuspHoneycomb.honeycombCollapseMap C ε hε
        (CuspCollapse.deckFibrePhase (C 0) (ToricSpace.cuspVector v) * p.1,
          p.2 - CuspHoneycombTiling.latticePoint v) =
      q
  simpa only [CuspHoneycomb.honeycombDeckMap, ToricSpace.cuspVector_cuspVector,
    CuspHoneycombTiling.latticePoint_neg, sub_eq_add_neg] using
    (honeycombCollapseMap_deck_invariant C ε hε (ToricSpace.cuspVector v) p).trans hp

theorem CuspCentralHomology.fundamentalCellMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : FundamentalCell) :
    fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q ↔
      ∃ v : (CuspHoneycombTiling.Lattice),
        (p.2 : (CuspHoneycombTiling.Plane)) =
            (q.2 : (CuspHoneycombTiling.Plane)) +
              CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) ∧
          p.1⁻¹ * (CuspCollapse.deckFibrePhase (C 0) v * q.1) ∈
            MulAction.stabilizer ToricSpace.CompactFibreTorus
              ((CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane))).1 :
                ToricSpace.Space) :=
  CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε (fundamentalCellInclusion p)
    (fundamentalCellInclusion q)

theorem CuspCentralHomology.fundamentalCellMap_isProperMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (fundamentalCellMap C ε hε) := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact (fundamentalCellMap_continuous C ε hε).isProperMap

theorem CuspCentralHomology.fundamentalCellMap_isClosedMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsClosedMap (fundamentalCellMap C ε hε) :=
  (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).isClosedMap

theorem CuspCentralHomology.fundamentalCellMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Topology.IsQuotientMap (fundamentalCellMap C ε hε) :=
  (fundamentalCellMap_isClosedMap C ε hε hε1 hC hR).isQuotientMap
    (fundamentalCellMap_continuous C ε hε) (fundamentalCellMap_surjective C ε hε)

theorem CuspHoneycomb.honeycombHomeomorph_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.branchVertices ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      {v : (CuspHoneycombTiling.Lattice) | y ∈ CuspHoneycombTiling.cell v} := by
  ext v
  exact honeycombHomeomorph_mem_positiveCell_iff C₀ v y

theorem CuspHoneycomb.honeycombHomeomorph_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.branchCount ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      {v : (CuspHoneycombTiling.Lattice) | y ∈ CuspHoneycombTiling.cell v}.ncard := by
  rw [← ToricSpace.branchVertices_ncard, honeycombHomeomorph_branchVertices]

theorem CuspHoneycombTiling.frontier_baseCell :
    frontier baseCell = ⋃ k : Fin 6, baseCell ∩ cell (ToricComponent.hexagonRay k) := by
  have hpre : dualStandardPlaneHomeomorph ⁻¹' CuspHoneycombHexagon.Hexagon = baseCell :=
    Set.ext dualStandardPlaneHomeomorph_mem_hexagon
  calc
    frontier baseCell = dualStandardPlaneHomeomorph ⁻¹' frontier CuspHoneycombHexagon.Hexagon := by
      rw [dualStandardPlaneHomeomorph.preimage_frontier, hpre]
    _ = ⋃ k : Fin 6, dualStandardPlaneHomeomorph ⁻¹' CuspHoneycombHexagon.side k := by
      rw [CuspHoneycombHexagon.frontier_hexagon, Set.preimage_iUnion]
    _ = ⋃ k : Fin 6, baseCell ∩ cell (ToricComponent.hexagonRay k) := by
      apply Set.iUnion_congr
      intro k
      rw [← dual_image_side, Homeomorph.image_eq_preimage_symm, Homeomorph.symm_symm]

theorem CuspHoneycombTiling.mem_frontier_baseCell_iff (y : Plane) :
    y ∈ frontier baseCell ↔
      y ∈ baseCell ∧ ∃ v : CuspHoneycombTiling.Lattice, v ≠ 0 ∧ y ∈ cell v := by
  rw [frontier_baseCell, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hy, hv⟩
    refine ⟨hy, ToricComponent.hexagonRay k, ?_, hv⟩
    fin_cases k <;> decide
  · rintro ⟨hy, v, hv, hyv⟩
    rcases (baseCell_inter_cell_nonempty_iff_hexagonRay v).mp ⟨y, hy, hyv⟩ with hz | ⟨k, rfl⟩
    · exact (hv hz).elim
    · exact ⟨k, hy, hyv⟩

theorem CuspHoneycombTiling.mem_interior_baseCell_iff (y : Plane) :
    y ∈ interior baseCell ↔ ∀ v : CuspHoneycombTiling.Lattice, y ∈ cell v ↔ v = 0 := by
  constructor
  · intro hy v
    constructor
    · intro hyv
      by_contra hv
      have hf := (mem_frontier_baseCell_iff y).mpr ⟨interior_subset hy, v, hv, hyv⟩
      exact ((mem_interior_iff_notMem_frontier (interior_subset hy)).mp hy) hf
    · rintro rfl
      simpa only [cell_zero] using interior_subset hy
  · intro hy
    have hbase : y ∈ baseCell := by simpa only [cell_zero] using (hy 0).mpr rfl
    apply (mem_interior_iff_notMem_frontier hbase).mpr
    intro hf
    obtain ⟨_, v, hv, hyv⟩ := (mem_frontier_baseCell_iff y).mp hf
    exact hv ((hy v).mp hyv)

theorem CuspHoneycombTiling.mem_interior_cell_iff (v : CuspHoneycombTiling.Lattice) (y : Plane) :
    y ∈ interior (cell v) ↔ ∀ w : CuspHoneycombTiling.Lattice, y ∈ cell w ↔ w = v := by
  have hpre : (Homeomorph.subRight (latticePoint v)) ⁻¹' baseCell = cell v := rfl
  have hint : y ∈ interior (cell v) ↔ y - latticePoint v ∈ interior baseCell := by
    rw [← hpre, ← Homeomorph.preimage_interior]
    rfl
  rw [hint, mem_interior_baseCell_iff]
  constructor
  · intro hy w
    have h := hy (w - v)
    rw [sub_latticePoint_mem_cell_iff, add_comm v (w - v), sub_add_cancel] at h
    exact h.trans sub_eq_zero
  · intro hy w
    rw [sub_latticePoint_mem_cell_iff, hy, add_eq_left]

theorem CuspHoneycombTiling.containingCells_eq_singleton_iff (y : Plane)
    (v : CuspHoneycombTiling.Lattice) :
    {w : CuspHoneycombTiling.Lattice | y ∈ cell w} = { v } ↔ y ∈ interior (cell v) := by
  rw [mem_interior_cell_iff]
  exact Set.ext_iff

theorem CuspHoneycombTiling.containingCells_ncard_eq_one_iff (y : Plane) :
    {v : CuspHoneycombTiling.Lattice | y ∈ cell v}.ncard = 1 ↔
      ∃ v : CuspHoneycombTiling.Lattice, y ∈ interior (cell v) := by
  rw [Set.ncard_eq_one]
  exact exists_congr fun v => containingCells_eq_singleton_iff y v

theorem CuspHoneycomb.honeycombHomeomorph_branchCount_eq_one_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : CuspHoneycombTiling.Plane) :
    ToricSpace.branchCount ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) = 1 ↔
      ∃ v : CuspHoneycombTiling.Lattice, y ∈ interior (CuspHoneycombTiling.cell v) := by
  rw [honeycombHomeomorph_branchCount, CuspHoneycombTiling.containingCells_ncard_eq_one_iff]

theorem ToricSpace.compactFibre_stabilizer_eq_bot_of_branchVertices_singleton (x : Space)
    (v : Fin 2 → ℤ) (hx : branchVertices x = { v }) :
    MulAction.stabilizer CompactFibreTorus x = ⊥ := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hv : ToricSpace.inclusion s z ∈ rayDivisor v := by
    change v ∈ branchVertices (ToricSpace.inclusion s z)
    rw [hx]
    exact Set.mem_singleton v
  obtain ⟨j, _, hjv⟩ := (mem_rayDivisor_inclusion v s z).mp hv
  apply compactFibre_stabilizer_eq_bot_of_at_most_one_zero s z j
  intro i hij hzi
  have hi : s.vertex i ∈ branchVertices (ToricSpace.inclusion s z) :=
    (mem_rayDivisor_vertex s i z).mpr hzi
  have hiv : s.vertex i = v := by simpa only [hx, Set.mem_singleton_iff] using hi
  exact hij (s.vertex_injective (hiv.trans hjv.symm))

theorem CuspHoneycomb.honeycombHomeomorph_stabilizer_eq_bot (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) (v : (CuspHoneycombTiling.Lattice))
    (hcells : {u : (CuspHoneycombTiling.Lattice) | y ∈ CuspHoneycombTiling.cell u} = { v }) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      ⊥ :=
  ToricSpace.compactFibre_stabilizer_eq_bot_of_branchVertices_singleton _ v
    ((honeycombHomeomorph_branchVertices C₀ y).trans hcells)

theorem CuspHoneycomb.honeycombHomeomorph_stabilizer_eq_bot_of_mem_interior
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (y : (CuspHoneycombTiling.Plane))
    (v : (CuspHoneycombTiling.Lattice)) (hy : y ∈ interior (CuspHoneycombTiling.cell v)) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((honeycombHomeomorph C₀ y).1 : ToricSpace.Space) =
      ⊥ :=
  honeycombHomeomorph_stabilizer_eq_bot C₀ y v
    ((CuspHoneycombTiling.containingCells_eq_singleton_iff y v).mpr hy)

theorem CuspHoneycomb.honeycombHomeomorph_stabilizer_triangleBarycenter
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : ToricFan.Triangle) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((honeycombHomeomorph C₀ (CuspHoneycombTiling.triangleBarycenter s)).1 :
          ToricSpace.Space) =
      ⊤ := by
  rw [honeycombHomeomorph_triangleBarycenter_coe]
  exact ToricSpace.compactFibre_stabilizer_inclusion_zero s

theorem CuspCentralHomology.fundamentalCellMap_eq_of_interior (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) : p = q := by
  obtain ⟨u, hb, hphase⟩ := (fundamentalCellMap_eq_iff C ε hε p q).mp h
  have hpcell :
    (p.2 : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell (ToricSpace.cuspVector u) := by
    rw [hb, CuspHoneycombTiling.mem_cell, add_sub_cancel_right]
    exact q.2.2
  have hpinterior : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior (CuspHoneycombTiling.cell 0) :=
    by simpa only [CuspHoneycombTiling.cell_zero] using hp
  have hcells :=
    (CuspHoneycombTiling.containingCells_eq_singleton_iff (p.2 : (CuspHoneycombTiling.Plane))
          0).mpr
      hpinterior
  have hcu : ToricSpace.cuspVector u = 0 := by
    have hu :
      ToricSpace.cuspVector u ∈
        {v : (CuspHoneycombTiling.Lattice) |
          (p.2 : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell v} :=
      hpcell
    simpa only [hcells, Set.mem_singleton_iff] using hu
  have hu : u = 0 := ToricSpace.cuspVector_injective (hcu.trans ToricSpace.cuspVector_zero.symm)
  subst u
  have hb' : (p.2 : (CuspHoneycombTiling.Plane)) = (q.2 : (CuspHoneycombTiling.Plane)) := by
    simpa only [ToricSpace.cuspVector_zero, CuspHoneycombTiling.latticePoint_zero, add_zero] using
      hb
  have hstab :=
    CuspHoneycomb.honeycombHomeomorph_stabilizer_eq_bot_of_mem_interior (C 0)
      (p.2 : (CuspHoneycombTiling.Plane)) 0 hpinterior
  have hphase' : p.1 = q.1 := by
    simpa only [hstab, Subgroup.mem_bot, CuspCollapse.deckFibrePhase_zero, one_mul,
      inv_mul_eq_one] using hphase
  exact Prod.ext hphase' (Subtype.ext hb')

theorem CuspCentralHomology.fundamentalCellMap_interior_iff_of_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell ↔
      (q.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  constructor
  · intro hp
    have hpq := fundamentalCellMap_eq_of_interior C ε hε p q hp h
    simpa only [← hpq] using hp
  · intro hq
    have hqp := fundamentalCellMap_eq_of_interior C ε hε q p hq h.symm
    simpa only [← hqp] using hq

theorem CuspCentralHomology.fundamentalCellMap_eq_or_frontier (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    p = q ∨
      ((p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell ∧
        (q.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) := by
  by_cases hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell
  · exact Or.inl (fundamentalCellMap_eq_of_interior C ε hε p q hp h)
  · right
    rw [CuspHoneycombTiling.baseCell_isClosed.frontier_eq]
    refine ⟨⟨p.2.2, hp⟩, q.2.2, ?_⟩
    intro hq
    exact hp ((fundamentalCellMap_interior_iff_of_eq C ε hε p q h).mpr hq)

theorem CuspCentralHomology.fundamentalCellMap_eq_base_or_frontier
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : (CuspHoneycombTiling.Plane)) = (q.2 : (CuspHoneycombTiling.Plane)) ∨
      ((p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell ∧
        (q.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) := by
  rcases fundamentalCellMap_eq_or_frontier C ε hε p q h with hpq | hfrontier
  · exact Or.inl (congrArg (fun r : FundamentalCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq)
  · exact Or.inr hfrontier

def CuspCentralHomology.Radial.cellGauge (x : CuspHoneycombTiling.Plane) : ℝ :=
  Max.max |2 * x 0 + x 1| (Max.max |x 0 - x 1| |x 0 + 2 * x 1|)

theorem CuspCentralHomology.Radial.cellGauge_continuous : Continuous cellGauge :=
  (((continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)).abs).max
    (((continuous_apply 0).sub (continuous_apply 1)).abs.max
      ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).abs)

theorem CuspCentralHomology.Radial.cellGauge_nonneg (x : CuspHoneycombTiling.Plane) :
    0 ≤ cellGauge x :=
  (abs_nonneg _).trans (le_max_left _ _)

@[simp]
theorem CuspCentralHomology.Radial.cellGauge_zero :
    cellGauge (0 : CuspHoneycombTiling.Plane) = 0 := by simp [cellGauge]

theorem CuspCentralHomology.Radial.cellGauge_smul (c : ℝ) (x : CuspHoneycombTiling.Plane) :
    cellGauge (c • x) = |c| * cellGauge x := by
  have h0 : 2 * (c * x 0) + c * x 1 = c * (2 * x 0 + x 1) := by ring
  have h1 : c * x 0 - c * x 1 = c * (x 0 - x 1) := by ring
  have h2 : c * x 0 + 2 * (c * x 1) = c * (x 0 + 2 * x 1) := by ring
  simp only [cellGauge, Pi.smul_apply, smul_eq_mul, h0, h1, h2, abs_mul,
    mul_max_of_nonneg _ _ (abs_nonneg c)]

theorem CuspCentralHomology.Radial.cellGauge_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c)
    (x : CuspHoneycombTiling.Plane) : cellGauge (c • x) = c * cellGauge x := by
  rw [cellGauge_smul, abs_of_nonneg hc]

@[simp]
theorem CuspCentralHomology.Radial.cellGauge_eq_zero_iff (x : CuspHoneycombTiling.Plane) :
    cellGauge x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h0 : |2 * x 0 + x 1| ≤ 0 := (le_max_left _ _).trans (le_of_eq hx)
    have h1 : |x 0 - x 1| ≤ 0 := (le_max_left _ _).trans ((le_max_right _ _).trans (le_of_eq hx))
    have h0' : 2 * x 0 + x 1 = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
    have h1' : x 0 - x 1 = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    funext i
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
  · rintro rfl
    exact cellGauge_zero

theorem CuspCentralHomology.Radial.cellGauge_pos_iff (x : CuspHoneycombTiling.Plane) :
    0 < cellGauge x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    simp only [hzero, cellGauge_zero, lt_self_iff_false] at hx
  · intro hx
    apply lt_of_le_of_ne (cellGauge_nonneg x)
    intro h
    exact hx ((cellGauge_eq_zero_iff x).mp h.symm)

theorem CuspCentralHomology.Radial.mem_baseCell_iff (x : CuspHoneycombTiling.Plane) :
    x ∈ CuspHoneycombTiling.baseCell ↔ cellGauge x ≤ 1 := by
  simp only [CuspHoneycombTiling.mem_baseCell, cellGauge, max_le_iff]

theorem CuspCentralHomology.Radial.mem_interior_baseCell_iff (x : CuspHoneycombTiling.Plane) :
    x ∈ interior CuspHoneycombTiling.baseCell ↔ cellGauge x < 1 := by
  constructor
  · intro hx
    have hle := (mem_baseCell_iff x).mp (interior_subset hx)
    apply lt_of_le_of_ne hle
    intro heq
    have hopen : IsOpen ((fun a : ℝ => a • x) ⁻¹' interior CuspHoneycombTiling.baseCell) :=
      isOpen_interior.preimage (continuous_id.smul continuous_const)
    have hone : (1 : ℝ) ∈ (fun a : ℝ => a • x) ⁻¹' interior CuspHoneycombTiling.baseCell := by
      simpa only [Set.mem_preimage, one_smul] using hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    have ha : (1 + δ / 2) • x ∈ interior CuspHoneycombTiling.baseCell :=
      hball
        (by
          change Dist.dist (1 + δ / 2) (1 : ℝ) < δ
          rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
          exact half_lt_self hδ)
    have hb := (mem_baseCell_iff _).mp (interior_subset ha)
    rw [cellGauge_smul_of_nonneg _ (by linarith), heq, mul_one] at hb
    linarith
  · intro hx
    have hopen : IsOpen {y : CuspHoneycombTiling.Plane | cellGauge y < 1} :=
      isOpen_lt cellGauge_continuous continuous_const
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hopen.mem_nhds hx)
    intro y hy
    exact (mem_baseCell_iff y).mpr hy.le

theorem CuspCentralHomology.Radial.mem_frontier_baseCell_iff (x : CuspHoneycombTiling.Plane) :
    x ∈ frontier CuspHoneycombTiling.baseCell ↔ cellGauge x = 1 := by
  rw [frontier, CuspHoneycombTiling.baseCell_isClosed.closure_eq, Set.mem_sdiff, mem_baseCell_iff,
    mem_interior_baseCell_iff, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

def CuspCentralHomology.fundamentalRadius (p : FundamentalCell) : ℝ :=
  Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane))

theorem CuspCentralHomology.fundamentalRadius_continuous : Continuous fundamentalRadius :=
  Radial.cellGauge_continuous.comp (continuous_subtype_val.comp continuous_snd)

theorem CuspCentralHomology.fundamentalRadius_eq_of_map_eq (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    fundamentalRadius p = fundamentalRadius q := by
  change
    Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) =
      Radial.cellGauge (q.2 : (CuspHoneycombTiling.Plane))
  rcases fundamentalCellMap_eq_base_or_frontier C ε hε p q h with he | ⟨hp, hq⟩
  · exact congrArg Radial.cellGauge he
  · rw [(Radial.mem_frontier_baseCell_iff _).mp hp, (Radial.mem_frontier_baseCell_iff _).mp hq]

def CuspCentralHomology.centralRadius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CuspRetraction.QuotientCentralFibre C ε → ℝ :=
  CuspHoneycombHexagon.CommonFibres.descend (fundamentalCellMap C ε hε) fundamentalRadius
    (fundamentalCellMap_surjective C ε hε)

@[simp]
theorem CuspCentralHomology.centralRadius_fundamentalCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    centralRadius C ε hε (fundamentalCellMap C ε hε p) =
      Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (fundamentalCellMap C ε hε) fundamentalRadius
    (fundamentalCellMap_surjective C ε hε) (fundamentalRadius_eq_of_map_eq C ε hε) p

def CuspCentralHomology.centralBoundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set (CuspRetraction.QuotientCentralFibre C ε) :=
  {q | centralRadius C ε hε q = 1}

def CuspCentralHomology.outerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : Set (CuspRetraction.QuotientCentralFibre C ε) :=
  {q | a < centralRadius C ε hε q}

def CuspCentralHomology.innerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set (CuspRetraction.QuotientCentralFibre C ε) :=
  {q | centralRadius C ε hε q < 1}

theorem CuspCentralHomology.fundamentalCellMap_mem_centralBoundary_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ centralBoundary C ε hε ↔
      (p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
  change centralRadius C ε hε (fundamentalCellMap C ε hε p) = 1 ↔ _
  rw [centralRadius_fundamentalCellMap]
  exact (Radial.mem_frontier_baseCell_iff _).symm

theorem CuspCentralHomology.fundamentalCellMap_mem_innerRegion_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ innerRegion C ε hε ↔
      (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  change centralRadius C ε hε (fundamentalCellMap C ε hε p) < 1 ↔ _
  rw [centralRadius_fundamentalCellMap]
  exact (Radial.mem_interior_baseCell_iff _).symm

theorem CuspCentralHomology.centralBoundary_eq_image (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    centralBoundary C ε hε =
      CuspHoneycomb.honeycombCollapseMap C ε hε ''
        ((Set.univ : Set ToricSpace.CompactFibreTorus) ×ˢ
          frontier CuspHoneycombTiling.baseCell) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
    exact
      ⟨(p.1, (p.2 : (CuspHoneycombTiling.Plane))),
        ⟨Set.mem_univ _, (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mp hq⟩, rfl⟩
  · rintro ⟨⟨φ, x⟩, ⟨_, hx⟩, rfl⟩
    let p : FundamentalCell := (φ, ⟨x, CuspHoneycombTiling.baseCell_isClosed.frontier_subset hx⟩)
    exact (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mpr hx

theorem CuspCentralHomology.centralBoundary_subset_outerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : a < 1) : centralBoundary C ε hε ⊆ outerRegion C ε hε a := by
  intro q hq
  change a < centralRadius C ε hε q
  change centralRadius C ε hε q = 1 at hq
  rwa [hq]

theorem CuspCentralHomology.outerRegion_union_innerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : a < 1) :
    outerRegion C ε hε a ∪ innerRegion C ε hε = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  by_cases hq : centralRadius C ε hε q < 1
  · exact Or.inr hq
  · exact Or.inl (ha.trans_le (le_of_not_gt hq))

theorem CuspCentralHomology.centralRadius_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Continuous (centralRadius C ε hε) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous (fundamentalCellMap C ε hε)
    fundamentalRadius (fundamentalCellMap_surjective C ε hε)
    (fundamentalCellMap_isQuotientMap C ε hε hε1 hC hR) fundamentalRadius_continuous
    (fundamentalRadius_eq_of_map_eq C ε hε)

theorem CuspCentralHomology.outerRegion_isOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) : IsOpen (outerRegion C ε hε a) :=
  isOpen_lt continuous_const (centralRadius_continuous C ε hε hε1 hC hR)

theorem CuspCentralHomology.innerRegion_isOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsOpen (innerRegion C ε hε) :=
  isOpen_lt (centralRadius_continuous C ε hε hε1 hC hR) continuous_const

theorem CuspCentralHomology.honeycombHomeomorph_baseCell_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : CuspHoneycombTiling.baseCell) :
    ((CuspHoneycomb.honeycombHomeomorph C₀ (x : (CuspHoneycombTiling.Plane))).1 :
        ToricSpace.Space) =
      ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space) := by
  let y : CuspHoneycombTiling.cell 0 := CuspHoneycombTiling.cellTranslationHomeomorph 0 x
  have hy : (y : (CuspHoneycombTiling.Plane)) = (x : (CuspHoneycombTiling.Plane)) := by
    change
      (x : (CuspHoneycombTiling.Plane)) + CuspHoneycombTiling.latticePoint 0 =
        (x : (CuspHoneycombTiling.Plane))
    rw [CuspHoneycombTiling.latticePoint_zero, add_zero]
  have hnorm : (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm y = x :=
    (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm_apply_apply x
  have h := CuspHoneycomb.honeycombHomeomorph_cell_coe C₀ 0 y
  rw [hy, hnorm, ToricSpace.cuspVector_zero, neg_zero, ToricSpace.twistedTranslate_zero] at h
  exact h

def CuspCentralHomology.edgeArcBase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) : CuspHoneycombTiling.baseCell :=
  (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).symm
    (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1

@[simp]
theorem CuspCentralHomology.compatibleCellHomeomorph_edgeArcBase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀ (edgeArcBase C₀ k t) =
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1 :=
  (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).apply_symm_apply _

theorem CuspCentralHomology.edgeArcBase_mem_frontier (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) :
    (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
  rw [CuspHoneycombTiling.frontier_baseCell, Set.mem_iUnion]
  refine ⟨k, (edgeArcBase C₀ k t).2, ?_⟩
  apply
    (CuspHoneycombHexagon.compatibleCellHomeomorph_mem_boundary_iff C₀ (edgeArcBase C₀ k t) k).mp
  rw [compatibleCellHomeomorph_edgeArcBase]
  exact (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).2

@[simp]
theorem CuspCentralHomology.honeycombHomeomorph_edgeArcBase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    CuspHoneycomb.honeycombHomeomorph C₀ (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) =
      edgeArcPositive C₀ k t := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ((CuspHoneycomb.honeycombHomeomorph C₀ (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane))).1 :
        ToricSpace.Space) =
      ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space)
  rw [honeycombHomeomorph_baseCell_coe, compatibleCellHomeomorph_edgeArcBase]

theorem CuspCentralHomology.exists_edgeArcBase_of_mem_frontier (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : (CuspHoneycombTiling.Plane)) (hx : x ∈ frontier CuspHoneycombTiling.baseCell) :
    ∃ k : Fin 6, ∃ t : unitInterval, (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) = x := by
  obtain ⟨k, hbase, hside⟩ :=
    Set.mem_iUnion.mp ((congrArg (x ∈ ·) CuspHoneycombTiling.frontier_baseCell).mp hx)
  let a : CuspHoneycombTiling.baseCell := ⟨x, hbase⟩
  have ha :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀ a ∈
      CuspHoneycombHexagon.positiveBoundary k :=
    (CuspHoneycombHexagon.compatibleCellHomeomorph_mem_boundary_iff C₀ a k).mpr hside
  obtain ⟨t, ht⟩ :=
    (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).surjective
      ⟨CuspHoneycombHexagon.compatibleCellHomeomorph C₀ a, ha⟩
  refine ⟨k, t, ?_⟩
  have hcell : edgeArcBase C₀ k t = a := by
    apply (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).injective
    rw [compatibleCellHomeomorph_edgeArcBase]
    exact congrArg Subtype.val ht
  exact congrArg Subtype.val hcell

theorem CuspCentralHomology.honeycombHomeomorph_mem_edgeArcs_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : (CuspHoneycombTiling.Plane)) :
    (∃ k : Fin 6,
        ∃ t : unitInterval, CuspHoneycomb.honeycombHomeomorph C₀ x = edgeArcPositive C₀ k t) ↔
      x ∈ frontier CuspHoneycombTiling.baseCell := by
  constructor
  · rintro ⟨k, t, h⟩
    have hx : x = (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) :=
      (CuspHoneycomb.honeycombHomeomorph C₀).injective
        (h.trans (honeycombHomeomorph_edgeArcBase C₀ k t).symm)
    rw [hx]
    exact edgeArcBase_mem_frontier C₀ k t
  · intro hx
    obtain ⟨k, t, ht⟩ := exists_edgeArcBase_of_mem_frontier C₀ x hx
    refine ⟨k, t, ?_⟩
    rw [← ht, honeycombHomeomorph_edgeArcBase]

theorem CuspCentralHomology.mem_centralBoundary_iff_edgeArc (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (q : CuspRetraction.QuotientCentralFibre C ε) :
    q ∈ centralBoundary C ε hε ↔
      ∃ k : Fin 6,
        ∃ t : unitInterval,
          ∃ u : ToricSpace.CompactFibreTorus,
            CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) = q := by
  rw [centralBoundary_eq_image]
  constructor
  · rintro ⟨⟨u, x⟩, ⟨_, hx⟩, hq⟩
    obtain ⟨k, t, ht⟩ := (honeycombHomeomorph_mem_edgeArcs_iff (C 0) x).mpr hx
    refine ⟨k, t, u, ?_⟩
    change
      CuspCollapse.centralCollapseMap C ε hε (u, CuspHoneycomb.honeycombHomeomorph (C 0) x) =
        q at hq
    rw [ht] at hq
    exact hq
  · rintro ⟨k, t, u, hq⟩
    refine
      ⟨(u, (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane))),
        ⟨Set.mem_univ _, edgeArcBase_mem_frontier (C 0) k t⟩, ?_⟩
    change
      CuspCollapse.centralCollapseMap C ε hε
          (u,
            CuspHoneycomb.honeycombHomeomorph (C 0)
              (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane))) =
        q
    rw [honeycombHomeomorph_edgeArcBase]
    exact hq

theorem CuspCentralHomology.centralCollapseMap_edgeArc_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) ∈
      centralBoundary C ε hε :=
  (mem_centralBoundary_iff_edgeArc C ε hε _).mpr ⟨k, t, u, rfl⟩

theorem CuspCentralHomology.centralProject_edgeCylinder_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6)
    (p : unitInterval × Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k p) ∈ centralBoundary C ε hε :=
  centralCollapseMap_edgeArc_mem_centralBoundary C ε hε k p.1 (hexagonCharacterSection k p.2)

def CuspCentralHomology.threeCirclesIntersectionHomologyZeroEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0).toAddEquiv.trans
      threeCirclesHomologyZeroEquiv.toAddEquiv).toIntLinearEquiv

theorem CuspCentralHomology.threeCirclesIntersectionHomologyZeroEquiv_map {X : Type}
    [TopologicalSpace X] (U V : Set X) {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) (f : C((U ∩ V : Set X), Y))
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (SingularMayerVietoris.singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesIntersectionHomologyZeroEquiv U V e a) :=
  threeCirclesHomologyZeroEquiv_map_homotopyEquiv e f a

theorem CuspCentralHomology.threeCirclesIntersectionLeftMap_zero_iff {X : Type}
    [TopologicalSpace X] (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) :
    SingularMayerVietoris.leftHomologyMap U V 0 a = 0 ↔
      sumCoordinates (threeCirclesIntersectionHomologyZeroEquiv U V e a) = 0 := by
  constructor
  · intro ha
    have hleft :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) 0 a =
        0 := by
      rw [SingularMayerVietoris.leftHomologyMap_apply] at ha
      exact congrArg Prod.fst ha
    have hsum :=
      threeCirclesIntersectionHomologyZeroEquiv_map U V e
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) a
    rw [hleft, map_zero] at hsum
    exact hsum.symm
  · intro ha
    have hleft :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) 0 a =
        0 := by
      apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv U).injective
      rw [map_zero, threeCirclesIntersectionHomologyZeroEquiv_map U V e]
      exact ha
    have hright :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) 0 a =
        0 := by
      apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv V).injective
      rw [map_zero, threeCirclesIntersectionHomologyZeroEquiv_map U V e]
      exact ha
    rw [SingularMayerVietoris.leftHomologyMap_apply, hleft, hright, neg_zero]
    rfl

theorem CuspCentralHomology.threeCirclesIntersection_mem_ker_iff {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) :
    a ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ↔
      threeCirclesIntersectionHomologyZeroEquiv U V e a ∈ LinearMap.ker sumCoordinates :=
  threeCirclesIntersectionLeftMap_zero_iff U V e a

def CuspCentralHomology.threeCirclesIntersectionKernelToSumEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ≃ₗ[ℤ]
      LinearMap.ker sumCoordinates :=
  ({    toFun
          a :=
          ⟨threeCirclesIntersectionHomologyZeroEquiv U V e a,
            (threeCirclesIntersection_mem_ker_iff U V e a).mp a.property⟩
        invFun
          b :=
          ⟨(threeCirclesIntersectionHomologyZeroEquiv U V e).symm b,
            by
            apply (threeCirclesIntersection_mem_ker_iff U V e _).mpr
            simpa only [LinearEquiv.apply_symm_apply] using b.property⟩
        left_inv
          a := Subtype.ext ((threeCirclesIntersectionHomologyZeroEquiv U V e).symm_apply_apply a)
        right_inv
          b := Subtype.ext ((threeCirclesIntersectionHomologyZeroEquiv U V e).apply_symm_apply b)
        map_add' a
          b := Subtype.ext ((threeCirclesIntersectionHomologyZeroEquiv U V e).map_add a b) } :
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ≃+
        LinearMap.ker sumCoordinates).toIntLinearEquiv

def CuspCentralHomology.threeCirclesIntersectionKernelEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((threeCirclesIntersectionKernelToSumEquiv U V e).toAddEquiv.trans
      sumCoordinatesKernelEquiv.toAddEquiv).toIntLinearEquiv

abbrev CuspCentralHomology.ThreeCircleSuspension :=
  Suspension.topSus ThreeCircles

def CuspCentralHomology.threeCircleSuspensionHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv ThreeCircleSuspension

def CuspCentralHomology.threeCircleSuspensionHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (contractibleCoverHomologyOneEquivKernel
        ((Suspension.topSus.northOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        ((Suspension.topSus.southOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        Suspension.topSus.northOpen_isOpen Suspension.topSus.southOpen_isOpen Suspension.topSus.open_cover).trans
    (threeCirclesIntersectionKernelEquiv
      ((Suspension.topSus.northOpen : Set CuspCentralHomology.ThreeCircleSuspension))
      ((Suspension.topSus.southOpen : Set CuspCentralHomology.ThreeCircleSuspension))
      (Suspension.topSus.middleBandHomotopyEquiv (X := ThreeCircles)))

def CuspCentralHomology.threeCircleSuspensionHomologyTwoEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (contractibleCoverHomologyHigherEquiv
        ((Suspension.topSus.northOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        ((Suspension.topSus.southOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        Suspension.topSus.northOpen_isOpen Suspension.topSus.southOpen_isOpen Suspension.topSus.open_cover 0).trans
    ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Suspension.topSus.middleBandHomotopyEquiv (X := ThreeCircles)) 1).trans
      threeCirclesHomologyOneEquiv)

theorem CuspCentralHomology.threeCircleSuspension_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology ThreeCircleSuspension (n + 3)) := by
  let := threeCircles_homology_subsingleton n
  exact
    ((contractibleCoverHomologyHigherEquiv
            ((Suspension.topSus.northOpen :
              Set CuspCentralHomology.ThreeCircleSuspension))
            ((Suspension.topSus.southOpen :
              Set CuspCentralHomology.ThreeCircleSuspension))
            Suspension.topSus.northOpen_isOpen Suspension.topSus.southOpen_isOpen Suspension.topSus.open_cover
            (n + 1)).trans
        (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Suspension.topSus.middleBandHomotopyEquiv (X := ThreeCircles))
          (n + 2))).injective.subsingleton

def CuspCentralHomology.threeCircleSuspensionBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | _ => 0

def CuspCentralHomology.threeCircleSuspensionHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension n ≃ₗ[ℤ]
      (Fin (threeCircleSuspensionBetti n) → ℤ) := by
  cases n with
  | zero =>
    exact threeCircleSuspensionHomologyZeroEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | succ n =>
    cases n with
    | zero => exact threeCircleSuspensionHomologyOneEquiv
    | succ n =>
      cases n with
      | zero => exact threeCircleSuspensionHomologyTwoEquiv
      | succ
        n =>
        change
          SingularMayerVietoris.SingularHomology ThreeCircleSuspension (n + 3) ≃ₗ[ℤ] (Fin 0 → ℤ)
        letI := threeCircleSuspension_homology_subsingleton n
        exact LinearEquiv.ofSubsingleton _ _

theorem CuspCentralHomology.doubleCylinder_mem_centralBoundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : unitInterval × ThreeCircles) :
    doubleCylinder C ε hε p ∈ centralBoundary C ε hε := by
  rcases p with ⟨t, a | (a | a)⟩
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 0 (t, a)
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 1 (unitInterval.symm t, a)
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 2 (t, a)

theorem CuspCentralHomology.range_doubleCylinder_eq_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set.range (doubleCylinder C ε hε) = centralBoundary C ε hε := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact doubleCylinder_mem_centralBoundary C ε hε p
  · intro hq
    obtain ⟨k, t, u, hu⟩ := (mem_centralBoundary_iff_edgeArc C ε hε q).mp hq
    rw [← hu]
    exact centralCollapseMap_edgeArc_mem_range_doubleCylinder C ε hε k t u

theorem CuspCentralHomology.range_doubleSuspensionMap_eq_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set.range (doubleSuspensionMap C ε hε) = centralBoundary C ε hε := by
  rw [range_doubleSuspensionMap, range_doubleCylinder_eq_centralBoundary]

theorem CuspCentralHomology.doubleSuspensionMap_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : ThreeCircleSuspension) :
    doubleSuspensionMap C ε hε p ∈ centralBoundary C ε hε := by
  rw [← range_doubleSuspensionMap_eq_centralBoundary]
  exact Set.mem_range_self p

def CuspCentralHomology.doubleSuspensionBoundaryMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : ThreeCircleSuspension) : centralBoundary C ε hε :=
  ⟨doubleSuspensionMap C ε hε p, doubleSuspensionMap_mem_centralBoundary C ε hε p⟩

theorem CuspCentralHomology.doubleSuspensionBoundaryMap_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (doubleSuspensionBoundaryMap C ε hε) :=
  (doubleSuspensionMap_continuous C ε hε).subtype_mk _

theorem CuspCentralHomology.doubleSuspensionBoundaryMap_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Function.Bijective (doubleSuspensionBoundaryMap C ε hε) := by
  constructor
  · intro p q h
    exact doubleSuspensionMap_injective C ε hε (congrArg Subtype.val h)
  · rintro ⟨q, hq⟩
    rw [← range_doubleSuspensionMap_eq_centralBoundary] at hq
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩

def CuspCentralHomology.doubleSuspensionBoundaryEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : ThreeCircleSuspension ≃ centralBoundary C ε hε :=
  Equiv.ofBijective (doubleSuspensionBoundaryMap C ε hε)
    (doubleSuspensionBoundaryMap_bijective C ε hε)

def CuspCentralHomology.doubleSuspensionBoundaryHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : ThreeCircleSuspension ≃ₜ centralBoundary C ε hε := by
  letI := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact
    (doubleSuspensionBoundaryEquiv C ε hε).toHomeomorphOfContinuousClosed
      (doubleSuspensionBoundaryMap_continuous C ε hε)
      (doubleSuspensionBoundaryMap_continuous C ε hε).isClosedMap

def CuspCentralHomology.centralBoundarySuspensionHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : centralBoundary C ε hε ≃ₜ ThreeCircleSuspension :=
  (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR).symm

@[simp]
theorem CuspCentralHomology.centralBoundarySuspensionHomeomorph_symm_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : ThreeCircleSuspension) :
    ((centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm p :
        CuspRetraction.QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε p :=
  rfl

def CuspCentralHomology.centralBoundaryHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (centralBoundary C ε hε) n ≃ₗ[ℤ]
      (Fin (threeCircleSuspensionBetti n) → ℤ) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) n).trans
    (threeCircleSuspensionHomologyEquiv n)

def CuspCentralHomology.centralBoundaryHomologyOneEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (centralBoundary C ε hε) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) 1).trans
    threeCircleSuspensionHomologyOneEquiv

abbrev CuspCentralHomology.InteriorPhaseCell :=
  ToricSpace.CompactFibreTorus × (interior CuspHoneycombTiling.baseCell)

def CuspCentralHomology.interiorCellInclusion (p : InteriorPhaseCell) : FundamentalCell :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), interior_subset p.2.2⟩)

@[simp]
theorem CuspCentralHomology.interiorCellInclusion_snd_coe (p : InteriorPhaseCell) :
    ((interiorCellInclusion p).2 : (CuspHoneycombTiling.Plane)) =
      (p.2 : (CuspHoneycombTiling.Plane)) :=
  rfl

theorem CuspCentralHomology.interiorCellInclusion_continuous : Continuous interiorCellInclusion :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem CuspCentralHomology.interiorCellInclusion_injective :
    Function.Injective interiorCellInclusion := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : FundamentalCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : FundamentalCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq

def CuspCentralHomology.interiorCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    InteriorPhaseCell → CuspRetraction.QuotientCentralFibre C ε :=
  fundamentalCellMap C ε hε ∘ interiorCellInclusion

theorem CuspCentralHomology.interiorCellMap_eq_fundamentalCellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : InteriorPhaseCell) :
    interiorCellMap C ε hε p = fundamentalCellMap C ε hε (interiorCellInclusion p) :=
  rfl

@[simp]
theorem CuspCentralHomology.interiorCellMap_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : InteriorPhaseCell) :
    interiorCellMap C ε hε p =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

theorem CuspCentralHomology.interiorCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (interiorCellMap C ε hε) :=
  (fundamentalCellMap_continuous C ε hε).comp interiorCellInclusion_continuous

theorem CuspCentralHomology.interiorCellMap_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Injective (interiorCellMap C ε hε) := by
  intro p q hpq
  apply interiorCellInclusion_injective
  exact
    fundamentalCellMap_eq_of_interior C ε hε (interiorCellInclusion p) (interiorCellInclusion q)
      p.2.2 hpq

def CuspCentralHomology.interiorImage (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set (CuspRetraction.QuotientCentralFibre C ε) :=
  Set.range (interiorCellMap C ε hε)

theorem CuspCentralHomology.fundamentalCellMap_mem_interiorImage_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ interiorImage C ε hε ↔
      (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  constructor
  · rintro ⟨q, hq⟩
    have he := fundamentalCellMap_eq_of_interior C ε hε (interiorCellInclusion q) p q.2.2 hq
    rw [← he]
    exact q.2.2
  · intro hp
    exact ⟨(p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), hp⟩), rfl⟩

def CuspCentralHomology.interiorCellMapToImage (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : InteriorPhaseCell) : interiorImage C ε hε :=
  ⟨interiorCellMap C ε hε p, Set.mem_range_self p⟩

theorem CuspCentralHomology.interiorCellMapToImage_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (interiorCellMapToImage C ε hε) :=
  (interiorCellMap_continuous C ε hε).subtype_mk _

theorem CuspCentralHomology.interiorCellMapToImage_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Surjective (interiorCellMapToImage C ε hε) := by
  rintro ⟨y, p, hp⟩
  exact ⟨p, Subtype.ext hp⟩

theorem CuspCentralHomology.interiorCellMapToImage_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Injective (interiorCellMapToImage C ε hε) := by
  intro p q hpq
  exact interiorCellMap_injective C ε hε (congrArg Subtype.val hpq)

def CuspCentralHomology.interiorPreimageHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : InteriorPhaseCell ≃ₜ (fundamentalCellMap C ε hε ⁻¹' interiorImage C ε hε)
    where
  toFun
    p := ⟨interiorCellInclusion p, (fundamentalCellMap_mem_interiorImage_iff C ε hε _).mpr p.2.2⟩
  invFun
    p :=
    (p.1.1,
      ⟨(p.1.2 : (CuspHoneycombTiling.Plane)),
        (fundamentalCellMap_mem_interiorImage_iff C ε hε p.1).mp p.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := interiorCellInclusion_continuous.subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

theorem CuspCentralHomology.interiorCellMapToImage_isProperMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (interiorCellMapToImage C ε hε) := by
  have hf :=
    (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).restrictPreimage (interiorImage C ε hε)
  have hg := (interiorPreimageHomeomorph C ε hε).isProperMap
  have hc := hf.comp hg
  have he :
    (interiorImage C ε hε).restrictPreimage (fundamentalCellMap C ε hε) ∘
        interiorPreimageHomeomorph C ε hε =
      interiorCellMapToImage C ε hε := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

theorem CuspCentralHomology.interiorCellMapToImage_isClosedMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsClosedMap (interiorCellMapToImage C ε hε) :=
  (interiorCellMapToImage_isProperMap C ε hε hε1 hC hR).isClosedMap

def CuspCentralHomology.interiorCellHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : InteriorPhaseCell ≃ₜ interiorImage C ε hε :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (interiorCellMapToImage C ε hε)
      ⟨interiorCellMapToImage_injective C ε hε, interiorCellMapToImage_surjective C ε hε⟩)
    (interiorCellMapToImage_continuous C ε hε)
    (interiorCellMapToImage_isClosedMap C ε hε hε1 hC hR)

@[simp]
theorem CuspCentralHomology.interiorCellHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    (interiorCellHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p :=
  rfl

theorem CuspCentralHomology.innerRegion_eq_interiorImage (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : innerRegion C ε hε = interiorImage C ε hε := by
  ext q
  obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
  exact
    (fundamentalCellMap_mem_innerRegion_iff C ε hε p).trans
      (fundamentalCellMap_mem_interiorImage_iff C ε hε p).symm

def CuspCentralHomology.innerRegionHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : InteriorPhaseCell ≃ₜ innerRegion C ε hε :=
  (interiorCellHomeomorph C ε hε hε1 hC hR).trans
    (Homeomorph.setCongr (innerRegion_eq_interiorImage C ε hε).symm)

@[simp]
theorem CuspCentralHomology.innerRegionHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    (innerRegionHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p :=
  interiorCellHomeomorph_coe C ε hε hε1 hC hR p

@[simp]
theorem CuspCentralHomology.innerRegionHomeomorph_honeycomb (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    (innerRegionHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) := by
  rw [innerRegionHomeomorph_coe, interiorCellMap_apply]

theorem CuspCentralHomology.innerRegionHomeomorph_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    centralRadius C ε hε
        (innerRegionHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) := by
  rw [innerRegionHomeomorph_coe, interiorCellMap_eq_fundamentalCellMap,
    centralRadius_fundamentalCellMap, interiorCellInclusion_snd_coe]

abbrev CuspCentralHomology.Radial.InteriorCell :=
  interior CuspHoneycombTiling.baseCell

def CuspCentralHomology.Radial.interiorCellZero : InteriorCell :=
  ⟨0, (mem_interior_baseCell_iff 0).mpr (by rw [cellGauge_zero]; norm_num)⟩

def CuspCentralHomology.Radial.interiorCellContract (s : unitInterval) (x : InteriorCell) :
    InteriorCell :=
  ⟨(1 - (s : ℝ)) • (x : CuspHoneycombTiling.Plane),
    by
    apply (mem_interior_baseCell_iff _).mpr
    rw [cellGauge_smul_of_nonneg _ (sub_nonneg.mpr s.2.2)]
    calc
      (1 - (s : ℝ)) * cellGauge x ≤ 1 * cellGauge x :=
        mul_le_mul_of_nonneg_right (sub_le_self 1 s.2.1) (cellGauge_nonneg x)
      _ = cellGauge x := (one_mul _)
      _ < 1 := (mem_interior_baseCell_iff x).mp x.2⟩

theorem CuspCentralHomology.Radial.interiorCellContract_continuous :
    Continuous (fun p : unitInterval × InteriorCell => interiorCellContract p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk
    _

@[simp]
theorem CuspCentralHomology.Radial.interiorCellContract_zero (x : InteriorCell) :
    interiorCellContract 0 x = x := by
  apply Subtype.ext
  simp [interiorCellContract]

@[simp]
theorem CuspCentralHomology.Radial.interiorCellContract_one (x : InteriorCell) :
    interiorCellContract 1 x = interiorCellZero := by
  apply Subtype.ext
  simp [interiorCellContract, interiorCellZero]

@[simp]
theorem CuspCentralHomology.Radial.interiorCellContract_fixed_zero (s : unitInterval) :
    interiorCellContract s interiorCellZero = interiorCellZero := by
  apply Subtype.ext
  simp [interiorCellContract, interiorCellZero]

def CuspCentralHomology.Radial.interiorCellContraction :
    (ContinuousMap.id InteriorCell).HomotopyRel
      (ContinuousMap.const InteriorCell interiorCellZero) { interiorCellZero }
    where
  toFun p := interiorCellContract p.1 p.2
  continuous_toFun := interiorCellContract_continuous
  map_zero_left := interiorCellContract_zero
  map_one_left := interiorCellContract_one
  prop' s x
    hx := by
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact interiorCellContract_fixed_zero s

def CuspCentralHomology.Radial.interiorCellPointHomotopyEquiv : InteriorCell ≃ₕ Unit
    where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ interiorCellZero
  left_inv := ⟨interiorCellContraction.toHomotopy.symm⟩
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id Unit) using 1
    ext u

def CuspCentralHomology.Radial.interiorCellProductHomotopyEquiv (X : Type*) [TopologicalSpace X] :
    (X × InteriorCell) ≃ₕ X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr interiorCellPointHomotopyEquiv).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv

abbrev CuspCentralHomology.Radial.CellFrontier :=
  frontier CuspHoneycombTiling.baseCell

abbrev CuspCentralHomology.Radial.Annulus (a : ℝ) :=
  { x : (CuspHoneycombTiling.Plane) // a < cellGauge x ∧ cellGauge x < 1 }

noncomputable def CuspCentralHomology.Radial.normalize (x : (CuspHoneycombTiling.Plane)) :
    (CuspHoneycombTiling.Plane) :=
  (cellGauge x)⁻¹ • x

theorem CuspCentralHomology.Radial.normalize_gauge (x : (CuspHoneycombTiling.Plane))
    (hx : x ≠ 0) : cellGauge (CuspCentralHomology.Radial.normalize x) = 1 := by
  rw [CuspCentralHomology.Radial.normalize,
    cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (cellGauge_nonneg x))]
  exact inv_mul_cancel₀ ((cellGauge_pos_iff x).mpr hx).ne'

theorem CuspCentralHomology.Radial.normalize_continuousOn :
    ContinuousOn CuspCentralHomology.Radial.normalize {x : (CuspHoneycombTiling.Plane) | x ≠ 0} :=
  (cellGauge_continuous.continuousOn.inv₀ (fun x hx => ((cellGauge_pos_iff x).mpr hx).ne')).smul
    continuous_id.continuousOn

noncomputable def CuspCentralHomology.Radial.direction
    (x : { x : (CuspHoneycombTiling.Plane) // x ≠ 0 }) : CellFrontier :=
  ⟨CuspCentralHomology.Radial.normalize x,
    (mem_frontier_baseCell_iff _).mpr (normalize_gauge x x.2)⟩

theorem CuspCentralHomology.Radial.direction_continuous : Continuous direction :=
  normalize_continuousOn.domRestrict.subtype_mk _

theorem CuspCentralHomology.Radial.cellGauge_smul_frontier (c : ℝ) (hc : 0 ≤ c)
    (u : CellFrontier) : cellGauge (c • (u : (CuspHoneycombTiling.Plane))) = c := by
  rw [cellGauge_smul_of_nonneg c hc, (mem_frontier_baseCell_iff _).mp u.2, mul_one]

noncomputable def CuspCentralHomology.Radial.radialRangeHomeomorph (R : Set ℝ)
    (hR : ∀ r ∈ R, 0 < r) :
    { x : (CuspHoneycombTiling.Plane) // cellGauge x ∈ R } ≃ₜ CellFrontier × R
    where
  toFun x := (direction ⟨x, (cellGauge_pos_iff x).mp (hR _ x.2)⟩, ⟨cellGauge x, x.2⟩)
  invFun
    p :=
    ⟨(p.2 : ℝ) • (p.1 : (CuspHoneycombTiling.Plane)),
      by
      rw [cellGauge_smul_frontier _ (hR _ p.2.2).le]
      exact p.2.2⟩
  left_inv
    x := by
    apply Subtype.ext
    change
      cellGauge x • ((cellGauge x)⁻¹ • (x : (CuspHoneycombTiling.Plane))) =
        (x : (CuspHoneycombTiling.Plane))
    rw [smul_smul, mul_inv_cancel₀ (hR _ x.2).ne', one_smul]
  right_inv
    p := by
    apply Prod.ext
    · apply Subtype.ext
      change
        CuspCentralHomology.Radial.normalize ((p.2 : ℝ) • (p.1 : (CuspHoneycombTiling.Plane))) =
          (p.1 : (CuspHoneycombTiling.Plane))
      rw [CuspCentralHomology.Radial.normalize, cellGauge_smul_frontier _ (hR _ p.2.2).le,
        smul_smul, inv_mul_cancel₀ (hR _ p.2.2).ne', one_smul]
    · apply Subtype.ext
      exact cellGauge_smul_frontier _ (hR _ p.2.2).le p.1
  continuous_toFun :=
    (direction_continuous.comp (continuous_subtype_val.subtype_mk _)).prodMk
      ((cellGauge_continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp continuous_fst)).subtype_mk
      _

noncomputable def CuspCentralHomology.Radial.annulusHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    Annulus a ≃ₜ CellFrontier × Set.Ioo a 1 :=
  radialRangeHomeomorph (Set.Ioo a 1) (fun _ hr => ha.trans_lt hr.1)

abbrev CuspCentralHomology.Radial.RadialDomain (R : Set ℝ) :=
  { x : (CuspHoneycombTiling.Plane) // cellGauge x ∈ R }

def CuspCentralHomology.Radial.radiusProjection (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) :
    C(RadialDomain R, CellFrontier) :=
  ⟨fun x => (radialRangeHomeomorph R hR x).1,
    continuous_fst.comp (radialRangeHomeomorph R hR).continuous⟩

def CuspCentralHomology.Radial.radiusSection (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (c : ℝ)
    (hc : c ∈ R) : C(CellFrontier, RadialDomain R) :=
  ⟨fun u => (radialRangeHomeomorph R hR).symm (u, ⟨c, hc⟩),
    (radialRangeHomeomorph R hR).symm.continuous.comp (continuous_id.prodMk continuous_const)⟩

theorem CuspCentralHomology.Radial.radiusProjection_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (x : RadialDomain R) :
    (radiusProjection R hR x : (CuspHoneycombTiling.Plane)) =
      CuspCentralHomology.Radial.normalize x :=
  rfl

theorem CuspCentralHomology.Radial.radiusSection_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (c : ℝ)
    (hc : c ∈ R) (u : CellFrontier) :
    (radiusSection R hR c hc u : (CuspHoneycombTiling.Plane)) =
      c • (u : (CuspHoneycombTiling.Plane)) :=
  rfl

theorem CuspCentralHomology.Radial.radiusProjection_comp_section (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (c : ℝ) (hc : c ∈ R) :
    (radiusProjection R hR).comp (radiusSection R hR c hc) = ContinuousMap.id CellFrontier := by
  apply ContinuousMap.ext
  intro u
  change ((radialRangeHomeomorph R hR) ((radialRangeHomeomorph R hR).symm (u, ⟨c, hc⟩))).1 = u
  rw [Homeomorph.apply_symm_apply]

def CuspCentralHomology.Radial.radiusBlend (c : ℝ) (s : unitInterval) (r : ℝ) : ℝ :=
  (1 - (s : ℝ)) * r + (s : ℝ) * c

theorem CuspCentralHomology.Radial.radiusBlend_mem {R : Set ℝ} (hconv : Convex ℝ R) (c : ℝ)
    (hc : c ∈ R) (s : unitInterval) (r : ℝ) (hr : r ∈ R) : radiusBlend c s r ∈ R :=
  hconv hr hc (sub_nonneg.mpr s.2.2) s.2.1 (sub_add_cancel 1 (s : ℝ))

def CuspCentralHomology.Radial.radiusHomotopyMap (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) : C(unitInterval × RadialDomain R, RadialDomain R)
    where
  toFun
    p :=
    (radialRangeHomeomorph R hR).symm
      ((radialRangeHomeomorph R hR p.2).1,
        ⟨radiusBlend c p.1 (cellGauge p.2), radiusBlend_mem hconv c hc p.1 _ p.2.2⟩)
  continuous_toFun :=
    (radialRangeHomeomorph R hR).symm.continuous.comp
      ((continuous_fst.comp ((radialRangeHomeomorph R hR).continuous.comp continuous_snd)).prodMk
        ((((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
                  (cellGauge_continuous.comp (continuous_subtype_val.comp continuous_snd))).add
              ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk
          _))

theorem CuspCentralHomology.Radial.radiusHomotopyMap_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R) :
    (radiusHomotopyMap R hR hconv c hc (s, x) : (CuspHoneycombTiling.Plane)) =
      radiusBlend c s (cellGauge x) • CuspCentralHomology.Radial.normalize x :=
  rfl

theorem CuspCentralHomology.Radial.radiusHomotopyMap_gauge (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R) :
    cellGauge (radiusHomotopyMap R hR hconv c hc (s, x)) = radiusBlend c s (cellGauge x) :=
  cellGauge_smul_frontier _ (hR _ (radiusBlend_mem hconv c hc s _ x.2)).le
    (radialRangeHomeomorph R hR x).1

theorem CuspCentralHomology.Radial.radiusHomotopyMap_zero (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (x : RadialDomain R) :
    radiusHomotopyMap R hR hconv c hc (0, x) = x := by
  apply Subtype.ext
  rw [radiusHomotopyMap_coe]
  change
    ((1 - (0 : ℝ)) * cellGauge x + 0 * c) • CuspCentralHomology.Radial.normalize x =
      (x : (CuspHoneycombTiling.Plane))
  rw [sub_zero, one_mul, MulZeroClass.zero_mul, add_zero, CuspCentralHomology.Radial.normalize,
    smul_smul, mul_inv_cancel₀ (hR _ x.2).ne', one_smul]

theorem CuspCentralHomology.Radial.radiusHomotopyMap_one (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (x : RadialDomain R) :
    radiusHomotopyMap R hR hconv c hc (1, x) =
      radiusSection R hR c hc (radiusProjection R hR x) := by
  apply Subtype.ext
  rw [radiusHomotopyMap_coe, radiusSection_coe, radiusProjection_coe]
  change
    ((1 - (1 : ℝ)) * cellGauge x + 1 * c) • CuspCentralHomology.Radial.normalize x =
      c • CuspCentralHomology.Radial.normalize x
  rw [sub_self, MulZeroClass.zero_mul, one_mul, zero_add]

theorem CuspCentralHomology.Radial.radiusHomotopyMap_fixed (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R)
    (hx : cellGauge x = c) : radiusHomotopyMap R hR hconv c hc (s, x) = x := by
  have hblend : radiusBlend c s (cellGauge x) = cellGauge x := by
    rw [radiusBlend, hx]
    ring
  apply Subtype.ext
  rw [radiusHomotopyMap_coe, hblend, CuspCentralHomology.Radial.normalize, smul_smul,
    mul_inv_cancel₀ (hR _ x.2).ne', one_smul]

def CuspCentralHomology.Radial.radiusHomotopy (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) :
    (ContinuousMap.id (RadialDomain R)).Homotopy
      ((radiusSection R hR c hc).comp (radiusProjection R hR))
    where
  toContinuousMap := radiusHomotopyMap R hR hconv c hc
  map_zero_left := radiusHomotopyMap_zero R hR hconv c hc
  map_one_left := radiusHomotopyMap_one R hR hconv c hc

def CuspCentralHomology.Radial.radialHomotopyEquiv (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) : RadialDomain R ≃ₕ CellFrontier
    where
  toFun := radiusProjection R hR
  invFun := radiusSection R hR c hc
  left_inv := ⟨(radiusHomotopy R hR hconv c hc).symm⟩
  right_inv := by rw [radiusProjection_comp_section]

def CuspCentralHomology.Radial.annulusFrontierHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Annulus a ≃ₕ CellFrontier :=
  radialHomotopyEquiv (Set.Ioo a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioo a 1) ((a + 1) / 2)
    ⟨by linarith, by linarith⟩

abbrev CuspCentralHomology.Radial.OpenCollar (a : ℝ) :=
  { x : (CuspHoneycombTiling.Plane) // a < cellGauge x ∧ cellGauge x ≤ 1 }

def CuspCentralHomology.Radial.frontierIntoOpenCollar (a : ℝ) (ha1 : a < 1) :
    C(CellFrontier, OpenCollar a) :=
  ⟨fun u =>
    ⟨u, by
      rw [(mem_frontier_baseCell_iff _).mp u.2]
      exact ⟨ha1, le_rfl⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

def CuspCentralHomology.Radial.openCollarRetraction (a : ℝ) (ha : 0 ≤ a) :
    C(OpenCollar a, CellFrontier) :=
  radiusProjection (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1)

def CuspCentralHomology.Radial.outwardOpenCollarHomotopy (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (ContinuousMap.id (OpenCollar a)).HomotopyRel
      ((frontierIntoOpenCollar a ha1).comp (openCollarRetraction a ha))
      {x : OpenCollar a | cellGauge x = 1}
    where
  toContinuousMap :=
    radiusHomotopyMap (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩
  map_zero_left :=
    radiusHomotopyMap_zero (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩
  map_one_left
    x := by
    apply Subtype.ext
    change
      ((1 - (1 : ℝ)) * cellGauge x + 1 * 1) • CuspCentralHomology.Radial.normalize x =
        CuspCentralHomology.Radial.normalize x
    rw [sub_self, MulZeroClass.zero_mul, one_mul, zero_add, one_smul]
  prop' s x
    hx :=
    radiusHomotopyMap_fixed (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩ s x hx

theorem CuspCentralHomology.Radial.outwardOpenCollarHomotopy_coe (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : OpenCollar a) :
    (outwardOpenCollarHomotopy a ha ha1 (s, x) : (CuspHoneycombTiling.Plane)) =
      ((1 - (s : ℝ)) + (s : ℝ) / cellGauge x) • (x : (CuspHoneycombTiling.Plane)) := by
  change radiusBlend 1 s (cellGauge x) • CuspCentralHomology.Radial.normalize x = _
  rw [CuspCentralHomology.Radial.normalize, smul_smul]
  congr 1
  rw [radiusBlend, mul_one, add_mul, mul_assoc, mul_inv_cancel₀ (ha.trans_lt x.2.1).ne', mul_one,
    div_eq_mul_inv]

theorem CuspCentralHomology.Radial.outwardOpenCollarHomotopy_gauge (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : OpenCollar a) :
    cellGauge (outwardOpenCollarHomotopy a ha ha1 (s, x)) =
      (1 - (s : ℝ)) * cellGauge x + (s : ℝ) := by
  change
    cellGauge
        (radiusHomotopyMap (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
          ⟨ha1, le_rfl⟩ (s, x)) =
      _
  simpa only [radiusBlend, mul_one] using
    radiusHomotopyMap_gauge (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩ s x

theorem CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : OpenCollar a)
    (hx : (x : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) :
    outwardOpenCollarHomotopy a ha ha1 (s, x) = x :=
  (outwardOpenCollarHomotopy a ha ha1).eq_fst s ((mem_frontier_baseCell_iff _).mp hx)

def CuspCentralHomology.Radial.circlePlaneComplexEquiv : CuspHoneycombTiling.Plane ≃L[ℝ] ℂ
    where
  toFun x := ⟨x 0, x 1⟩
  invFun z := ![z.re, z.im]
  left_inv
    x := by
    funext i
    fin_cases i <;> rfl
  right_inv
    z := by
    cases z
    rfl
  map_add' _ _ := rfl
  map_smul' c x := by apply Complex.ext <;> simp
  continuous_toFun := by
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

theorem CuspCentralHomology.Radial.circleFrontier_ne_zero
    (x : frontier CuspHoneycombTiling.baseCell) : (x : CuspHoneycombTiling.Plane) ≠ 0 := by
  intro hx
  have hg := (mem_frontier_baseCell_iff (x : CuspHoneycombTiling.Plane)).mp x.property
  exact zero_ne_one (by simpa only [hx, cellGauge_zero] using hg)

theorem CuspCentralHomology.Radial.circleFrontierComplex_ne_zero
    (x : frontier CuspHoneycombTiling.baseCell) :
    circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane) ≠ 0 := by
  intro hx
  exact circleFrontier_ne_zero x (circlePlaneComplexEquiv.map_eq_zero_iff.mp hx)

def CuspCentralHomology.Radial.frontierCircleForward (x : frontier CuspHoneycombTiling.baseCell) :
    Circle :=
  ⟨NormedSpace.normalize (circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane)),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (circleFrontierComplex_ne_zero x))⟩

@[simp]
theorem CuspCentralHomology.Radial.frontierCircleForward_coe
    (x : frontier CuspHoneycombTiling.baseCell) :
    (frontierCircleForward x : ℂ) =
      ‖circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane)‖⁻¹ •
        circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane) :=
  rfl

theorem CuspCentralHomology.Radial.frontierCircleForward_continuous :
    Continuous frontierCircleForward := by
  apply Continuous.subtype_mk
  have h :
    Continuous
      (fun x : frontier CuspHoneycombTiling.baseCell =>
        circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane)) :=
    circlePlaneComplexEquiv.continuous.comp continuous_subtype_val
  exact (h.norm.inv₀ fun x => norm_ne_zero_iff.mpr (circleFrontierComplex_ne_zero x)).smul h

theorem CuspCentralHomology.Radial.circleComplexPlane_ne_zero (z : Circle) :
    circlePlaneComplexEquiv.symm (z : ℂ) ≠ 0 := by
  intro hz
  exact z.coe_ne_zero (circlePlaneComplexEquiv.symm.map_eq_zero_iff.mp hz)

theorem CuspCentralHomology.Radial.circleComplexPlaneGauge_pos (z : Circle) :
    0 < cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)) :=
  (cellGauge_pos_iff _).mpr (circleComplexPlane_ne_zero z)

def CuspCentralHomology.Radial.frontierCircleInverse (z : Circle) :
    frontier CuspHoneycombTiling.baseCell :=
  ⟨(cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)))⁻¹ • circlePlaneComplexEquiv.symm (z : ℂ),
    (mem_frontier_baseCell_iff _).mpr
      (by
        rw [cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (cellGauge_nonneg _)),
          inv_mul_cancel₀ (ne_of_gt (circleComplexPlaneGauge_pos z))])⟩

@[simp]
theorem CuspCentralHomology.Radial.frontierCircleInverse_coe (z : Circle) :
    (frontierCircleInverse z : CuspHoneycombTiling.Plane) =
      (cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)))⁻¹ •
        circlePlaneComplexEquiv.symm (z : ℂ) :=
  rfl

theorem CuspCentralHomology.Radial.frontierCircleInverse_continuous :
    Continuous frontierCircleInverse := by
  apply Continuous.subtype_mk
  have h : Continuous (fun z : Circle => circlePlaneComplexEquiv.symm (z : ℂ)) :=
    circlePlaneComplexEquiv.symm.continuous.comp continuous_subtype_val
  exact
    ((cellGauge_continuous.comp h).inv₀ fun z => ne_of_gt (circleComplexPlaneGauge_pos z)).smul h

@[simp]
theorem CuspCentralHomology.Radial.frontierCircleInverse_forward
    (x : frontier CuspHoneycombTiling.baseCell) :
    frontierCircleInverse (frontierCircleForward x) = x := by
  apply Subtype.ext
  change
    (cellGauge (circlePlaneComplexEquiv.symm (frontierCircleForward x : ℂ)))⁻¹ •
        circlePlaneComplexEquiv.symm (frontierCircleForward x : ℂ) =
      (x : CuspHoneycombTiling.Plane)
  rw [frontierCircleForward_coe, map_smul, circlePlaneComplexEquiv.symm_apply_apply,
    cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (norm_nonneg _)),
    (mem_frontier_baseCell_iff _).mp x.property, mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (circleFrontierComplex_ne_zero x)), one_smul]

@[simp]
theorem CuspCentralHomology.Radial.frontierCircleForward_inverse (z : Circle) :
    frontierCircleForward (frontierCircleInverse z) = z := by
  apply Circle.ext
  change
    NormedSpace.normalize
        (circlePlaneComplexEquiv (frontierCircleInverse z : CuspHoneycombTiling.Plane)) =
      (z : ℂ)
  rw [frontierCircleInverse_coe, map_smul, circlePlaneComplexEquiv.apply_symm_apply,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (circleComplexPlaneGauge_pos z))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe

def CuspCentralHomology.Radial.frontierCellCircleHomeomorph :
    frontier CuspHoneycombTiling.baseCell ≃ₜ Circle
    where
  toFun := frontierCircleForward
  invFun := frontierCircleInverse
  left_inv := frontierCircleInverse_forward
  right_inv := frontierCircleForward_inverse
  continuous_toFun := frontierCircleForward_continuous
  continuous_invFun := frontierCircleInverse_continuous

@[simp]
theorem CuspCentralHomology.Radial.frontierCellCircleHomeomorph_symm_coe (z : Circle) :
    (frontierCellCircleHomeomorph.symm z : CuspHoneycombTiling.Plane) =
      (cellGauge ![(z : ℂ).re, (z : ℂ).im])⁻¹ • ![(z : ℂ).re, (z : ℂ).im] :=
  rfl

def CuspCentralHomology.Radial.annulusCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Annulus a ≃ₕ Circle :=
  (annulusFrontierHomotopyEquiv a ha ha1).trans frontierCellCircleHomeomorph.toHomotopyEquiv

def CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv (X : Type*) [TopologicalSpace X] (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) : (X × Annulus a) ≃ₕ X × Circle :=
  (ContinuousMap.HomotopyEquiv.refl X).prodCongr (annulusCircleHomotopyEquiv a ha ha1)

abbrev CuspCentralHomology.OverlapPhaseCell (a : ℝ) :=
  ToricSpace.CompactFibreTorus × Radial.Annulus a

def CuspCentralHomology.annulusCellInclusion (a : ℝ) (p : OverlapPhaseCell a) :
    InteriorPhaseCell :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), (Radial.mem_interior_baseCell_iff _).mpr p.2.2.2⟩)

@[simp]
theorem CuspCentralHomology.annulusCellInclusion_snd_coe (a : ℝ) (p : OverlapPhaseCell a) :
    ((annulusCellInclusion a p).2 : (CuspHoneycombTiling.Plane)) =
      (p.2 : (CuspHoneycombTiling.Plane)) :=
  rfl

theorem CuspCentralHomology.annulusCellInclusion_continuous (a : ℝ) :
    Continuous (annulusCellInclusion a) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem CuspCentralHomology.annulusCellInclusion_injective (a : ℝ) :
    Function.Injective (annulusCellInclusion a) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : InteriorPhaseCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : InteriorPhaseCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq

def CuspCentralHomology.overlapRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : Set (CuspRetraction.QuotientCentralFibre C ε) :=
  outerRegion C ε hε a ∩ innerRegion C ε hε

def CuspCentralHomology.overlapIntoInner (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : C(overlapRegion C ε hε a, innerRegion C ε hε) :=
  ⟨fun q => ⟨(q : CuspRetraction.QuotientCentralFibre C ε), q.2.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def CuspCentralHomology.overlapCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) : overlapRegion C ε hε a :=
  ⟨(innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p) :
      CuspRetraction.QuotientCentralFibre C ε),
    by
    constructor
    · change a < centralRadius C ε hε _
      rw [innerRegionHomeomorph_radius, annulusCellInclusion_snd_coe]
      exact p.2.2.1
    · exact (innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p)).2⟩

@[simp]
theorem CuspCentralHomology.overlapCellMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    (overlapCellMap C ε hε hε1 hC hR a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  innerRegionHomeomorph_honeycomb C ε hε hε1 hC hR (annulusCellInclusion a p)

theorem CuspCentralHomology.overlapCellMap_intoInner (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    overlapIntoInner C ε hε a (overlapCellMap C ε hε hε1 hC hR a p) =
      innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p) :=
  rfl

theorem CuspCentralHomology.overlapCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) : Continuous (overlapCellMap C ε hε hε1 hC hR a) :=
  (continuous_subtype_val.comp
        ((innerRegionHomeomorph C ε hε hε1 hC hR).continuous.comp
          (annulusCellInclusion_continuous a))).subtype_mk
    _

def CuspCentralHomology.overlapCellInverse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (q : overlapRegion C ε hε a) : OverlapPhaseCell a :=
  let p := (innerRegionHomeomorph C ε hε hε1 hC hR).symm (overlapIntoInner C ε hε a q)
  (p.1,
    ⟨(p.2 : (CuspHoneycombTiling.Plane)), by
      constructor
      · rw [← innerRegionHomeomorph_radius C ε hε hε1 hC hR p]
        dsimp only [p]
        rw [Homeomorph.apply_symm_apply]
        exact q.2.1
      · exact (Radial.mem_interior_baseCell_iff _).mp p.2.2⟩)

theorem CuspCentralHomology.overlapCellInverse_interior (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (q : overlapRegion C ε hε a) :
    annulusCellInclusion a (overlapCellInverse C ε hε hε1 hC hR a q) =
      (innerRegionHomeomorph C ε hε hε1 hC hR).symm (overlapIntoInner C ε hε a q) :=
  rfl

theorem CuspCentralHomology.overlapCellInverse_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) :
    Continuous (overlapCellInverse C ε hε hε1 hC hR a) := by
  have hp :=
    (innerRegionHomeomorph C ε hε hε1 hC hR).symm.continuous.comp
      (overlapIntoInner C ε hε a).continuous
  exact
    (continuous_fst.comp hp).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp hp)).subtype_mk _)

def CuspCentralHomology.overlapPhaseHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) : OverlapPhaseCell a ≃ₜ overlapRegion C ε hε a
    where
  toFun := overlapCellMap C ε hε hε1 hC hR a
  invFun := overlapCellInverse C ε hε hε1 hC hR a
  left_inv
    p := by
    apply annulusCellInclusion_injective a
    rw [overlapCellInverse_interior, overlapCellMap_intoInner, Homeomorph.symm_apply_apply]
  right_inv
    q := by
    apply Subtype.ext
    change
      (innerRegionHomeomorph C ε hε hε1 hC hR
            (annulusCellInclusion a (overlapCellInverse C ε hε hε1 hC hR a q)) :
          CuspRetraction.QuotientCentralFibre C ε) =
        (q : CuspRetraction.QuotientCentralFibre C ε)
    rw [overlapCellInverse_interior, Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := overlapCellMap_continuous C ε hε hε1 hC hR a
  continuous_invFun := overlapCellInverse_continuous C ε hε hε1 hC hR a

@[simp]
theorem CuspCentralHomology.overlapPhaseHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    (overlapPhaseHomeomorph C ε hε hε1 hC hR a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  overlapCellMap_coe C ε hε hε1 hC hR a p

def CuspCentralHomology.overlapHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) :
    overlapRegion C ε hε a ≃ₜ ToricSpace.CompactFibreTorus × Radial.CellFrontier × Set.Ioo a 1 :=
  (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm.trans
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr (Radial.annulusHomeomorph a ha))

def CuspCentralHomology.innerRegionHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : innerRegion C ε hε ≃ₕ ToricSpace.CompactFibreTorus :=
  (innerRegionHomeomorph C ε hε hε1 hC hR).symm.toHomotopyEquiv.trans
    (Radial.interiorCellProductHomotopyEquiv ToricSpace.CompactFibreTorus)

def CuspCentralHomology.overlapCircleHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    overlapRegion C ε hε a ≃ₕ ToricSpace.CompactFibreTorus × Circle :=
  (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm.toHomotopyEquiv.trans
    (Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha ha1)

theorem CuspCentralHomology.overlapIntoInner_phase_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (innerRegionHomotopyEquiv C ε hε hε1 hC hR).toFun.comp (overlapIntoInner C ε hε a) =
      (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus)).comp
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun := by
  ext q
  rfl

abbrev CuspCentralHomology.CollarPhaseCell (a : ℝ) :=
  ToricSpace.CompactFibreTorus × Radial.OpenCollar a

def CuspCentralHomology.collarCellInclusion (a : ℝ) (p : CollarPhaseCell a) : FundamentalCell :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), (Radial.mem_baseCell_iff _).mpr p.2.2.2⟩)

theorem CuspCentralHomology.collarCellInclusion_continuous (a : ℝ) :
    Continuous (collarCellInclusion a) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem CuspCentralHomology.collarCellInclusion_injective (a : ℝ) :
    Function.Injective (collarCellInclusion a) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : FundamentalCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : FundamentalCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq

theorem CuspCentralHomology.fundamentalCellMap_mem_outerRegion_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ outerRegion C ε hε a ↔
      a < Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) := by
  change a < centralRadius C ε hε (fundamentalCellMap C ε hε p) ↔ _
  rw [centralRadius_fundamentalCellMap]

def CuspCentralHomology.collarCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) (p : CollarPhaseCell a) : outerRegion C ε hε a :=
  ⟨fundamentalCellMap C ε hε (collarCellInclusion a p),
    (fundamentalCellMap_mem_outerRegion_iff C ε hε a _).mpr p.2.2.1⟩

@[simp]
theorem CuspCentralHomology.collarCellMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (p : CollarPhaseCell a) :
    (collarCellMap C ε hε a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

@[simp]
theorem CuspCentralHomology.centralRadius_collarCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (p : CollarPhaseCell a) :
    centralRadius C ε hε (collarCellMap C ε hε a p) =
      Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) :=
  centralRadius_fundamentalCellMap C ε hε (collarCellInclusion a p)

theorem CuspCentralHomology.collarCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) : Continuous (collarCellMap C ε hε a) :=
  ((fundamentalCellMap_continuous C ε hε).comp (collarCellInclusion_continuous a)).subtype_mk _

theorem CuspCentralHomology.collarCellMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) : Function.Surjective (collarCellMap C ε hε a) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp⟩ := fundamentalCellMap_surjective C ε hε q
  have hg : a < Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) := by
    apply (fundamentalCellMap_mem_outerRegion_iff C ε hε a p).mp
    rwa [hp]
  refine
    ⟨(p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), hg, (Radial.mem_baseCell_iff _).mp p.2.2⟩), ?_⟩
  apply Subtype.ext
  exact hp

def CuspCentralHomology.collarPreimageHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) :
    CollarPhaseCell a ≃ₜ (fundamentalCellMap C ε hε ⁻¹' outerRegion C ε hε a)
    where
  toFun
    p :=
    ⟨collarCellInclusion a p, (fundamentalCellMap_mem_outerRegion_iff C ε hε a _).mpr p.2.2.1⟩
  invFun
    p :=
    (p.1.1,
      ⟨(p.1.2 : (CuspHoneycombTiling.Plane)),
        (fundamentalCellMap_mem_outerRegion_iff C ε hε a p.1).mp p.2,
        (Radial.mem_baseCell_iff _).mp p.1.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (collarCellInclusion_continuous a).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

theorem CuspCentralHomology.collarCellMap_isProperMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (collarCellMap C ε hε a) := by
  have hf :=
    (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).restrictPreimage (outerRegion C ε hε a)
  have hc := hf.comp (collarPreimageHomeomorph C ε hε a).isProperMap
  have he :
    (outerRegion C ε hε a).restrictPreimage (fundamentalCellMap C ε hε) ∘
        collarPreimageHomeomorph C ε hε a =
      collarCellMap C ε hε a := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

theorem CuspCentralHomology.collarCellMap_isClosedMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsClosedMap (collarCellMap C ε hε a) :=
  (collarCellMap_isProperMap C ε hε a hε1 hC hR).isClosedMap

theorem CuspCentralHomology.collarCellMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Topology.IsQuotientMap (collarCellMap C ε hε a) :=
  (collarCellMap_isClosedMap C ε hε a hε1 hC hR).isQuotientMap (collarCellMap_continuous C ε hε a)
    (collarCellMap_surjective C ε hε a)

def CuspCentralHomology.collarCellHomotopy (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    C(unitInterval × CollarPhaseCell a, CollarPhaseCell a)
    where
  toFun p := (p.2.1, Radial.outwardOpenCollarHomotopy a ha ha1 (p.1, p.2.2))
  continuous_toFun :=
    (continuous_fst.comp continuous_snd).prodMk
      ((Radial.outwardOpenCollarHomotopy a ha ha1).continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

@[simp]
theorem CuspCentralHomology.collarCellHomotopy_zero (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (p : CollarPhaseCell a) : collarCellHomotopy a ha ha1 (0, p) = p := by
  apply Prod.ext
  · rfl
  · exact (Radial.outwardOpenCollarHomotopy a ha ha1).apply_zero p.2

theorem CuspCentralHomology.collarCellHomotopy_fixed (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a)
    (hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) :
    collarCellHomotopy a ha ha1 (s, p) = p := by
  apply Prod.ext
  · rfl
  · exact Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p.2 hp

theorem CuspCentralHomology.collarCellHomotopy_compatible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (p q : CollarPhaseCell a) (h : collarCellMap C ε hε a p = collarCellMap C ε hε a q) :
    collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)) =
      collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, q)) := by
  have he :
    fundamentalCellMap C ε hε (collarCellInclusion a p) =
      fundamentalCellMap C ε hε (collarCellInclusion a q) :=
    congrArg Subtype.val h
  rcases
    fundamentalCellMap_eq_or_frontier C ε hε (collarCellInclusion a p) (collarCellInclusion a q)
      he with
    hpq | ⟨hp, hq⟩
  · rw [collarCellInclusion_injective a hpq]
  · rw [collarCellHomotopy_fixed a ha ha1 s p hp, collarCellHomotopy_fixed a ha ha1 s q hq]
    exact h

def CuspCentralHomology.outerRegionBoundaryInclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha1 : a < 1) : C(centralBoundary C ε hε, outerRegion C ε hε a)
    where
  toFun x := ⟨x, centralBoundary_subset_outerRegion C ε hε a ha1 x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def CuspCentralHomology.outerRegionDeformation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (x : outerRegion C ε hε a) : outerRegion C ε hε a :=
  CuspHoneycombHexagon.CommonFibres.descend (collarCellMap C ε hε a)
    (fun p => collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective C ε hε a) x

@[simp]
theorem CuspCentralHomology.outerRegionDeformation_collarCellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a) :
    outerRegionDeformation C ε hε a ha ha1 s (collarCellMap C ε hε a p) =
      collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (collarCellMap C ε hε a)
    (fun p => collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective C ε hε a) (collarCellHomotopy_compatible C ε hε a ha ha1 s) p

theorem CuspCentralHomology.outerRegionDeformation_collarCellMap_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a) :
    (outerRegionDeformation C ε hε a ha ha1 s (collarCellMap C ε hε a p) :
        CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (p.1,
          ((1 - (s : ℝ)) + (s : ℝ) / Radial.cellGauge p.2) •
            (p.2 : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionDeformation_collarCellMap, collarCellMap_coe]
  change
    CuspHoneycomb.honeycombCollapseMap C ε hε
        (p.1,
          (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p.2) : (CuspHoneycombTiling.Plane))) =
      _
  rw [Radial.outwardOpenCollarHomotopy_coe]

@[simp]
theorem CuspCentralHomology.outerRegionDeformation_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (x : outerRegion C ε hε a) :
    outerRegionDeformation C ε hε a ha ha1 0 x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  rw [outerRegionDeformation_collarCellMap, collarCellHomotopy_zero]

theorem CuspCentralHomology.outerRegionDeformation_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (x : outerRegion C ε hε a) :
    centralRadius C ε hε (outerRegionDeformation C ε hε a ha ha1 s x) =
      (1 - (s : ℝ)) * centralRadius C ε hε x + (s : ℝ) := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  rw [outerRegionDeformation_collarCellMap, centralRadius_collarCellMap,
    centralRadius_collarCellMap]
  exact Radial.outwardOpenCollarHomotopy_gauge a ha ha1 s p.2

theorem CuspCentralHomology.outerRegionDeformation_one_mem_boundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : outerRegion C ε hε a) :
    (outerRegionDeformation C ε hε a ha ha1 1 x : CuspRetraction.QuotientCentralFibre C ε) ∈
      centralBoundary C ε hε := by
  change centralRadius C ε hε (outerRegionDeformation C ε hε a ha ha1 1 x) = 1
  rw [outerRegionDeformation_radius]
  simp

theorem CuspCentralHomology.outerRegionDeformation_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (x : outerRegion C ε hε a)
    (hx : (x : CuspRetraction.QuotientCentralFibre C ε) ∈ centralBoundary C ε hε) :
    outerRegionDeformation C ε hε a ha ha1 s x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  have hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
    apply (Radial.mem_frontier_baseCell_iff _).mpr
    change centralRadius C ε hε (collarCellMap C ε hε a p) = 1 at hx
    rwa [centralRadius_collarCellMap] at hx
  rw [outerRegionDeformation_collarCellMap, collarCellHomotopy_fixed a ha ha1 s p hp]

theorem CuspCentralHomology.outerRegionDeformation_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Continuous
      (fun p : unitInterval × outerRegion C ε hε a =>
        outerRegionDeformation C ε hε a ha ha1 p.1 p.2) := by
  apply (collarCellMap_isQuotientMap C ε hε a hε1 hC hR).continuous_lift_prod_right
  have hc := (collarCellMap_continuous C ε hε a).comp (collarCellHomotopy a ha ha1).continuous
  simpa only [outerRegionDeformation_collarCellMap, Function.comp_def, Prod.eta] using hc

def CuspCentralHomology.outerRegionRetraction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : C(outerRegion C ε hε a, centralBoundary C ε hε)
    where
  toFun
    x :=
    ⟨outerRegionDeformation C ε hε a ha ha1 1 x,
      outerRegionDeformation_one_mem_boundary C ε hε a ha ha1 x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((outerRegionDeformation_continuous C ε hε a ha ha1 hε1 hC hR).comp
            (continuous_const.prodMk continuous_id))).subtype_mk
      _

@[simp]
theorem CuspCentralHomology.outerRegionRetraction_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : outerRegion C ε hε a) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR x :
        CuspRetraction.QuotientCentralFibre C ε) =
      outerRegionDeformation C ε hε a ha ha1 1 x :=
  rfl

theorem CuspCentralHomology.outerRegionRetraction_collarCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : CollarPhaseCell a) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR (collarCellMap C ε hε a p) :
        CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (p.1, (Radial.cellGauge p.2)⁻¹ • (p.2 : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionRetraction_coe, outerRegionDeformation_collarCellMap_coe]
  simp

@[simp]
theorem CuspCentralHomology.outerRegionRetraction_comp_inclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR).comp
        (outerRegionBoundaryInclusion C ε hε a ha1) =
      ContinuousMap.id (centralBoundary C ε hε) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    (outerRegionDeformation C ε hε a ha ha1 1 (outerRegionBoundaryInclusion C ε hε a ha1 x) :
        CuspRetraction.QuotientCentralFibre C ε) =
      x
  exact
    congrArg Subtype.val
      (outerRegionDeformation_fixed C ε hε a ha ha1 1
        (outerRegionBoundaryInclusion C ε hε a ha1 x) x.2)

def CuspCentralHomology.outerRegionHomotopyRel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (ContinuousMap.id (outerRegion C ε hε a)).HomotopyRel
      ((outerRegionBoundaryInclusion C ε hε a ha1).comp
        (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR))
      {x : outerRegion C ε hε a |
        (x : CuspRetraction.QuotientCentralFibre C ε) ∈ centralBoundary C ε hε}
    where
  toFun p := outerRegionDeformation C ε hε a ha ha1 p.1 p.2
  continuous_toFun := outerRegionDeformation_continuous C ε hε a ha ha1 hε1 hC hR
  map_zero_left := outerRegionDeformation_zero C ε hε a ha ha1
  map_one_left _ := rfl
  prop' := outerRegionDeformation_fixed C ε hε a ha ha1

def CuspCentralHomology.outerRegionBoundaryHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : outerRegion C ε hε a ≃ₕ centralBoundary C ε hε
    where
  toFun := outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
  invFun := outerRegionBoundaryInclusion C ε hε a ha1
  left_inv := ⟨(outerRegionHomotopyRel C ε hε a ha ha1 hε1 hC hR).toHomotopy.symm⟩
  right_inv := by
    refine ⟨?_⟩
    rw [outerRegionRetraction_comp_inclusion]
    exact ContinuousMap.Homotopy.refl _

@[simp]
theorem CuspCentralHomology.outerRegionBoundaryHomotopyEquiv_apply
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : outerRegion C ε hε a) :
    outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR x =
      outerRegionRetraction C ε hε a ha ha1 hε1 hC hR x :=
  rfl

abbrev CuspCentralHomology.BoundaryPhaseCell :=
  ToricSpace.CompactFibreTorus × Radial.CellFrontier

theorem CuspCentralHomology.honeycombCollapseMap_frontier_mem_boundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : BoundaryPhaseCell) :
    CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) ∈
      centralBoundary C ε hε := by
  rw [centralBoundary_eq_image]
  exact ⟨(p.1, (p.2 : (CuspHoneycombTiling.Plane))), ⟨Set.mem_univ _, p.2.2⟩, rfl⟩

def CuspCentralHomology.boundaryCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(BoundaryPhaseCell, centralBoundary C ε hε)
    where
  toFun
    p :=
    ⟨CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))),
      honeycombCollapseMap_frontier_mem_boundary C ε hε p⟩
  continuous_toFun := by
    have hi :
      Continuous (fun p : BoundaryPhaseCell => (p.1, (p.2 : (CuspHoneycombTiling.Plane)))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact ((CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp hi).subtype_mk _

@[simp]
theorem CuspCentralHomology.boundaryCellMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : BoundaryPhaseCell) :
    (boundaryCellMap C ε hε p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

def CuspCentralHomology.circleBoundaryCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(ToricSpace.CompactFibreTorus × Circle, centralBoundary C ε hε) :=
  (boundaryCellMap C ε hε).comp
    ⟨fun p => (p.1, Radial.frontierCellCircleHomeomorph.symm p.2),
      continuous_fst.prodMk
        (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd)⟩

@[simp]
theorem CuspCentralHomology.circleBoundaryCellMap_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : ToricSpace.CompactFibreTorus × Circle) :
    circleBoundaryCellMap C ε hε p =
      boundaryCellMap C ε hε (p.1, Radial.frontierCellCircleHomeomorph.symm p.2) :=
  rfl

def CuspCentralHomology.overlapIntoOuter (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : C(overlapRegion C ε hε a, outerRegion C ε hε a) :=
  ⟨fun q => ⟨(q : CuspRetraction.QuotientCentralFibre C ε), q.2.1⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem CuspCentralHomology.overlapIntoOuter_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (q : overlapRegion C ε hε a) :
    (overlapIntoOuter C ε hε a q : CuspRetraction.QuotientCentralFibre C ε) =
      (q : CuspRetraction.QuotientCentralFibre C ε) :=
  rfl

def CuspCentralHomology.annulusIntoCollar (a : ℝ) (p : OverlapPhaseCell a) : CollarPhaseCell a :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), p.2.2.1, p.2.2.2.le⟩)

theorem CuspCentralHomology.overlapIntoOuter_phaseHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    overlapIntoOuter C ε hε a (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
      collarCellMap C ε hε a (annulusIntoCollar a p) := by
  apply Subtype.ext
  rw [overlapIntoOuter_coe, overlapPhaseHomeomorph_coe, collarCellMap_coe]
  rfl

theorem CuspCentralHomology.outerRegionRetraction_overlapPhaseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : OverlapPhaseCell a) :
    outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
        (overlapIntoOuter C ε hε a (overlapPhaseHomeomorph C ε hε hε1 hC hR a p)) =
      boundaryCellMap C ε hε (p.1, (Radial.annulusHomeomorph a ha p.2).1) := by
  apply Subtype.ext
  rw [overlapIntoOuter_phaseHomeomorph, outerRegionRetraction_collarCellMap, boundaryCellMap_coe]
  rfl

theorem CuspCentralHomology.overlapCircleHomotopyEquiv_phaseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : OverlapPhaseCell a) :
    overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1
        (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
      (p.1, Radial.annulusCircleHomotopyEquiv a ha ha1 p.2) := by
  change
    Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha ha1
        ((overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
          (overlapPhaseHomeomorph C ε hε hε1 hC hR a p)) =
      _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem CuspCentralHomology.overlapIntoOuter_boundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion C ε hε a) :
    outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR (overlapIntoOuter C ε hε a q) =
      circleBoundaryCellMap C ε hε (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1 q) := by
  obtain ⟨p, rfl⟩ := (overlapPhaseHomeomorph C ε hε hε1 hC hR a).surjective q
  rw [outerRegionBoundaryHomotopyEquiv_apply, outerRegionRetraction_overlapPhaseHomeomorph,
    overlapCircleHomotopyEquiv_phaseHomeomorph, circleBoundaryCellMap_apply]
  congr 1
  apply Prod.ext
  · rfl
  · change
      (Radial.annulusHomeomorph a ha p.2).1 =
        Radial.frontierCellCircleHomeomorph.symm
          (Radial.frontierCellCircleHomeomorph (Radial.annulusHomeomorph a ha p.2).1)
    exact (Radial.frontierCellCircleHomeomorph.symm_apply_apply _).symm

theorem CuspCentralHomology.overlapIntoOuter_boundary_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).toFun.comp
        (overlapIntoOuter C ε hε a) =
      (circleBoundaryCellMap C ε hε).comp
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  exact overlapIntoOuter_boundary C ε hε hε1 hC hR a ha ha1 q

def CuspCentralHomology.phaseOrbitVertex : Radial.CellFrontier :=
  ⟨![(1 / 3 : ℝ), 1 / 3],
    (Radial.mem_frontier_baseCell_iff _).mpr (by norm_num [Radial.cellGauge])⟩

@[simp]
theorem CuspCentralHomology.phaseOrbitVertex_coe :
    (phaseOrbitVertex : (CuspHoneycombTiling.Plane)) = ![(1 / 3 : ℝ), 1 / 3] :=
  rfl

theorem CuspCentralHomology.phaseOrbitVertex_eq_triangleBarycenter :
    (phaseOrbitVertex : (CuspHoneycombTiling.Plane)) =
      CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle 0) := by
  rw [CuspHoneycombTiling.triangleBarycenter_zeroTriangle]
  funext i
  fin_cases i <;> norm_num [phaseOrbitVertex, ToricComponent.hexagonRay]

theorem CuspCentralHomology.honeycombCollapseMap_phaseOrbitVertex
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (φ : ToricSpace.CompactFibreTorus) :
    CuspHoneycomb.honeycombCollapseMap C ε hε
        (φ, (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (1, (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) := by
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε _ _).mpr
  refine ⟨0, by simp, ?_⟩
  rw [phaseOrbitVertex_eq_triangleBarycenter,
    CuspHoneycomb.honeycombHomeomorph_stabilizer_triangleBarycenter]
  trivial

theorem CuspCentralHomology.phaseOrbitAnchor_coe :
    (Radial.frontierCellCircleHomeomorph.symm 1 : (CuspHoneycombTiling.Plane)) =
      ![(1 / 2 : ℝ), 0] := by
  rw [Radial.frontierCellCircleHomeomorph_symm_coe]
  ext i
  fin_cases i <;> norm_num [Radial.cellGauge, Pi.smul_apply, smul_eq_mul]

theorem CuspCentralHomology.phaseOrbitSegment_coordinates (s : unitInterval) :
    (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)) =
      ![(1 / 2 : ℝ) - (s : ℝ) / 6, (s : ℝ) / 3] := by
  ext i
  fin_cases i <;> simp [Pi.add_apply, smul_eq_mul] <;> ring

theorem CuspCentralHomology.phaseOrbitSegment_mem_frontier (s : unitInterval) :
    (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)) ∈
      frontier CuspHoneycombTiling.baseCell := by
  apply (Radial.mem_frontier_baseCell_iff _).mpr
  rw [phaseOrbitSegment_coordinates]
  simp only [Radial.cellGauge, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : 2 * ((1 / 2 : ℝ) - (s : ℝ) / 6) + (s : ℝ) / 3 = 1 := by ring
  rw [h0, abs_one]
  apply max_eq_left
  apply max_le
  · apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2]
  · apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2]

def CuspCentralHomology.phaseOrbitSegment : C(unitInterval, Radial.CellFrontier)
    where
  toFun
    s :=
    ⟨(1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)),
      phaseOrbitSegment_mem_frontier s⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
        (continuous_subtype_val.smul continuous_const)

@[simp]
theorem CuspCentralHomology.phaseOrbitSegment_coe (s : unitInterval) :
    (phaseOrbitSegment s : (CuspHoneycombTiling.Plane)) =
      (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)) :=
  rfl

@[simp]
theorem CuspCentralHomology.phaseOrbitSegment_zero :
    phaseOrbitSegment 0 = Radial.frontierCellCircleHomeomorph.symm 1 := by
  apply Subtype.ext
  rw [phaseOrbitSegment_coe, phaseOrbitAnchor_coe]
  simp

@[simp]
theorem CuspCentralHomology.phaseOrbitSegment_one : phaseOrbitSegment 1 = phaseOrbitVertex := by
  apply Subtype.ext
  rw [phaseOrbitSegment_coe, phaseOrbitVertex_coe]
  simp

theorem CuspCentralHomology.boundaryCellMap_phaseOrbitVertex (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (φ : ToricSpace.CompactFibreTorus) :
    boundaryCellMap C ε hε (φ, phaseOrbitVertex) = boundaryCellMap C ε hε (1, phaseOrbitVertex) :=
  Subtype.ext (honeycombCollapseMap_phaseOrbitVertex C ε hε φ)

def CuspCentralHomology.boundaryPhaseOrbit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(ToricSpace.CompactFibreTorus, centralBoundary C ε hε) :=
  (circleBoundaryCellMap C ε hε).comp ⟨fun φ => (φ, 1), continuous_id.prodMk continuous_const⟩

def CuspCentralHomology.boundaryPhaseOrbitHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (boundaryPhaseOrbit C ε hε).Homotopy
      (ContinuousMap.const ToricSpace.CompactFibreTorus
        (boundaryCellMap C ε hε (1, phaseOrbitVertex)))
    where
  toFun p := boundaryCellMap C ε hε (p.2, phaseOrbitSegment p.1)
  continuous_toFun :=
    (boundaryCellMap C ε hε).continuous.comp
      (continuous_snd.prodMk (phaseOrbitSegment.continuous.comp continuous_fst))
  map_zero_left
    φ := by
    change boundaryCellMap C ε hε (φ, phaseOrbitSegment 0) = circleBoundaryCellMap C ε hε (φ, 1)
    rw [phaseOrbitSegment_zero, circleBoundaryCellMap_apply]
  map_one_left
    φ := by
    change boundaryCellMap C ε hε (φ, phaseOrbitSegment 1) = _
    rw [phaseOrbitSegment_one]
    exact boundaryCellMap_phaseOrbitVertex C ε hε φ

theorem CuspCentralHomology.boundaryPhaseOrbit_nullhomotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : (boundaryPhaseOrbit C ε hε).Nullhomotopic :=
  ⟨boundaryCellMap C ε hε (1, phaseOrbitVertex), ⟨boundaryPhaseOrbitHomotopy C ε hε⟩⟩

def CuspCentralHomology.innerRegionInclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(innerRegion C ε hε, CuspRetraction.QuotientCentralFibre C ε) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def CuspCentralHomology.innerRegionInclusionHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (innerRegionInclusion C ε hε).Homotopy
      (ContinuousMap.const (innerRegion C ε hε)
        (CuspHoneycomb.honeycombCollapseMap C ε hε
          (1, (phaseOrbitVertex : (CuspHoneycombTiling.Plane)))))
    where
  toFun
    p :=
    let x := (innerRegionHomeomorph C ε hε hε1 hC hR).symm p.2
    CuspHoneycomb.honeycombCollapseMap C ε hε
      (x.1,
        (1 - (p.1 : ℝ)) • (x.2 : (CuspHoneycombTiling.Plane)) +
          (p.1 : ℝ) • (phaseOrbitVertex : (CuspHoneycombTiling.Plane)))
  continuous_toFun := by
    have hx :=
      (innerRegionHomeomorph C ε hε hε1 hC hR).symm.continuous.comp
        (continuous_snd : Continuous (Prod.snd : unitInterval × innerRegion C ε hε → _))
    have hs : Continuous (fun p : unitInterval × innerRegion C ε hε => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact
      (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp
        ((continuous_fst.comp hx).prodMk
          (((continuous_const.sub hs).smul
                (continuous_subtype_val.comp (continuous_snd.comp hx))).add
            (hs.smul continuous_const)))
  map_zero_left
    q := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
            (1 - (0 : ℝ)) •
                (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 :
                  (CuspHoneycombTiling.Plane)) +
              (0 : ℝ) • (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) =
        (q : CuspRetraction.QuotientCentralFibre C ε)
    rw [sub_zero, one_smul, zero_smul, add_zero]
    simpa only [Homeomorph.apply_symm_apply] using
      (innerRegionHomeomorph_honeycomb C ε hε hε1 hC hR
          ((innerRegionHomeomorph C ε hε hε1 hC hR).symm q)).symm
  map_one_left
    q := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
            (1 - (1 : ℝ)) •
                (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 :
                  (CuspHoneycombTiling.Plane)) +
              (1 : ℝ) • (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) =
        _
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact honeycombCollapseMap_phaseOrbitVertex C ε hε _

theorem CuspCentralHomology.innerRegionInclusion_nullhomotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : (innerRegionInclusion C ε hε).Nullhomotopic :=
  ⟨CuspHoneycomb.honeycombCollapseMap C ε hε
      (1, (phaseOrbitVertex : (CuspHoneycombTiling.Plane))),
    ⟨innerRegionInclusionHomotopy C ε hε hε1 hC hR⟩⟩

def CuspCentralHomology.boundaryLoop (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(Circle, centralBoundary C ε hε) :=
  (circleBoundaryCellMap C ε hε).comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩

@[simp]
theorem CuspCentralHomology.boundaryLoop_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (z : Circle) : boundaryLoop C ε hε z = circleBoundaryCellMap C ε hε (1, z) :=
  rfl

def CuspCentralHomology.centralBoundaryInclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(centralBoundary C ε hε, CuspRetraction.QuotientCentralFibre C ε) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def CuspCentralHomology.boundaryLoopInCentral (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(Circle, CuspRetraction.QuotientCentralFibre C ε) :=
  (centralBoundaryInclusion C ε hε).comp (boundaryLoop C ε hε)

def CuspCentralHomology.boundaryLoopContraction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (boundaryLoopInCentral C ε hε).Homotopy
      (ContinuousMap.const Circle (CuspHoneycomb.honeycombCollapseMap C ε hε (1, 0)))
    where
  toFun
    p :=
    CuspHoneycomb.honeycombCollapseMap C ε hε
      (1,
        (1 - (p.1 : ℝ)) •
          (Radial.frontierCellCircleHomeomorph.symm p.2 : (CuspHoneycombTiling.Plane)))
  continuous_toFun :=
    (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp
      (continuous_const.prodMk
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp
            (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd))))
  map_zero_left
    z := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (1,
            (1 - (0 : ℝ)) •
              (Radial.frontierCellCircleHomeomorph.symm z : (CuspHoneycombTiling.Plane))) =
        CuspHoneycomb.honeycombCollapseMap C ε hε
          (1, (Radial.frontierCellCircleHomeomorph.symm z : (CuspHoneycombTiling.Plane)))
    simp only [sub_zero, one_smul]
  map_one_left
    z := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (1,
            (1 - (1 : ℝ)) •
              (Radial.frontierCellCircleHomeomorph.symm z : (CuspHoneycombTiling.Plane))) =
        CuspHoneycomb.honeycombCollapseMap C ε hε (1, 0)
    simp only [sub_self, zero_smul]

theorem CuspCentralHomology.boundaryLoopInCentral_nullhomotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : (boundaryLoopInCentral C ε hε).Nullhomotopic :=
  ⟨CuspHoneycomb.honeycombCollapseMap C ε hε (1, 0), ⟨boundaryLoopContraction C ε hε⟩⟩

theorem CuspCentralHomology.centralBoundaryInclusion_comp_boundaryLoop_nullhomotopic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    ((centralBoundaryInclusion C ε hε).comp (boundaryLoop C ε hε)).Nullhomotopic :=
  boundaryLoopInCentral_nullhomotopic C ε hε

theorem CuspCentralHomology.centralBoundary_pathConnectedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : PathConnectedSpace (centralBoundary C ε hε) :=
  (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.surjective.pathConnectedSpace
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.continuous

theorem CuspCentralHomology.overlapRegion_pathConnectedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    PathConnectedSpace (overlapRegion C ε hε a) := by
  let : PathConnectedSpace Radial.CellFrontier :=
    Radial.frontierCellCircleHomeomorph.symm.surjective.pathConnectedSpace
      Radial.frontierCellCircleHomeomorph.symm.continuous
  let : PathConnectedSpace (Set.Ioo a 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo a 1).isPathConnected (Set.nonempty_Ioo.mpr ha1))
  exact
    (overlapHomeomorph C ε hε hε1 hC hR a ha).symm.surjective.pathConnectedSpace
      (overlapHomeomorph C ε hε hε1 hC hR a ha).symm.continuous

theorem CuspCentralHomology.halfCoverLeftHomologyZero_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Injective
      (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
        0) := by
  let := centralBoundary_pathConnectedSpace C ε hε hε1 hC hR
  let := overlapRegion_pathConnectedSpace C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num)
  let e := outerRegionBoundaryHomotopyEquiv C ε hε (1 / 2) (by norm_num) (by norm_num) hε1 hC hR
  let i : C((overlapRegion C ε hε (1 / 2)), (outerRegion C ε hε (1 / 2))) :=
    ContinuousMap.inclusion
      (Set.inter_subset_left :
        (outerRegion C ε hε (1 / 2)) ∩ (innerRegion C ε hε) ⊆ (outerRegion C ε hε (1 / 2)))
  let g : C((overlapRegion C ε hε (1 / 2)), (centralBoundary C ε hε)) := e.toFun.comp i
  intro a b hab
  have hi :
    SingularMayerVietoris.singularHomologyMap i 0 a =
      SingularMayerVietoris.singularHomologyMap i 0 b := by
    have h := congrArg Prod.fst hab
    simp only [SingularMayerVietoris.leftHomologyMap_apply] at h
    change
      SingularMayerVietoris.singularHomologyMap i 0 a =
        SingularMayerVietoris.singularHomologyMap i 0 b at h
    exact h
  have hg :
    SingularMayerVietoris.singularHomologyMap g 0 a =
      SingularMayerVietoris.singularHomologyMap g 0 b := by
    dsimp [g]
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact congrArg (SingularMayerVietoris.singularHomologyMap e.toFun 0) hi
  apply
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (overlapRegion C ε hε (1 / 2))).injective
  have hn :=
    congrArg (PeriodTorusHigherHomology.connectedHomologyZeroEquiv (centralBoundary C ε hε)) hg
  exact
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural g a).symm.trans
      (hn.trans (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural g b))

theorem CuspCentralHomology.halfCoverRightHomologyOne_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective
      (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
        1) := by
  let hU := outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)
  let hV := innerRegion_isOpen C ε hε hε1 hC hR
  let hc := outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)
  intro a
  have hz :
    SingularMayerVietoris.connectingHomomorphism (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
        hU hV hc 0 a =
      0 := by
    apply halfCoverLeftHomologyZero_injective C ε hε hε1 hC hR
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.connectingHomomorphism_comp_left (outerRegion C ε hε (1 / 2))
          (innerRegion C ε hε) hU hV hc 0)
        a
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h
  have hm :
    a ∈
      LinearMap.ker
        (SingularMayerVietoris.connectingHomomorphism (outerRegion C ε hε (1 / 2))
          (innerRegion C ε hε) hU hV hc 0) :=
    hz
  rw [←
    SingularMayerVietoris.exact_at_ambient (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε) hU hV
      hc 0] at hm
  exact hm

theorem CuspCentralHomology.innerRegionInclusion_homology_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (innerRegionInclusion C ε hε) (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_nullhomotopic _
    (innerRegionInclusion_nullhomotopic C ε hε hε1 hC hR) (n + 1) (Nat.succ_ne_zero n)

theorem CuspCentralHomology.centralBoundaryInclusion_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 1) := by
  let e := outerRegionBoundaryHomotopyEquiv C ε hε (1 / 2) (by norm_num) (by norm_num) hε1 hC hR
  let E := PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 1
  have he :
    (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε (1 / 2))).comp e.symm.toFun =
      centralBoundaryInclusion C ε hε := by
    apply ContinuousMap.ext
    intro q
    rfl
  intro a
  obtain ⟨⟨x, y⟩, hxy⟩ := halfCoverRightHomologyOne_surjective C ε hε hε1 hC hR a
  refine ⟨E x, ?_⟩
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε (1 / 2))) 1 (E.symm (E x)) =
      a
  rw [E.symm_apply_apply]
  have hv :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (innerRegion C ε hε)) 1 =
      0 :=
    innerRegionInclusion_homology_eq_zero C ε hε hε1 hC hR 0
  simpa only [SingularMayerVietoris.rightHomologyMap_apply, hv, LinearMap.zero_apply,
    add_zero] using hxy

theorem CuspCentralHomology.centralBoundaryInclusion_homology_one_injective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 1) := by
  let := centralSingularH1_finite C ε hε hC
  let i :=
    (centralBoundaryHomologyOneEquiv C ε hε hε1 hC hR).trans
      (centralSingularH1Equiv C ε hε hC).symm
  exact
    IsNoetherian.injective_of_surjective_of_injective i.toLinearMap
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 1) i.injective
      (centralBoundaryInclusion_homology_one_surjective C ε hε hε1 hC hR)

theorem CuspCentralHomology.boundaryLoop_homology_one_eq_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.singularHomologyMap (boundaryLoop C ε hε) 1 = 0 := by
  have hzero :=
    singularHomologyMap_eq_zero_of_nullhomotopic _
      (centralBoundaryInclusion_comp_boundaryLoop_nullhomotopic C ε hε) 1 (by decide)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at hzero
  apply LinearMap.ext
  intro a
  apply centralBoundaryInclusion_homology_one_injective C ε hε hε1 hC hR
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hzero a

@[simp]
theorem CuspCentralHomology.centralCollapseMap_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : CuspCollapse.PhasePositiveSpace) :
    CuspQuotient.branchCount C ε (CuspCollapse.centralCollapseMap C ε hε p).1 =
      ToricSpace.branchCount (p.2.1 : ToricSpace.Space) := by
  change ToricSpace.branchCount (ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space)) = _
  exact ToricSpace.branchCount_torusAction _ _

@[simp]
theorem CuspCentralHomology.fundamentalCellMap_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    CuspQuotient.branchCount C ε (fundamentalCellMap C ε hε p).1 =
      ToricSpace.branchCount
        ((CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane))).1 :
          ToricSpace.Space) :=
  centralCollapseMap_branchCount C ε hε
    (p.1, CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane)))

theorem CuspCentralHomology.edgeArcPositive_branchCount_ge_two (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    2 ≤ ToricSpace.branchCount ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) := by
  by_cases ht0 : t = 0
  · subst t
    rw [edgeArcPositive_zero_branchCount]
    decide
  by_cases ht1 : t = 1
  · subst t
    rw [edgeArcPositive_one_branchCount]
    decide
  rw [edgeArcPositive_branchCount C₀ k t ht0 ht1]

theorem CuspCentralHomology.mem_centralBoundary_iff_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (q : CuspRetraction.QuotientCentralFibre C ε) :
    q ∈ centralBoundary C ε hε ↔ 2 ≤ CuspQuotient.branchCount C ε q.1 := by
  constructor
  · intro hq
    obtain ⟨k, t, u, rfl⟩ := (mem_centralBoundary_iff_edgeArc C ε hε q).mp hq
    rw [centralCollapseMap_branchCount]
    exact edgeArcPositive_branchCount_ge_two (C 0) k t
  · intro hq
    obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
    apply (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mpr
    by_contra hp
    have hi : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell :=
      (mem_interior_iff_notMem_frontier p.2.2).mpr hp
    have hb :
      ToricSpace.branchCount
          ((CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane))).1 :
            ToricSpace.Space) =
        1 :=
      (CuspHoneycomb.honeycombHomeomorph_branchCount_eq_one_iff (C 0)
            (p.2 : (CuspHoneycombTiling.Plane))).mpr
        ⟨0, by simpa only [CuspHoneycombTiling.cell_zero] using hi⟩
    rw [fundamentalCellMap_branchCount, hb] at hq
    exact (by decide : ¬2 ≤ (1 : ℕ)) hq

def CuspCentralHomology.phaseMultiply (u : ToricSpace.CompactFibreTorus)
    (p : CuspCollapse.PhasePositiveSpace) : CuspCollapse.PhasePositiveSpace :=
  (u * p.1, p.2)

theorem CuspCentralHomology.centralCollapseRelation_phaseMultiply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : ToricSpace.CompactFibreTorus) (p q : CuspCollapse.PhasePositiveSpace)
    (h : CuspCollapse.centralCollapseRelation C₀ p q) :
    CuspCollapse.centralCollapseRelation C₀ (phaseMultiply u p) (phaseMultiply u q) := by
  obtain ⟨v, hv, hu⟩ := h
  refine ⟨v, hv, ?_⟩
  change
    (u * p.1)⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * (u * q.1)) ∈
      MulAction.stabilizer ToricSpace.CompactFibreTorus (p.2.1 : ToricSpace.Space)
  have he :
    (u * p.1)⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * (u * q.1)) =
      p.1⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * q.1) := by
    calc
      _ = p.1⁻¹ * ((u⁻¹ * u) * (CuspCollapse.deckFibrePhase C₀ v * q.1)) := by
        simp only [mul_inv_rev]
        ac_rfl
      _ = p.1⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * q.1) := by rw [inv_mul_cancel, one_mul]
  rw [he]
  exact hu

def CuspCentralHomology.phaseMultiplyModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.CentralCollapseModel C₀ → CuspCollapse.CentralCollapseModel C₀ :=
  Quotient.map' (phaseMultiply u) (centralCollapseRelation_phaseMultiply C₀ u)

def CuspCentralHomology.centralPhaseAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (u : ToricSpace.CompactFibreTorus) (x : CuspRetraction.QuotientCentralFibre C ε) :
    CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralCollapseModelMap C ε hε
    (phaseMultiplyModel (C 0) u ((CuspCollapse.centralCollapseEquiv C ε hε).symm x))

@[simp]
theorem CuspCentralHomology.centralPhaseAction_collapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (p : CuspCollapse.PhasePositiveSpace) :
    centralPhaseAction C ε hε u (CuspCollapse.centralCollapseMap C ε hε p) =
      CuspCollapse.centralCollapseMap C ε hε (u * p.1, p.2) := by
  unfold centralPhaseAction
  rw [CuspCollapse.centralCollapseEquiv_symm_map]
  rfl

@[simp]
theorem CuspCentralHomology.centralPhaseAction_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (x : CuspRetraction.QuotientCentralFibre C ε) :
    CuspQuotient.branchCount C ε (centralPhaseAction C ε hε u x).1 =
      CuspQuotient.branchCount C ε x.1 := by
  obtain ⟨p, rfl⟩ := CuspCollapse.centralCollapseMap_surjective C ε hε x
  rw [centralPhaseAction_collapse, centralCollapseMap_branchCount, centralCollapseMap_branchCount]

theorem CuspCentralHomology.centralPhaseAction_mem_boundary_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (x : CuspRetraction.QuotientCentralFibre C ε) :
    centralPhaseAction C ε hε u x ∈ centralBoundary C ε hε ↔ x ∈ centralBoundary C ε hε := by
  rw [mem_centralBoundary_iff_branchCount, centralPhaseAction_branchCount,
    mem_centralBoundary_iff_branchCount]

def CuspCentralHomology.boundaryPhaseAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (x : centralBoundary C ε hε) :
    centralBoundary C ε hε :=
  ⟨centralPhaseAction C ε hε u x.1, (centralPhaseAction_mem_boundary_iff C ε hε u x.1).mpr x.2⟩

theorem CuspCentralHomology.centralPhaseAction_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × CuspRetraction.QuotientCentralFibre C ε =>
        centralPhaseAction C ε hε p.1 p.2) := by
  apply (CuspCollapse.centralCollapseMap_isQuotientMap C ε hε hC).continuous_lift_prod_right
  have hm :
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × CuspCollapse.PhasePositiveSpace =>
        (p.1 * p.2.1, p.2.2)) :=
    (continuous_fst.mul continuous_snd.fst).prodMk continuous_snd.snd
  exact
    ((CuspCollapse.centralCollapseMap_continuous C ε hε).comp hm).congr
      (fun p => (centralPhaseAction_collapse C ε hε p.1 p.2).symm)

theorem CuspCentralHomology.boundaryPhaseAction_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × centralBoundary C ε hε =>
        boundaryPhaseAction C ε hε p.1 p.2) :=
  ((centralPhaseAction_continuous C ε hε hC).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
    _

def CuspCentralHomology.boundaryPhaseActionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    C(ToricSpace.CompactFibreTorus × centralBoundary C ε hε, centralBoundary C ε hε) :=
  ⟨fun p => boundaryPhaseAction C ε hε p.1 p.2, boundaryPhaseAction_continuous C ε hε hC⟩

@[simp]
theorem CuspCentralHomology.centralPhaseAction_honeycombCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (p : CuspHoneycomb.PhasePlane) :
    centralPhaseAction C ε hε u (CuspHoneycomb.honeycombCollapseMap C ε hε p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (u * p.1, p.2) :=
  centralPhaseAction_collapse C ε hε u (p.1, CuspHoneycomb.honeycombHomeomorph (C 0) p.2)

@[simp]
theorem CuspCentralHomology.boundaryPhaseAction_boundaryCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (p : BoundaryPhaseCell) :
    boundaryPhaseAction C ε hε u (boundaryCellMap C ε hε p) =
      boundaryCellMap C ε hε (u * p.1, p.2) := by
  apply Subtype.ext
  exact centralPhaseAction_honeycombCollapseMap C ε hε u (p.1, p.2)

@[simp]
theorem CuspCentralHomology.boundaryPhaseAction_circleBoundaryCellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (p : ToricSpace.CompactFibreTorus × Circle) :
    boundaryPhaseAction C ε hε u (circleBoundaryCellMap C ε hε p) =
      circleBoundaryCellMap C ε hε (u * p.1, p.2) := by
  rw [circleBoundaryCellMap_apply, boundaryPhaseAction_boundaryCellMap,
    circleBoundaryCellMap_apply]

theorem CuspCentralHomology.circleBoundaryCellMap_phaseAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (z : Circle) :
    circleBoundaryCellMap C ε hε (u, z) = boundaryPhaseAction C ε hε u (boundaryLoop C ε hε z) := by
  rw [boundaryLoop_apply, boundaryPhaseAction_circleBoundaryCellMap, mul_one]

theorem CuspCentralHomology.circleBoundaryCellMap_eq_phaseAction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    circleBoundaryCellMap C ε hε =
      (boundaryPhaseActionMap C ε hε hC).comp
        ((ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap (boundaryLoop C ε hε)) := by
  apply ContinuousMap.ext
  intro p
  exact circleBoundaryCellMap_phaseAction C ε hε p.1 p.2

def PeriodDomain.periodVector (p : PeriodDomain) : Lattice →+ ComplexPlane₂
    where
  toFun c := p.val.matrix *ᵥ (fun i => (c i : ℂ))
  map_zero' := by
    simp only [Pi.zero_apply, Int.cast_zero]
    exact Matrix.mulVec_zero _
  map_add' c
    d := by
    simp only [Pi.add_apply, Int.cast_add]
    exact Matrix.mulVec_add _ _ _

@[simp]
theorem PeriodDomain.periodVector_apply (p : PeriodDomain) (c : Lattice) :
    p.periodVector c = p.val.matrix *ᵥ (fun i => (c i : ℂ)) :=
  rfl

theorem PeriodDomain.periodVector_eq_sum (p : PeriodDomain) (c : Lattice) :
    p.periodVector c = ∑ i, c i • p.basis i := by
  ext j
  simp [periodVector, Matrix.mulVec, dotProduct, p.basis_apply, zsmul_eq_mul, mul_comm]

theorem PeriodDomain.periodVector_injective (p : PeriodDomain) :
    Function.Injective p.periodVector := by
  intro c d h
  have hi : LinearIndependent ℤ p.basis := p.basis.linearIndependent.restrict_scalars' ℤ
  apply funext
  apply (Fintype.linearIndependent_iffₛ.mp hi) c d
  rw [← p.periodVector_eq_sum, ← p.periodVector_eq_sum]
  exact h

theorem PeriodDomain.mem_lattice_iff (p : PeriodDomain) (z : ComplexPlane₂) :
    z ∈ p.lattice ↔ ∃ c : Lattice, p.periodVector c = z := by
  rw [p.lattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (p.periodVector_eq_sum c).trans hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (p.periodVector_eq_sum c).symm.trans hc⟩

theorem PeriodDomain.periodVector_mem_lattice (p : PeriodDomain) (c : Lattice) :
    p.periodVector c ∈ p.lattice :=
  (p.mem_lattice_iff _).mpr ⟨c, rfl⟩

def PeriodDomain.periodLatticeMap (p : PeriodDomain) : Lattice →+ p.lattice :=
  p.periodVector.codRestrict p.lattice.toAddSubgroup p.periodVector_mem_lattice

theorem PeriodDomain.periodLatticeMap_bijective (p : PeriodDomain) :
    Function.Bijective p.periodLatticeMap := by
  constructor
  · intro c d h
    exact p.periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨c, hc⟩ := (p.mem_lattice_iff z).mp z.property
    exact ⟨c, Subtype.ext hc⟩

def PeriodDomain.periodLatticeEquiv (p : PeriodDomain) : Lattice ≃+ p.lattice :=
  AddEquiv.ofBijective p.periodLatticeMap p.periodLatticeMap_bijective

def PeriodDomain.latticeEquiv (p : PeriodDomain) : p.lattice ≃+ Lattice :=
  p.periodLatticeEquiv.symm

theorem PeriodDomain.periodVector_latticeEquiv (p : PeriodDomain) (z : p.lattice) :
    p.periodVector (p.latticeEquiv z) = z :=
  congrArg Subtype.val (p.periodLatticeEquiv.apply_symm_apply z)

theorem PeriodDomain.quotientCovering (p : PeriodDomain) :
    IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
  apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (p.lattice : Set ComplexPlane₂)
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact DiscreteTopology.isDiscrete

def PeriodDomain.zeroLift (p : PeriodDomain) : p.lattice.mkQ ⁻¹' ({0} : Set p.Torus) :=
  ⟨0, by simp⟩

def PeriodDomain.fundamentalGroupEquiv (p : PeriodDomain) :
    FundamentalGroup p.Torus 0 ≃* Multiplicative Lattice :=
  ((p.quotientCovering.fundamentalGroupEquiv p.zeroLift).trans MulOpposite.opMulEquiv.symm).trans
    p.latticeEquiv.toMultiplicative

theorem PeriodDomain.fundamentalGroupEquiv_monodromy (p : PeriodDomain)
    (g : FundamentalGroup p.Torus 0) :
    p.periodVector (p.fundamentalGroupEquiv g).toAdd =
      (p.quotientCovering.isCoveringMap.monodromy g p.zeroLift : ComplexPlane₂) := by
  have h := p.quotientCovering.unop_fundamentalGroupToMulOpposite_smul (e := p.zeroLift) (γ := g)
  change
    p.periodVector
        (p.latticeEquiv
          (p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift g).unop.toAdd) =
      _
  rw [p.periodVector_latticeEquiv]
  change
    ((p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift g).unop.toAdd : ComplexPlane₂) +
        0 =
      _ at h
  simpa only [add_zero] using h

@[simp]
theorem PeriodDomain.mkQ_periodVector (p : PeriodDomain) (c : Lattice) :
    p.lattice.mkQ (p.periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr (p.periodVector_mem_lattice c)

def PeriodDomain.periodLoop (p : PeriodDomain) (c : Lattice) : Path (0 : p.Torus) 0 :=
  ((Path.segment (0 : ComplexPlane₂) (p.periodVector c)).map p.lattice.continuous_mkQ).cast
    (map_zero p.lattice.mkQ).symm (p.mkQ_periodVector c).symm

theorem PeriodDomain.periodLoop_apply (p : PeriodDomain) (c : Lattice) (t : unitInterval) :
    p.periodLoop c t = p.lattice.mkQ ((t : ℝ) • p.periodVector c) := by
  simp only [periodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply, Path.segment_apply,
    AffineMap.lineMap_apply_module, smul_zero, zero_add]

theorem PeriodDomain.periodLoop_monodromy (p : PeriodDomain) (c : Lattice) :
    p.quotientCovering.isCoveringMap.monodromy (FirstHurewicz.loopQuotient (p.periodLoop c))
        p.zeroLift =
      ⟨p.periodVector c, p.mkQ_periodVector c⟩ := by
  apply
    p.quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (Path.segment (0 : ComplexPlane₂) (p.periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

@[simp]
theorem PeriodDomain.fundamentalGroupEquiv_periodLoop (p : PeriodDomain) (c : Lattice) :
    p.fundamentalGroupEquiv (FirstHurewicz.loopQuotient (p.periodLoop c)) =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply p.periodVector_injective
  rw [p.fundamentalGroupEquiv_monodromy, p.periodLoop_monodromy]
  rfl

def PeriodDomain.singularH1Equiv (p : PeriodDomain) :
    FirstHurewicz.SingularH1 p.Torus ≃ₗ[ℤ] Lattice :=
  FirstHurewicz.singularH1EquivOfPi1 (0 : p.Torus) p.fundamentalGroupEquiv

@[simp]
theorem PeriodDomain.singularH1Equiv_loopHomologyClass (p : PeriodDomain)
    (q : Path (0 : p.Torus) 0) :
    p.singularH1Equiv (FirstHurewicz.loopHomologyClass q) =
      (p.fundamentalGroupEquiv (FirstHurewicz.loopQuotient q)).toAdd :=
  FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass (0 : p.Torus) p.fundamentalGroupEquiv q

@[simp]
theorem PeriodDomain.singularH1Equiv_periodLoop (p : PeriodDomain) (c : Lattice) :
    p.singularH1Equiv (FirstHurewicz.loopHomologyClass (p.periodLoop c)) = c := by
  rw [p.singularH1Equiv_loopHomologyClass, p.fundamentalGroupEquiv_periodLoop]
  rfl

@[simp]
theorem PeriodDomain.singularH1Equiv_symm_apply (p : PeriodDomain) (c : Lattice) :
    p.singularH1Equiv.symm c = FirstHurewicz.loopHomologyClass (p.periodLoop c) := by
  apply p.singularH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, p.singularH1Equiv_periodLoop]

abbrev PeriodTorusHigherHomology.ProductTorus (n : ℕ) :=
  Fin n → AddCircle (1 : ℝ)

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

def PeriodTorusHigherHomology.productTorusSuccHomeomorph (n : ℕ) :
    ProductTorus (n + 1) ≃ₜ AddCircle (1 : ℝ) × ProductTorus n
    where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := Fin.cons_self_tail x
  right_inv x := by simp
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

@[simp]
theorem PeriodTorusHigherHomology.productTorusSuccHomeomorph_apply (n : ℕ)
    (x : ProductTorus (n + 1)) : productTorusSuccHomeomorph n x = (x 0, fun i => x i.succ) :=
  rfl

def PeriodTorusHigherHomology.productTorusZeroHomeomorph : ProductTorus 0 ≃ₜ PUnit
    where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

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

theorem PeriodTorusHigherHomology.standardLattice_le_coordinateProjection_ker :
    standardLattice ≤ LinearMap.ker (coordinateProjection 4).toIntLinearMap := by
  intro x hx
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact (coordinateProjection_eq_zero_iff 4 _).mpr ⟨v, rfl⟩

def PeriodTorusHigherHomology.flatTorusCircleMap : RealTorus₄ →ₗ[ℤ] ProductTorus 4 :=
  standardLattice.liftQ (coordinateProjection 4).toIntLinearMap
    standardLattice_le_coordinateProjection_ker

theorem PeriodTorusHigherHomology.flatTorusCircleMap_continuous : Continuous flatTorusCircleMap :=
  by
  apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
  exact coordinateProjection_continuous 4

theorem PeriodTorusHigherHomology.flatTorusCircleMap_injective :
    Function.Injective flatTorusCircleMap := by
  intro a b hab
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective a
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective b
  have hz : coordinateProjection 4 (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hab
  obtain ⟨v, hv⟩ := (coordinateProjection_eq_zero_iff 4 (x - y)).mp hz
  apply (Elliptic.flatTorus_mkQ_eq_iff x y).mpr
  exact ⟨v, hv⟩

theorem PeriodTorusHigherHomology.flatTorusCircleMap_surjective :
    Function.Surjective flatTorusCircleMap := by
  intro t
  obtain ⟨x, hx⟩ := coordinateProjection_surjective 4 t
  exact ⟨standardLattice.mkQ x, hx⟩

def PeriodTorusHigherHomology.flatTorusCircleHomeomorph : RealTorus₄ ≃ₜ ProductTorus 4 :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective flatTorusCircleMap
      ⟨flatTorusCircleMap_injective, flatTorusCircleMap_surjective⟩)
    flatTorusCircleMap_continuous flatTorusCircleMap_continuous.isClosedMap

@[simp]
theorem PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ (x : RealPlane₄) :
    flatTorusCircleHomeomorph (standardLattice.mkQ x) = coordinateProjection 4 x :=
  rfl

def PeriodTorusHigherHomology.periodTorusCircleHomeomorph (p : PeriodDomain) :
    p.Torus ≃ₜ ProductTorus 4 :=
  (Elliptic.flatTorusPeriodHomeomorph p).symm.trans flatTorusCircleHomeomorph

@[simp]
theorem PeriodTorusHigherHomology.periodTorusCircleHomeomorph_flatProjection (p : PeriodDomain)
    (x : Elliptic.RealCoordinates) :
    periodTorusCircleHomeomorph p (Elliptic.flatProjection p x) = coordinateProjection 4 x := by
  rw [periodTorusCircleHomeomorph, Homeomorph.trans_apply,
    Elliptic.flatTorusPeriodHomeomorph_symm_flatProjection, flatTorusCircleHomeomorph_mkQ]

@[simp]
theorem PeriodTorusHigherHomology.periodTorusCircleHomeomorph_zero (p : PeriodDomain) :
    periodTorusCircleHomeomorph p 0 = 0 := by
  have h := periodTorusCircleHomeomorph_flatProjection p 0
  simpa only [Elliptic.flatProjection, map_zero] using h

theorem PeriodTorusHigherHomology.periodTorusCircleHomeomorph_periodLoop_apply (p : PeriodDomain)
    (v : Lattice) (t : unitInterval) :
    periodTorusCircleHomeomorph p (p.periodLoop v t) = coordinatePeriodLoop 4 v t := by
  rw [PeriodDomain.periodLoop_apply]
  have hv : (t : ℝ) • p.periodVector v = Elliptic.periodEquiv p ((t : ℝ) • Elliptic.realCast v) :=
    by rw [map_smul, Elliptic.periodEquiv_realCast, p.periodVector_eq_sum]
  rw [hv]
  change
    periodTorusCircleHomeomorph p (Elliptic.flatProjection p ((t : ℝ) • Elliptic.realCast v)) = _
  rw [periodTorusCircleHomeomorph_flatProjection]
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

theorem PeriodTorusHigherHomology.periodTorusCircleHomeomorph_periodLoop (p : PeriodDomain)
    (v : Lattice) :
    (p.periodLoop v).map (periodTorusCircleHomeomorph p).continuous =
      (coordinatePeriodLoop 4 v).cast (periodTorusCircleHomeomorph_zero p)
        (periodTorusCircleHomeomorph_zero p) := by
  apply Path.ext
  funext t
  exact periodTorusCircleHomeomorph_periodLoop_apply p v t

def CuspCentralHomology.circleCoordinateHomeomorph : Circle ≃ₜ AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

@[simp]
theorem CuspCentralHomology.circleCoordinateHomeomorph_symm_apply (x : AddCircle (1 : ℝ)) :
    circleCoordinateHomeomorph.symm x = AddCircle.toCircle x :=
  AddCircle.homeomorphCircle_apply one_ne_zero x

theorem CuspCentralHomology.circleCoordinateHomeomorph_mul (u v : Circle) :
    circleCoordinateHomeomorph (u * v) =
      circleCoordinateHomeomorph u + circleCoordinateHomeomorph v := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_add,
    ← circleCoordinateHomeomorph_symm_apply, ← circleCoordinateHomeomorph_symm_apply,
    Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

theorem CuspCentralHomology.circleCoordinateHomeomorph_zpow (u : Circle) (n : ℤ) :
    circleCoordinateHomeomorph (u ^ n) = n • circleCoordinateHomeomorph u := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply,
    AddCircle.toCircle_zsmul, ← circleCoordinateHomeomorph_symm_apply,
    Homeomorph.symm_apply_apply]

theorem CuspCentralHomology.circleCoordinateHomeomorph_exp (x : ℝ) :
    circleCoordinateHomeomorph (Circle.exp (2 * Real.pi * x)) = (x : AddCircle (1 : ℝ)) := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply,
    AddCircle.toCircle_apply_mk, div_one]

def CuspCentralHomology.compactFibreTorusHomeomorph :
    ToricSpace.CompactFibreTorus ≃ₜ PeriodTorusHigherHomology.ProductTorus 2 :=
  Homeomorph.piCongrRight (fun _ : Fin 2 => circleCoordinateHomeomorph)

theorem CuspCentralHomology.compactFibreTorusHomeomorph_mul (u v : ToricSpace.CompactFibreTorus) :
    compactFibreTorusHomeomorph (u * v) =
      compactFibreTorusHomeomorph u + compactFibreTorusHomeomorph v := by
  funext i
  exact circleCoordinateHomeomorph_mul (u i) (v i)

theorem CuspCentralHomology.compactFibreTorusHomeomorph_exp (x : Fin 2 → ℝ) :
    compactFibreTorusHomeomorph (fun i => Circle.exp (2 * Real.pi * x i)) =
      PeriodTorusHigherHomology.coordinateProjection 2 x := by
  funext i
  exact circleCoordinateHomeomorph_exp (x i)

def CuspCentralHomology.productTorusLastHomeomorph (n : ℕ) :
    PeriodTorusHigherHomology.ProductTorus (n + 1) ≃ₜ
      PeriodTorusHigherHomology.ProductTorus n × AddCircle (1 : ℝ)
    where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv p := by simp only [Fin.snoc_castSucc, Fin.snoc_last]
  continuous_toFun :=
    (continuous_pi (fun i => continuous_apply i.castSucc)).prodMk (continuous_apply (Fin.last n))
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (continuous_snd :
          Continuous
            (fun p : PeriodTorusHigherHomology.ProductTorus n × AddCircle (1 : ℝ) => p.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        ((continuous_apply j).comp continuous_fst :
          Continuous
            (fun p : PeriodTorusHigherHomology.ProductTorus n × AddCircle (1 : ℝ) => p.1 j))

def CuspCentralHomology.fibreTorusCircleHomeomorph :
    (ToricSpace.CompactFibreTorus × Circle) ≃ₜ PeriodTorusHigherHomology.ProductTorus 3 :=
  (compactFibreTorusHomeomorph.prodCongr circleCoordinateHomeomorph).trans
    (productTorusLastHomeomorph 2).symm

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

def PeriodTorusHigherHomology.CirclePaths.quarterIntersection :
    ↥(PeriodTorusHigherHomology.CircleTopology.arcU ∩
        PeriodTorusHigherHomology.CircleTopology.arcV) :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.symm
    (Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩)

def PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection :
    ↥(PeriodTorusHigherHomology.CircleTopology.arcU ∩
        PeriodTorusHigherHomology.CircleTopology.arcV) :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.symm
    (Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩)

def PeriodTorusHigherHomology.CirclePaths.quarterPoint :
    (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  quarterIntersection.val

def PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint :
    (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  threeQuarterIntersection.val

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterPoint_coe :
    quarterPoint = ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersection_component :
    PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph quarterIntersection =
      Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩ :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.apply_symm_apply _

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection_component :
    PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph threeQuarterIntersection =
      Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩ :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.apply_symm_apply _

def PeriodTorusHigherHomology.CirclePaths.quarterU :
    PeriodTorusHigherHomology.CircleTopology.arcU :=
  ⟨quarterPoint, quarterIntersection.property.1⟩

def PeriodTorusHigherHomology.CirclePaths.quarterV :
    PeriodTorusHigherHomology.CircleTopology.arcV :=
  ⟨quarterPoint, quarterIntersection.property.2⟩

def PeriodTorusHigherHomology.CirclePaths.threeQuarterU :
    PeriodTorusHigherHomology.CircleTopology.arcU :=
  ⟨threeQuarterPoint, threeQuarterIntersection.property.1⟩

def PeriodTorusHigherHomology.CirclePaths.threeQuarterV :
    PeriodTorusHigherHomology.CircleTopology.arcV :=
  ⟨threeQuarterPoint, threeQuarterIntersection.property.2⟩

def PeriodTorusHigherHomology.CirclePaths.uPath : Path quarterU threeQuarterU
    where
  toFun
    t :=
    PeriodTorusHigherHomology.CircleTopology.arcUHomeomorph.symm
      ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by
        have ht := t.property
        constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun :=
    PeriodTorusHigherHomology.CircleTopology.arcUHomeomorph.symm.continuous.comp
      ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
        (fun t => by
          change (1 / 4 : ℝ) + (t : ℝ) / 2 ∈ Set.Ioo (0 : ℝ) 1
          constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change
      (((1 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    norm_num
  target' := by
    apply Subtype.ext
    change
      (((1 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((3 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    norm_num

def PeriodTorusHigherHomology.CirclePaths.vPath : Path threeQuarterV quarterV
    where
  toFun
    t :=
    PeriodTorusHigherHomology.CircleTopology.arcVHomeomorph.symm
      ⟨(3 / 4 : ℝ) + (t : ℝ) / 2, by
        have ht := t.property
        constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun :=
    PeriodTorusHigherHomology.CircleTopology.arcVHomeomorph.symm.continuous.comp
      ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
        (fun t => by
          change (3 / 4 : ℝ) + (t : ℝ) / 2 ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2)
          constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change
      (((3 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((3 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    norm_num
  target' := by
    apply Subtype.ext
    change
      (((3 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    convert AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ) using 1
    norm_num

def PeriodTorusHigherHomology.CirclePaths.uCirclePath : Path quarterPoint threeQuarterPoint :=
  uPath.map continuous_subtype_val

def PeriodTorusHigherHomology.CirclePaths.vCirclePath : Path threeQuarterPoint quarterPoint :=
  vPath.map continuous_subtype_val

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.uCirclePath_apply (t : unitInterval) :
    uCirclePath t =
      (((1 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.vCirclePath_apply (t : unitInterval) :
    vCirclePath t =
      (((3 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

def PeriodTorusHigherHomology.CirclePaths.quarterLoop : Path quarterPoint quarterPoint
    where
  toFun t := (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  continuous_toFun :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.add continuous_subtype_val)
  source' := by
    change
      (((1 / 4 : ℝ) + (0 : unitInterval) : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        _;
    simp
  target' := AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ)

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_apply (t : unitInterval) :
    quarterLoop t =
      (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.uCirclePath_trans_vCirclePath :
    uCirclePath.trans vCirclePath = quarterLoop := by
  apply Path.ext
  funext t
  rw [Path.trans_apply]
  split_ifs <;> simp only [uCirclePath_apply, vCirclePath_apply, quarterLoop_apply]
  · congr 1
    ring
  · congr 1
    ring

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

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterTranslation_zero :
    circleTranslation (1 / 4) (0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      quarterPoint := by simp only [circleTranslation_apply, add_zero, quarterPoint_coe]

theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_eq_translation :
    quarterLoop =
      (positiveLoop.map (circleTranslation (1 / 4)).continuous).cast quarterTranslation_zero.symm
        quarterTranslation_zero.symm := by
  apply Path.ext
  funext t
  change
    (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) +
        ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  exact AddCircle.coe_add (1 : ℝ) (1 / 4 : ℝ) (t : ℝ)

theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_homologyClass :
    FirstHurewicz.loopHomologyClass quarterLoop = FirstHurewicz.loopHomologyClass positiveLoop := by
  have hc :
    FirstHurewicz.loopHomologyClass quarterLoop =
      FirstHurewicz.loopHomologyClass (positiveLoop.map (circleTranslation (1 / 4)).continuous) :=
    by
    apply
      FirstHurewicz.homologyToChainClass_injective
        (PeriodTorusHigherHomology.CircleTopology.Circle)
    rw [FirstHurewicz.homologyToChainClass_loopHomologyClass,
      FirstHurewicz.homologyToChainClass_loopHomologyClass, quarterLoop_eq_translation,
      FirstHurewicz.pathClass_cast]
  exact hc.trans (loopHomologyClass_map_circleTranslation (1 / 4) positiveLoop)

theorem PeriodTorusHigherHomology.CirclePaths.boundaryOne_arcSum :
    FirstHurewicz.boundaryOne (PeriodTorusHigherHomology.CircleTopology.Circle)
        (FirstHurewicz.pathChain uCirclePath + FirstHurewicz.pathChain vCirclePath) =
      0 := by
  rw [map_add, FirstHurewicz.boundaryOne_pathChain, FirstHurewicz.boundaryOne_pathChain]
  abel

def PeriodTorusHigherHomology.CirclePaths.arcSumCycle :
    FirstHurewicz.Cycles1 (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  FirstHurewicz.mkCycle1 (PeriodTorusHigherHomology.CircleTopology.Circle)
    (FirstHurewicz.pathChain uCirclePath + FirstHurewicz.pathChain vCirclePath) boundaryOne_arcSum

theorem PeriodTorusHigherHomology.CirclePaths.arcSumCycle_class :
    FirstHurewicz.cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) arcSumCycle =
      FirstHurewicz.loopHomologyClass quarterLoop := by
  apply
    FirstHurewicz.homologyToChainClass_injective (PeriodTorusHigherHomology.CircleTopology.Circle)
  rw [FirstHurewicz.homologyToChainClass_cycleClass,
    FirstHurewicz.homologyToChainClass_loopHomologyClass]
  change
    FirstHurewicz.chainClass (PeriodTorusHigherHomology.CircleTopology.Circle)
        (FirstHurewicz.pathChain uCirclePath + FirstHurewicz.pathChain vCirclePath) =
      _
  rw [map_add, ← uCirclePath_trans_vCirclePath, FirstHurewicz.pathClass_trans]
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.arcSumCycle_positiveLoop_class :
    FirstHurewicz.cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) arcSumCycle =
      FirstHurewicz.loopHomologyClass positiveLoop :=
  arcSumCycle_class.trans quarterLoop_homologyClass

def PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection (X : Type*)
    [TopologicalSpace X] :
    C(X,
      ↥(PeriodTorusHigherHomology.CircleTopology.productU X ∩
          PeriodTorusHigherHomology.CircleTopology.productV X)) :=
  ⟨fun x => ⟨(quarterPoint, x), quarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

def PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection (X : Type*)
    [TopologicalSpace X] :
    C(X,
      ↥(PeriodTorusHigherHomology.CircleTopology.productU X ∩
          PeriodTorusHigherHomology.CircleTopology.productV X)) :=
  ⟨fun x => ⟨(threeQuarterPoint, x), threeQuarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_component (X : Type*)
    [TopologicalSpace X] (x : X) :
    PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X
        (quarterIntersectionSection X x) =
      Sum.inl x := by
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib
          (PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph quarterIntersection,
            x)) =
      _
  rw [quarterIntersection_component]
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_comp (X : Type*)
    [TopologicalSpace X] :
    (PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X).toFun.comp
        (quarterIntersectionSection X) =
      ⟨Sum.inl, continuous_inl⟩ := by
  apply ContinuousMap.ext
  intro x
  exact quarterIntersectionSection_component X x

@[simp]
theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_component
    (X : Type*) [TopologicalSpace X] (x : X) :
    PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X
        (threeQuarterIntersectionSection X x) =
      Sum.inr x := by
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib
          (PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph
              threeQuarterIntersection,
            x)) =
      _
  rw [threeQuarterIntersection_component]
  rfl

theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_comp (X : Type*)
    [TopologicalSpace X] :
    (PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X).toFun.comp
        (threeQuarterIntersectionSection X) =
      ⟨Sum.inr, continuous_inr⟩ := by
  apply ContinuousMap.ext
  intro x
  exact threeQuarterIntersectionSection_component X x

def PeriodTorusHigherHomology.positiveCircleCross (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1) :=
  crossProductHomology (PeriodTorusHigherHomology.CircleTopology.Circle) X n
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop)

theorem PeriodTorusHigherHomology.positiveCircleCross_arcSum_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        (n + 1)
        (crossProductCycles (PeriodTorusHigherHomology.CircleTopology.Circle) X n
          CirclePaths.arcSumCycle b) := by
  have h :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (PeriodTorusHigherHomology.CircleTopology.Circle)) 1
        CirclePaths.arcSumCycle =
      FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop :=
    CirclePaths.arcSumCycle_positiveLoop_class
  change
    crossProductHomology (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) =
      _
  rw [← h]
  exact
    crossProductHomology_cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) X n
      CirclePaths.arcSumCycle b

theorem PeriodTorusHigherHomology.quarterIntersectionHomology_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.singularHomologyMap (CirclePaths.quarterIntersectionSection X) n
          a) =
      (a, 0) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CirclePaths.quarterIntersectionSection_comp]
  exact sumHomologyEquiv_inl X X n a

theorem PeriodTorusHigherHomology.threeQuarterIntersectionHomology_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.singularHomologyMap (CirclePaths.threeQuarterIntersectionSection X)
          n a) =
      (0, a) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CirclePaths.threeQuarterIntersectionSection_comp]
  exact sumHomologyEquiv_inr X X n a

def PeriodTorusHigherHomology.intersectionDifferenceCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (FirstHurewicz.singularComplex
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)))
      n :=
  SingularMayerVietoris.ModuleHomology.mapCycles
      (FirstHurewicz.singularChainMap (CirclePaths.threeQuarterIntersectionSection X)) n b -
    SingularMayerVietoris.ModuleHomology.mapCycles
      (FirstHurewicz.singularChainMap (CirclePaths.quarterIntersectionSection X)) n b

@[simp]
theorem PeriodTorusHigherHomology.intersectionDifferenceCycle_val (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (intersectionDifferenceCycle X n b).1 =
      FirstHurewicz.inducedChain (CirclePaths.threeQuarterIntersectionSection X) n b.1 -
        FirstHurewicz.inducedChain (CirclePaths.quarterIntersectionSection X) n b.1 := by
  change
    (SingularMayerVietoris.ModuleHomology.mapCycles
            (FirstHurewicz.singularChainMap (CirclePaths.threeQuarterIntersectionSection X)) n
            b).1 -
        (SingularMayerVietoris.ModuleHomology.mapCycles
            (FirstHurewicz.singularChainMap (CirclePaths.quarterIntersectionSection X)) n b).1 =
      _
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val,
    SingularMayerVietoris.ModuleHomology.mapCycles_val]

theorem PeriodTorusHigherHomology.intersectionDifferenceCycle_class_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex
            (CircleTopology.productU X ∩ CircleTopology.productV X :
              Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)))
          n (intersectionDifferenceCycle X n b)) =
      (-SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b,
        SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) := by
  rw [intersectionDifferenceCycle, map_sub, map_sub, ←
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, ←
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  change
    productIntersectionHomologyEquiv X n
          (SingularMayerVietoris.singularHomologyMap
            (CirclePaths.threeQuarterIntersectionSection X) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b)) -
        productIntersectionHomologyEquiv X n
          (SingularMayerVietoris.singularHomologyMap (CirclePaths.quarterIntersectionSection X) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b)) =
      _
  rw [threeQuarterIntersectionHomology_coordinates, quarterIntersectionHomology_coordinates]
  simp only [Prod.mk_sub_mk, zero_sub, sub_zero]

theorem PeriodTorusHigherHomology.quarterIntersectionSection_toU (X : Type) [TopologicalSpace X] :
    (CircleTopology.productIntersectionToU X).comp (CirclePaths.quarterIntersectionSection X) =
      ((CircleTopology.productUHomeomorph X).symm :
            C(CircleTopology.arcU × X, CircleTopology.productU X)).comp
        ((ContinuousMap.const X CirclePaths.quarterU).prodMk (ContinuousMap.id X)) :=
  rfl

theorem PeriodTorusHigherHomology.quarterIntersectionSection_toV (X : Type) [TopologicalSpace X] :
    (CircleTopology.productIntersectionToV X).comp (CirclePaths.quarterIntersectionSection X) =
      ((CircleTopology.productVHomeomorph X).symm :
            C(CircleTopology.arcV × X, CircleTopology.productV X)).comp
        ((ContinuousMap.const X CirclePaths.quarterV).prodMk (ContinuousMap.id X)) :=
  rfl

theorem PeriodTorusHigherHomology.threeQuarterIntersectionSection_toU (X : Type)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionToU X).comp
        (CirclePaths.threeQuarterIntersectionSection X) =
      ((CircleTopology.productUHomeomorph X).symm :
            C(CircleTopology.arcU × X, CircleTopology.productU X)).comp
        ((ContinuousMap.const X CirclePaths.threeQuarterU).prodMk (ContinuousMap.id X)) :=
  rfl

theorem PeriodTorusHigherHomology.threeQuarterIntersectionSection_toV (X : Type)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionToV X).comp
        (CirclePaths.threeQuarterIntersectionSection X) =
      ((CircleTopology.productVHomeomorph X).symm :
            C(CircleTopology.arcV × X, CircleTopology.productV X)).comp
        ((ContinuousMap.const X CirclePaths.threeQuarterV).prodMk (ContinuousMap.id X)) :=
  rfl

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

private theorem PeriodTorusHigherHomology.const_prodMk_id_eq_crossInsertLeft_mo1973_12793
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) :
    (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y) = crossInsertLeft x := by
  apply ContinuousMap.ext
  intro y
  rfl

def PeriodTorusHigherHomology.uCrossChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (CircleTopology.productU X) (n + 1) :=
  FirstHurewicz.inducedChain
    ((CircleTopology.productUHomeomorph X).symm :
      C(CircleTopology.arcU × X, CircleTopology.productU X))
    (n + 1)
    (crossProductEdge CircleTopology.arcU X n (FirstHurewicz.pathChain CirclePaths.uPath) b.1)

def PeriodTorusHigherHomology.vCrossChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (CircleTopology.productV X) (n + 1) :=
  FirstHurewicz.inducedChain
    ((CircleTopology.productVHomeomorph X).symm :
      C(CircleTopology.arcV × X, CircleTopology.productV X))
    (n + 1)
    (crossProductEdge CircleTopology.arcV X n (FirstHurewicz.pathChain CirclePaths.vPath) b.1)

theorem PeriodTorusHigherHomology.uCrossChain_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (CircleTopology.productU X)).d (n + 1) n).hom
        (uCrossChain X n b) =
      FirstHurewicz.inducedChain (CircleTopology.productIntersectionToU X) n
        (intersectionDifferenceCycle X n b).1 := by
  rw [uCrossChain, ← FirstHurewicz.inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub]
  congr 1
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1)
        (threeQuarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1) (quarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm

theorem PeriodTorusHigherHomology.vCrossChain_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (CircleTopology.productV X)).d (n + 1) n).hom
        (vCrossChain X n b) =
      -FirstHurewicz.inducedChain (CircleTopology.productIntersectionToV X) n
          (intersectionDifferenceCycle X n b).1 := by
  rw [vCrossChain, ← FirstHurewicz.inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub, neg_sub]
  congr 1
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1) (quarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1)
        (threeQuarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm

theorem PeriodTorusHigherHomology.uCrossChain_inclusion (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.inducedChain (CircleTopology.productUInclusion X) (n + 1) (uCrossChain X n b) =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.uCirclePath) b.1 := by
  have hi :
    (CircleTopology.productUInclusion X).comp
        ((CircleTopology.productUHomeomorph X).symm :
          C(CircleTopology.arcU × X, CircleTopology.productU X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
            C(CircleTopology.arcU, (PeriodTorusHigherHomology.CircleTopology.Circle))).prodMap
        (ContinuousMap.id X) :=
    rfl
  rw [uCrossChain, ← LinearMap.comp_apply, ← FirstHurewicz.inducedChain_comp, hi,
    crossProductEdge_natural, FirstHurewicz.inducedChain_id, LinearMap.id_apply,
    FirstHurewicz.inducedChain_pathChain]
  rfl

theorem PeriodTorusHigherHomology.vCrossChain_inclusion (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.inducedChain (CircleTopology.productVInclusion X) (n + 1) (vCrossChain X n b) =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.vCirclePath) b.1 := by
  have hi :
    (CircleTopology.productVInclusion X).comp
        ((CircleTopology.productVHomeomorph X).symm :
          C(CircleTopology.arcV × X, CircleTopology.productV X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
            C(CircleTopology.arcV, (PeriodTorusHigherHomology.CircleTopology.Circle))).prodMap
        (ContinuousMap.id X) :=
    rfl
  rw [vCrossChain, ← LinearMap.comp_apply, ← FirstHurewicz.inducedChain_comp, hi,
    crossProductEdge_natural, FirstHurewicz.inducedChain_id, LinearMap.id_apply,
    FirstHurewicz.inducedChain_pathChain]
  rfl

theorem PeriodTorusHigherHomology.arcCrossChains_inclusion_sum (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.inducedChain (CircleTopology.productUInclusion X) (n + 1) (uCrossChain X n b) +
        FirstHurewicz.inducedChain (CircleTopology.productVInclusion X) (n + 1)
          (vCrossChain X n b) =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.uCirclePath +
          FirstHurewicz.pathChain CirclePaths.vCirclePath)
        b.1 := by rw [uCrossChain_inclusion, vCrossChain_inclusion, map_add, LinearMap.add_apply]

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

def PeriodTorusHigherHomology.positiveCircleSmallCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularMayerVietoris.smallComplex (CircleTopology.productU X) (CircleTopology.productV X))
      (n + 1) :=
  twoChainSmallCycle (CircleTopology.productU X) (CircleTopology.productV X) n (uCrossChain X n b)
    (vCrossChain X n b) (intersectionDifferenceCycle X n b) (uCrossChain_boundary X n b)
    (vCrossChain_boundary X n b)

theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_val (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
            (CircleTopology.productV X))
          (n + 1) (positiveCircleSmallCycle X n b)).1 =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.uCirclePath +
          FirstHurewicz.pathChain CirclePaths.vCirclePath)
        b.1 :=
  (twoChainSmallCycle_ambient_val (CircleTopology.productU X) (CircleTopology.productV X) n
        (uCrossChain X n b) (vCrossChain X n b) (intersectionDifferenceCycle X n b)
        (uCrossChain_boundary X n b) (vCrossChain_boundary X n b)).trans
    (arcCrossChains_inclusion_sum X n b)

theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_eq (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
          (CircleTopology.productV X))
        (n + 1) (positiveCircleSmallCycle X n b) =
      crossProductCycles (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        CirclePaths.arcSumCycle b := by
  apply Subtype.ext
  exact positiveCircleSmallCycle_ambient_val X n b

theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_class (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        (n + 1)
        (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
            (CircleTopology.productV X))
          (n + 1) (positiveCircleSmallCycle X n b)) =
      positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) :=
  by
  rw [positiveCircleSmallCycle_ambient_eq]
  exact (positiveCircleCross_arcSum_cycleClass X n b).symm

theorem PeriodTorusHigherHomology.circleConnecting_positiveCircleCross_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    circleMayerVietorisConnecting X n
        (positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex
          (CircleTopology.productU X ∩ CircleTopology.productV X :
            Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)))
        n (intersectionDifferenceCycle X n b) := by
  rw [← positiveCircleSmallCycle_ambient_class]
  exact
    connectingHomomorphism_twoChain (CircleTopology.productU X) (CircleTopology.productV X)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X) n (uCrossChain X n b) (vCrossChain X n b)
      (intersectionDifferenceCycle X n b) (uCrossChain_boundary X n b)
      (vCrossChain_boundary X n b)

theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross_cycleClass
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    circleBoundaryCoordinates X n
        (positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) =
      (-SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b,
        SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) := by
  change
    productIntersectionHomologyEquiv X n
        (circleMayerVietorisConnecting X n
          (positiveCircleCross X n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b))) =
      _
  rw [circleConnecting_positiveCircleCross_cycleClass]
  exact intersectionDifferenceCycle_class_coordinates X n b

theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundaryCoordinates X n (positiveCircleCross X n b) = (-b, b) := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) n
      b
  exact circleBoundaryCoordinates_positiveCircleCross_cycleClass X n c

@[simp]
theorem PeriodTorusHigherHomology.circleBoundary_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundary X n (positiveCircleCross X n b) = b := by
  rw [circleBoundary_apply, circleBoundaryCoordinates_positiveCircleCross]
  exact neg_neg b

def PeriodTorusHigherHomology.circleProductMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
      (PeriodTorusHigherHomology.CircleTopology.Circle) × Y) :=
  ⟨fun z => (z.1, f z.2), continuous_fst.prodMk (f.continuous.comp continuous_snd)⟩

def PeriodTorusHigherHomology.intersectionProductMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    C(↥(CircleTopology.productU X ∩ CircleTopology.productV X),
      ↥(CircleTopology.productU Y ∩ CircleTopology.productV Y)) :=
  ⟨fun z => ⟨circleProductMap f z.val, z.property⟩,
    ((circleProductMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem PeriodTorusHigherHomology.circleProductMap_projection {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (CircleTopology.productProjection Y).comp (circleProductMap f) =
      f.comp (CircleTopology.productProjection X) :=
  rfl

theorem PeriodTorusHigherHomology.intersectionProductMap_homotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (CircleTopology.productIntersectionHomotopyEquiv Y).toFun.comp (intersectionProductMap f) =
      (CircleTopology.sumContinuousMap f f).comp
        (CircleTopology.productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  let c : ↥(CircleTopology.arcU ∩ CircleTopology.arcV) := ⟨z.val.1, z.property⟩
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × Y => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × Y => t.2)
        (Homeomorph.sumProdDistrib (CircleTopology.intersectionHomeomorph c, f z.val.2)) =
      Sum.map f f
        (Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
          (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
          (Homeomorph.sumProdDistrib (CircleTopology.intersectionHomeomorph c, z.val.2)))
  cases h : CircleTopology.intersectionHomeomorph c <;> rfl

theorem PeriodTorusHigherHomology.circleProjectionHomology_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (circleProjectionHomology Y n).comp
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) n) =
      (SingularMayerVietoris.singularHomologyMap f n).comp (circleProjectionHomology X n) := by
  rw [← singularHomologyMap_comp, circleProductMap_projection, singularHomologyMap_comp]

theorem PeriodTorusHigherHomology.sumHomologyEquiv_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X'))
    (g : C(Y, Y')) (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    sumHomologyEquiv X' Y' n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.sumContinuousMap f g) n a) =
      (SingularMayerVietoris.singularHomologyMap f n (sumHomologyEquiv X Y n a).1,
        SingularMayerVietoris.singularHomologyMap g n (sumHomologyEquiv X Y n a).2) := by
  have hsum :
    CircleTopology.sumContinuousMap f g =
      sumElimMap ((sumInlMap X' Y').comp f) ((sumInrMap X' Y').comp g) := by
    ext x
    cases x <;> rfl
  simp only [hsum, sumHomologyEquiv_sumElim, singularHomologyMap_comp, LinearMap.comp_apply,
    map_add, sumHomologyEquiv_inl, sumHomologyEquiv_inr, Prod.mk_add_mk, add_zero, zero_add]

theorem PeriodTorusHigherHomology.productIntersectionHomologyEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    productIntersectionHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n a) =
      (SingularMayerVietoris.singularHomologyMap f n (productIntersectionHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap f n
          (productIntersectionHomologyEquiv X n a).2) := by
  have h :=
    congrArg (fun g => SingularMayerVietoris.singularHomologyMap g n)
      (intersectionProductMap_homotopyEquiv f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  calc
    _ =
        sumHomologyEquiv Y Y n
          (SingularMayerVietoris.singularHomologyMap (CircleTopology.sumContinuousMap f f) n
            (SingularMayerVietoris.singularHomologyMap
              (CircleTopology.productIntersectionHomotopyEquiv X).toFun n a)) :=
      congrArg (sumHomologyEquiv Y Y n) (LinearMap.congr_fun h a)
    _ = _ := sumHomologyEquiv_naturality f f n _

theorem PeriodTorusHigherHomology.circleProductMap_mapsToU {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (CircleTopology.productU X) (CircleTopology.productU Y) :=
  fun _ h => h

theorem PeriodTorusHigherHomology.circleProductMap_mapsToV {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (CircleTopology.productV X) (CircleTopology.productV Y) :=
  fun _ h => h

theorem PeriodTorusHigherHomology.circleProductIntersectionRestriction_eq {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    SingularMayerVietoris.intersectionRestriction (circleProductMap f) (CircleTopology.productU X)
        (CircleTopology.productV X) (CircleTopology.productU Y) (CircleTopology.productV Y)
        (circleProductMap_mapsToU f) (circleProductMap_mapsToV f) =
      intersectionProductMap f :=
  rfl

theorem PeriodTorusHigherHomology.circleMayerVietorisConnecting_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n).comp
        (circleMayerVietorisConnecting X n) =
      (circleMayerVietorisConnecting Y n).comp
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality (circleProductMap f)
      (CircleTopology.productU X) (CircleTopology.productV X) (CircleTopology.productU Y)
      (CircleTopology.productV Y) (circleProductMap_mapsToU f) (circleProductMap_mapsToV f)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X) (CircleTopology.productU_open Y)
      (CircleTopology.productV_open Y) (CircleTopology.product_cover Y) n
  rw [circleProductIntersectionRestriction_eq] at h
  exact h

theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundaryCoordinates Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap f n (circleBoundaryCoordinates X n a).1,
        SingularMayerVietoris.singularHomologyMap f n (circleBoundaryCoordinates X n a).2) := by
  have h := LinearMap.congr_fun (circleMayerVietorisConnecting_naturality f n) a
  change
    SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n
        (circleMayerVietorisConnecting X n a) =
      circleMayerVietorisConnecting Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) at h
  change
    productIntersectionHomologyEquiv Y n
        (circleMayerVietorisConnecting Y n
          (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a)) =
      _
  rw [← h]
  exact productIntersectionHomologyEquiv_naturality f n (circleMayerVietorisConnecting X n a)

theorem PeriodTorusHigherHomology.circleBoundary_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundary Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap f n (circleBoundary X n a) := by
  change
    -(circleBoundaryCoordinates Y n
            (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a)).1 =
      SingularMayerVietoris.singularHomologyMap f n (-(circleBoundaryCoordinates X n a).1)
  rw [circleBoundaryCoordinates_naturality, map_neg]

theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleProductHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap f (n + 1) (circleProductHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap f n (circleProductHomologyEquiv X n a).2) := by
  apply Prod.ext
  · exact LinearMap.congr_fun (circleProjectionHomology_naturality f (n + 1)) a
  · exact circleBoundary_naturality f n a

theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        ((circleProductHomologyEquiv X n).symm a) =
      (circleProductHomologyEquiv Y n).symm
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a.1,
          SingularMayerVietoris.singularHomologyMap f n a.2) := by
  apply (circleProductHomologyEquiv Y n).injective
  rw [circleProductHomologyEquiv_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCycles_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap (f.prodMap g))
        (n + 1) (crossProductCycles X Y n a b) =
      crossProductCycles X' Y' n
        (SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap f) 1 a)
        (SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap g) n b) :=
  by
  apply Subtype.ext
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, crossProductCycles_val]
  exact crossProductEdge_natural f g n a.1 b.1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : (FirstHurewicz.singularComplex X).homology 1)
    (b : (FirstHurewicz.singularComplex Y).homology n) :
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap (f.prodMap g)) (n + 1)).hom
        (crossProductHomology X Y n a b) =
      crossProductHomology X' Y' n
        ((HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap f) 1).hom a)
        ((HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap g) n).hom b) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Y) n
      b
  rw [crossProductHomology_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, crossProductHomology_cycleClass,
    crossProductCycles_natural]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_snd {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(X × Y, Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      0 := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology Unit 1) :=
    point_homology_subsingleton 1 (by decide)
  let f : C(X, Unit) := ContinuousMap.const X ()
  have hz : SingularMayerVietoris.singularHomologyMap f 1 a = 0 := Subsingleton.elim _ _
  have hn := crossProductHomology_natural f (ContinuousMap.id Y) n a b
  change
    SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      crossProductHomology Unit Y n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id Y) n b) at hn
  rw [hz, map_zero, LinearMap.zero_apply] at hn
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1)
          (SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
            (crossProductHomology X Y n a b)) := by
      exact
        LinearMap.congr_fun
          (singularHomologyMap_comp (f.prodMap (ContinuousMap.id Y))
            (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1))
          (crossProductHomology X Y n a b)
    _ = 0 := by rw [hn, map_zero]

@[simp]
theorem PeriodTorusHigherHomology.circleProjection_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProjectionHomology X (n + 1) (positiveCircleCross X n b) = 0 :=
  crossProductHomology_snd n (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) b

@[simp]
theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProductHomologyEquiv X n (positiveCircleCross X n b) = (0, b) := by
  apply Prod.ext
  · exact circleProjection_positiveCircleCross X n b
  · exact circleBoundary_positiveCircleCross X n b

theorem PeriodTorusHigherHomology.positiveCircleCross_eq_symm (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    positiveCircleCross X n b = (circleProductHomologyEquiv X n).symm (0, b) := by
  apply (circleProductHomologyEquiv X n).injective
  rw [circleProductHomologyEquiv_positiveCircleCross, LinearEquiv.apply_symm_apply]

theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    (circleProductHomologyEquiv X n).symm a =
      circleSectionHomology X (n + 1) a.1 + positiveCircleCross X n a.2 := by
  apply (circleProductHomologyEquiv X n).injective
  rw [LinearEquiv.apply_symm_apply, map_add, circleProductHomologyEquiv_section,
    circleProductHomologyEquiv_positiveCircleCross]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem PeriodTorusHigherHomology.positiveCircleCross_naturality {X : Type} [TopologicalSpace X]
    {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        (positiveCircleCross X n b) =
      positiveCircleCross Y n (SingularMayerVietoris.singularHomologyMap f n b) := by
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
          ((circleProductHomologyEquiv X n).symm (0, b)) :=
      congrArg (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1))
        (positiveCircleCross_eq_symm X n b)
    _ =
        (circleProductHomologyEquiv Y n).symm
          (0, SingularMayerVietoris.singularHomologyMap f n b) := by
      simpa only [map_zero] using circleProductHomologyEquiv_symm_naturality f n (0, b)
    _ = _ :=
      (positiveCircleCross_eq_symm Y n (SingularMayerVietoris.singularHomologyMap f n b)).symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.circleParametrizedMap {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D)) : C(X × _root_.Circle, D) :=
  a.comp ((ContinuousMap.id X).prodMap α)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.circleParametrizedOrbit {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D)) : C(X, D) :=
  a.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X (α 1)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.circleParametrizedSourceHomeomorph (X : Type) [TopologicalSpace X] :
    (AddCircle (1 : ℝ) × X) ≃ₜ (X × _root_.Circle) :=
  (circleCoordinateHomeomorph.symm.prodCongr (Homeomorph.refl X)).trans
    (Homeomorph.prodComm _root_.Circle X)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.additiveCircleParametrizedMap {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (β : C(AddCircle (1 : ℝ), D)) :
    C(AddCircle (1 : ℝ) × X, D) :=
  (a.comp (Homeomorph.prodComm D X : C(D × X, X × D))).comp (β.prodMap (ContinuousMap.id X))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.circleParametrizedMap_comp_source {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D)) :
    (circleParametrizedMap a α).comp
        (circleParametrizedSourceHomeomorph X : C(AddCircle (1 : ℝ) × X, X × _root_.Circle)) =
      additiveCircleParametrizedMap a
        (α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.parameterMap_positiveCircleCross_eq_zero {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (β : C(AddCircle (1 : ℝ), D))
    (hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0) (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n b) =
      0 := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural β (ContinuousMap.id X) n
      (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) b
  change
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n b) =
      PeriodTorusHigherHomology.crossProductHomology D X n
        (SingularMayerVietoris.singularHomologyMap β 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n b) at h
  rw [hβ, LinearMap.zero_apply, map_zero, LinearMap.zero_apply] at h
  exact h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.additiveCircleParametrizedHomologyMap_eq_zero {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (a : C(X × D, D)) (β : C(AddCircle (1 : ℝ), D))
    (hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0) (n : ℕ)
    (hsection :
      SingularMayerVietoris.singularHomologyMap
          ((additiveCircleParametrizedMap a β).comp
            (PeriodTorusHigherHomology.CircleTopology.productSection X))
          (n + 1) =
        0) :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) = 0 := by
  have hs (c : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)
        (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) c) =
      0 := by
    change
      ((SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β)
                (n + 1)).comp
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.CircleTopology.productSection X) (n + 1)))
          c =
        0
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, hsection, LinearMap.zero_apply]
  have hc (c : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n c) =
      0 := by
    rw [additiveCircleParametrizedMap, PeriodTorusHigherHomology.singularHomologyMap_comp,
      LinearMap.comp_apply, parameterMap_positiveCircleCross_eq_zero β hβ, map_zero]
  apply LinearMap.ext
  intro c
  change
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) c = 0
  obtain ⟨p, rfl⟩ := (PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm.surjective c
  rw [PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross, map_add, hs,
    hc, add_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.circleParametrizedHomologyMap_eq_zero {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ)
    (horbit :
      SingularMayerVietoris.singularHomologyMap (circleParametrizedOrbit a α) (n + 1) = 0) :
    SingularMayerVietoris.singularHomologyMap (circleParametrizedMap a α) (n + 1) = 0 := by
  let β : C(AddCircle (1 : ℝ), D) :=
    α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
  have hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0 := by
    rw [show β = α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
        from rfl,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hα, LinearMap.zero_comp]
  have hsectionMap :
    (additiveCircleParametrizedMap a β).comp
        (PeriodTorusHigherHomology.CircleTopology.productSection X) =
      circleParametrizedOrbit a α := by
    apply ContinuousMap.ext
    intro x
    change a (x, α (circleCoordinateHomeomorph.symm 0)) = a (x, α 1)
    rw [circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]
  have hzero :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) = 0 :=
    additiveCircleParametrizedHomologyMap_eq_zero a β hβ n (by rw [hsectionMap]; exact horbit)
  have hcomp :
    (SingularMayerVietoris.singularHomologyMap (circleParametrizedMap a α) (n + 1)).comp
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X)
            (n + 1)).toLinearMap =
      0 := by
    rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
      PeriodTorusHigherHomology.singularHomologyMap_comp, circleParametrizedMap_comp_source]
    exact hzero
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X)
          (n + 1)).surjective
      c
  exact LinearMap.congr_fun hcomp d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.circleParametrizedHomologyMap_eq_zero_of_nullhomotopic {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ)
    (horbit : (circleParametrizedOrbit a α).Nullhomotopic) :
    SingularMayerVietoris.singularHomologyMap (circleParametrizedMap a α) (n + 1) = 0 :=
  circleParametrizedHomologyMap_eq_zero a α hα n
    (singularHomologyMap_eq_zero_of_nullhomotopic _ horbit (n + 1) (Nat.succ_ne_zero n))

theorem CuspCentralHomology.boundaryPhaseAction_parametrizedOrbit
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    circleParametrizedOrbit (boundaryPhaseActionMap C ε hε hC) (boundaryLoop C ε hε) =
      boundaryPhaseOrbit C ε hε := by
  apply ContinuousMap.ext
  intro u
  exact (circleBoundaryCellMap_phaseAction C ε hε u 1).symm

theorem CuspCentralHomology.circleBoundaryCellMap_homology_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (circleBoundaryCellMap C ε hε) (n + 1) = 0 := by
  rw [circleBoundaryCellMap_eq_phaseAction C ε hε hC]
  change
    SingularMayerVietoris.singularHomologyMap
        (circleParametrizedMap (boundaryPhaseActionMap C ε hε hC) (boundaryLoop C ε hε)) (n + 1) =
      0
  apply circleParametrizedHomologyMap_eq_zero_of_nullhomotopic
  · exact boundaryLoop_homology_one_eq_zero C ε hε hε1 hC hR
  · rw [boundaryPhaseAction_parametrizedOrbit]
    exact boundaryPhaseOrbit_nullhomotopic C ε hε

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.rightCircleSection (X : Type) [TopologicalSpace X] :
    C(X, X × _root_.Circle) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.rightCircleProjection_section (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
            n).comp
        (SingularMayerVietoris.singularHomologyMap (rightCircleSection X) n) =
      LinearMap.id := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact PeriodTorusHigherHomology.singularHomologyMap_id X n

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.rightCircleProjection_surjective_allDegrees (X : Type)
    [TopologicalSpace X] (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        n) := by
  intro a
  exact
    ⟨SingularMayerVietoris.singularHomologyMap (rightCircleSection X) n a,
      LinearMap.congr_fun (rightCircleProjection_section X n) a⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.rightCircleProjection_surjective (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        (n + 1)) :=
  rightCircleProjection_surjective_allDegrees X (n + 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.rightCircleProductHomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (X × _root_.Circle) (n + 1) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X).symm
        (n + 1)).trans
    (PeriodTorusHigherHomology.circleProductHomologyEquiv X n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem CuspCentralHomology.rightCircleProductHomologyEquiv_fst (X : Type) [TopologicalSpace X]
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X × _root_.Circle) (n + 1)) :
    (rightCircleProductHomologyEquiv X n a).1 =
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        (n + 1) a := by
  change
    PeriodTorusHigherHomology.circleProjectionHomology X (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          ((circleParametrizedSourceHomeomorph X).symm :
            C(X × _root_.Circle, AddCircle (1 : ℝ) × X))
          (n + 1) a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem CuspCentralHomology.rightCircleProductHomologyEquiv_symm_projection (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        (n + 1) ((rightCircleProductHomologyEquiv X n).symm a) =
      a.1 := by rw [← rightCircleProductHomologyEquiv_fst, LinearEquiv.apply_symm_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.rightCircleProjectionKernelEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
          (n + 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  ({    toFun a := (rightCircleProductHomologyEquiv X n a).2
        invFun
          b :=
          ⟨(rightCircleProductHomologyEquiv X n).symm (0, b), by
            rw [LinearMap.mem_ker, rightCircleProductHomologyEquiv_symm_projection]⟩
        left_inv
          a := by
          apply Subtype.ext
          apply (rightCircleProductHomologyEquiv X n).injective
          rw [LinearEquiv.apply_symm_apply]
          apply Prod.ext
          · rw [rightCircleProductHomologyEquiv_fst]
            exact a.property.symm
          · rfl
        right_inv
          b := by
          change
            ((rightCircleProductHomologyEquiv X n)
                  ((rightCircleProductHomologyEquiv X n).symm (0, b))).2 =
              b
          rw [LinearEquiv.apply_symm_apply]
        map_add' a
          b := by
          change (rightCircleProductHomologyEquiv X n ((a : _) + b)).2 = _
          rw [map_add]
          rfl } :
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
            (n + 1)) ≃+
        SingularMayerVietoris.SingularHomology X n).toIntLinearEquiv

abbrev PeriodTorusHigherHomology.binomialModule (r n : ℕ) :=
  Fin (r.choose n) → ℤ

def PeriodTorusHigherHomology.binomialPascalIndexEquiv (r n : ℕ) :
    Fin ((r + 1).choose (n + 1)) ≃ Fin (r.choose (n + 1)) ⊕ Fin (r.choose n) :=
  (finCongr ((Nat.choose_succ_succ' r n).trans (Nat.add_comm _ _))).trans finSumFinEquiv.symm

def PeriodTorusHigherHomology.binomialModuleSuccEquiv (r n : ℕ) :
    binomialModule (r + 1) (n + 1) ≃ₗ[ℤ] binomialModule r (n + 1) × binomialModule r n :=
  (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (binomialPascalIndexEquiv r n)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ ℤ)

@[simp]
theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_apply_fst (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose (n + 1))) :
    (binomialModuleSuccEquiv r n x).1 i = x ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_apply_snd (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose n)) :
    (binomialModuleSuccEquiv r n x).2 i = x ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) :=
  rfl

def PeriodTorusHigherHomology.integerBinomialZeroEquiv (r : ℕ) : ℤ ≃ₗ[ℤ] binomialModule r 0 :=
  (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (finCongr (Nat.choose_zero_right r)).symm)

@[simp]
theorem PeriodTorusHigherHomology.binomialModule_finrank (r n : ℕ) :
    Module.finrank ℤ (binomialModule r n) = r.choose n :=
  Module.finrank_fin_fun ℤ

theorem PeriodTorusHigherHomology.binomialModule_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (binomialModule r n) := by
  change Subsingleton (Fin (r.choose n) → ℤ)
  rw [Nat.choose_eq_zero_of_lt h]
  infer_instance

instance PeriodTorusHigherHomology.binomialModule_zero_succ_subsingleton (n : ℕ) :
    Subsingleton (binomialModule 0 (n + 1)) :=
  binomialModule_subsingleton_of_lt (Nat.zero_lt_succ n)

theorem PeriodTorusHigherHomology.binomialModule_eq_zero_of_lt {r n : ℕ} (h : r < n)
    (x : binomialModule r n) : x = 0 :=
  @Subsingleton.elim (binomialModule r n) (binomialModule_subsingleton_of_lt h) x 0

def PeriodTorusHigherHomology.productTorusHomologyEquiv :
    (r n : ℕ) → SingularMayerVietoris.SingularHomology (ProductTorus r) n ≃ₗ[ℤ] binomialModule r n
  | r, 0 => (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r)
  | 0, n + 1 =>
    by
    letI := totallyDisconnected_homology_subsingleton PUnit (n + 1) (Nat.succ_ne_zero n)
    exact
      (homeomorphHomologyEquiv productTorusZeroHomeomorph (n + 1)).trans
        (LinearEquiv.ofSubsingleton (SingularMayerVietoris.SingularHomology PUnit (n + 1))
          (binomialModule 0 (n + 1)))
  | r + 1, n + 1 =>
    ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
        ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                (productTorusHomologyEquiv r n).toAddEquiv).trans
            (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv

@[simp]
theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_zero (r : ℕ) :
    productTorusHomologyEquiv r 0 =
      (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r) := by
  cases r <;> rfl

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ (r n : ℕ) :
    productTorusHomologyEquiv (r + 1) (n + 1) =
      ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
          ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
            (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                  (productTorusHomologyEquiv r n).toAddEquiv).trans
              (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv :=
  rfl

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_apply (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      (productTorusHomologyEquiv r (n + 1)
          (circleProjectionHomology (ProductTorus r) (n + 1)
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)),
        productTorusHomologyEquiv r n
          (circleBoundary (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a))) := by
  rw [productTorusHomologyEquiv_succ]
  change
    binomialModuleSuccEquiv r n
        ((binomialModuleSuccEquiv r n).symm
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
              (productTorusHomologyEquiv r n).toAddEquiv)
            (circleProductHomologyEquiv (ProductTorus r) n
              (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)))) =
      _
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_apply]
  rfl

theorem PeriodTorusHigherHomology.productTorus_homology_free (r n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  Module.Free.of_equiv (productTorusHomologyEquiv r n).symm

theorem PeriodTorusHigherHomology.productTorus_homology_finite (r n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  Module.Finite.of_surjective (productTorusHomologyEquiv r n).symm.toLinearMap
    (productTorusHomologyEquiv r n).symm.surjective

theorem PeriodTorusHigherHomology.productTorus_homology_finrank (r n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) = r.choose n := by
  rw [(productTorusHomologyEquiv r n).finrank_eq]
  exact binomialModule_finrank r n

theorem PeriodTorusHigherHomology.productTorus_homology_torsionFree (r n : ℕ) :
    Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) := by
  let := productTorus_homology_free r n
  infer_instance

theorem PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (ProductTorus r) n) := by
  let := binomialModule_subsingleton_of_lt h
  exact (productTorusHomologyEquiv r n).injective.subsingleton

def CuspCentralHomology.compactFibreTorusHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n ≃ₗ[ℤ]
      PeriodTorusHigherHomology.binomialModule 2 n :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph n).trans
    (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 n)

def CuspCentralHomology.fibreTorusCircleHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n ≃ₗ[ℤ]
      PeriodTorusHigherHomology.binomialModule 3 n :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv fibreTorusCircleHomeomorph n).trans
    (PeriodTorusHigherHomology.productTorusHomologyEquiv 3 n)

def CuspCentralHomology.fibreTorusCircleHomologyThreeEquiv :
    SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) 3 ≃ₗ[ℤ] ℤ :=
  (fibreTorusCircleHomologyEquiv 3).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

theorem CuspCentralHomology.compactFibreTorus_homology_subsingleton_of_lt {n : ℕ} (hn : 2 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph
        n).injective.subsingleton

theorem CuspCentralHomology.compactFibreTorus_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus (n + 3)) :=
  compactFibreTorus_homology_subsingleton_of_lt (by omega)

theorem CuspCentralHomology.fibreTorusCircle_homology_subsingleton_of_lt {n : ℕ} (hn : 3 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv fibreTorusCircleHomeomorph
        n).injective.subsingleton

theorem CuspCentralHomology.fibreTorusCircle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) (n + 4)) :=
  fibreTorusCircle_homology_subsingleton_of_lt (by omega)

def CuspCentralHomology.outerRegionSuspensionHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    outerRegion C ε hε a ≃ₕ ThreeCircleSuspension :=
  (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).trans
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).toHomotopyEquiv

def CuspCentralHomology.innerRegionHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (innerRegion C ε hε) n ≃ₗ[ℤ]
      PeriodTorusHigherHomology.binomialModule 2 n :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (innerRegionHomotopyEquiv C ε hε hε1 hC hR) n).trans
    (compactFibreTorusHomologyEquiv n)

def CuspCentralHomology.overlapRegionHomologyThreeEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) 3 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) 3).trans
    fibreTorusCircleHomologyThreeEquiv

theorem CuspCentralHomology.outerRegion_homology_subsingleton (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (outerRegion C ε hε a) (n + 3)) := by
  let := threeCircleSuspension_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (outerRegionSuspensionHomotopyEquiv C ε hε hε1 hC hR a ha ha1)
        (n + 3)).injective.subsingleton

theorem CuspCentralHomology.innerRegion_homology_subsingleton (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (innerRegion C ε hε) (n + 3)) := by
  let := compactFibreTorus_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (innerRegionHomotopyEquiv C ε hε hε1 hC hR) (n + 3)).injective.subsingleton

theorem CuspCentralHomology.overlapRegion_homology_subsingleton (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) (n + 4)) := by
  let := fibreTorusCircle_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) (n + 4)).injective.subsingleton

def CuspCentralHomology.middleInnerHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (innerRegion C ε hε) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (innerRegionHomotopyEquiv C ε hε hε1 hC hR)
    n

def CuspCentralHomology.middleOverlapHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n

theorem CuspCentralHomology.overlapIntoOuter_homology_eq_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (overlapIntoOuter C ε hε a) (n + 1) = 0 := by
  have hm :=
    congrArg
      (fun f : C((overlapRegion C ε hε a), centralBoundary C ε hε) =>
        SingularMayerVietoris.singularHomologyMap f (n + 1))
      (overlapIntoOuter_boundary_map C ε hε hε1 hC hR a ha ha1)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    circleBoundaryCellMap_homology_eq_zero C ε hε hε1 hC hR n] at hm
  apply LinearMap.ext
  intro z
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR) (n + 1)).injective
  simpa only [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, map_zero] using LinearMap.congr_fun hm z

theorem CuspCentralHomology.middleInnerProjection_natural (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    (middleInnerHomologyEquiv C ε hε hε1 hC hR n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) n) =
      (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.fst :
              C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
            n).comp
        (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 n).toLinearMap := by
  have hm :=
    congrArg
      (fun f : C((overlapRegion C ε hε a), ToricSpace.CompactFibreTorus) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (overlapIntoInner_phase_map C ε hε hε1 hC hR a ha ha1)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, middleInnerHomologyEquiv,
    middleOverlapHomologyEquiv,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_toLinearMap] using hm

theorem CuspCentralHomology.middleInnerProjection_zero_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) n) :
    SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) n z = 0 ↔
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          n (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 n z) =
        0 := by
  have hm := LinearMap.congr_fun (middleInnerProjection_natural C ε hε hε1 hC hR a ha ha1 n) z
  change
    middleInnerHomologyEquiv C ε hε hε1 hC hR n
        (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) n z) =
      _ at hm
  constructor
  · intro hz
    rw [hz, map_zero] at hm
    exact hm.symm
  · intro hz
    apply (middleInnerHomologyEquiv C ε hε hε1 hC hR n).injective
    simpa only [map_zero] using hm.trans hz

theorem CuspCentralHomology.overlapIntoInner_homology_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1)) := by
  intro z
  obtain ⟨w, hw⟩ :=
    rightCircleProjection_surjective ToricSpace.CompactFibreTorus n
      (middleInnerHomologyEquiv C ε hε hε1 hC hR (n + 1) z)
  refine ⟨(middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm w, ?_⟩
  apply (middleInnerHomologyEquiv C ε hε hε1 hC hR (n + 1)).injective
  have hm :=
    LinearMap.congr_fun (middleInnerProjection_natural C ε hε hε1 hC hR a ha ha1 (n + 1))
      ((middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hw] using
    hm

theorem CuspCentralHomology.middleLeftHomologyMap_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) (n + 1)) :
    SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) (n + 1) z =
      (0, -SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z) := by
  calc
    SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) (n + 1) z =
        (SingularMayerVietoris.singularHomologyMap (overlapIntoOuter C ε hε a) (n + 1) z,
          -SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z) :=
      SingularMayerVietoris.leftHomologyMap_apply (outerRegion C ε hε a) (innerRegion C ε hε)
        (n + 1) z
    _ = _ := by
      rw [overlapIntoOuter_homology_eq_zero C ε hε hε1 hC hR a ha ha1 n, LinearMap.zero_apply]

theorem CuspCentralHomology.middleLeftHomology_mem_ker_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) (n + 1)) :
    z ∈
        LinearMap.ker
          (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
            (n + 1)) ↔
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1) z) =
        0 := by
  change
    SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) (n + 1) z =
        0 ↔
      _
  rw [middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 n z]
  constructor
  · intro hz
    have hi :
      -SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z = 0 :=
      congrArg Prod.snd hz
    exact
      (middleInnerProjection_zero_iff C ε hε hε1 hC hR a ha ha1 (n + 1) z).mp (neg_eq_zero.mp hi)
  · intro hz
    rw [(middleInnerProjection_zero_iff C ε hε hε1 hC hR a ha ha1 (n + 1) z).mpr hz, neg_zero]
    rfl

def CuspCentralHomology.middleLeftKernelToProjectionEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
          (n + 1)) ≃ₗ[ℤ]
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1)) :=
  ({    toFun
          z :=
          ⟨middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1) z.1,
            (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 n z.1).mp z.2⟩
        invFun
          z :=
          ⟨(middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm z.1,
            (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 n _).mpr
              (by
                rw [LinearEquiv.apply_symm_apply]
                exact z.2)⟩
        left_inv z := Subtype.ext (LinearEquiv.symm_apply_apply _ z.1)
        right_inv z := Subtype.ext (LinearEquiv.apply_symm_apply _ z.1)
        map_add' z
          w := by
          apply Subtype.ext
          exact map_add (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)) z.1 w.1 } :
      LinearMap.ker
          (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
            (n + 1)) ≃+
        LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.fst :
              C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
            (n + 1))).toIntLinearEquiv

def CuspCentralHomology.middleLeftKernelEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
          (n + 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n :=
  ((middleLeftKernelToProjectionEquiv C ε hε hε1 hC hR a ha ha1 n).toAddEquiv.trans
      (rightCircleProjectionKernelEquiv ToricSpace.CompactFibreTorus
          n).toAddEquiv).toIntLinearEquiv

theorem CuspCentralHomology.coverConnecting_injective_of_vanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    Function.Injective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← SingularMayerVietoris.exact_at_ambient U V hU hV hcover n]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero, LinearMap.zero_apply]

theorem CuspCentralHomology.coverConnecting_surjective_of_vanishing {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U n)]
    [Subsingleton (SingularMayerVietoris.SingularHomology V n)] :
    Function.Surjective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  intro a
  have ha : a ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n) := by
    exact Subsingleton.elim _ _
  rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover n] at ha
  exact ha

def CuspCentralHomology.coverConnectingEquivOfVanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology U n)]
    [Subsingleton (SingularMayerVietoris.SingularHomology V n)] :
    SingularMayerVietoris.SingularHomology X (n + 1) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n :=
  LinearEquiv.ofBijective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n)
    ⟨coverConnecting_injective_of_vanishing U V hU hV hcover n,
      coverConnecting_surjective_of_vanishing U V hU hV hcover n⟩

theorem CuspCentralHomology.coverHomology_subsingleton_of_vanishing {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n)] :
    Subsingleton (SingularMayerVietoris.SingularHomology X (n + 1)) :=
  (coverConnecting_injective_of_vanishing U V hU hV hcover n).subsingleton

def CuspCentralHomology.coverConnectingToKernel {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X (n + 1) →ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n).codRestrict
        (LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n))
        (by
          intro a
          rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover n]
          exact ⟨a, rfl⟩)).toAddMonoidHom

theorem CuspCentralHomology.coverConnectingToKernel_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    Function.Surjective (coverConnectingToKernel U V hU hV hcover n) := by
  intro a
  have ha :
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n) ∈
      LinearMap.range (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) :=
    (SingularMayerVietoris.exact_at_intersection U V hU hV hcover n).symm.le a.property
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

@[simp]
theorem CuspCentralHomology.coverConnectingToKernel_eq_zero_iff {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    coverConnectingToKernel U V hU hV hcover n a = 0 ↔
      SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n a = 0 := by
  constructor
  · exact fun ha => congrArg Subtype.val ha
  · exact fun ha => Subtype.ext ha

theorem CuspCentralHomology.coverConnectingToKernel_ker {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.ker (coverConnectingToKernel U V hU hV hcover n) =
      LinearMap.ker (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  ext a
  exact coverConnectingToKernel_eq_zero_iff U V hU hV hcover n a

theorem CuspCentralHomology.coverConnectingToKernel_exact {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (SingularMayerVietoris.rightHomologyMap U V (n + 1)) =
      LinearMap.ker (coverConnectingToKernel U V hU hV hcover n) := by
  rw [coverConnectingToKernel_ker]
  exact SingularMayerVietoris.exact_at_ambient U V hU hV hcover n

theorem CuspCentralHomology.coverConnectingToKernel_injective_of_vanishing {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    Function.Injective (coverConnectingToKernel U V hU hV hcover n) := by
  intro a b hab
  apply coverConnecting_injective_of_vanishing U V hU hV hcover n
  exact congrArg Subtype.val hab

def CuspCentralHomology.coverConnectingKernelEquivOfVanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    SingularMayerVietoris.SingularHomology X (n + 1) ≃ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n) :=
  LinearEquiv.ofBijective (coverConnectingToKernel U V hU hV hcover n)
    ⟨coverConnectingToKernel_injective_of_vanishing U V hU hV hcover n,
      coverConnectingToKernel_surjective U V hU hV hcover n⟩

def CuspCentralHomology.integerExtensionLift {B : Type*} [AddCommGroup B] [Module ℤ B]
    (d : B →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : B :=
  Classical.choose (hd 1)

@[simp]
theorem CuspCentralHomology.integerExtensionLift_spec {B : Type*} [AddCommGroup B] [Module ℤ B]
    (d : B →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : d (integerExtensionLift d hd) = 1 :=
  Classical.choose_spec (hd 1)

def CuspCentralHomology.integerExtensionAssembly {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (b : B) : (A × ℤ) →ₗ[ℤ] B :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun az := i az.1 + az.2 • b
      map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, map_zero, zero_smul, add_zero]
      map_add' az
        aw := by
        change i (az.1 + aw.1) + (az.2 + aw.2) • b = (i az.1 + az.2 • b) + (i aw.1 + aw.2 • b)
        rw [map_add, add_zsmul]
        exact add_add_add_comm _ _ _ _ }

@[simp]
theorem CuspCentralHomology.integerExtensionAssembly_apply {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (b : B) (az : A × ℤ) :
    integerExtensionAssembly i b az = i az.1 + az.2 • b :=
  rfl

theorem CuspCentralHomology.integerExtension_boundary_inclusion {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) : d (i a) = 0 := by
  have ha : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hexact] at ha
  exact ha

theorem CuspCentralHomology.integerExtensionAssembly_boundary {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) (hb : d b = 1) (az : A × ℤ) :
    d (integerExtensionAssembly i b az) = az.2 := by
  rw [integerExtensionAssembly_apply, map_add, map_zsmul,
    integerExtension_boundary_inclusion i d hexact, hb, zero_add]
  simp

theorem CuspCentralHomology.integerExtensionAssembly_injective {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker d) (b : B)
    (hb : d b = 1) : Function.Injective (integerExtensionAssembly i b) := by
  intro az aw h
  have hsnd : az.2 = aw.2 := by
    have hd := congrArg d h
    simpa only [integerExtensionAssembly_boundary i d hexact b hb] using hd
  apply Prod.ext _ hsnd
  apply hi
  apply add_right_cancel (b := aw.2 • b)
  simpa only [integerExtensionAssembly_apply, hsnd] using h

theorem CuspCentralHomology.integerExtensionAssembly_surjective {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) (hb : d b = 1) :
    Function.Surjective (integerExtensionAssembly i b) := by
  intro y
  have hk : y - d y • b ∈ LinearMap.ker d := by
    change d (y - d y • b) = 0
    rw [map_sub, map_zsmul, hb]
    simp
  rw [← hexact] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨(a, d y), ?_⟩
  change i a + d y • b = y
  rw [ha, sub_add_cancel]

def CuspCentralHomology.splitIntegerExtensionEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ) (hi : Function.Injective i)
    (hd : Function.Surjective d) (hexact : LinearMap.range i = LinearMap.ker d) :
    B ≃ₗ[ℤ] (A × ℤ) :=
  (LinearEquiv.ofBijective (integerExtensionAssembly i (integerExtensionLift d hd))
      ⟨integerExtensionAssembly_injective i d hi hexact (integerExtensionLift d hd)
          (integerExtensionLift_spec d hd),
        integerExtensionAssembly_surjective i d hexact (integerExtensionLift d hd)
          (integerExtensionLift_spec d hd)⟩).symm

@[simp]
theorem CuspCentralHomology.splitIntegerExtensionEquiv_symm_apply {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (az : A × ℤ) :
    (splitIntegerExtensionEquiv i d hi hd hexact).symm az =
      i az.1 + az.2 • integerExtensionLift d hd :=
  rfl

@[simp]
theorem CuspCentralHomology.splitIntegerExtensionEquiv_snd {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) :
    (splitIntegerExtensionEquiv i d hi hd hexact b).2 = d b := by
  have h :=
    integerExtensionAssembly_boundary i d hexact (integerExtensionLift d hd)
      (integerExtensionLift_spec d hd) (splitIntegerExtensionEquiv i d hi hd hexact b)
  change
    d
        ((splitIntegerExtensionEquiv i d hi hd hexact).symm
          (splitIntegerExtensionEquiv i d hi hd hexact b)) =
      _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

def CuspCentralHomology.signedRightMap {C E : Type*} [AddCommGroup C] [AddCommGroup E]
    [Module ℤ C] [Module ℤ E] (A : Type*) [AddCommGroup A] [Module ℤ A] (p : E →ₗ[ℤ] C) :
    E →ₗ[ℤ] (A × C) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun e := (0, -p e)
      map_zero' := by simp only [map_zero, neg_zero, Prod.mk_zero_zero]
      map_add' e
        f := by
        apply Prod.ext
        · exact (add_zero 0).symm
        · exact (congrArg Neg.neg (p.map_add e f)).trans (neg_add (p e) (p f)) }

@[simp]
theorem CuspCentralHomology.signedRightMap_apply {A C E : Type*} [AddCommGroup A] [AddCommGroup C]
    [AddCommGroup E] [Module ℤ A] [Module ℤ C] [Module ℤ E] (p : E →ₗ[ℤ] C) (e : E) :
    signedRightMap A p e = (0, -p e) :=
  rfl

def CuspCentralHomology.firstSummandMap {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℤ A] [Module ℤ B] (r : (A × C) →ₗ[ℤ] B) : A →ₗ[ℤ] B :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun a := r (a, 0)
      map_zero' := r.map_zero
      map_add' a b := by simpa only [Prod.mk_add_mk, add_zero] using r.map_add (a, 0) (b, 0) }

@[simp]
theorem CuspCentralHomology.firstSummandMap_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] (r : (A × C) →ₗ[ℤ] B) (a : A) :
    firstSummandMap r a = r (a, 0) :=
  rfl

theorem CuspCentralHomology.firstSummandMap_injective {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    Function.Injective (firstSummandMap r) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  have hmem : (a, 0) ∈ LinearMap.ker r := ha
  rw [hker] at hmem
  obtain ⟨e, he⟩ := hmem
  change a = 0
  exact (congrArg Prod.fst he).symm

theorem CuspCentralHomology.secondSummand_eq_zero {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) (c : C) : r (0, c) = 0 := by
  have hmem : (0, c) ∈ LinearMap.range (signedRightMap A p) := by
    obtain ⟨e, he⟩ := hp (-c)
    refine ⟨e, ?_⟩
    simp only [signedRightMap_apply, he, neg_neg]
  rw [← hker] at hmem
  exact hmem

theorem CuspCentralHomology.firstSummandMap_apply_fst {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) (ac : A × C) :
    firstSummandMap r ac.1 = r ac := by
  have h := r.map_add (ac.1, 0) (0, ac.2)
  simpa only [firstSummandMap_apply, Prod.mk_add_mk, add_zero, zero_add,
    secondSummand_eq_zero p hp r hker] using h.symm

theorem CuspCentralHomology.firstSummandMap_range {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    LinearMap.range (firstSummandMap r) = LinearMap.range r := by
  ext b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a, 0), ha⟩
  · rintro ⟨ac, hac⟩
    exact ⟨ac.1, (firstSummandMap_apply_fst p hp r hker ac).trans hac⟩

theorem CuspCentralHomology.eq_signedRightMap_of_apply {A C E : Type*} [AddCommGroup A]
    [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ C] [Module ℤ E]
    (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C) (hl : ∀ e, left e = (0, -p e)) :
    left = signedRightMap A p := by
  apply LinearMap.ext
  intro e
  exact hl e

theorem CuspCentralHomology.firstSummandMap_injective_of_signed_formula {A B C E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ E] (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C) (r : (A × C) →ₗ[ℤ] B)
    (hl : ∀ e, left e = (0, -p e)) (hexact : LinearMap.range left = LinearMap.ker r) :
    Function.Injective (firstSummandMap r) := by
  apply firstSummandMap_injective p r
  rw [← eq_signedRightMap_of_apply left p hl]
  exact hexact.symm

theorem CuspCentralHomology.firstSummandMap_range_of_signed_formula {A B C E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ E] (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C)
    (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B) (hl : ∀ e, left e = (0, -p e))
    (hexact : LinearMap.range left = LinearMap.ker r) :
    LinearMap.range (firstSummandMap r) = LinearMap.range r := by
  apply firstSummandMap_range p hp r
  rw [← eq_signedRightMap_of_apply left p hl]
  exact hexact.symm

def CuspCentralHomology.middleConnectingKernelEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
          1) ≃ₗ[ℤ]
      ℤ :=
  (middleLeftKernelEquiv C ε hε hε1 hC hR a ha ha1 0).trans
    ((compactFibreTorusHomologyEquiv 0).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ))

def CuspCentralHomology.middleQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 2 →ₗ[ℤ] ℤ :=
  (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).toLinearMap.comp
    (coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1)

theorem CuspCentralHomology.middleQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Function.Surjective (middleQuotientMap C ε hε hε1 hC hR a ha ha1) :=
  (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).surjective.comp
    (coverConnectingToKernel_surjective (outerRegion C ε hε a) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1)

theorem CuspCentralHomology.middleQuotientMap_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.ker (middleQuotientMap C ε hε hε1 hC hR a ha ha1) =
      LinearMap.ker
        (coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε)
          (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
          (outerRegion_union_innerRegion C ε hε a ha1) 1) := by
  ext x
  change
    middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1
          (coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε) _ _ _ 1 x) =
        0 ↔
      _
  constructor
  · intro hx
    apply (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).injective
    simpa only [map_zero] using hx
  · intro hx
    change coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε) _ _ _ 1 x = 0 at hx
    rw [hx, map_zero]

theorem CuspCentralHomology.middleOuterInclusion_eq_firstSummand
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2 =
      firstSummandMap
        (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2) := by
  apply LinearMap.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2 x =
      SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2 x +
        SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (innerRegion C ε hε)) 2 0
  rw [map_zero, add_zero]

theorem CuspCentralHomology.middleOuterInclusion_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2) := by
  rw [middleOuterInclusion_eq_firstSummand C ε hε a]
  exact
    firstSummandMap_injective_of_signed_formula
      (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) 2)
      (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 1)
      (SingularMayerVietoris.exact_at_pair (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) 2)

theorem CuspCentralHomology.middleOuterInclusion_range (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2) =
      LinearMap.range
        (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2) := by
  rw [middleOuterInclusion_eq_firstSummand C ε hε a]
  exact
    firstSummandMap_range_of_signed_formula
      (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) 2)
      (overlapIntoInner_homology_surjective C ε hε hε1 hC hR a ha ha1 1)
      (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 1)
      (SingularMayerVietoris.exact_at_pair (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) 2)

theorem CuspCentralHomology.middleSecondHomology_exact (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2) =
      LinearMap.ker (middleQuotientMap C ε hε hε1 hC hR a ha ha1) := by
  rw [middleOuterInclusion_range C ε hε hε1 hC hR a ha ha1, middleQuotientMap_ker]
  exact
    coverConnectingToKernel_exact (outerRegion C ε hε a) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1

def CuspCentralHomology.middleSecondHomologySplit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 2 ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology (outerRegion C ε hε a) 2 × ℤ) :=
  splitIntegerExtensionEquiv
    (SingularMayerVietoris.singularHomologyMap
      (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2)
    (middleQuotientMap C ε hε hε1 hC hR a ha ha1)
    (middleOuterInclusion_injective C ε hε hε1 hC hR a ha ha1)
    (middleQuotientMap_surjective C ε hε hε1 hC hR a ha ha1)
    (middleSecondHomology_exact C ε hε hε1 hC hR a ha ha1)

def CuspCentralHomology.middleIntegerFourEquiv : ((Fin 3 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ({    toFun p := ![p.1 0, p.1 1, p.1 2, p.2]
        invFun v := (![v 0, v 1, v 2], v 3)
        left_inv
          p := by
          apply Prod.ext
          · funext i
            fin_cases i <;> rfl
          · rfl
        right_inv
          v := by
          funext i
          fin_cases i <;> rfl
        map_add' p
          q := by
          funext i
          fin_cases i <;> rfl } :
      ((Fin 3 → ℤ) × ℤ) ≃+ (Fin 4 → ℤ)).toIntLinearEquiv

def CuspCentralHomology.middleOuterHomologyTwoEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (outerRegion C ε hε a) 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (outerRegionSuspensionHomotopyEquiv C ε hε hε1 hC hR a ha ha1) 2).trans
    threeCircleSuspensionHomologyTwoEquiv

def CuspCentralHomology.centralSingularH3Equiv_of_admissible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 3 ≃ₗ[ℤ]
      (Fin 2 → ℤ) := by
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 0
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 0
  exact
    ((coverConnectingKernelEquivOfVanishing (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
              (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)) (innerRegion_isOpen C ε hε hε1 hC hR)
              (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) 2).trans
          (middleLeftKernelEquiv C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 1)).trans
      (compactFibreTorusHomologyEquiv 1)

def CuspCentralHomology.centralSingularH2Equiv_of_admissible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 2 ≃ₗ[ℤ]
      (Fin 4 → ℤ) :=
  (((middleSecondHomologySplit C ε hε hε1 hC hR (1 / 2) (by norm_num)
              (by norm_num)).toAddEquiv.trans
          (AddEquiv.prodCongr
            (middleOuterHomologyTwoEquiv C ε hε hε1 hC hR (1 / 2) (by norm_num)
                (by norm_num)).toAddEquiv
            (AddEquiv.refl ℤ))).trans
      middleIntegerFourEquiv.toAddEquiv).toIntLinearEquiv

def CuspControlledRetraction.normalizedPosition (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : ToricSpace.Space) : (Fin 2 → ℝ) :=
  ToricSpace.realCuspVector
    (ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) (ToricSpace.time x)
      (ToricSpace.position x))

theorem CuspControlledRetraction.inverseDisplacement_positiveTwist_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) (‖t‖ : ℂ) =
      ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) t := by
  unfold ToricSpace.inverseDisplacement
  congr 1
  simp only [ToricSpace.displacementMatrix, CuspPositive.driftMatrix_positiveTwist,
    Complex.norm_of_nonneg (norm_nonneg t)]

theorem CuspControlledRetraction.realCuspVector_continuous :
    Continuous ToricSpace.realCuspVector := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 1
  · exact (continuous_apply 0).neg

theorem CuspControlledRetraction.normalizedPosition_continuousAt (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {ε : ℝ} (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    {x : ToricSpace.Space} (hx : ToricSpace.time x ≠ 0) (ht : ‖ToricSpace.time x‖ < ε) :
    ContinuousAt (normalizedPosition C₀) x := by
  have htpos : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx
  have hlog : Real.log ‖ToricSpace.time x‖ < 0 := Real.log_neg htpos (ht.trans hε1)
  have hinv :=
    ToricSpace.inverseDisplacement_continuousAt (CuspPositive.positiveTwist C₀)
      (fun _ _ => continuousAt_const) hlog (hR _ htpos ht) (ToricSpace.position x)
  have hp :
    ContinuousAt (fun y : ToricSpace.Space => (ToricSpace.time y, ToricSpace.position y)) x :=
    ToricSpace.time_holomorphic.continuous.continuousAt.prodMk
      (ToricSpace.position_continuousAt hx hlog.ne)
  exact
    realCuspVector_continuous.continuousAt.comp
      (ContinuousAt.comp (f := fun y : ToricSpace.Space =>
        (ToricSpace.time y, ToricSpace.position y)) (g := fun p : ℂ × (Fin 2 → ℝ) =>
        ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) p.1 p.2) hinv hp)

theorem CuspControlledRetraction.normalizedPosition_twistedTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x ≠ 0) (ht : ‖ToricSpace.time x‖ < ε) :
    normalizedPosition C₀ (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v x) =
      normalizedPosition C₀ x + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) := by
  have htpos : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx
  have hlog : Real.log ‖ToricSpace.time x‖ < 0 := Real.log_neg htpos (ht.trans hε1)
  unfold normalizedPosition
  rw [ToricSpace.time_twistedTranslate,
    ToricSpace.position_twistedTranslate_displacement (CuspPositive.positiveTwist C₀) v
      ((ToricSpace.mem_openTorus_iff x).mpr hx) hlog.ne,
    ToricSpace.inverseDisplacement_add,
    ToricSpace.inverseDisplacement_displacement (CuspPositive.positiveTwist C₀) hlog
      (hR _ htpos ht),
    map_add, ToricSpace.realCuspVector_latticeReal]
  rfl

theorem CuspControlledRetraction.normalizedPosition_closedPositive_continuousAt
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε)
    {q : ToricSpace.ClosedPositiveTube η} (hq : ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0) :
    ContinuousAt
      (fun r : ToricSpace.ClosedPositiveTube η => normalizedPosition C₀ (r.1 : ToricSpace.Space))
      q :=
  ContinuousAt.comp (f := fun r : ToricSpace.ClosedPositiveTube η => (r.1 : ToricSpace.Space))
    (g := normalizedPosition C₀) (normalizedPosition_continuousAt C₀ hε1 hR hq (q.2.trans_lt hηε))
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

theorem CuspControlledRetraction.normalizedPosition_closedPositive_continuousOn
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    ContinuousOn
      (fun q : ToricSpace.ClosedPositiveTube η => normalizedPosition C₀ (q.1 : ToricSpace.Space))
      {q | ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0} := by
  intro q hq
  exact (normalizedPosition_closedPositive_continuousAt C₀ hε1 hR hηε hq).continuousWithinAt

theorem CuspControlledRetraction.normalizedPosition_closedPositive_twistedTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    {q : ToricSpace.ClosedPositiveTube η} (hq : ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0) :
    normalizedPosition C₀ ((CuspPositive.closedPositiveTranslate C₀ η v q).1 : ToricSpace.Space) =
      normalizedPosition C₀ (q.1 : ToricSpace.Space) +
        CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) :=
  normalizedPosition_twistedTranslate C₀ hε1 hR v hq (q.2.trans_lt hηε)

noncomputable def CuspControlledRetraction.Interpolation.tentWeight (ρ r : ℝ) : ℝ :=
  Max.max 0 (1 - |r - ρ| / (ρ / 2))

theorem CuspControlledRetraction.Interpolation.tentWeight_continuous (ρ : ℝ) :
    Continuous (tentWeight ρ) :=
  continuous_const.max
    (continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const (ρ / 2)))

theorem CuspControlledRetraction.Interpolation.tentWeight_self (ρ : ℝ) : tentWeight ρ ρ = 1 := by
  simp [tentWeight]

theorem CuspControlledRetraction.Interpolation.tentWeight_eq_zero_of_half_le_abs {ρ : ℝ}
    (hρ : 0 < ρ) (r : ℝ) (hr : ρ / 2 ≤ |r - ρ|) : tentWeight ρ r = 0 := by
  apply max_eq_left
  have hdiv : 1 ≤ |r - ρ| / (ρ / 2) :=
    (le_div_iff₀ (half_pos hρ)).mpr (by simpa only [one_mul] using hr)
  linarith

theorem CuspControlledRetraction.Interpolation.tentWeight_eq_zero_of_le_half {ρ : ℝ} (hρ : 0 < ρ)
    (r : ℝ) (hr : r ≤ ρ / 2) : tentWeight ρ r = 0 := by
  apply tentWeight_eq_zero_of_half_le_abs hρ r
  linarith [neg_le_abs (r - ρ)]

noncomputable def CuspControlledRetraction.Interpolation.interpolate {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (p : unitInterval × X) : E :=
  a p.2 + ((p.1 : ℝ) * tentWeight ρ (h p.2)) • (b p.2 - a p.2)

theorem CuspControlledRetraction.Interpolation.interpolate_zero {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (x : X) :
    interpolate ρ h a b (0, x) = a x := by simp [interpolate]

theorem CuspControlledRetraction.Interpolation.interpolate_eq_left_of_height_le_half {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (s : unitInterval) (x : X) (hx : h x ≤ ρ / 2) : interpolate ρ h a b (s, x) = a x := by
  simp only [interpolate, tentWeight_eq_zero_of_le_half hρ (h x) hx, MulZeroClass.mul_zero,
    zero_smul, add_zero]

theorem CuspControlledRetraction.Interpolation.interpolate_fixed_of_height_zero {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (s : unitInterval) (x : X) (hx : h x = 0) : interpolate ρ h a b (s, x) = a x :=
  interpolate_eq_left_of_height_le_half ρ h a b hρ s x (by rw [hx]; exact (half_pos hρ).le)

theorem CuspControlledRetraction.Interpolation.interpolate_one_of_height_eq {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (x : X)
    (hx : h x = ρ) : interpolate ρ h a b (1, x) = b x := by
  simp [interpolate, hx, tentWeight_self]

theorem CuspControlledRetraction.Interpolation.interpolate_translate {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (T : X → X) (d : E) (hT : ∀ x, h (T x) = h x) (ha : ∀ x, a (T x) = a x + d)
    (hb : ∀ x, h x ≠ 0 → b (T x) = b x + d) (s : unitInterval) (x : X) :
    interpolate ρ h a b (s, T x) = interpolate ρ h a b (s, x) + d := by
  by_cases hx : h x = 0
  · rw [interpolate_fixed_of_height_zero ρ h a b hρ s (T x) ((hT x).trans hx),
      interpolate_fixed_of_height_zero ρ h a b hρ s x hx, ha x]
  · simp only [interpolate, hT x, ha x, hb x hx, add_sub_add_right_eq_sub]
    exact add_right_comm _ _ _

theorem CuspControlledRetraction.Interpolation.interpolate_continuous {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X] (ρ : ℝ) (h : X → ℝ)
    (a b : X → E) (hρ : 0 < ρ) (hh : Continuous h) (ha : Continuous a)
    (hb : ContinuousOn b {x : X | h x ≠ 0}) : Continuous (interpolate ρ h a b) := by
  have hw : Continuous (fun p : unitInterval × X => (p.1 : ℝ) * tentWeight ρ (h p.2)) :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((tentWeight_continuous ρ).comp (hh.comp continuous_snd))
  have hu : ContinuousOn (interpolate ρ h a b) {p : unitInterval × X | h p.2 ≠ 0} :=
    (ha.comp continuous_snd).continuousOn.add
      (hw.continuousOn.smul
        ((hb.comp continuous_snd.continuousOn (fun _ hp => hp)).sub
          (ha.comp continuous_snd).continuousOn))
  have hv : ContinuousOn (interpolate ρ h a b) {p : unitInterval × X | h p.2 < ρ / 2} :=
    (ha.comp continuous_snd).continuousOn.congr fun p hp =>
      interpolate_eq_left_of_height_le_half ρ h a b hρ p.1 p.2 hp.le
  have hcover :
    {p : unitInterval × X | h p.2 ≠ 0} ∪ {p : unitInterval × X | h p.2 < ρ / 2} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : h p.2 = 0
    · right
      change h p.2 < ρ / 2
      rw [hp]
      exact half_pos hρ
    · exact Or.inl hp
  rw [← continuousOn_univ, ← hcover]
  exact
    hu.union_of_isOpen hv (isOpen_ne_fun (hh.comp continuous_snd) continuous_const)
      (isOpen_Iio.preimage (hh.comp continuous_snd))

def CuspControlledRetraction.positiveHeight {η : ℝ} (q : ToricSpace.ClosedPositiveTube η) : ℝ :=
  ‖ToricSpace.time (q.1 : ToricSpace.Space)‖

theorem CuspControlledRetraction.positiveHeight_continuous {η : ℝ} :
    Continuous (positiveHeight : ToricSpace.ClosedPositiveTube η → ℝ) :=
  (ToricSpace.time_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).norm

theorem CuspControlledRetraction.positiveHeight_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    positiveHeight (CuspPositive.closedPositiveTranslate C₀ η v q) = positiveHeight q := by
  change
    ‖ToricSpace.time
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v
            (q.1 : ToricSpace.Space))‖ =
      _
  rw [ToricSpace.time_twistedTranslate]
  rfl

def CuspControlledRetraction.positiveEndpoint {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0) :
    C(ToricSpace.ClosedPositiveTube η, CuspPositiveRetraction.PositiveCentralFibre)
    where
  toFun q := ⟨(P (1, q)).1, hone q⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (P.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk
      _

def CuspControlledRetraction.endpointPosition {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(ToricSpace.ClosedPositiveTube η, CuspHoneycombTiling.Plane)
    where
  toFun q := (CuspHoneycomb.honeycombHomeomorph C₀).symm (positiveEndpoint P hone q)
  continuous_toFun :=
    (CuspHoneycomb.honeycombHomeomorph C₀).symm.continuous.comp
      (positiveEndpoint P hone).continuous

theorem CuspControlledRetraction.positiveEndpoint_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    positiveEndpoint P hone (CuspPositive.closedPositiveTranslate C₀ η v q) =
      CuspCollapse.positiveCentralTranslate C₀ v (positiveEndpoint P hone q) := by
  apply Subtype.ext
  exact congrArg (fun x : ToricSpace.ClosedPositiveTube η => x.1) (hequiv 1 v q)

theorem CuspControlledRetraction.endpointPosition_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    endpointPosition P hone C₀ (CuspPositive.closedPositiveTranslate C₀ η v q) =
      endpointPosition P hone C₀ q + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) :=
  by
  change
    (CuspHoneycomb.honeycombHomeomorph C₀).symm
        (positiveEndpoint P hone (CuspPositive.closedPositiveTranslate C₀ η v q)) =
      _
  rw [positiveEndpoint_equivariant P hone C₀ hequiv,
    CuspHoneycomb.honeycombHomeomorph_symm_equivariant]
  rfl

private theorem CuspControlledRetraction.normalizedPosition_height_continuousOn_mo1973_13101
    {η : ℝ} (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    ContinuousOn
      (fun q : ToricSpace.ClosedPositiveTube η => normalizedPosition C₀ (q.1 : ToricSpace.Space))
      {q | positiveHeight q ≠ 0} := by
  simpa only [positiveHeight, ne_eq, norm_eq_zero] using
    normalizedPosition_closedPositive_continuousOn C₀ hε1 hR hηε

def CuspControlledRetraction.centralInterpolation {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) :
    C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η)
    where
  toFun
    p :=
    CuspPositiveRetraction.positiveCentralInclusion η hη
      (CuspHoneycomb.honeycombHomeomorph C₀
        (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
          (fun q => normalizedPosition C₀ (q.1 : ToricSpace.Space)) p))
  continuous_toFun :=
    (CuspPositiveRetraction.positiveCentralInclusion η hη).continuous.comp
      ((CuspHoneycomb.honeycombHomeomorph C₀).continuous.comp
        (Interpolation.interpolate_continuous ρ positiveHeight (endpointPosition P hone C₀)
          (fun q => normalizedPosition C₀ (q.1 : ToricSpace.Space)) hρ positiveHeight_continuous
          (endpointPosition P hone C₀).continuous
          (normalizedPosition_height_continuousOn_mo1973_13101 C₀ hε1 hR hηε)))

theorem CuspControlledRetraction.centralInterpolation_apply {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) =
      CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀
          (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
            (fun r => normalizedPosition C₀ (r.1 : ToricSpace.Space)) (s, q))) :=
  rfl

theorem CuspControlledRetraction.centralInterpolation_zero {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (q : ToricSpace.ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (0, q) = P (1, q) := by
  rw [centralInterpolation_apply, Interpolation.interpolate_zero]
  change
    CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀
          ((CuspHoneycomb.honeycombHomeomorph C₀).symm (positiveEndpoint P hone q))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem CuspControlledRetraction.centralInterpolation_central {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η) :
    ToricSpace.time
        ((centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)).1 : ToricSpace.Space) =
      0 :=
  (CuspHoneycomb.honeycombHomeomorph C₀
      (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
        (fun r => normalizedPosition C₀ (r.1 : ToricSpace.Space)) (s, q))).2

theorem CuspControlledRetraction.centralInterpolation_eq_endpoint_of_height_le_half {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η)
    (hq : positiveHeight q ≤ ρ / 2) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) = P (1, q) := by
  rw [centralInterpolation_apply,
    Interpolation.interpolate_eq_left_of_height_le_half _ _ _ _ hρ s q hq]
  change
    CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀
          ((CuspHoneycomb.honeycombHomeomorph C₀).symm (positiveEndpoint P hone q))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem CuspControlledRetraction.centralInterpolation_fixed {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hfix : ∀ s q, ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η)
    (hq : ToricSpace.time (q.1 : ToricSpace.Space) = 0) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) = q := by
  rw [centralInterpolation_eq_endpoint_of_height_le_half P hone C₀ hε1 hR hηε hη ρ hρ s q
      (by simpa only [positiveHeight, hq, norm_zero] using (half_pos hρ).le)]
  exact hfix 1 q hq

theorem CuspControlledRetraction.centralInterpolation_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ
        (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
      CuspPositive.closedPositiveTranslate C₀ η v
        (centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)) := by
  have he :=
    Interpolation.interpolate_translate ρ positiveHeight (endpointPosition P hone C₀)
      (fun q => normalizedPosition C₀ (q.1 : ToricSpace.Space)) hρ
      (CuspPositive.closedPositiveTranslate C₀ η v)
      (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))
      (positiveHeight_translate C₀ η v) (endpointPosition_equivariant P hone C₀ hequiv v)
      (fun q hq =>
        normalizedPosition_closedPositive_twistedTranslate C₀ hε1 hR hηε v
          (norm_ne_zero_iff.mp hq))
      s q
  rw [centralInterpolation_apply, he, CuspHoneycomb.honeycombHomeomorph_equivariant]
  rfl

theorem CuspControlledRetraction.centralInterpolation_nonincreasing {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η) :
    positiveHeight (centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)) ≤
      positiveHeight q := by
  change
    ‖ToricSpace.time
          ((centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)).1 : ToricSpace.Space)‖ ≤
      _
  rw [centralInterpolation_central, norm_zero]
  exact norm_nonneg _

theorem CuspControlledRetraction.centralInterpolation_one_of_height_eq {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (q : ToricSpace.ClosedPositiveTube η) (hq : positiveHeight q = ρ) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (1, q) =
      CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : ToricSpace.Space))) :=
  by rw [centralInterpolation_apply, Interpolation.interpolate_one_of_height_eq _ _ _ _ q hq]

def CuspControlledRetraction.Concatenation.slice {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P : C(unitInterval × X, Y)) (s : unitInterval) : C(X, Y) :=
  ⟨fun x => P (s, x), P.continuous.comp (continuous_const.prodMk continuous_id)⟩

def CuspControlledRetraction.Concatenation.asHomotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P : C(unitInterval × X, Y)) : (slice P 0).Homotopy (slice P 1)
    where
  toContinuousMap := P
  map_zero_left _ := rfl
  map_one_left _ := rfl

def CuspControlledRetraction.Concatenation.connectingHomotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x)) :
    (slice P 1).Homotopy (slice K 1)
    where
  toContinuousMap := K
  map_zero_left := hjoin
  map_one_left _ := rfl

def CuspControlledRetraction.Concatenation.map {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x)) :
    C(unitInterval × X, Y) :=
  ((asHomotopy P).trans (connectingHomotopy P K hjoin)).toContinuousMap

@[simp]
theorem CuspControlledRetraction.Concatenation.map_zero {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x))
    (x : X) : CuspControlledRetraction.Concatenation.map P K hjoin (0, x) = P (0, x) :=
  ContinuousMap.Homotopy.apply_zero _ x

@[simp]
theorem CuspControlledRetraction.Concatenation.map_one {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x))
    (x : X) : CuspControlledRetraction.Concatenation.map P K hjoin (1, x) = K (1, x) :=
  ContinuousMap.Homotopy.apply_one _ x

theorem CuspControlledRetraction.Concatenation.map_property {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P K : C(unitInterval × X, Y)) (hjoin : ∀ x, K (0, x) = P (1, x))
    (R : C(X, Y) → Prop) (hP : ∀ s, R (slice P s)) (hK : ∀ s, R (slice K s)) (s : unitInterval) :
    R (slice (CuspControlledRetraction.Concatenation.map P K hjoin) s) := by
  let F : (slice P 0).HomotopyWith (slice P 1) R :=
    { toHomotopy := asHomotopy P
      prop' := hP }
  let G : (slice P 1).HomotopyWith (slice K 1) R :=
    { toHomotopy := connectingHomotopy P K hjoin
      prop' := hK }
  exact (F.trans G).prop s

theorem CuspControlledRetraction.exists_positive_modification (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (hηε : η < ε) (hη : 0 ≤ η) (ρ : ℝ) (hρ : 0 < ρ)
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hzero : ∀ q, P (0, q) = q)
    (hfix :
      ∀ s (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (hmono : ∀ s q, positiveHeight (P (s, q)) ≤ positiveHeight q) :
    ∃ Q : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η),
      (∀ q, Q (0, q) = q) ∧
        (∀ s (q : ToricSpace.ClosedPositiveTube η),
            ToricSpace.time (q.1 : ToricSpace.Space) = 0 → Q (s, q) = q) ∧
          (∀ q : ToricSpace.ClosedPositiveTube η,
              ToricSpace.time ((Q (1, q)).1 : ToricSpace.Space) = 0) ∧
            (∀ s v q,
                Q (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
                  CuspPositive.closedPositiveTranslate C₀ η v (Q (s, q))) ∧
              (∀ s q, positiveHeight (Q (s, q)) ≤ positiveHeight q) ∧
                (∀ q,
                    positiveHeight q = ρ →
                      Q (1, q) =
                        CuspPositiveRetraction.positiveCentralInclusion η hη
                          (CuspHoneycomb.honeycombHomeomorph C₀
                            (normalizedPosition C₀ (q.1 : ToricSpace.Space)))) ∧
                  (∀ q, positiveHeight q ≤ ρ / 2 → Q (1, q) = P (1, q)) := by
  let K := centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ
  have hjoin : ∀ q, K (0, q) = P (1, q) := centralInterpolation_zero P hone C₀ hε1 hR hηε hη ρ hρ
  let Q := Concatenation.map P K hjoin
  let R : C(ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η) → Prop := fun f =>
    (∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → f q = q) ∧
      (∀ v q,
          f (CuspPositive.closedPositiveTranslate C₀ η v q) =
            CuspPositive.closedPositiveTranslate C₀ η v (f q)) ∧
        (∀ q, positiveHeight (f q) ≤ positiveHeight q)
  have hQP (s : unitInterval) : R (Concatenation.slice Q s) := by
    apply Concatenation.map_property P K hjoin R
    · intro t
      exact ⟨hfix t, hequiv t, hmono t⟩
    · intro t
      exact
        ⟨centralInterpolation_fixed P hone C₀ hε1 hR hηε hη ρ hρ hfix t,
          centralInterpolation_equivariant P hone C₀ hε1 hR hηε hη ρ hρ hequiv t,
          centralInterpolation_nonincreasing P hone C₀ hε1 hR hηε hη ρ hρ t⟩
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    exact (Concatenation.map_zero P K hjoin q).trans (hzero q)
  · intro s q hq
    exact (hQP s).1 q hq
  · intro q
    change ToricSpace.time (((Concatenation.map P K hjoin) (1, q)).1 : ToricSpace.Space) = 0
    rw [Concatenation.map_one]
    exact centralInterpolation_central P hone C₀ hε1 hR hηε hη ρ hρ 1 q
  · intro s v q
    exact (hQP s).2.1 v q
  · intro s q
    exact (hQP s).2.2 q
  · intro q hq
    exact
      (Concatenation.map_one P K hjoin q).trans
        (centralInterpolation_one_of_height_eq P hone C₀ hε1 hR hηε hη ρ hρ q hq)
  · intro q hq
    exact
      (Concatenation.map_one P K hjoin q).trans
        (centralInterpolation_eq_endpoint_of_height_le_half P hone C₀ hε1 hR hηε hη ρ hρ 1 q hq)

theorem CuspControlledRetraction.exists_positive_controlled_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ (η : ℝ) (hη : 0 < η),
            η ≤ η₀ →
              ∀ ρ : ℝ,
                0 < ρ →
                  ρ ≤ η →
                    ∃ P :
                      C(unitInterval × ToricSpace.ClosedPositiveTube η,
                        ToricSpace.ClosedPositiveTube η),
                      (∀ q, P (0, q) = q) ∧
                        (∀ s (q : ToricSpace.ClosedPositiveTube η),
                            ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) ∧
                          (∀ q : ToricSpace.ClosedPositiveTube η,
                              ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0) ∧
                            (∀ s v q,
                                P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
                                  CuspPositive.closedPositiveTranslate C₀ η v (P (s, q))) ∧
                              (∀ s q,
                                  ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
                                    ‖ToricSpace.time (q.1 : ToricSpace.Space)‖) ∧
                                (∀ q,
                                  ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ = ρ →
                                    P (1, q) =
                                      CuspPositiveRetraction.positiveCentralInclusion η hη.le
                                        (CuspHoneycomb.honeycombHomeomorph C₀
                                          (normalizedPosition C₀ (q.1 : ToricSpace.Space)))) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ :=
    CuspPositiveRetraction.exists_positive_closed_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀ ρ hρ _hρη
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono⟩ := hP η hη hηη₀
  obtain ⟨Q, hQzero, hQfix, hQone, hQequiv, hQmono, hQend, _hQnear⟩ :=
    exists_positive_modification C₀ hε1 hR (hηη₀.trans_lt hη₀ε) hη.le ρ hρ P hzero hfix hone
      hequiv hmono
  exact ⟨Q, hQzero, hQfix, hQone, hQequiv, hQmono, hQend⟩

def CuspControlledRetraction.polarDeformation {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q) :
    C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η) :=
  ⟨fun p => CuspRetraction.polarSpread P p.1 p.2, CuspRetraction.polarSpread_continuous P hfix⟩

theorem CuspControlledRetraction.polarDeformation_closedPolarMap {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (φ : ToricSpace.CompactTorus) (q : ToricSpace.ClosedPositiveTube η) :
    polarDeformation P hfix (s, ToricSpace.closedPolarMap η (φ, q)) =
      ToricSpace.closedPolarMap η (φ, P (s, q)) :=
  CuspRetraction.polarSpread_closedPolarMap P hfix s (φ, q)

theorem CuspControlledRetraction.polarDeformation_properties (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (hzero : ∀ q : ToricSpace.ClosedPositiveTube η, P (0, q) = q)
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (hequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η),
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (hmono :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ‖ToricSpace.time ((P (s, q)).1 : ToricSpace.Space)‖ ≤
          ‖ToricSpace.time (q.1 : ToricSpace.Space)‖) :
    (∀ x, polarDeformation P hfix (0, x) = x) ∧
      (∀ s (x : CuspRetraction.ClosedTube η),
          ToricSpace.time (x : ToricSpace.Space) = 0 → polarDeformation P hfix (s, x) = x) ∧
        (∀ x, ToricSpace.time (polarDeformation P hfix (1, x) : ToricSpace.Space) = 0) ∧
          (∀ s v x,
              polarDeformation P hfix (s, CuspRetraction.closedTranslate (fun _ => C₀) η v x) =
                CuspRetraction.closedTranslate (fun _ => C₀) η v
                  (polarDeformation P hfix (s, x))) ∧
            (∀ s φ x,
                polarDeformation P hfix (s, CuspRetraction.closedCompactAction η φ x) =
                  CuspRetraction.closedCompactAction η φ (polarDeformation P hfix (s, x))) ∧
              (∀ s (u : Fin 2 → ℂˣ),
                  (∀ i, ‖(u i : ℂ)‖ = 1) →
                    ∀ x,
                      polarDeformation P hfix (s, CuspRetraction.closedFibreAction η u x) =
                        CuspRetraction.closedFibreAction η u (polarDeformation P hfix (s, x))) ∧
                (∀ s x,
                  ‖ToricSpace.time (polarDeformation P hfix (s, x) : ToricSpace.Space)‖ ≤
                    ‖ToricSpace.time (x : ToricSpace.Space)‖) :=
  ⟨CuspRetraction.polarSpread_zero P hfix hzero, CuspRetraction.polarSpread_fixed P hfix,
    CuspRetraction.polarSpread_one_central P hfix hone,
    CuspRetraction.polarSpread_frozen_equivariant C₀ P hfix hequiv,
    CuspRetraction.polarSpread_compactTorus_equivariant P hfix,
    CuspRetraction.polarSpread_fibre_torus_equivariant P hfix,
    CuspRetraction.polarSpread_norm_time_le P hfix hmono⟩

abbrev CuspControlledRetraction.PuncturedPositiveTube (η : ℝ) :=
  { q : ToricSpace.ClosedPositiveTube η // ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0 }

abbrev CuspControlledRetraction.PuncturedClosedTube (η : ℝ) :=
  { x : CuspRetraction.ClosedTube η // ToricSpace.time (x : ToricSpace.Space) ≠ 0 }

theorem CuspControlledRetraction.puncturedPolarMap_mem_iff (η : ℝ)
    (p : ToricSpace.CompactTorus × ToricSpace.ClosedPositiveTube η) :
    ToricSpace.closedPolarMap η p ∈
        {x : CuspRetraction.ClosedTube η | ToricSpace.time (x : ToricSpace.Space) ≠ 0} ↔
      p.2 ∈
        {q : ToricSpace.ClosedPositiveTube η | ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0} := by
  change
    ToricSpace.time (ToricSpace.compactTorusAction p.1 (p.2.1 : ToricSpace.Space)) ≠ 0 ↔
      ToricSpace.time (p.2.1 : ToricSpace.Space) ≠ 0
  rw [← norm_ne_zero_iff, ToricSpace.norm_time_compactTorusAction, norm_ne_zero_iff]

def CuspControlledRetraction.puncturedPolarMap (η : ℝ) :
    ToricSpace.CompactTorus × PuncturedPositiveTube η → PuncturedClosedTube η :=
  ProductRestriction.productRestriction (ToricSpace.closedPolarMap η)
    {q : ToricSpace.ClosedPositiveTube η | ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0}
    {x : CuspRetraction.ClosedTube η | ToricSpace.time (x : ToricSpace.Space) ≠ 0}
    (puncturedPolarMap_mem_iff η)

@[simp]
theorem CuspControlledRetraction.puncturedPolarMap_closed_coe (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarMap η p : CuspRetraction.ClosedTube η) =
      ToricSpace.closedPolarMap η (p.1, p.2.1) :=
  rfl

@[simp]
theorem CuspControlledRetraction.norm_time_puncturedPolarMap (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    ‖ToricSpace.time ((puncturedPolarMap η p).1 : ToricSpace.Space)‖ =
      ‖ToricSpace.time (p.2.1.1 : ToricSpace.Space)‖ :=
  ToricSpace.norm_time_compactTorusAction p.1 (p.2.1.1 : ToricSpace.Space)

theorem CuspControlledRetraction.puncturedPolarMap_continuous (η : ℝ) :
    Continuous (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_continuous _ _ _ _
    (ToricSpace.closedPolarMap_continuous η)

theorem CuspControlledRetraction.puncturedPolarMap_isClosedMap (η : ℝ) :
    IsClosedMap (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_isClosedMap _ _ _ _
    (ToricSpace.closedPolarMap_isClosedMap η)

theorem CuspControlledRetraction.puncturedPolarMap_surjective (η : ℝ) :
    Function.Surjective (puncturedPolarMap η) :=
  ProductRestriction.productRestriction_surjective _ _ _ _
    (ToricSpace.closedPolarMap_surjective η)

theorem CuspControlledRetraction.puncturedPolarMap_injective (η : ℝ) :
    Function.Injective (puncturedPolarMap η) := by
  rintro ⟨u, q⟩ ⟨v, r⟩ h
  have hclosed : ToricSpace.closedPolarMap η (u, q.1) = ToricSpace.closedPolarMap η (v, r.1) :=
    congrArg Subtype.val h
  have hqr : q = r := by
    apply Subtype.ext
    simpa only [ToricSpace.closedModulusRetraction_closedPolarMap] using
      congrArg (ToricSpace.closedModulusRetraction η) hclosed
  subst r
  have huv : u = v :=
    ToricSpace.compactTorusAction_injective_of_time_ne_zero q.property
      (congrArg (fun x : CuspRetraction.ClosedTube η => (x : ToricSpace.Space)) hclosed)
  exact Prod.ext huv rfl

theorem CuspControlledRetraction.puncturedPolarMap_bijective (η : ℝ) :
    Function.Bijective (puncturedPolarMap η) :=
  ⟨puncturedPolarMap_injective η, puncturedPolarMap_surjective η⟩

def CuspControlledRetraction.puncturedPolarHomeomorph (η : ℝ) :
    (ToricSpace.CompactTorus × PuncturedPositiveTube η) ≃ₜ PuncturedClosedTube η :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (puncturedPolarMap η) (puncturedPolarMap_bijective η))
    (puncturedPolarMap_continuous η) (puncturedPolarMap_isClosedMap η)

@[simp]
theorem CuspControlledRetraction.puncturedPolarHomeomorph_symm_map (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    (puncturedPolarHomeomorph η).symm (puncturedPolarMap η p) = p :=
  (puncturedPolarHomeomorph η).symm_apply_apply p

@[simp]
theorem CuspControlledRetraction.puncturedPolarMap_symm (η : ℝ) (x : PuncturedClosedTube η) :
    puncturedPolarMap η ((puncturedPolarHomeomorph η).symm x) = x :=
  (puncturedPolarHomeomorph η).apply_symm_apply x

@[simp]
theorem CuspControlledRetraction.puncturedPolarHomeomorph_symm_positive_coe (η : ℝ)
    (x : PuncturedClosedTube η) :
    ((puncturedPolarHomeomorph η).symm x).2.1 = ToricSpace.closedModulusRetraction η x.1 := by
  have h :=
    congrArg (fun y : PuncturedClosedTube η => ToricSpace.closedModulusRetraction η y.1)
      (puncturedPolarMap_symm η x)
  simpa only [puncturedPolarMap_closed_coe,
    ToricSpace.closedModulusRetraction_closedPolarMap] using h

def CuspControlledRetraction.centralCompactPolar
    (p : ToricSpace.CompactTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    CuspRetraction.CentralFibre :=
  ⟨ToricSpace.compactTorusAction p.1 (p.2.1 : ToricSpace.Space), by
    simp only [ToricSpace.compactTorusAction, ToricSpace.time_torusAction, p.2.2,
      MulZeroClass.mul_zero]⟩

theorem CuspControlledRetraction.centralCompactPolar_continuous :
    Continuous centralCompactPolar :=
  (ToricSpace.compactTorusAction_continuous.comp
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))).subtype_mk
    _

@[simp]
theorem CuspControlledRetraction.centralModulus_centralCompactPolar
    (p : ToricSpace.CompactTorus × CuspPositiveRetraction.PositiveCentralFibre) :
    CuspCollapse.centralModulus (centralCompactPolar p) = p.2 := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ToricSpace.modulus (ToricSpace.compactTorusAction p.1 (p.2.1 : ToricSpace.Space)) =
      (p.2.1 : ToricSpace.Space)
  rw [ToricSpace.modulus_compactTorusAction]
  exact p.2.1.2

def CuspControlledRetraction.prescribedPositiveCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (q : PuncturedPositiveTube η) : CuspPositiveRetraction.PositiveCentralFibre :=
  CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : ToricSpace.Space))

def CuspControlledRetraction.prescribedPolarCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) : CuspRetraction.CentralFibre :=
  centralCompactPolar (p.1, prescribedPositiveCollapse C₀ η p.2)

def CuspControlledRetraction.prescribedCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) : CuspRetraction.CentralFibre :=
  prescribedPolarCollapse C₀ η ((puncturedPolarHomeomorph η).symm x)

@[simp]
theorem CuspControlledRetraction.prescribedCollapse_puncturedPolarMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (p : ToricSpace.CompactTorus × PuncturedPositiveTube η) :
    prescribedCollapse C₀ η (puncturedPolarMap η p) = prescribedPolarCollapse C₀ η p := by
  unfold prescribedCollapse
  rw [puncturedPolarHomeomorph_symm_map]

theorem CuspControlledRetraction.prescribedCollapse_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (u : ToricSpace.CompactTorus) (q : PuncturedPositiveTube η) :
    (prescribedCollapse C₀ η (puncturedPolarMap η (u, q)) : ToricSpace.Space) =
      ToricSpace.compactTorusAction u
        ((CuspHoneycomb.honeycombHomeomorph C₀
              (normalizedPosition C₀ (q.1.1 : ToricSpace.Space))).1 :
          ToricSpace.Space) := by
  rw [prescribedCollapse_puncturedPolarMap]
  rfl

@[simp]
theorem CuspControlledRetraction.prescribedCollapse_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (x : PuncturedClosedTube η) :
    CuspCollapse.centralModulus (prescribedCollapse C₀ η x) =
      prescribedPositiveCollapse C₀ η ((puncturedPolarHomeomorph η).symm x).2 :=
  centralModulus_centralCompactPolar _

theorem CuspControlledRetraction.normalizedPosition_puncturedPositive_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    Continuous
      (fun q : PuncturedPositiveTube η => normalizedPosition C₀ (q.1.1 : ToricSpace.Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact
    (normalizedPosition_closedPositive_continuousAt C₀ hε1 hR hηε q.2).comp
      continuous_subtype_val.continuousAt

theorem CuspControlledRetraction.prescribedPositiveCollapse_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    Continuous (prescribedPositiveCollapse C₀ η) :=
  (CuspHoneycomb.honeycombHomeomorph C₀).continuous.comp
    (normalizedPosition_puncturedPositive_continuous C₀ hε1 hR hηε)

theorem CuspControlledRetraction.prescribedPolarCollapse_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    Continuous (prescribedPolarCollapse C₀ η) :=
  centralCompactPolar_continuous.comp
    (continuous_fst.prodMk
      ((prescribedPositiveCollapse_continuous C₀ hε1 hR hηε).comp continuous_snd))

theorem CuspControlledRetraction.prescribedCollapse_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (hηε : η < ε) : Continuous (prescribedCollapse C₀ η) :=
  (prescribedPolarCollapse_continuous C₀ hε1 hR hηε).comp
    (puncturedPolarHomeomorph η).symm.continuous

theorem CuspControlledRetraction.polarDeformation_prescribedCollapse_of_puncturedEndpoint
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd :
      ∀ q : PuncturedPositiveTube η,
        ‖ToricSpace.time (q.1.1 : ToricSpace.Space)‖ = ρ →
          P (1, q.1) =
            CuspPositiveRetraction.positiveCentralInclusion η hη
              (prescribedPositiveCollapse C₀ η q))
    (x : PuncturedClosedTube η) (hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ) :
    polarDeformation P hfix (1, x.1) =
      CuspRetraction.centralIntoClosedTube η hη (prescribedCollapse C₀ η x) := by
  obtain ⟨⟨φ, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  have hq : ‖ToricSpace.time (q.1.1 : ToricSpace.Space)‖ = ρ := by
    simpa only [norm_time_puncturedPolarMap] using hx
  apply Subtype.ext
  change
    (polarDeformation P hfix (1, ToricSpace.closedPolarMap η (φ, q.1)) : ToricSpace.Space) =
      (prescribedCollapse C₀ η (puncturedPolarMap η (φ, q)) : ToricSpace.Space)
  rw [polarDeformation_closedPolarMap, hEnd q hq, prescribedCollapse_polar]
  rfl

theorem CuspControlledRetraction.polarDeformation_prescribedCollapse
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hfix :
      ∀ (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η),
        ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (ρ : ℝ) (hη : 0 ≤ η)
    (hEnd :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ = ρ →
          P (1, q) =
            CuspPositiveRetraction.positiveCentralInclusion η hη
              (CuspHoneycomb.honeycombHomeomorph C₀
                (normalizedPosition C₀ (q.1 : ToricSpace.Space))))
    (x : PuncturedClosedTube η) (hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ) :
    polarDeformation P hfix (1, x.1) =
      CuspRetraction.centralIntoClosedTube η hη (prescribedCollapse C₀ η x) :=
  polarDeformation_prescribedCollapse_of_puncturedEndpoint C₀ P hfix ρ hη
    (fun q hq => hEnd q.1 hq) x hx

theorem CuspControlledRetraction.exists_frozen_controlled_deformation_below
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < ε ∧
          ∀ (η : ℝ) (hη : 0 < η),
            η ≤ η₀ →
              ∀ ρ : ℝ,
                0 < ρ →
                  ρ ≤ η →
                    ∃ H :
                      C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η),
                      (∀ x, H (0, x) = x) ∧
                        (∀ s (x : CuspRetraction.ClosedTube η),
                            ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                          (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                            (∀ s v x,
                                H (s, CuspRetraction.closedTranslate (fun _ => C₀) η v x) =
                                  CuspRetraction.closedTranslate (fun _ => C₀) η v (H (s, x))) ∧
                              (∀ s φ x,
                                  H (s, CuspRetraction.closedCompactAction η φ x) =
                                    CuspRetraction.closedCompactAction η φ (H (s, x))) ∧
                                (∀ s (u : Fin 2 → ℂˣ),
                                    (∀ i, ‖(u i : ℂ)‖ = 1) →
                                      ∀ x,
                                        H (s, CuspRetraction.closedFibreAction η u x) =
                                          CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                                  (∀ s x,
                                      ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                        ‖ToricSpace.time (x : ToricSpace.Space)‖) ∧
                                    (∀ x : PuncturedClosedTube η,
                                      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
                                        H (1, x.1) =
                                          CuspRetraction.centralIntoClosedTube η hη.le
                                            (prescribedCollapse C₀ η x)) := by
  obtain ⟨η₀, hη₀, hη₀ε, hP⟩ := exists_positive_controlled_deformation_below C₀ ε hε hε1 hR
  refine ⟨η₀, hη₀, hη₀ε, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  obtain ⟨P, hzero, hfix, hone, hequiv, hmono, hEnd⟩ := hP η hη hηη₀ ρ hρ hρη
  obtain ⟨hHzero, hHfix, hHone, hHequiv, hHcompact, hHfibre, hHmono⟩ :=
    polarDeformation_properties C₀ P hfix hzero hone hequiv hmono
  refine ⟨polarDeformation P hfix, hHzero, hHfix, hHone, hHequiv, hHcompact, hHfibre, hHmono, ?_⟩
  exact polarDeformation_prescribedCollapse C₀ P hfix ρ hη.le hEnd

theorem CuspControlledRetraction.closedHomotopyDescentRetraction_endpoint_of_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hHequiv :
      ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : CuspRetraction.ClosedTube η),
        H (s, CuspRetraction.closedTranslate C η v x) =
          CuspRetraction.closedTranslate C η v (H (s, x)))
    (hCanalytic : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hone : ∀ x : CuspRetraction.ClosedTube η, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0)
    (hη : 0 ≤ η) (x : CuspRetraction.ClosedTube η) (y : CuspRetraction.CentralFibre)
    (hEndx : H (1, x) = CuspRetraction.centralIntoClosedTube η hη y) :
    (CuspRetraction.closedHomotopyDescentRetraction C hηε H hHequiv hCanalytic hone
          (CuspRetraction.closedQuotientMap C hηε x) :
        CuspQuotient.QuotientSpace C ε) =
      (CuspRetraction.closedQuotientMap C hηε (CuspRetraction.centralIntoClosedTube η hη y) :
        CuspQuotient.QuotientSpace C ε) := by
  change
    (CuspRetraction.closedHomotopyDescent C hηε H 1 (CuspRetraction.closedQuotientMap C hηε x) :
        CuspQuotient.QuotientSpace C ε) =
      _
  rw [CuspRetraction.closedHomotopyDescent_closedQuotientMap C hηε H hHequiv, hEndx]

theorem CuspControlledRetraction.closedFrozenStraightening_symm_fixed
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hCcont : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (x : CuspRetraction.ClosedTube η)
    (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    ((CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε)).symm x = x :=
  by
  apply ((CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε)).injective
  rw [((CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD
        hηε)).apply_symm_apply,
    CuspPositiveRetraction.closedFrozenStraightening_fixed C hε hε1 hCcont hRC hRD hηε x hx]

theorem CuspControlledRetraction.straightenedHomotopy_endpoint_of_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hCcont : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hη : 0 ≤ η) (x : CuspRetraction.ClosedTube η) (y : CuspRetraction.CentralFibre)
    (he :
      H (1, (CuspPositiveRetraction.closedFrozenStraightening C hε hε1 hCcont hRC hRD hηε) x) =
        CuspRetraction.centralIntoClosedTube η hη y) :
    (CuspPositiveRetraction.straightenedHomotopy C hε hε1 hCcont hRC hRD hηε H) (1, x) =
      CuspRetraction.centralIntoClosedTube η hη y := by
  rw [CuspPositiveRetraction.straightenedHomotopy_apply, he]
  exact
    closedFrozenStraightening_symm_fixed C hε hε1 hCcont hRC hRD hηε
      (CuspRetraction.centralIntoClosedTube η hη y) y.2

def CuspControlledRetraction.puncturedStraightening (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨CuspRetraction.closedTubeChangeTwist C (CuspRetraction.frozen C) η x.1,
    by
    change
      ToricSpace.time
          (CuspRetraction.changeTwist C (CuspRetraction.frozen C) (x.1 : ToricSpace.Space)) ≠
        0
    rw [CuspRetraction.time_changeTwist]
    exact x.2⟩

theorem CuspControlledRetraction.puncturedStraightening_base (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (x : PuncturedClosedTube η) :
    ToricSpace.time ((puncturedStraightening C η x).1 : ToricSpace.Space) =
      ToricSpace.time (x.1 : ToricSpace.Space) :=
  CuspRetraction.time_changeTwist C (CuspRetraction.frozen C) (x.1 : ToricSpace.Space)

def CuspControlledRetraction.straightenedPrescribedCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) : PuncturedClosedTube η → CuspRetraction.CentralFibre :=
  prescribedCollapse (C 0) η ∘ puncturedStraightening C η

theorem CuspControlledRetraction.puncturedStraightening_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hηε : η < ε) : Continuous (puncturedStraightening C η) := by
  apply Continuous.subtype_mk
  exact
    (CuspRetraction.closedTubeChangeTwist_continuous C (CuspRetraction.frozen C) hε hε1 hC
          (fun _ _ => continuousOn_const) rfl hRC hηε).comp
      continuous_subtype_val

theorem CuspControlledRetraction.straightenedPrescribedCollapse_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) : Continuous (straightenedPrescribedCollapse C η) :=
  (prescribedCollapse_continuous (C 0) hε1 (CuspPositive.smallDrift_positiveTwist (C 0) hRD)
        hηε).comp
    (puncturedStraightening_continuous C hε hε1 hC hRC hηε)

theorem CuspControlledRetraction.straightenedHomotopy_prescribed_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (hηε : η < ε) (H : C(unitInterval × CuspRetraction.ClosedTube η, CuspRetraction.ClosedTube η))
    (hη : 0 ≤ η) {ρ : ℝ}
    (hEnd :
      ∀ x : PuncturedClosedTube η,
        ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
          H (1, x.1) = CuspRetraction.centralIntoClosedTube η hη (prescribedCollapse (C 0) η x))
    (x : PuncturedClosedTube η) (hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ) :
    CuspPositiveRetraction.straightenedHomotopy C hε hε1 hC hRC hRD hηε H (1, x.1) =
      CuspRetraction.centralIntoClosedTube η hη (straightenedPrescribedCollapse C η x) := by
  apply
    straightenedHomotopy_endpoint_of_eq C hε hε1 hC hRC hRD hηε H hη x.1
      (straightenedPrescribedCollapse C η x)
  exact
    hEnd (puncturedStraightening C η x)
      ((congrArg Norm.norm (puncturedStraightening_base C η x)).trans hx)

theorem CuspControlledRetraction.exists_closed_tube_controlled_deformation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ ρ : ℝ,
                  0 < ρ →
                    ρ ≤ η →
                      ∃ H :
                        C(unitInterval × CuspRetraction.ClosedTube η,
                          CuspRetraction.ClosedTube η),
                        (∀ x, H (0, x) = x) ∧
                          (∀ s (x : CuspRetraction.ClosedTube η),
                              ToricSpace.time (x : ToricSpace.Space) = 0 → H (s, x) = x) ∧
                            (∀ x, ToricSpace.time (H (1, x) : ToricSpace.Space) = 0) ∧
                              (∀ s v x,
                                  H (s, CuspRetraction.closedTranslate C η v x) =
                                    CuspRetraction.closedTranslate C η v (H (s, x))) ∧
                                (∀ s (u : Fin 2 → ℂˣ),
                                    (∀ i, ‖(u i : ℂ)‖ = 1) →
                                      ∀ x,
                                        H (s, CuspRetraction.closedFibreAction η u x) =
                                          CuspRetraction.closedFibreAction η u (H (s, x))) ∧
                                  (∀ s x,
                                      ‖ToricSpace.time (H (s, x) : ToricSpace.Space)‖ ≤
                                        ‖ToricSpace.time (x : ToricSpace.Space)‖) ∧
                                    (∀ x : PuncturedClosedTube η,
                                      ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
                                        H (1, x.1) =
                                          CuspRetraction.centralIntoClosedTube η hη.le
                                            (straightenedPrescribedCollapse C η x)) := by
  obtain ⟨ε, hε, hεr, hε1, hRC, hRD⟩ := CuspRetraction.exists_common_frozen_radius C hr hC
  have hCε : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε) := fun i j =>
    (hC i j).mono (Metric.ball_subset_ball hεr.le)
  have hRP : ToricSpace.SmallDrift (CuspPositive.positiveTwist (C 0)) ε :=
    CuspPositive.smallDrift_positiveTwist (C 0) hRD
  obtain ⟨η₀, hη₀, hη₀ε, hH⟩ := exists_frozen_controlled_deformation_below (C 0) ε hε hε1 hRP
  refine ⟨η₀, hη₀, hη₀ε.trans hεr, hη₀ε.trans hε1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηε : η < ε := hηη₀.trans_lt hη₀ε
  obtain ⟨H, hzero, hfix, hone, hequiv, _hcompact, hfibre, hmono, hEnd⟩ := hH η hη hηη₀ ρ hρ hρη
  refine
    ⟨CuspPositiveRetraction.straightenedHomotopy C hε hε1 hCε hRC hRD hηε H,
      CuspPositiveRetraction.straightenedHomotopy_zero C hε hε1 hCε hRC hRD hηε H hzero,
      CuspPositiveRetraction.straightenedHomotopy_fixed C hε hε1 hCε hRC hRD hηε H hfix,
      CuspPositiveRetraction.straightenedHomotopy_one_central C hε hε1 hCε hRC hRD hηε H hone,
      CuspPositiveRetraction.straightenedHomotopy_equivariant C hε hε1 hCε hRC hRD hηε H hequiv,
      CuspPositiveRetraction.straightenedHomotopy_fibre_torus_equivariant C hε hε1 hCε hRC hRD hηε
        H hfibre,
      CuspPositiveRetraction.straightenedHomotopy_norm_time_le C hε hε1 hCε hRC hRD hηε H hmono,
      ?_⟩
  exact straightenedHomotopy_prescribed_endpoint C hε hε1 hCε hRC hRD hηε H hη.le hEnd

theorem CuspControlledRetraction.exists_closed_quotient_controlled_strongDeformationRetraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ ρ : ℝ,
                  0 < ρ →
                    ρ ≤ η →
                      ∃ R :
                        C(CuspRetraction.ClosedQuotient C r η,
                          CuspRetraction.QuotientCentralFibre C r),
                        R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                            ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                          ∃ H :
                            (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                              ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                              {q : CuspRetraction.ClosedQuotient C r η |
                                CuspQuotient.projection C r q = 0},
                            (∀ s q,
                                ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                                  ‖CuspQuotient.projection C r q‖) ∧
                              (∀ (hηr : η < r) (x : PuncturedClosedTube η),
                                ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
                                  R (CuspRetraction.closedQuotientMap C hηr x.1) =
                                    CuspCollapse.centralProject C r hr
                                      (straightenedPrescribedCollapse C η x)) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hH⟩ :=
    exists_closed_tube_controlled_deformation C hr (fun i j => (hC i j).continuousOn)
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  have hηr : η < r := hηη₀.trans_lt hη₀r
  obtain ⟨H, hzero, hfix, hone, hequiv, _hfibre, hmono, hEnd⟩ := hH η hη hηη₀ ρ hρ hρη
  refine
    ⟨CuspRetraction.closedHomotopyDescentRetraction C hηr H hequiv hC hone,
      CuspRetraction.closedHomotopyDescentRetraction_comp_inclusion C hηr H hequiv hC hfix hone
        hη.le,
      CuspRetraction.closedHomotopyDescentHomotopyRel C hηr H hequiv hC hzero hfix hone hη.le,
      CuspRetraction.closedHomotopyDescent_norm_nonincrease C hηr H hequiv hmono, ?_⟩
  intro hηr' x hx
  apply Subtype.ext
  exact
    closedHomotopyDescentRetraction_endpoint_of_eq C hηr H hequiv hC hone hη.le x.1
      (straightenedPrescribedCollapse C η x) (hEnd x hx)

abbrev CuspControlledRetraction.ToricLevel (η : ℝ) (t : ℂ) :=
  { x : CuspRetraction.ClosedTube η // ToricSpace.time (x : ToricSpace.Space) = t }

abbrev CuspControlledRetraction.QuotientLevel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η : ℝ)
    (t : ℂ) :=
  { q : CuspRetraction.ClosedQuotient C r η // CuspQuotient.projection C r q = t }

noncomputable def CuspControlledRetraction.levelProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ) (x : ToricLevel η t) : QuotientLevel C r η t :=
  ⟨CuspRetraction.closedQuotientMap C hηr x.1, x.2⟩

theorem CuspControlledRetraction.levelProjection_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ) : Function.Surjective (levelProjection C hηr t) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := CuspRetraction.closedQuotientMap_surjective C hηr q
  exact ⟨⟨x, hq⟩, rfl⟩

theorem CuspControlledRetraction.levelProjection_isOpenQuotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ} (hηr : η < r) (t : ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsOpenQuotientMap (levelProjection C hηr t) :=
  (CuspRetraction.closedQuotientMap_isOpenQuotientMap C hηr hC).restrictPreimage
    {q : CuspRetraction.ClosedQuotient C r η | CuspQuotient.projection C r q = t}

theorem CuspControlledRetraction.levelProjection_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Topology.IsQuotientMap (levelProjection C hηr t) :=
  (levelProjection_isOpenQuotientMap C hηr t hC).isQuotientMap

noncomputable def CuspControlledRetraction.levelTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (t : ℂ) (v : Fin 2 → ℤ) (x : ToricLevel η t) : ToricLevel η t :=
  ⟨CuspRetraction.closedTranslate C η v x.1,
    by
    change ToricSpace.time (ToricSpace.twistedTranslate C v (x.1 : ToricSpace.Space)) = t
    rw [ToricSpace.time_twistedTranslate]
    exact x.2⟩

theorem CuspControlledRetraction.levelProjection_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (t : ℂ) (x y : ToricLevel η t) :
    levelProjection C hηr t x = levelProjection C hηr t y ↔
      ∃ v : Fin 2 → ℤ, CuspRetraction.closedTranslate C η v y.1 = x.1 := by
  constructor
  · intro hxy
    have hq :=
      congrArg (fun q : QuotientLevel C r η t => (q : CuspRetraction.ClosedQuotient C r η)) hxy
    obtain ⟨v, hv⟩ := (CuspRetraction.closedQuotientMap_eq_iff C hηr x.1 y.1).mp hq
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    apply (CuspRetraction.closedQuotientMap_eq_iff C hηr x.1 y.1).mpr
    exact ⟨v, congrArg (fun z : CuspRetraction.ClosedTube η => (z : ToricSpace.Space)) hv⟩

theorem CuspControlledRetraction.levelProjection_eq_iff_levelTranslate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ} (hηr : η < r) (t : ℂ) (x y : ToricLevel η t) :
    levelProjection C hηr t x = levelProjection C hηr t y ↔
      ∃ v : Fin 2 → ℤ, levelTranslate C η t v y = x := by
  constructor
  · intro hxy
    obtain ⟨v, hv⟩ := (levelProjection_eq_iff C hηr t x y).mp hxy
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    apply (levelProjection_eq_iff C hηr t x y).mpr
    exact ⟨v, congrArg (fun z : ToricLevel η t => (z : CuspRetraction.ClosedTube η)) hv⟩

theorem CuspControlledRetraction.levelProjection_fibre_compatible_of_invariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ} {Z : Type*} (hηr : η < r) (t : ℂ)
    (f : ToricLevel η t → Z)
    (hinv : ∀ (v : Fin 2 → ℤ) (x : ToricLevel η t), f (levelTranslate C η t v x) = f x) :
    ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y := by
  intro x y hxy
  obtain ⟨v, hv⟩ := (levelProjection_eq_iff_levelTranslate C hηr t x y).mp hxy
  rw [← hv]
  exact hinv v y

noncomputable def CuspControlledRetraction.levelDescend (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} {Z : Type*} (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z) :
    QuotientLevel C r η t → Z :=
  CuspHoneycombHexagon.CommonFibres.descend (levelProjection C hηr t) f
    (levelProjection_surjective C hηr t)

theorem CuspControlledRetraction.levelDescend_levelProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} {Z : Type*} (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y)
    (x : ToricLevel η t) : levelDescend C hηr t f (levelProjection C hηr t x) = f x :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (levelProjection C hηr t) f
    (levelProjection_surjective C hηr t) hcompat x

theorem CuspControlledRetraction.levelDescend_unique (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ}
    {Z : Type*} (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y)
    (g : QuotientLevel C r η t → Z) (hg : ∀ x, g (levelProjection C hηr t x) = f x) :
    g = levelDescend C hηr t f := by
  funext q
  obtain ⟨x, rfl⟩ := levelProjection_surjective C hηr t q
  rw [hg, levelDescend_levelProjection C hηr t f hcompat]

theorem CuspControlledRetraction.levelDescend_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} {Z : Type*} [TopologicalSpace Z] (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hf : Continuous f)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y) :
    Continuous (levelDescend C hηr t f) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous (levelProjection C hηr t) f
    (levelProjection_surjective C hηr t) (levelProjection_isQuotientMap C hηr t hC) hf hcompat

abbrev CuspControlledRetraction.ActualQuotientFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (t : ℂ) :=
  { q : CuspQuotient.QuotientSpace C r // CuspQuotient.projection C r q = t }

def CuspControlledRetraction.quotientLevelFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) : QuotientLevel C r η t ≃ₜ ActualQuotientFibre C r t
    where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, by rw [q.2]; exact htη⟩, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _

def CuspControlledRetraction.levelToPunctured (η : ℝ) (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    PuncturedClosedTube η :=
  ⟨x.1, fun hx => ht (x.2.symm.trans hx)⟩

def CuspControlledRetraction.prescribedFibreUpstairs (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (η : ℝ) (t : ℂ) (ht : t ≠ 0) (x : ToricLevel η t) :
    CuspRetraction.QuotientCentralFibre C r :=
  CuspCollapse.centralProject C r hr
    (straightenedPrescribedCollapse C η (levelToPunctured η t ht x))

def CuspControlledRetraction.prescribedFibreCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ) (ht : t ≠ 0) :
    QuotientLevel C r η t → CuspRetraction.QuotientCentralFibre C r :=
  levelDescend C hηr t (prescribedFibreUpstairs C r hr η t ht)

def CuspControlledRetraction.prescribedActualFibreCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) :
    ActualQuotientFibre C r t → CuspRetraction.QuotientCentralFibre C r :=
  prescribedFibreCollapse C r hr hηr t ht ∘ (quotientLevelFibreHomeomorph C r η t htη).symm

theorem CuspControlledRetraction.prescribedFibreCollapse_eq_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ)
    (ht : t ≠ 0)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd :
      ∀ x : PuncturedClosedTube η,
        ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ‖t‖ →
          R (CuspRetraction.closedQuotientMap C hηr x.1) =
            CuspCollapse.centralProject C r hr (straightenedPrescribedCollapse C η x)) :
    (fun q : QuotientLevel C r η t => R q.1) = prescribedFibreCollapse C r hr hηr t ht := by
  let f := prescribedFibreUpstairs C r hr η t ht
  let g := fun q : QuotientLevel C r η t => R q.1
  have hg (x : ToricLevel η t) : g (levelProjection C hηr t x) = f x :=
    hEnd (levelToPunctured η t ht x) (congrArg Norm.norm x.2)
  have hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y := by
    intro x y hxy
    exact (hg x).symm.trans ((congrArg g hxy).trans (hg y))
  exact levelDescend_unique C hηr t f hcompat g hg

theorem CuspControlledRetraction.prescribedFibreCollapse_levelProjection_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {η : ℝ} (hηr : η < r) (t : ℂ)
    (ht : t ≠ 0)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd :
      ∀ x : PuncturedClosedTube η,
        ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ‖t‖ →
          R (CuspRetraction.closedQuotientMap C hηr x.1) =
            CuspCollapse.centralProject C r hr (straightenedPrescribedCollapse C η x))
    (x : ToricLevel η t) :
    prescribedFibreCollapse C r hr hηr t ht (levelProjection C hηr t x) =
      prescribedFibreUpstairs C r hr η t ht x := by
  rw [← prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R hEnd]
  exact hEnd (levelToPunctured η t ht x) (congrArg Norm.norm x.2)

theorem CuspControlledRetraction.exists_controlled_actual_fibre_retraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η),
                  ∃ R :
                    C(CuspRetraction.ClosedQuotient C r η,
                      CuspRetraction.QuotientCentralFibre C r),
                    R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                      ∃ H :
                        (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                          ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                          {q : CuspRetraction.ClosedQuotient C r η |
                            CuspQuotient.projection C r q = 0},
                        (∀ s q,
                            ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                              ‖CuspQuotient.projection C r q‖) ∧
                          ∀ hηr : η < r,
                            Continuous (prescribedActualFibreCollapse C r hr hηr t ht htη) ∧
                              (∀ q : ActualQuotientFibre C r t,
                                  R ((quotientLevelFibreHomeomorph C r η t htη).symm q).1 =
                                    prescribedActualFibreCollapse C r hr hηr t ht htη q) ∧
                                (∀ x : ToricLevel η t,
                                  prescribedFibreCollapse C r hr hηr t ht
                                      (levelProjection C hηr t x) =
                                    prescribedFibreUpstairs C r hr η t ht x) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hR⟩ :=
    exists_closed_quotient_controlled_strongDeformationRetraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ t ht htη
  obtain ⟨R, hRinc, H, hmono, hEnd⟩ := hR η hη hηη₀ ‖t‖ (norm_pos_iff.mpr ht) htη
  refine ⟨R, hRinc, H, hmono, ?_⟩
  intro hηr
  have he := prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R (hEnd hηr)
  refine ⟨?_, ?_, ?_⟩
  · unfold prescribedActualFibreCollapse
    rw [← he]
    exact
      (R.continuous.comp continuous_subtype_val).comp
        (quotientLevelFibreHomeomorph C r η t htη).symm.continuous
  · intro q
    exact congrFun he ((quotientLevelFibreHomeomorph C r η t htη).symm q)
  · exact prescribedFibreCollapse_levelProjection_of_endpoint C r hr hηr t ht R (hEnd hηr)

def CuspCentralHomology.fibreIntoOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (htδ : ‖t‖ < δ) : C(CuspControlledRetraction.ActualQuotientFibre C r t, OpenQuotient C r δ)
    where
  toFun q := ⟨q.1, by rw [q.2]; exact htδ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

def CuspCentralHomology.openLevelFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (t : ℂ) (htδ : ‖t‖ < δ) :
    { q : OpenQuotient C r δ // CuspQuotient.projection C r q = t } ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t
    where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨fibreIntoOpen C r δ t htδ q, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (fibreIntoOpen C r δ t htδ).continuous

def CuspCentralHomology.fibreRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ) :
    CuspControlledRetraction.ActualQuotientFibre C δ t ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t :=
  ((openQuotientRadiusHomeomorph C hδr hC).subtype (p := fun q =>
        CuspQuotient.projection C δ q = t) (q := fun q : OpenQuotient C r δ =>
        CuspQuotient.projection C r q = t)
        (fun q => by rw [openQuotientRadiusHomeomorph_projection])).trans
    (openLevelFibreHomeomorph C r δ t htδ)

def CuspCentralHomology.centralRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ)
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ) :
    CuspRetraction.QuotientCentralFibre C δ ≃ₜ CuspRetraction.QuotientCentralFibre C r :=
  fibreRadiusHomeomorph C r δ 0 hδr hC (by simpa only [norm_zero] using hδ)

def CuspCentralHomology.centralSingularH2Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 ≃ₗ[ℤ]
      (Fin 4 → ℤ) := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs :
    0 < δ ∧
      δ < r ∧
        δ < 1 ∧
          ToricSpace.SmallDrift C δ ∧
            ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 2).trans
      (centralSingularH2Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

def CuspCentralHomology.centralSingularH3Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3 ≃ₗ[ℤ]
      (Fin 2 → ℤ) := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs :
    0 < δ ∧
      δ < r ∧
        δ < 1 ∧
          ToricSpace.SmallDrift C δ ∧
            ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 3).trans
      (centralSingularH3Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

theorem CuspCentralHomology.centralSingularH2_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) :=
  Module.Free.of_equiv (centralSingularH2Equiv C r hr hC).symm

theorem CuspCentralHomology.centralSingularH3_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3) :=
  Module.Free.of_equiv (centralSingularH3Equiv C r hr hC).symm

theorem CuspCentralHomology.centralSingularH2_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) :=
  Module.Finite.of_surjective (centralSingularH2Equiv C r hr hC).symm.toLinearMap
    (centralSingularH2Equiv C r hr hC).symm.surjective

theorem CuspCentralHomology.centralSingularH3_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3) :=
  Module.Finite.of_surjective (centralSingularH3Equiv C r hr hC).symm.toLinearMap
    (centralSingularH3Equiv C r hr hC).symm.surjective

theorem CuspCentralHomology.centralSingularH2_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) =
      4 := by
  rw [(centralSingularH2Equiv C r hr hC).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem CuspCentralHomology.centralSingularH3_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 3) =
      2 := by
  rw [(centralSingularH3Equiv C r hr hC).finrank_eq]
  exact Module.finrank_fin_fun ℤ

def CuspCentralHomology.centralSingularH4Equiv_of_admissible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 4 ≃ₗ[ℤ] ℤ := by
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 1
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 1
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 0
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 0
  exact
    (coverConnectingEquivOfVanishing (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
          (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)) (innerRegion_isOpen C ε hε hε1 hC hR)
          (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) 3).trans
      (overlapRegionHomologyThreeEquiv C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num))

theorem CuspCentralHomology.centralSingularHomology_subsingleton_of_admissible
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε)
        (n + 5)) := by
  let :=
    outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) (n + 2)
  let := innerRegion_homology_subsingleton C ε hε hε1 hC hR (n + 2)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        ((outerRegion C ε hε (1 / 2)) ∩ (innerRegion C ε hε) :
          Set (CuspRetraction.QuotientCentralFibre C ε))
        (n + 4)) :=
    overlapRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) n
  exact
    coverHomology_subsingleton_of_vanishing (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) (n + 4)

def CuspCentralHomology.centralSingularH4Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4 ≃ₗ[ℤ] ℤ := by
  let δ : ℝ := Classical.choose (CuspQuotient.exists_admissible_radius C hr hC)
  have hs :
    0 < δ ∧
      δ < r ∧
        δ < 1 ∧
          ToricSpace.SmallDrift C δ ∧
            ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    Classical.choose_spec (CuspQuotient.exists_admissible_radius C hr hC)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hs.2.1.le hC hs.1).symm 4).trans
      (centralSingularH4Equiv_of_admissible C δ hs.1 hs.2.2.1 hs.2.2.2.2 hs.2.2.2.1)

theorem CuspCentralHomology.centralSingularHomology_subsingleton
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r)
        (n + 5)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hR, hCδ⟩ := CuspQuotient.exists_admissible_radius C hr hC
  let := centralSingularHomology_subsingleton_of_admissible C δ hδ hδ1 hCδ hR n
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (centralRadiusHomeomorph C r δ hδr.le hC hδ).symm (n + 5)).injective.subsingleton

theorem CuspCentralHomology.centralSingularHomology_subsingleton_of_four_lt
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {n : ℕ} (hn : 4 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) := by
  have he : (n - 5) + 5 = n := Nat.sub_add_cancel (by omega)
  rw [← he]
  exact centralSingularHomology_subsingleton C r hr hC (n - 5)

def CuspCentralHomology.centralSingularHomologyHigherEquivZero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) (n + 5) ≃ₗ[ℤ]
      (Fin 0 → ℤ) := by
  letI := centralSingularHomology_subsingleton C r hr hC n
  exact LinearEquiv.ofSubsingleton _ _

theorem CuspCentralHomology.centralSingularH4_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4) :=
  Module.Free.of_equiv (centralSingularH4Equiv C r hr hC).symm

theorem CuspCentralHomology.centralSingularH4_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4) :=
  Module.Finite.of_surjective (centralSingularH4Equiv C r hr hC).symm.toLinearMap
    (centralSingularH4Equiv C r hr hC).symm.surjective

theorem CuspCentralHomology.centralSingularH4_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 4) =
      1 := by
  rw [(centralSingularH4Equiv C r hr hC).finrank_eq]
  simp

theorem covering_monodromy_naturality {E F X Y : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y] {p : E → X} {q : F → Y} (hp : IsCoveringMap p)
    (hq : IsCoveringMap q) (r : ContinuousMap E F) (f : ContinuousMap X Y)
    (hcomm : ∀ z, q (r z) = f (p z)) (e : E) (γ : Path.Homotopic.Quotient (p e) (p e)) :
    (hq.monodromy (γ.map f) ⟨r e, hcomm e⟩ : F) = r (hp.monodromy γ ⟨e, rfl⟩ : E) := by
  let e' : p ⁻¹' {p e} := hp.monodromy γ ⟨e, rfl⟩
  let f' : q ⁻¹' {f (p e)} := ⟨r e', (hcomm e').trans (congrArg f e'.property)⟩
  have hc : (ContinuousMap.mk q hq.continuous).comp r = f.comp ⟨p, hp.continuous⟩ :=
    ContinuousMap.ext hcomm
  have he : hq.monodromy (γ.map f) ⟨r e, hcomm e⟩ = f' := by
    apply hq.monodromy_eq_of_map_eq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map r)
    apply eq_of_heq
    have hmap {f₁ f₂ : ContinuousMap E Y} (h : f₁ = f₂) :
      HEq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map f₁) ((hp.liftPathQuotient γ ⟨e, rfl⟩).map f₂) := by
      subst f₂
      rfl
    apply (heq_of_eq Path.Homotopic.Quotient.map_comp.symm).trans
    apply (hmap hc).trans
    rw [Path.Homotopic.Quotient.map_comp, hp.map_liftPathQuotient]
    have hm :
      (γ.cast rfl (show p e' = p e from e'.property)).map f =
        (γ.map f).cast rfl (congrArg f e'.property) :=
      Path.Homotopic.Quotient.map_cast γ
    apply (heq_of_eq hm).trans
    exact
      Path.Homotopic.Quotient.cast_heq _ _ |>.trans (Path.Homotopic.Quotient.cast_heq _ _).symm
  exact congrArg Subtype.val he

def homeomorphFundamentalGroupEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x)
    where
  __ := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x)
  left_inv
    γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (γ t)
  right_inv
    γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (γ t)

def CuspUniformization.sourcePeriodCoordinates : Lattice ≃+ FullPeriodMatrix.IntegerPeriods
    where
  toFun v := (![v 2, v 3], ![v 0, v 1])
  invFun c := ![c.2 0, c.2 1, c.1 0, c.1 1]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv c := by apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_add' v w := by apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

def CuspUniformization.cuspLatticeProjection : Lattice →+ (Fin 2 → ℤ)
    where
  toFun v := ![v 0, v 1]
  map_zero' := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl

theorem CuspUniformization.cuspLatticeProjection_eq_zero_iff (v : Lattice) :
    cuspLatticeProjection v = 0 ↔ (M₀ - 1) *ᵥ v = 0 := by
  rw [M₀_sub_one_kernel]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h₀, h₁⟩
    ext i
    fin_cases i <;> assumption

theorem CuspUniformization.exponentialLift_period_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (z : ComplexPlane₂) (m n : Fin 2 → ℤ) :
    exponentialLift ε s hs
        (z + (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) =
      ToricSpace.tubeTranslate C (CuspQuotient.disc ε) n (exponentialLift ε s hs z) := by
  apply Subtype.ext
  change
    exponentialPoint (exponential s)
        (z + (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) =
      ToricSpace.twistedTranslate C n (exponentialPoint (exponential s) z)
  rw [twistedTranslate_exponentialPoint]
  apply (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mpr
  exact ⟨m, by abel⟩

def CuspUniformization.fibreFundamentalGroupMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    FundamentalGroup (periodData C s hlog hRp).Torus 0 →*
      FundamentalGroup (CuspQuotient.QuotientSpace C ε)
        (CuspQuotient.quotientMap C ε (exponentialLift ε s hs 0)) :=
  FundamentalGroup.map ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩ 0

theorem CuspUniformization.fibreFundamentalGroupMap_marking (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp γ) =
      Multiplicative.ofAdd (((periodData C s hlog hRp).fundamentalGroupEquiv γ).toAdd.2) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  let p := periodData C s hlog hRp
  let hq := CuspQuotient.quotientMap_covering C ε hε hε1 hC hR
  let c := (p.fundamentalGroupEquiv γ).toAdd
  have hnat :=
    covering_monodromy_naturality p.quotientCovering.isCoveringMap hq.isCoveringMap
      ⟨exponentialLift ε s hs, exponentialLift_continuous ε s hs⟩
      ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩ (fun _ => rfl)
      (0 : ComplexPlane₂) γ
  have hper := p.fundamentalGroupEquiv_monodromy γ
  have htrans := exponentialLift_period_translate C ε s hs 0 c.1 c.2
  have he :
    ToricSpace.tubeTranslate C (CuspQuotient.disc ε)
        (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
            (fibreFundamentalGroupMap C ε s hs hlog hRp γ)).toAdd
        (exponentialLift ε s hs 0) =
      ToricSpace.tubeTranslate C (CuspQuotient.disc ε) c.2 (exponentialLift ε s hs 0) := by
    rw [CuspQuotient.fundamentalGroupEquivAt_monodromy]
    change
      (hq.isCoveringMap.monodromy
            (Path.Homotopic.Quotient.map γ
              ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩)
            ⟨exponentialLift ε s hs 0, rfl⟩ :
          ToricSpace.Tube (CuspQuotient.disc ε)) =
        _
    apply hnat.trans
    apply (congrArg (exponentialLift ε s hs) hper.symm).trans
    change
      exponentialLift ε s hs
          ((fun i => (c.1 i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (c.2 j : ℂ))) =
        _
    simpa only [zero_add] using htrans
  exact hq.isCancelSMul.right_cancel _ _ (exponentialLift ε s hs 0) he

theorem CuspUniformization.fibrePeriodLoop_marking (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (m n : Fin 2 → ℤ) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp
          (FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (m, n)⟧)) =
      Multiplicative.ofAdd n := by
  rw [fibreFundamentalGroupMap_marking, FullPeriodMatrix.fundamentalGroupEquiv_periodLoop]
  rfl

theorem CuspUniformization.fibreFundamentalGroupMap_eq_one_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreFundamentalGroupMap C ε s hs hlog hRp γ = 1 ↔
      ((periodData C s hlog hRp).fundamentalGroupEquiv γ).toAdd.2 = 0 := by
  rw [←
    (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)).map_eq_one_iff,
    fibreFundamentalGroupMap_marking]
  rfl

theorem CuspUniformization.fibreFundamentalGroupMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective (fibreFundamentalGroupMap C ε s hs hlog hRp) := by
  intro γ
  let n :=
    (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0) γ).toAdd
  refine ⟨FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (0, n)⟧, ?_⟩
  apply
    (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)).injective
  rw [fibrePeriodLoop_marking]
  rfl

theorem CuspUniformization.fibre_integerPeriod_loop_nullhomotopic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (m : Fin 2 → ℤ) :
    Path.Homotopic
      (((periodData C s hlog hRp).periodLoop (m, 0)).map (fibreMap_continuous C ε s hs hlog hRp))
      (Path.refl (CuspQuotient.quotientMap C ε (exponentialLift ε s hs 0))) := by
  have he :=
    (fibreFundamentalGroupMap_eq_one_iff C ε s hs hlog hRp hε hε1 hC hR
          (FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (m, 0)⟧)).mpr
      (by rw [FullPeriodMatrix.fundamentalGroupEquiv_periodLoop]; rfl)
  exact Path.Homotopic.Quotient.eq.mp he

def CuspUniformization.fibreBasePoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    CuspQuotient.projection C ε ⁻¹' {exponential s} :=
  fibreMapToFibre C ε s hs hlog hRp 0

def CuspUniformization.fibreInclusionFundamentalGroupMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    FundamentalGroup (CuspQuotient.projection C ε ⁻¹' {exponential s})
        (fibreBasePoint C ε s hs hlog hRp) →*
      FundamentalGroup (CuspQuotient.QuotientSpace C ε)
        (CuspQuotient.quotientMap C ε (exponentialLift ε s hs 0)) :=
  FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (fibreBasePoint C ε s hs hlog hRp)

theorem CuspUniformization.fibreInclusionFundamentalGroupMap_comp_homeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreInclusionFundamentalGroupMap C ε s hs hlog hRp
        (homeomorphFundamentalGroupEquiv (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0 γ) =
      fibreFundamentalGroupMap C ε s hs hlog hRp γ := by
  obtain ⟨γ⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem CuspUniformization.fibreInclusionFundamentalGroupMap_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective (fibreInclusionFundamentalGroupMap C ε s hs hlog hRp) := by
  intro γ
  obtain ⟨δ, hδ⟩ := fibreFundamentalGroupMap_surjective C ε s hs hlog hRp hε hε1 hC hR γ
  refine
    ⟨homeomorphFundamentalGroupEquiv (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0 δ, ?_⟩
  rw [fibreInclusionFundamentalGroupMap_comp_homeomorph]
  exact hδ

def CuspCentralHomology.centralBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 2
  | 4 => 1
  | _ => 0

def CuspCentralHomology.centralSingularHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n ≃ₗ[ℤ]
      (Fin (centralBetti n) → ℤ) :=
  match n with
  | 0 => (centralSingularH0Equiv C r hr).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => centralSingularH1Equiv C r hr hC
  | 2 => centralSingularH2Equiv C r hr hC
  | 3 => centralSingularH3Equiv C r hr hC
  | 4 => (centralSingularH4Equiv C r hr hC).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 => centralSingularHomologyHigherEquivZero C r hr hC n

theorem CuspCentralHomology.centralSingularHomology_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) :=
  Module.Free.of_equiv (centralSingularHomologyEquiv C r hr hC n).symm

theorem CuspCentralHomology.centralSingularHomology_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) :=
  Module.Finite.of_surjective (centralSingularHomologyEquiv C r hr hC n).symm.toLinearMap
    (centralSingularHomologyEquiv C r hr hC n).symm.surjective

theorem CuspCentralHomology.centralSingularHomology_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) =
      centralBetti n := by
  rw [(centralSingularHomologyEquiv C r hr hC n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem CuspCentralHomology.centralSingularHomology_torsionFree (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Module.IsTorsionFree ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n) := by
  let := centralSingularHomology_free C r hr hC n
  infer_instance

def CuspCentralHomology.centralSingularEulerCharacteristic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) : ℤ :=
  ∑ i : Fin 5,
    (-1 : ℤ) ^ (i : ℕ) *
      (Module.finrank ℤ
          (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) i) :
        ℤ)

theorem CuspCentralHomology.centralSingularEulerCharacteristic_eq_two
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    centralSingularEulerCharacteristic C r = 2 := by
  unfold centralSingularEulerCharacteristic
  simp_rw [centralSingularHomology_finrank C r hr hC]
  norm_num [Fin.sum_univ_succ, centralBetti]

def ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (CuspRetraction.QuotientCentralFibre D.correction D.radius) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (FullSpace D) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (fullCentralHomotopyEquiv D) n

@[simp]
theorem ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv_toLinearMap
    (D : SpecialPeriods.CuspFamily.Data) (n : ℕ) :
    (fullCentralHomologyEquiv D n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (fullCentralInclusion D) n := by
  change SingularMayerVietoris.singularHomologyMap (fullCentralHomotopyEquiv D).toFun n = _
  rw [fullCentralHomotopyEquiv_toFun]

def ThreefoldHomologyFinitenessCusp.fullHomologyCoordinates (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (FullSpace D) n ≃ₗ[ℤ]
      (Fin (CuspCentralHomology.centralBetti n) → ℤ) :=
  (fullCentralHomologyEquiv D n).symm.trans
    (CuspCentralHomology.centralSingularHomologyEquiv D.correction D.radius D.radius_pos
      D.holomorphic n)

theorem ThreefoldHomologyFinitenessCusp.fullHomology_free (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) : Module.Free ℤ (SingularMayerVietoris.SingularHomology (FullSpace D) n) :=
  Module.Free.of_equiv (fullHomologyCoordinates D n).symm

theorem ThreefoldHomologyFinitenessCusp.fullHomology_finite (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) : Module.Finite ℤ (SingularMayerVietoris.SingularHomology (FullSpace D) n) :=
  Module.Finite.of_surjective (fullHomologyCoordinates D n).symm.toLinearMap
    (fullHomologyCoordinates D n).symm.surjective

theorem ThreefoldHomologyFinitenessCusp.fullHomology_finrank (D : SpecialPeriods.CuspFamily.Data)
    (n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology (FullSpace D) n) =
      CuspCentralHomology.centralBetti n := by
  rw [(fullHomologyCoordinates D n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem ThreefoldHomologyFinitenessCusp.fullHomology_subsingleton_of_four_lt
    (D : SpecialPeriods.CuspFamily.Data) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (FullSpace D) n) := by
  have :=
    CuspCentralHomology.centralSingularHomology_subsingleton_of_four_lt D.correction D.radius
      D.radius_pos D.holomorphic hn
  refine ⟨fun a b => (fullCentralHomologyEquiv D n).symm.injective ?_⟩
  exact Subsingleton.elim _ _

end Mathoverflow1973

end
