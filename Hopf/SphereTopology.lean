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
Original source lines 62392--81182; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.SingularHomology
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
import Lib.Algebra.Module.IntegerPresentation

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

theorem NoExotic.IntLinearAutomorphism.apply_eq_mul (e : ℤ ≃ₗ[ℤ] ℤ) (k : ℤ) : e k = e 1 * k := by
  simpa only [smul_eq_mul, mul_one, mul_comm] using e.map_smul k 1

theorem NoExotic.IntLinearAutomorphism.apply_one_eq_one_or_neg_one (e : ℤ ≃ₗ[ℤ] ℤ) :
    e 1 = 1 ∨ e 1 = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := e.symm 1)
  rw [← apply_eq_mul, e.apply_symm_apply]

theorem MorseCancellation.two_sphere_map_unit_of_homology_bijective {Y : Type} [TopologicalSpace Y]
    (e : (Smale.Hemisphere.Sphere 2) ≃ₜ Y) (g : C((Smale.Hemisphere.Sphere 2), Y))
    (hg : Function.Bijective (SingularMayerVietoris.singularHomologyMap g 2)) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap g 2 =
          k •
            SingularMayerVietoris.singularHomologyMap (e : C((Smale.Hemisphere.Sphere 2), Y)) 2 :=
  by
  let H := SphereHomology.unitSphereHomologyTopEquiv 1
  let B := LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap g 2) hg
  let J := PeriodTorusHigherHomology.homeomorphHomologyEquiv e 2
  let K : ℤ ≃ₗ[ℤ] ℤ := H.symm.trans (B.trans (J.symm.trans H))
  refine ⟨K 1, NoExotic.IntLinearAutomorphism.apply_one_eq_one_or_neg_one K, ?_⟩
  apply LinearMap.ext
  intro a
  change B a = K 1 • J a
  apply J.symm.injective
  rw [map_zsmul, J.symm_apply_apply]
  apply H.injective
  rw [map_zsmul]
  have hh := NoExotic.IntLinearAutomorphism.apply_eq_mul K (H a)
  simpa only [K, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, smul_eq_mul] using hh

def Smale.PuncturedBall.toSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    C(Space E R, Metric.sphere (0 : E) 1) :=
  Smale.PuncturedRadial.toSphere.comp (toPunctured R)

theorem Smale.PuncturedBall.toSphere_fromSphere {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) (u : Metric.sphere (0 : E) 1) :
    toSphere R (fromSphere R r hr hrR u) = u :=
  Smale.PuncturedRadial.toSphere_fromSphere r hr u

def Smale.PuncturedBall.deformation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (ContinuousMap.id (Space E R)).Homotopy ((fromSphere R r hr hrR).comp (toSphere R))
    where
  toFun
    q :=
    ⟨blendVector R r q, Smale.PuncturedRadial.blendVector_ne_zero r hr (q.1, toPunctured R q.2),
      norm_blendVector_lt R r hr hrR q.1 q.2⟩
  continuous_toFun := (continuous_blendVector R r).subtype_mk _
  map_zero_left
    x := by
    apply Subtype.ext
    simp [blendVector, Smale.PuncturedRadial.blendVector, toPunctured]
  map_one_left
    x := by
    apply Subtype.ext
    simp [blendVector, Smale.PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      Smale.PuncturedRadial.toSphere, Smale.RadialExtension.direction, div_eq_mul_inv, smul_smul]

def Smale.PuncturedBall.sphereHomotopyEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (r : ℝ) (hr : 0 < r) (hrR : r < R) : Metric.sphere (0 : E) 1 ≃ₕ Space E R
    where
  toFun := fromSphere R r hr hrR
  invFun := toSphere R
  left_inv := by
    have h :
      (toSphere (E := E) R).comp (fromSphere R r hr hrR) =
        ContinuousMap.id (Metric.sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere R r hr hrR)
    rw [h]
  right_inv := ⟨(deformation R r hr hrR).symm⟩

def MorseCancellation.nativeBeltTubeSource {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1,
      d.chart.beltSource d.radius d.radius_pos)
    where
  toFun
    z :=
    ⟨(z.1, z.2.val),
      d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
        ⟨Set.mem_univ _, by
          rw [mem_closedBall_zero_iff]
          exact z.2.property.2.le.trans (by norm_num)⟩⟩
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def MorseCancellation.nativeBeltTubeInComplement {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Metric.sphere (0 : d.chart.PositiveCoordinates) 1 ×
        Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel))
    where
  toFun
    z := by
    let y := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (nativeBeltTubeSource d z)
    refine ⟨y.val, ?_⟩
    intro hy
    have hz := (d.beltNormal_eq_zero_iff y.property).mpr hy
    have heq : d.beltNormal y.val = d.radius • z.2.val :=
      d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (nativeBeltTubeSource d z)
    rw [heq] at hz
    exact (smul_ne_zero d.radius_pos.ne' z.2.property.1) hz
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp
            (nativeBeltTubeSource d).continuous)).subtype_mk
      _

def MorseCancellation.nativeBeltTubeMeridian {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    C(Metric.sphere (0 : d.chart.NegativeCoordinates) 1,
      ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    ((ContinuousMap.const _ v).prodMk (Smale.PuncturedBall.fromSphere 1 r hr hr1))

theorem MorseCancellation.nativeBeltTube_homotopic_meridian {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) {X : Type} [TopologicalSpace X]
    (a : C(X, Metric.sphere (0 : d.chart.PositiveCoordinates) 1))
    (b : C(X, Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (ha : a.Homotopic (ContinuousMap.const _ v)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ((nativeBeltTubeInComplement d).comp (a.prodMk b)).Homotopic
      ((nativeBeltTubeMeridian d v r hr hr1).comp ((Smale.PuncturedBall.toSphere 1).comp b)) := by
  let c := (Smale.PuncturedBall.toSphere 1).comp b
  let b' := (Smale.PuncturedBall.fromSphere 1 r hr hr1).comp c
  have hb : b.Homotopic b' := by
    have H := (Smale.PuncturedBall.deformation 1 r hr hr1).compContinuousMap b
    exact ⟨H⟩
  have hpair := ha.prodMk hb
  have hh := (ContinuousMap.Homotopic.refl (nativeBeltTubeInComplement d)).comp hpair
  have heq :
    (nativeBeltTubeInComplement d).comp ((ContinuousMap.const _ v).prodMk b') =
      (nativeBeltTubeMeridian d v r hr hr1).comp c := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [heq] at hh
  exact hh

theorem MorseCancellation.nativeBeltTubeMeridian_eq {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (S : AdaptedWindows E f)
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) :
    nativeBeltTubeMeridian (S.data q) v r hr hr1 =
      nativeUpperMeridianInComplement S q v ⟨r, hr.le, hr1.le⟩ hr := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change
    (S.data q).chart.splitChart.symm
        ((Smale.MorseHandle.ambientMap (S.data q).radius (v.val, r • u.val)).swap) =
      (S.data q).chart.splitChart.symm (Degree.BeltPassage.upper (S.data q).radius r u.val v.val)
  congr 1
  simp only [Smale.MorseHandle.ambientMap, Degree.BeltPassage.upper, Prod.swap, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property, mul_one, smul_smul]

def MorseCancellation.parameterBallBoundary {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] (r : ℝ)
    (hr : 0 < r) : C(Metric.sphere (0 : A) 1, Metric.closedBall (0 : A) r)
    where
  toFun
    u := ⟨r • u.val, by rw [mem_closedBall_zero_iff, Smale.LocalDegree.norm_radius_smul r hr u]⟩
  continuous_toFun := by
    have h : Continuous (fun u : Metric.sphere (0 : A) 1 => r • u.val) :=
      continuous_const.smul continuous_subtype_val
    exact h.subtype_mk _

def MorseCancellation.parameterBallCenter {A : Type} [NormedAddCommGroup A] (r : ℝ) (hr : 0 < r) :
    Metric.closedBall (0 : A) r :=
  ⟨0, by simpa using hr.le⟩

def MorseCancellation.parameterBallContraction {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (r : ℝ) (hr : 0 < r) :
    (parameterBallBoundary (A := A) r hr).Homotopy
      (ContinuousMap.const _ (parameterBallCenter r hr))
    where
  toFun
    z :=
    ⟨(1 - (z.1 : ℝ)) • (r • z.2.val),
      by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr z.1.property.2),
        Smale.LocalDegree.norm_radius_smul r hr z.2]
      exact mul_le_of_le_one_left hr.le (by linarith [z.1.property.1])⟩
  continuous_toFun := by
    have h :
      Continuous
        (fun z : unitInterval × Metric.sphere (0 : A) 1 => (1 - (z.1 : ℝ)) • (r • z.2.val)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left u := by apply Subtype.ext; simp [parameterBallBoundary]
  map_one_left u := by apply Subtype.ext; simp [parameterBallCenter]

theorem MorseCancellation.parameterBall_boundary_nullhomotopic {A : Type} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {Y : Type} [TopologicalSpace Y] (r : ℝ) (hr : 0 < r)
    (g : C(Metric.closedBall (0 : A) r, Y)) :
    (g.comp (parameterBallBoundary r hr)).Homotopic
      (ContinuousMap.const _ (g (parameterBallCenter r hr))) := by
  have h := (ContinuousMap.Homotopic.refl g).comp ⟨parameterBallContraction r hr⟩
  exact h

theorem MorseCancellation.normalized_pos_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ) (hr : 0 < r) (x : F) : ‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ hr.ne', mul_one]

def MorseCancellation.beltBallCoordinates {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius)) :
    C(Metric.closedBall (0 : A) ε,
      Metric.sphere (0 : d.chart.PositiveCoordinates) 1 × d.chart.NegativeCoordinates) :=
  ⟨fun z => ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm (F z)).val,
    continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm.continuous.comp
        F.continuous)⟩

theorem MorseCancellation.beltBallCoordinates_normal {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (z : Metric.closedBall (0 : A) ε) :
    (beltBallCoordinates d ε F z).2 = d.radius⁻¹ • d.beltNormal (F z).val :=
  rfl

def MorseCancellation.beltBallBoundaryNormal {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (ε : ℝ) (hε : 0 < ε)
    (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, Smale.PuncturedBall.Space d.chart.NegativeCoordinates 1) :=
  ⟨fun u => ⟨(beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2, hne u, hsmall _⟩,
    ((beltBallCoordinates d ε F).continuous.snd.comp
          (parameterBallBoundary ε hε).continuous).subtype_mk
      _⟩

def MorseCancellation.beltBallBoundaryInComplement {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) :
    C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)) :=
  (nativeBeltTubeInComplement d).comp
    (((ContinuousMap.fst.comp (beltBallCoordinates d ε F)).comp
          (parameterBallBoundary ε hε)).prodMk
      (beltBallBoundaryNormal d ε hε F hsmall hne))

theorem MorseCancellation.beltBallBoundaryInComplement_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne u).val =
      (F (parameterBallBoundary ε hε u)).val := by
  let y := F (parameterBallBoundary ε hε u)
  let e := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
  change
    (e
          (nativeBeltTubeSource d
            ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)))).val =
      y.val
  have hs :
    nativeBeltTubeSource d ((e.symm y).val.1, (beltBallBoundaryNormal d ε hε F hsmall hne u)) =
      e.symm y := by
    apply Subtype.ext
    rfl
  rw [hs, e.apply_symm_apply]

theorem MorseCancellation.beltBallBoundary_homotopic_meridian {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (beltBallBoundaryInComplement d ε hε F hsmall hne).Homotopic
      ((nativeBeltTubeMeridian d (beltBallCoordinates d ε F (parameterBallCenter ε hε)).1 r hr
            hr1).comp
        ((Smale.PuncturedBall.toSphere 1).comp (beltBallBoundaryNormal d ε hε F hsmall hne))) := by
  let a := ContinuousMap.fst.comp (beltBallCoordinates d ε F)
  have ha := parameterBall_boundary_nullhomotopic ε hε a
  exact
    nativeBeltTube_homotopic_meridian d (a.comp (parameterBallBoundary ε hε))
      (beltBallBoundaryNormal d ε hε F hsmall hne) (a (parameterBallCenter ε hε)) ha r hr hr1

theorem MorseCancellation.beltBallBoundary_normalized_coe {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (ε : ℝ) (hε : 0 < ε) (F : C(Metric.closedBall (0 : A) ε, d.chart.beltTarget d.radius))
    (hsmall : ∀ z, ‖(beltBallCoordinates d ε F z).2‖ < 1)
    (hne : ∀ u, (beltBallCoordinates d ε F (parameterBallBoundary ε hε u)).2 ≠ 0)
    (u : Metric.sphere (0 : A) 1) :
    (Smale.PuncturedBall.toSphere 1 (beltBallBoundaryNormal d ε hε F hsmall hne u)).val =
      ‖d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        d.beltNormal (F (parameterBallBoundary ε hε u)).val := by
  change
    ‖d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val‖⁻¹ •
        (d.radius⁻¹ • d.beltNormal (F (parameterBallBoundary ε hε u)).val) =
      _
  exact normalized_pos_smul d.radius⁻¹ (inv_pos.mpr d.radius_pos) _

theorem MorseCancellation.normal_boundary_homotopic_native_meridian {E M A : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (g : A → d.UpperLevel)
    {L : A ≃L[ℝ] d.chart.NegativeCoordinates} {s : Set A}
    (b : Smale.LocalDegree.BoundaryData (d.beltNormal ∘ g) L s) (hc : ContinuousOn g s)
    (hdomain : ∀ z ∈ s, g z ∈ d.beltNormalDomain)
    (hsmall : ∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (g z)‖ < 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ J : C(Metric.sphere (0 : A) 1, ((Set.range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)),
      (∀ u, (J u).val = g (b.radius • u.val)) ∧
        ∃ v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1,
          J.Homotopic ((nativeBeltTubeMeridian d v r hr hr1).comp b.normalizedMap) := by
  let F : C(Metric.closedBall (0 : A) b.radius, d.chart.beltTarget d.radius) :=
    { toFun := fun z => ⟨g z.val, hdomain z.val (b.ball_subset z.property)⟩
      continuous_toFun :=
        (hc.comp_continuous continuous_subtype_val (fun z => b.ball_subset z.property)).subtype_mk
          _ }
  have hsmallF : ∀ z, ‖(beltBallCoordinates d b.radius F z).2‖ < 1 := by
    intro z
    rw [beltBallCoordinates_normal]
    exact hsmall z.val (b.ball_subset z.property)
  have hne :
    ∀ u,
      (beltBallCoordinates d b.radius F (parameterBallBoundary b.radius b.radius_pos u)).2 ≠ 0 := by
    intro u
    rw [beltBallCoordinates_normal]
    exact smul_ne_zero (inv_ne_zero d.radius_pos.ne') (b.map u).property
  let J := beltBallBoundaryInComplement d b.radius b.radius_pos F hsmallF hne
  have hJ : ∀ u, (J u).val = g (b.radius • u.val) := by
    intro u
    exact beltBallBoundaryInComplement_coe d b.radius b.radius_pos F hsmallF hne u
  let v := (beltBallCoordinates d b.radius F (parameterBallCenter b.radius b.radius_pos)).1
  have hH := beltBallBoundary_homotopic_meridian d b.radius b.radius_pos F hsmallF hne r hr hr1
  have heq :
    (Smale.PuncturedBall.toSphere 1).comp
        (beltBallBoundaryNormal d b.radius b.radius_pos F hsmallF hne) =
      b.normalizedMap := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    exact beltBallBoundary_normalized_coe d b.radius b.radius_pos F hsmallF hne u
  rw [heq] at hH
  exact ⟨J, hJ, v, hH⟩

theorem MorseCancellation.exists_small_native_belt_neighborhood {E M A : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (G : A → d.UpperLevel) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) {t : Set A}
    (ht : t ∈ 𝓝 (0 : A)) (hc : ContinuousOn G t) (hcenter : G 0 = d.surgery.beltSphere v) :
    ∃ s : Set A,
      s ∈ 𝓝 (0 : A) ∧
        s ⊆ t ∧
          ContinuousOn G s ∧
            (∀ z ∈ s, G z ∈ d.beltNormalDomain) ∧
              (∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1) := by
  have hG : ContinuousAt G 0 := hc.continuousAt ht
  have hdomain : G 0 ∈ d.beltNormalDomain := hcenter ▸ d.belt_mem_normalDomain v
  have hsplit : ContinuousAt d.chart.splitChart (G 0).val :=
    d.chart.splitChart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.splitChart.open_source.mem_nhds hdomain)
  have hGM : ContinuousAt (fun z : A => (G z).val) 0 :=
    (continuous_subtype_val : Continuous (Subtype.val : d.UpperLevel → M)).continuousAt.comp hG
  have hsplitG : ContinuousAt (fun z : A => d.chart.splitChart (G z).val) 0 :=
    ContinuousAt.comp (f := fun z : A => (G z).val) hsplit hGM
  have hnormal : ContinuousAt (fun z => d.beltNormal (G z)) 0 := by
    change ContinuousAt (fun z : A => (d.chart.splitChart (G z).val).1) 0
    exact hsplitG.fst
  have hsize : ContinuousAt (fun z => ‖d.radius⁻¹ • d.beltNormal (G z)‖) 0 :=
    (hnormal.const_smul d.radius⁻¹).norm
  have hzero : ‖d.radius⁻¹ • d.beltNormal (G 0)‖ < 1 := by
    rw [hcenter, d.beltNormal_belt, smul_zero, norm_zero]
    norm_num
  have h₀ : G ⁻¹' d.beltNormalDomain ∈ 𝓝 (0 : A) :=
    hG.preimage_mem_nhds (d.isOpen_beltNormalDomain.mem_nhds hdomain)
  have h₁ : {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1} ∈ 𝓝 (0 : A) :=
    hsize.preimage_mem_nhds (Iio_mem_nhds hzero)
  let s := t ∩ (G ⁻¹' d.beltNormalDomain ∩ {z : A | ‖d.radius⁻¹ • d.beltNormal (G z)‖ < 1})
  refine
    ⟨s, Filter.inter_mem ht (Filter.inter_mem h₀ h₁), Set.inter_subset_left,
      hc.mono Set.inter_subset_left, ?_, ?_⟩
  · intro z hz
    exact hz.2.1
  · intro z hz
    exact hz.2.2

theorem Degree.MorseRearrangement.exists_radius_supported_bump_preparation {E F H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] [T2Space M] (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ Φ.source)
    {C : Set M} (hC : ∀ y ∈ C, y ∉ Φ '' tsupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∀ e : Diffeomorph J J M M ∞,
              (∀ y, e y = Smale.SupportedDiffeomorph.bumpFamily Φ β (a, y)) →
                Nonempty
                  (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e (Φ '' tsupport β) C) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    Smale.SupportedDiffeomorph.exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  have hone : ∀ y, A (1, y) = e y := by
    intro y
    rw [he]
    by_cases hy : y ∈ Φ.target
    · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
      have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
      rw [hpoint] at hh
      change A (1, y) = Smale.SupportedDiffeomorph.extendMap Φ (fun x => x + β x • a) y
      rw [Smale.SupportedDiffeomorph.extendMap_of_mem Φ _ hy]
      exact hh
    · have hnot : y ∉ Φ '' tsupport β := by
        rintro ⟨x, hx, rfl⟩
        exact hy (Φ.map_source' (hsupport hx))
      rw [hfix 1 y hnot, Smale.SupportedDiffeomorph.bumpFamily_fixed_outside Φ β a hnot]
  refine
    ⟨{  family := A
        smooth := hA
        zero := hzero
        one := hone
        slices := ?_
        fixedOutside := hfix
        fixedOn := fun t y hy => hfix t y (hC y hy) }⟩
  intro t
  obtain ⟨d, hd⟩ := hdiff t
  exact ⟨d, fun y => (hd y).symm⟩

theorem Degree.MorseRearrangement.ambient_patch_support_compact {G K N X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] [TopologicalSpace X]
    (p : Smale.NativeTransversality.Patch J X (N := N)) :
    IsCompact (p.chart.symm '' tsupport p.cutoff) :=
  p.cutoff_compact.isCompact.image_of_continuousOn
    (p.chart.contMDiffOn_invFun.continuousOn.mono p.cutoff_support)

theorem Degree.MorseRearrangement.exists_ambient_patch_in_open {G K N X : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] [TopologicalSpace X] [FiniteDimensional ℝ G]
    [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace X] [T2Space X] {f : X → N}
    (hf : Continuous f) {U : Set N} (hU : IsOpen U) (x : X) (hfxU : f x ∈ U) :
    ∃ p : Smale.NativeTransversality.Patch J X (N := N),
      p.Compatible f ∧ x ∈ interior p.core ∧ p.chart.symm '' tsupport p.cutoff ⊆ U := by
  let c := NoExotic.modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  let V : Set G := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcv : c (f x) ∈ V :=
    ⟨c.map_source' hcx, by
      change c.symm (c (f x)) ∈ U
      have heq : c.symm (c (f x)) = f x := c.left_inv' hcx
      rw [heq]
      exact hfxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcv)
  obtain ⟨β, hβ, hsupport, W, hW, hcenter, -, hone⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {c (f x)}) (U :=
      Metric.ball (c (f x)) r) isClosed_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (c (f x)) r).of_isClosed_subset (isClosed_tsupport β)
      (hsupport.trans Metric.ball_subset_closedBall)
  let O : Set N := c.source ∩ c ⁻¹' W
  have hO : IsOpen O := c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source hW
  have hfx : f x ∈ O := ⟨hcx, hcenter (Set.mem_singleton _)⟩
  obtain ⟨C, hC, -, hxC, hCO⟩ :=
    exists_compact_closed_between (isCompact_singleton (x := x)) (hO.preimage hf)
      (Set.singleton_subset_iff.mpr hfx)
  let p : Smale.NativeTransversality.Patch J X (N := N) :=
    { core := C
      core_compact := hC
      chart := c
      cutoff := β
      cutoff_smooth := hβ
      cutoff_compact := hcompact
      cutoff_support := hsupport.trans (hball.trans Set.inter_subset_left)
      plateau := O
      plateau_open := hO
      plateau_source := Set.inter_subset_left
      plateau_one := by
        intro y hy
        filter_upwards [hW.mem_nhds hy.2] with z hz
        exact hone hz }
  refine ⟨p, hCO, hxC (Set.mem_singleton x), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hball (hsupport hz)).2

theorem Degree.MorseRearrangement.exists_relative_ambient_patch_step {D Z G H H' K X Y N : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'} {J : ModelWithCorners ℝ G K}
    [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    [LindelofSpace (X × Y)] {ι : Type*} [Finite ι]
    (p : ι → Smale.NativeTransversality.Patch J X (N := N)) (i : ι) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {B : Set X}
    (hB : IsCompact B) (htrans : ∀ x ∈ B, ∀ y, Smale.NativeTransversality.At I I' J f g x y)
    {C : Set N} (hC : ∀ y ∈ C, y ∉ (p i).chart.symm '' tsupport (p i).cutoff) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
        (∀ x ∈ B ∪ (p i).core, ∀ y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y) ∧
          Nonempty
            (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e
              ((p i).chart.symm '' tsupport (p i).cutoff) C) := by
  let A : G × X → N := fun q =>
    Smale.SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
        (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
        (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    Smale.SupportedDiffeomorph.exists_radius_ambient_bumpFamily (p i).chart.symm
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support
  have hA : ContMDiffOn (𝓘(ℝ, G).prod I) J ∞ A (Metric.ball (0 : G) δ ×ˢ Set.univ) := by
    intro q hq
    have hsmall : ‖q.1‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hq.1
    have hpair :
      ContMDiffAt (𝓘(ℝ, G).prod I) (𝓘(ℝ, G).prod J) ∞ (fun r : G × X => (r.1, f r.2)) q :=
      contMDiffAt_fst.prodMk (hf.comp contMDiff_snd).contMDiffAt
    exact ((hsmooth (q.1, f q.2) hsmall).comp q hpair).contMDiffWithinAt
  have hzero : (fun x => A (0, x)) = f := by
    funext x
    exact Smale.SupportedDiffeomorph.bumpFamily_zero _ _ _
  have hregular :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ z ∈ B ×ˢ (Set.univ : Set Y),
        Smale.NativeTransversality.At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply
      Smale.NativeTransversality.eventually_on_compact Metric.isOpen_ball hA hg hdim
        (hB.prod isCompact_univ) (Metric.mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨η, hη, hisotopy⟩ :=
    exists_radius_supported_bump_preparation (p i).chart.symm (p i).cutoff_smooth
      (p i).cutoff_compact (p i).cutoff_support hC
  obtain ⟨a, ha, e, he, -, -, hnew⟩ :=
    Smale.ChartMapPerturbation.exists_ambient_transverse_plateau (p i).chart hf hg
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim (lt_min hε hη)
  have hgood :=
    hsmall
      (show a ∈ Metric.ball (0 : G) ε by
        simpa only [Metric.mem_ball, dist_zero_right] using (lt_min_iff.mp ha).1)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hisotopy a (lt_min_iff.mp ha).2 e he⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, Set.mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

def Degree.MorseRearrangement.compose_supported_ambient_isotopies {G K N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] {e d : Diffeomorph J J N N ∞} {K₁ K₂ C : Set N}
    (A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K₁ C)
    (B : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy d K₂ C) :
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy (e.trans d) (K₁ ∪ K₂) C
    where
  family := fun p => B.family (p.1, A.family p)
  smooth := B.smooth.comp (contMDiff_fst.prodMk A.smooth)
  zero := fun x => by rw [A.zero, B.zero]
  one := fun x => by change B.family (1, A.family (1, x)) = d (e x); rw [A.one, B.one]
  slices := by
    intro t
    obtain ⟨d₁, hd₁⟩ := A.slices t
    obtain ⟨d₂, hd₂⟩ := B.slices t
    refine ⟨d₁.trans d₂, ?_⟩
    intro x
    change d₂ (d₁ x) = B.family (t, A.family (t, x))
    rw [hd₁, hd₂]
  fixedOutside := by
    intro t x hx
    rw [A.fixedOutside t x (fun h => hx (Or.inl h)), B.fixedOutside t x (fun h => hx (Or.inr h))]
  fixedOn := by
    intro t x hx
    rw [A.fixedOn t x hx, B.fixedOn t x hx]

theorem Degree.MorseRearrangement.exists_finite_relative_patch_diffeomorph
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [LindelofSpace (X × Y)] {ι : Type*}
    [Finite ι] (p : ι → Smale.NativeTransversality.Patch J X (N := N)) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g) (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {U : Set N}
    (hsupport : ∀ j, (p j).chart.symm '' tsupport (p j).cutoff ⊆ U) (s : Finset ι) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            (∀ j, (p j).Compatible (e ∘ f)) ∧
              ∀ j ∈ s,
                ∀ x ∈ (p j).core, ∀ y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
  classical
    induction s using Finset.induction_on with
  |
    empty =>
    let A : Smale.SupportedDiffeomorph.SupportedRelativeIsotopy (Diffeomorph.refl J N ∞) ∅ Uᶜ :=
      { family := Prod.snd
        smooth := contMDiff_snd
        zero := fun _ => rfl
        one := fun _ => rfl
        slices := fun _ => ⟨Diffeomorph.refl J N ∞, fun _ => rfl⟩
        fixedOutside := fun _ _ _ => rfl
        fixedOn := fun _ _ _ => rfl }
    refine ⟨Diffeomorph.refl J N ∞, ∅, isCompact_empty, Set.empty_subset _, ⟨A⟩, hcompatible, ?_⟩
    intro j hj
    simp at hj
  | @insert i s _ ih =>
    obtain ⟨e₁, C₁, hC₁, hC₁U, ⟨A₁⟩, hc₁, ht₁⟩ := ih
    let B : Set X := ⋃ j ∈ s, (p j).core
    have hB : IsCompact B := s.isCompact_biUnion (fun j _ => (p j).core_compact)
    have htrans : ∀ x ∈ B, ∀ y, Smale.NativeTransversality.At I I' J (e₁ ∘ f) g x y := by
      intro x hx y
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact ht₁ j hj x hxj y
    obtain ⟨e₂, hc₂, ht₂, ⟨A₂⟩⟩ :=
      exists_relative_ambient_patch_step (C := Uᶜ) p i (e₁.contMDiff.comp hf) hg hc₁ hdim hB
        htrans (fun y hy hys => hy (hsupport i hys))
    refine
      ⟨e₁.trans e₂, C₁ ∪ ((p i).chart.symm '' tsupport (p i).cutoff),
        hC₁.union (ambient_patch_support_compact (p i)), Set.union_subset hC₁U (hsupport i),
        ⟨compose_supported_ambient_isotopies A₁ A₂⟩, hc₂, ?_⟩
    intro j hj x hx y
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact ht₂ x (Or.inr hx) y
    · exact ht₂ x (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hjs, hx⟩)) y

theorem Degree.MorseRearrangement.exists_supported_ambient_transverse_in_open
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [TopologicalSpace Y]
    [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y] [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [CompactSpace X] [T2Space X] {f : X → N}
    {g : Y → N} (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G) {U : Set N}
    (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            ∀ x y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
  classical
  choose p hp hx hs using fun x : X =>
    exists_ambient_patch_in_open (J := J) hf.continuous hU x (hfU (Set.mem_range_self x))
  have hcover : (Set.univ : Set X) ⊆ ⋃ x : X, interior (p x).core := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hscover⟩ :=
    isCompact_univ.elim_finite_subcover (fun x : X => interior (p x).core)
      (fun _ => isOpen_interior) hcover
  obtain ⟨e, C, hC, hCU, hIso, -, ht⟩ :=
    exists_finite_relative_patch_diffeomorph (fun i : s => p i.1) hf hg (fun i => hp i.1) hdim
      (fun i => hs i.1) Finset.univ
  refine ⟨e, C, hC, hCU, hIso, ?_⟩
  intro x y
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hscover (Set.mem_univ x))
  exact ht ⟨i, hi⟩ (Finset.mem_univ _) x (interior_subset hxi) y

theorem Degree.MorseRearrangement.exists_supported_ambient_disjoint_in_open
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {U : Set N}
    (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧
        C ⊆ U ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e C Uᶜ) ∧
            Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  classical
  let d := Module.finrank ℝ G - (Module.finrank ℝ D + Module.finrank ℝ Z)
  let f' : X × Smale.Hemisphere.Sphere d → N := f ∘ Prod.fst
  have hf' : ContMDiff (I.prod (𝓡 d)) J ∞ f' := hf.comp contMDiff_fst
  have hdim' :
    Module.finrank ℝ (D × EuclideanSpace ℝ (Fin d)) + Module.finrank ℝ Z = Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    dsimp [d]
    omega
  have hf'U : Set.range f' ⊆ U := by
    rintro _ ⟨x, rfl⟩
    exact hfU (Set.mem_range_self x.1)
  obtain ⟨e, C, hC, hCU, hIso, ht⟩ :=
    exists_supported_ambient_transverse_in_open hf' hg hdim' hU hf'U
  have htrans : ∀ x y, Smale.NativeTransversality.At I I' J (e ∘ f) g x y := by
    intro x y
    let w : Smale.Hemisphere.Sphere d := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
    apply
      native_transverse_of_ignored_factor (I'' := 𝓡 d) w
        ((e.contMDiff.comp hf).mdifferentiable (by simp) x)
    exact ht (x, w) y
  exact ⟨e, C, hC, hCU, hIso, disjoint_ranges_of_native_transverse_dimension htrans hdim⟩

theorem Degree.MorseRearrangement.exists_supported_ambient_disjoint_fixing_closed
    {D Z G H H' K X Y N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {C : Set N}
    (hC : IsClosed C) (hfC : Disjoint (Set.range f) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧
        K ⊆ Cᶜ ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K C) ∧
            Disjoint (Set.range (e ∘ f)) (Set.range g) := by
  have hfU : Set.range f ⊆ Cᶜ := fun _ hx hy => Set.disjoint_left.mp hfC hx hy
  obtain ⟨e, K, hK, hKU, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_in_open hf hg hdim hC.isOpen_compl hfU
  refine ⟨e, K, hK, hKU, ?_, hdisj⟩
  simpa only [compl_compl] using hIso

def Degree.MorseRearrangement.otherSheetImages {ι X N : Type*} (a : ι → X → N) (i : ι) : Set N :=
  ⋃ j : { j : ι // j ≠ i }, Set.range (a j.val)

theorem Degree.MorseRearrangement.mem_otherSheetImages {ι X N : Type*} (a : ι → X → N) (i j : ι)
    (hji : j ≠ i) (x : X) : a j x ∈ otherSheetImages a i :=
  Set.mem_iUnion.mpr ⟨⟨j, hji⟩, Set.mem_range_self x⟩

def Degree.MorseRearrangement.sheetSum (X : Type) : ℕ → Type
  | 0 => PEmpty
  | n + 1 => X ⊕ sheetSum X n

instance Degree.MorseRearrangement.sheetSumTopology {X : Type} [TopologicalSpace X] :
    (n : ℕ) → TopologicalSpace (sheetSum X n)
  | 0 => inferInstanceAs (TopologicalSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumTopology (X := X) n
    inferInstanceAs (TopologicalSpace (X ⊕ sheetSum X n))

instance Degree.MorseRearrangement.sheetSumCompact {X : Type} [TopologicalSpace X]
    [CompactSpace X] : (n : ℕ) → CompactSpace (sheetSum X n)
  | 0 => inferInstanceAs (CompactSpace PEmpty)
  | n + 1 =>
    let _ := sheetSumCompact (X := X) n
    inferInstanceAs (CompactSpace (X ⊕ sheetSum X n))

instance Degree.MorseRearrangement.sheetSumT2 {X : Type} [TopologicalSpace X] [T2Space X] :
    (n : ℕ) → T2Space (sheetSum X n)
  | 0 => inferInstanceAs (T2Space PEmpty)
  | n + 1 =>
    let _ := sheetSumT2 (X := X) n
    inferInstanceAs (T2Space (X ⊕ sheetSum X n))

instance Degree.MorseRearrangement.sheetSumSecondCountable {X : Type} [TopologicalSpace X]
    [SecondCountableTopology X] : (n : ℕ) → SecondCountableTopology (sheetSum X n)
  | 0 => inferInstanceAs (SecondCountableTopology PEmpty)
  | n + 1 =>
    let _ := sheetSumSecondCountable (X := X) n
    inferInstanceAs (SecondCountableTopology (X ⊕ sheetSum X n))

instance Degree.MorseRearrangement.sheetSumChartedSpace {X : Type} [TopologicalSpace X] {H : Type}
    [TopologicalSpace H] [ChartedSpace H X] : (n : ℕ) → ChartedSpace H (sheetSum X n)
  | 0 => ChartedSpace.empty H PEmpty
  | n + 1 =>
    let _ := sheetSumChartedSpace (X := X) (H := H) n
    inferInstanceAs (ChartedSpace H (X ⊕ sheetSum X n))

instance Degree.MorseRearrangement.sheetSumIsManifold {X : Type} [TopologicalSpace X] {E H : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [ChartedSpace H X] [IsManifold I ∞ X] : (n : ℕ) → IsManifold I ∞ (sheetSum X n)
  | 0 =>
    let _ : ChartedSpace H PEmpty := sheetSumChartedSpace (X := X) 0
    inferInstanceAs (IsManifold I ∞ PEmpty)
  | n + 1 =>
    let _ := sheetSumIsManifold (X := X) (I := I) n
    inferInstanceAs (IsManifold I ∞ (X ⊕ sheetSum X n))

def Degree.MorseRearrangement.sheetSumMap {X : Type} {N : Type} :
    (n : ℕ) → (Fin n → X → N) → sheetSum X n → N
  | 0, _, x => x.elim
  | n + 1, a, x => Sum.elim (a 0) (sheetSumMap n (fun i => a i.succ)) x

theorem Degree.MorseRearrangement.range_sheetSumMap {X : Type} [TopologicalSpace X] {N : Type}
    (n : ℕ) (a : Fin n → X → N) : Set.range (sheetSumMap n a) = ⋃ i, Set.range (a i) := by
  induction n with
  | zero =>
    ext y
    simp only [Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro ⟨x, _⟩
      exact x.elim
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    ext y
    constructor
    · rintro ⟨x, hx⟩
      rcases x with x | x
      · exact Set.mem_iUnion.mpr ⟨0, ⟨x, hx⟩⟩
      · have hy : y ∈ Set.range (sheetSumMap n (fun i => a i.succ)) := ⟨x, hx⟩
        rw [ih] at hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion.mpr ⟨i.succ, hi⟩
    · intro hy
      obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp hy
      cases i using Fin.cases with
      | zero => exact ⟨Sum.inl x, hx⟩
      | succ
        i =>
        have hy' : y ∈ ⋃ i : Fin n, Set.range (a i.succ) := Set.mem_iUnion.mpr ⟨i, ⟨x, hx⟩⟩
        rw [← ih] at hy'
        obtain ⟨z, hz⟩ := hy'
        exact ⟨Sum.inr z, hz⟩

theorem Degree.MorseRearrangement.contMDiff_sheetSumMap {X : Type} [TopologicalSpace X]
    {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {G K N : Type} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace N]
    [ChartedSpace K N] (n : ℕ) (a : Fin n → X → N) (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ContMDiff I J ∞ (sheetSumMap n a) := by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih => exact (ha 0).sumElim (ih (fun i => a i.succ) (fun i => ha i.succ))

theorem Degree.MorseRearrangement.exists_sheetSumMap_for_finite_family {X : Type}
    [TopologicalSpace X] {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {G K N : Type}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
    [TopologicalSpace N] [ChartedSpace K N] {ι : Type} [Finite ι] (a : ι → X → N)
    (ha : ∀ i, ContMDiff I J ∞ (a i)) :
    ∃ (n : ℕ) (b : sheetSum X n → N), ContMDiff I J ∞ b ∧ Set.range b = ⋃ i, Set.range (a i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  let a' : Fin (Fintype.card ι) → X → N := fun j => a (e.symm j)
  refine
    ⟨Fintype.card ι, sheetSumMap (Fintype.card ι) a',
      contMDiff_sheetSumMap _ a' (fun j => ha (e.symm j)), ?_⟩
  rw [range_sheetSumMap]
  ext y
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    exact Set.mem_iUnion.mpr ⟨e.symm j, hj⟩
  · intro hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨e i, ?_⟩
    simpa only [a', e.symm_apply_apply] using hi

theorem Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V) {a b c : ℝ} (ha : a < c)
    (hb : c < b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (z : { y : M // f y = c }) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          { y : M // f y = c } { y : M // f y = c } ∞)
      (K T : Set { y : M // f y = c }),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K T →
          ∃ (r : ℝ) (C : Set M) (W V' : (y : M) → TangentSpace 𝓘(ℝ, E) y) (H G : Flow ℝ M),
            0 < r ∧
              r < c - a ∧
                IsCompact C ∧
                  C ⊆ f ⁻¹' Set.Ioo a b ∧
                    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                        (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                      (∀ y, IsMIntegralCurve (fun t => H t y) W) ∧
                        (∀ y,
                            Set.range (fun t => H t y) = Set.range (fun t => F t y) ∧
                              (∀ p,
                                  Filter.Tendsto (fun t => H t y) Filter.atTop (𝓝 p) ↔
                                    Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p)) ∧
                                ∀ p,
                                  Filter.Tendsto (fun t => H t y) Filter.atBot (𝓝 p) ↔
                                    Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 p)) ∧
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ y, IsMIntegralCurve (fun t => G t y) V') ∧
                              (∀ y, V' y = 0 ↔ V y = 0) ∧
                                (∀ y,
                                    y ∉ Smale.ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f y (V' y) < 0) ∧
                                  (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ x in 𝓝 y, V' x = V x) ∧
                                    (∀ y ∉ C, ∀ᶠ x in 𝓝 y, V' x = W x) ∧
                                      (∀ x : { y : M // f y = c }, G 1 x = H 1 (D x)) ∧
                                        (∀ x : { y : M // f y = c }, f (H 1 x) = c - r) ∧
                                          (∀ x : { y : M // f y = c },
                                              ∀ t : ℝ, t ≤ 0 → G t x = H t x) ∧
                                            (∀ x : { y : M // f y = c },
                                                ∀ t : ℝ, 0 ≤ t → G t (H 1 x) = H t (H 1 x)) ∧
                                              ∀ x ∈ T, ∀ t : ℝ, G t x = H t x := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  dsimp only
  intro D K T hK I
  obtain
    ⟨r, W, H, A, hr, hrbound, hW, hH, hWzero, hWneg, hWgerm, hgeometry, hsource, -, hformula,
      hheight, hmodel⟩ :=
    Degree.FlowTimeChange.exists_normalized_whole_level_cylinder hf hV hdesc F hF ha hb hband hreg
      z
  obtain
    ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, hneg, hgerm, -, -, hfull, hend, hfixed, -, hleft,
      hright, -⟩ :=
    exists_native_whole_level_holonomy A hsource hf hr (fun p hp => hheight p ⟨hp.1.le, hp.2.le⟩)
      W hW hmodel H hH D hK I
  have hCband : C ⊆ f ⁻¹' Set.Ioo a b := by
    intro y hy
    have hh := (hCsub hy).2
    change f y ∈ Set.Ioo (c - r) c at hh
    exact ⟨by linarith [hh.1], lt_trans hh.2 hb⟩
  have hcritical (y : M) (hy : y ∈ Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 y, V' x = V x := by
    have hout : y ∉ C := fun hc => hband y ⟨(hCband hc).1.le, (hCband hc).2.le⟩ hy
    filter_upwards [hgerm y hout, hWgerm y hy] with x hx hx'
    exact hx.trans hx'
  obtain ⟨htailLeft, htailRight⟩ :=
    native_whole_level_exterior_tails A Subtype.val H G hformula D Ψ hleft hright hfull
  have hA0 (x : { y : M // f y = c }) : A (x, 0) = (x : M) := by rw [hformula, H.map_zero_apply]
  have hA1 (x : { y : M // f y = c }) : A (x, 1) = H 1 x := hformula (x, 1)
  refine
    ⟨r, C, W, V', H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV', hG, fun y =>
      (hzero y).trans (hWzero y), fun y hy => hneg y (hWneg y hy), hcritical, hgerm, ?_, ?_, ?_,
      ?_, ?_⟩
  · intro x
    rw [← hA0 x, hend, hA1]
  · intro x
    have hh := hheight (x, 1) (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    rw [hA1, mul_one] at hh
    exact hh
  · intro x t ht
    simpa only [hA0] using htailLeft x t ht
  · intro x t ht
    simpa only [hA1] using htailRight x t ht
  · intro x hx t
    have hh := hfixed x hx 0 t
    rw [hA0, zero_add, hformula] at hh
    exact hh

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_morseSurgeryData_of_field_germ_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hunique : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x = f p → x = p)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : Smale.ManifoldMorse.MorseSurgeryData E f p,
      d.radius < ε ∧
        d.chart = c ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
              f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p) ∧
            ∀ z,
              z ∈
                  Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
                    Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) →
                ∀ᶠ x in 𝓝 (d.chart.splitChart.symm z), V x = d.chart.descentField x := by
  obtain ⟨ρ, hρ, hρε, W, hW, -, heqW, hblockW, hband⟩ :=
    c.exists_isolated_fieldCompatibleBlock_lt hfinite hunique V heq hε
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hmodel :
    ∀ z,
      z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) →
        ∀ᶠ x in 𝓝 (c.splitChart.symm z), V x = c.descentField x := by
    intro z hz
    filter_upwards [hW.mem_nhds (hblockW hz).2] with x hx
    exact heqW x hx
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    exact hmodel _ (Smale.MorseHandle.modelMap_mem_product hρ z)
  obtain ⟨e, hfront, hfixed, horbit⟩ :=
    c.exists_attachingUnionHomeomorph_with_level_and_orbits hf hV hzero hdesc F hF ρ hρ hblock
      hagreement hband
  have hregular (b : ℝ) (hb : b ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2)) (hne : b ≠ f p) (x : M)
    (hx : f x = b) : x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro hcrit
    exact hne (hx.symm.trans (congrArg f (hband x hcrit (hx ▸ hb))))
  have hlower : ∀ x, f x = f p - ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨le_rfl, by linarith [sq_nonneg ρ]⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hupper : ∀ x, f x = f p + ρ ^ 2 → x ∉ Smale.ManifoldMorse.criticalPoints E f :=
    hregular _ ⟨by linarith [sq_nonneg ρ], le_rfl⟩ (by nlinarith [sq_pos_of_pos hρ])
  have hbottom : ∀ x, f x = f p - ρ ^ 2 → ∀ t : ℝ, 0 < t → f (F t x) < f p - ρ ^ 2 := by
    intro x hx t ht
    have hh :=
      Smale.FlowConstruction.strictAnti_flow_height hf (hV.of_le (by simp)) F hF hzero hdesc
        (hlower x hx) ht
    simpa only [F.map_zero_apply, hx] using hh
  have hlevel :=
    Smale.FlowConstruction.frontier_sublevel_eq_of_strict_flow hf.continuous F
      (Smale.FlowConstruction.antitone_flow_height hf F hF hzero hdesc) hbottom
  have horbits :=
    c.followsModelBoundaryOrbits_of_flow (hV.of_le (by simp)) F hF ρ hρ hblock (e := e) (horbit :=
      horbit) hmodel
  exact
    ⟨{  radius := ρ
        radius_pos := hρ
        chart := c
        block := hblock
        attachmentHomeomorph := e
        attachment_frontier := hfront
        attachment_fixed := hfixed
        attachment_model_orbits := horbits
        surgery := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e hfront
        oldExterior_eq := fun _ => rfl
        newExterior_eq := fun _ => rfl
        oldPiece_eq := fun _ => rfl
        newPiece_eq := fun _ => rfl
        belt_eq := c.beltSphere_eq_beltCoreMap hf.continuous ρ hρ hblock hlevel e hfront hfixed
        lower_regular := hlower
        upper_regular := hupper }, hρε, rfl, hband, hmodel⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_adapted_windows_with_prescribed_flow {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        Smale.ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x) :
    ∃ S : AdaptedWindows E f, S.field = V ∧ S.flow = F ∧ ∀ p, (S.data p).chart = c p := by
  have hfinite := Smale.ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := Smale.ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : Smale.ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (hr p)
  choose d hd hchart hisolated hgerm using hex
  have hseparated (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart⟩

theorem AdaptedWindows.exists_embedded_level_transport {E M G H X : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold J ∞ X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (γ : C(X, { x : M // f x = a })) (x₀ : X) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f b) →
            ∃ D :
              PartialDiffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                { x : M // f x = a } { x : M // f x = b } ∞,
              D.source = {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f b} ∧
                D.target = {y | y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a} ∧
                  ∃ Γ : C(X, { x : M // f x = b }),
                    ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
                      Function.Injective Γ ∧
                        (∀ z,
                            Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
                          (∀ z, D (γ z) = Γ z) ∧
                            (∀ z, D.symm (Γ z) = γ z) ∧
                              ∀ z, ∃ t : ℝ, S.flow t (γ z).val = (Γ z).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  let _ := Smale.RegularLevel.isManifold hf ha
  let _ := Smale.RegularLevel.isManifold hf hb
  change
    ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          (∀ z, (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f b) → _
  intro hγ hγi hγd hreach
  obtain ⟨t, ht⟩ := hreach x₀
  let zb : { x : M // f x = b } := ⟨S.flow t (γ x₀).val, ht⟩
  obtain ⟨D, hsource, htarget, horbit⟩ := S.exists_native_level_basin_transport hf ha hb (γ x₀) zb
  have hmaps (z : X) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hDγ : ContMDiff J 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hmaps z))).comp z hγ.contMDiffAt
  let Γ : C(X, { x : M // f x = b }) := ⟨D ∘ γ, hDγ.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro x y hxy
    exact hγi (D.toPartialEquiv.injOn (hmaps x) (hmaps y) hxy)
  have hΓd : ∀ z, Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv J 𝓘(ℝ, Smale.RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hmaps z)) (hγ.mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv D (hmaps z)).1.comp (hγd z)
  refine ⟨D, hsource, htarget, Γ, hDγ, hΓi, hΓd, fun _ => rfl, ?_, ?_⟩
  · intro z
    exact D.left_inv' (hmaps z)
  · intro z
    exact horbit (γ z) (hmaps z)

def MorseCancellation.standardCircleParametrization :
    Diffeomorph (𝓡 1) (𝓡 1) (Smale.Hemisphere.Sphere 1) Circle ∞ := by
  let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
  exact Smale.SphereCoordinates.standardParametrization ℂ 1

theorem MorseCancellation.contMDiff_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ) :
    ContMDiff (𝓡 1) J ∞ (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.contMDiff

theorem MorseCancellation.injective_comp_standardCircle {N : Type*} [TopologicalSpace N]
    {γ : Circle → N} (hγ : Function.Injective γ) :
    Function.Injective (γ ∘ standardCircleParametrization) :=
  hγ.comp standardCircleParametrization.injective

theorem MorseCancellation.injective_derivative_comp_standardCircle {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] {γ : Circle → N} (hγ : ContMDiff (𝓡 1) J ∞ γ)
    (hi : ∀ z, Function.Injective (mfderiv (𝓡 1) J γ z)) (z : Smale.Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z) := by
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  exact
    (hi _).comp
      (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).injective

theorem MorseCancellation.transverse_comp_standardCircle {G H N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [TopologicalSpace N]
    [ChartedSpace H N] {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] {γ : Circle → N}
    (hγ : ContMDiff (𝓡 1) J ∞ γ) (B : D →L[ℝ] G) (z : Smale.Hemisphere.Sphere 1)
    (htrans :
      Function.Surjective
        ((mfderiv (𝓡 1) J γ (standardCircleParametrization z) :
              EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
          B)) :
    Function.Surjective
      ((mfderiv (𝓡 1) J (γ ∘ standardCircleParametrization) z :
            EuclideanSpace ℝ (Fin 1) →L[ℝ] G).coprod
        B) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] G := mfderiv (𝓡 1) J γ (standardCircleParametrization z)
  let P : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 1) (𝓡 1) standardCircleParametrization z
  have hP : Function.Surjective P :=
    (standardCircleParametrization.mfderivToContinuousLinearEquiv (by simp) z).surjective
  rw [mfderiv_comp z (hγ.mdifferentiableAt (by simp))
      (standardCircleParametrization.contMDiff.mdifferentiableAt (by simp))]
  change Function.Surjective ((L.comp P).coprod B)
  exact surjective_coprod_comp_left L B P hP htrans

theorem AdaptedWindows.attachingSphere_reaches_lower_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hap : a < f p) (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q < f p → f q < a)
    (u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) :
    ((S.data p).surgery.attachingSphere u).val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let x := (S.data p).surgery.attachingSphere u
  have hback := (S.attaching_basin_iff hf p x).mpr ⟨u, rfl⟩
  obtain ⟨r, hr, q, hq, -, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hxreg : x.val ∉ Smale.ManifoldMorse.criticalPoints E f :=
    (S.data p).lower_regular x.val x.property
  have hxp : f x.val < f p := by
    have hh := x.property
    change f x.val = f p - (S.data p).radius ^ 2 at hh
    rw [hh]
    nlinarith [(S.data p).radius_pos]
  have hqa : f q < a := hgap ⟨q, hq⟩ ((hheights hxreg).1.trans hxp)
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward hap hqa

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_attaching_circle_lower_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 1 + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ e :
      Diffeomorph (𝓡 1) (𝓡 1) (Smale.Hemisphere.Sphere 1)
        (Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1) ∞,
      ∃ D :
        PartialDiffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data p).LowerLevel { y : M // f y = a } ∞,
        D.source = {x | x.val ∈ Degree.FlowCancellation.levelBasin S.flow f a} ∧
          D.target =
              {y |
                y.val ∈
                  Degree.FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p)} ∧
            ∃ Γ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }),
              ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
                Function.Injective Γ ∧
                  (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
                    (∀ z, D ((S.data p).surgery.attachingSphere (e z)) = Γ z) ∧
                      (∀ z, D.symm (Γ z) = (S.data p).surgery.attachingSphere (e z)) ∧
                        ∀ z,
                          ∃ t : ℝ,
                            S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val :=
  by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.isManifold hf ha
  let e := Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 1
  let γ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf 1).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf 1).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf 1).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf 1 (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Smale.Hemisphere.Sphere 1) :
    (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  obtain ⟨D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ
      (MorseCancellation.standardCircleParametrization.symm (1 : Circle)) hγ hγi hγd hreach
  exact ⟨e, D, hsource, htarget, Γ, hΓ, hΓi, hΓd, hD, hiD, hflow⟩

theorem AdaptedWindows.backward_basin_reaches_attaching_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)) :
    x ∈ Degree.FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨r, hr, q, hq, hback', hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x
  have hrp : r = p.val := tendsto_nhds_unique hback' hback
  have hqp : f q < f p := by
    have hh := (hheights hx).1.trans (hheights hx).2
    rwa [hrp] at hh
  have hqlo : f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper ⟨q, hq⟩).trans (S.separated ⟨q, hq⟩ p hqp)
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (S.toSurgeryWindows.lower_lt_value p) hqlo

theorem AdaptedWindows.transported_attaching_range_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {X : Type*}
    (e : X → Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (he : Function.Surjective e) (Γ : X → { y : M // f y = a })
    (hflow : ∀ z, ∃ t : ℝ, S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val)
    (y : { x : M // f x = a }) :
    y ∈ Set.range Γ ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := hflow z
    have hback :=
      (S.attaching_basin_iff hf p ((S.data p).surgery.attachingSphere (e z))).mpr ⟨e z, rfl⟩
    rw [← ht]
    exact (MorseCancellation.flow_time_atBot_limit_iff S.flow t _ p.val).mpr hback
  · intro hy
    obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p (ha y.val y.property) hy
    let x : (S.data p).LowerLevel := ⟨S.flow t y.val, ht⟩
    have hxback : Filter.Tendsto (fun s => S.flow s x.val) Filter.atBot (𝓝 p.val) :=
      (MorseCancellation.flow_time_atBot_limit_iff S.flow t y.val p.val).mpr hy
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p x).mp hxback
    obtain ⟨z, hz⟩ := he u
    obtain ⟨s, hs⟩ := hflow z
    have hattach : S.flow t y.val = ((S.data p).surgery.attachingSphere (e z)).val := by
      rw [hz]
      exact (congrArg Subtype.val hu).symm
    have hshared : S.flow 0 (Γ z).val = S.flow (s + t) y.val := by
      rw [S.flow.map_zero_apply, S.flow.map_add, hattach, hs]
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun w hw => S.descent w (ha w hw)) (Γ z).property y.property hshared

theorem AdaptedWindows.forward_endpoint_of_attaching_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hbranches :
      ∀ u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
          (𝓝 p.val))
    {x : M} (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val)) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val) := by
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf q hx hback
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff S.flow t x q.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  have hyforward : Filter.Tendsto (fun s => S.flow s y.val) Filter.atTop (𝓝 p.val) := by
    rw [← hu]
    exact hbranches u
  exact (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mp hyforward

theorem AdaptedWindows.attaching_branches_of_same_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hflow : T.flow = S.flow)
    (hbranches :
      ∀ u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
          (𝓝 p.val)) :
    ∀ u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val) := by
  intro u
  let x := (T.data q).surgery.attachingSphere u
  have hback := (T.attaching_basin_iff hf q x).mpr ⟨u, rfl⟩
  rw [hflow] at hback ⊢
  exact
    S.forward_endpoint_of_attaching_branches hf p q hbranches
      ((T.data q).lower_regular x.val x.property) hback

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        Smale.ManifoldMorse.SignedMorseChart (E := E) f p.val)
    (hmodel :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ S : AdaptedWindows E f,
      S.field = V ∧ S.flow = F ∧ (∀ p, (S.data p).chart = c p) ∧ ∀ p, (S.data p).radius < ε p := by
  have hfinite := Smale.ManifoldMorse.finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := Smale.ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex (p : Smale.ManifoldMorse.criticalPoints E f) :=
    exists_morseSurgeryData_of_field_germ_lt hf hfinite hV F hF hzero hdesc (c p)
      (fun x hx hfx => hinj hx p.property hfx) (hmodel p) (lt_min (hr p) (hε p))
  choose d hd hchart hisolated hgerm using hex
  have hdr (p : Smale.ManifoldMorse.criticalPoints E f) : (d p).radius < r p :=
    (hd p).trans_le (min_le_left _ _)
  have hde (p : Smale.ManifoldMorse.criticalPoints E f) : (d p).radius < ε p :=
    (hd p).trans_le (min_le_right _ _)
  have hseparated (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := hseparated
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hgerm }, rfl, rfl, hchart, hde⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_same_flow_windows_avoiding_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ T : AdaptedWindows E f,
      T.field = S.field ∧
        T.flow = S.flow ∧
          (∀ p, (T.data p).chart = (S.data p).chart) ∧
            (∀ p : Smale.ManifoldMorse.criticalPoints E f,
                f p < a → T.toSurgeryWindows.upper p < a) ∧
              ∀ p : Smale.ManifoldMorse.criticalPoints E f,
                a < f p → a < T.toSurgeryWindows.lower p := by
  let ε : Smale.ManifoldMorse.criticalPoints E f → ℝ := fun p => Real.sqrt |f p - a|
  have hε (p : Smale.ManifoldMorse.criticalPoints E f) : 0 < ε p := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (sub_ne_zero.mpr (fun h => ha p.val h p.property))
  obtain ⟨T, hfield, hflow, hcharts, hsmall⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
      S.integral S.zero S.descent (fun p => (S.data p).chart) S.critical_model_germ ε hε
  have hsq (p : Smale.ManifoldMorse.criticalPoints E f) : (T.data p).radius ^ 2 < |f p - a| := by
    have hp := mul_pos (sub_pos.mpr (hsmall p)) (add_pos (hε p) (T.data p).radius_pos)
    have heq : (ε p) ^ 2 = |f p - a| := Real.sq_sqrt (abs_nonneg _)
    nlinarith
  refine ⟨T, hfield, hflow, hcharts, ?_, ?_⟩
  · intro p hp
    have hh := hsq p
    rw [abs_of_neg (sub_neg.mpr hp)] at hh
    change f p + (T.data p).radius ^ 2 < a
    linarith
  · intro p hp
    have hh := hsq p
    rw [abs_of_pos (sub_pos.mpr hp)] at hh
    change a < f p - (T.data p).radius ^ 2
    linarith

theorem AdaptedWindows.regular_interval_around_level {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    {a : ℝ} (hreg : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ l u : ℝ,
      l < a ∧ a < u ∧ ∀ x, f x ∈ Set.Icc l u → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
  have ha : a ∉ f '' Smale.ManifoldMorse.criticalPoints E f := by
    rintro ⟨x, hx, hfx⟩
    exact hreg x hfx hx
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp ((S.finite.image f).isClosed.isOpen_compl.mem_nhds ha)
  refine ⟨a - ε / 2, a + ε / 2, by linarith, by linarith, ?_⟩
  intro x hx hcrit
  have hh : f x ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  exact hball hh ⟨x, hcrit, rfl⟩

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.realize_one_handle_minimum_branches {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (p r :
      Smale.ManifoldMorse.criticalPoints E f),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
            (∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
              (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                MorseCancellation.nativeMorseIndex E f p = 0 ∧
                  MorseCancellation.nativeMorseIndex E f r = 0 ∧
                    p ≠ r ∧
                      f p < S.toSurgeryWindows.lower q ∧
                        f r < S.toSurgeryWindows.lower q ∧
                          (∀ x : (S.data q).LowerLevel,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
                                x ∈ Set.range (S.data q).surgery.attachingSphere) ∧
                            Filter.Tendsto
                                (fun t => G t ((S.data q).surgery.attachingSphere u).val)
                                Filter.atTop (𝓝 p.val) ∧
                              Filter.Tendsto
                                  (fun t => G t ((S.data q).surgery.attachingSphere v).val)
                                  Filter.atTop (𝓝 r.val) ∧
                                (∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
                                    Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 p.val) ∨
                                      Filter.Tendsto
                                        (fun t => G t ((S.data q).surgery.attachingSphere w).val)
                                        Filter.atTop (𝓝 r.val)) ∧
                                  ∀ j : Smale.ManifoldMorse.criticalPoints E f,
                                    j ≠ q →
                                      j ≠ p →
                                        j ≠ r →
                                          ∀ x,
                                            ¬(Filter.Tendsto (fun t => G t x) Filter.atBot
                                                  (𝓝 q.val) ∧
                                                Filter.Tendsto (fun t => G t x) Filter.atTop
                                                  (𝓝 j.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, p, r, hp, hr, hpr, hpq, hrq, hpu, hrv, hall⟩ :=
    S.place_one_handle_in_distinct_minimum_basins hf q hone u v hnot
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, hρ, hρbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 p.val) ∨
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
        (𝓝 r.val) :=
    (hall w).imp ((hforward _ p.val).mpr) ((hforward _ r.val).mpr)
  refine
    ⟨V, G, p, r, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hp, hr, hpr,
      hpq, hrq, hbq, (hforward _ p.val).mpr hpu, (hforward _ r.val).mpr hrv, hends, ?_⟩
  intro j hjq hjp hjr x hx
  have hmono :=
    Smale.FlowConstruction.antitone_flow_height hf G hG (fun y hy => (hzero y).mpr (S.zero y hy))
      hdesc x
  have hforwardHeight := hf.continuous.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuous.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f q :=
    (hmono.le_of_tendsto hforwardHeight 0).trans (hmono.ge_of_tendsto hbackwardHeight 0)
  have hjq' : f j < f q :=
    lt_of_le_of_ne hle (fun h => hjq (Subtype.ext (S.distinct j.property q.property h)))
  have hjlow : f j < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper j).trans (S.separated j q hjq')
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
      (S.toSurgeryWindows.lower_lt_value q) hjlow
  let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
  have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
  have hzj : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 j.val) :=
    (MorseCancellation.flow_time_atTop_limit_iff G t x j.val).mpr hx.2
  obtain ⟨w, hw⟩ := (hbq z).mp hzq
  have hh := hends w
  rw [hw] at hh
  rcases hh with hp' | hr'
  · exact hjp (Subtype.ext (tendsto_nhds_unique hzj hp'))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzj hr'))

theorem AdaptedWindows.exists_relative_level_surgery_system {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ Smale.ManifoldMorse.criticalPoints E f) (z : { y : M // f y = c })
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := Smale.RegularLevel.chartedSpace hf hc
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          { y : M // f y = c } { y : M // f y = c } ∞)
      (K P : Set { y : M // f y = c }),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K P →
          ∃ T : AdaptedWindows E f,
            (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < ε p) ∧
                (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f,
                    ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
                  (∀ x : { y : M // f y = c },
                      ∀ p : M,
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
                          Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p)) ∧
                    (∀ x : { y : M // f y = c },
                        ∀ p : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
                            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p)) ∧
                      ∀ x ∈ P,
                        Set.range (fun t => T.flow t x.val) =
                          Set.range (fun t => S.flow t x.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf hc
  dsimp only
  intro D K P hK I
  obtain ⟨a, b, ha, hb, hband⟩ := S.regular_interval_around_level hc
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright, hprotected⟩ :=
    Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral ha hb hband hc z D K P hK I
  have hmodel (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct hV G hG
      (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val D
      (fun x p => (hgeometry x).2.1 p) (fun x p => (hgeometry x).2.2 p) hend hleft hright
  refine ⟨T, hcharts, hradii, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x p
    rw [hflow]
    exact hback x p
  · intro x p
    rw [hflow]
    exact hforward x p
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = (fun t => H t x.val) := funext (fun t => hprotected x hx t)
    rw [heq]
    exact (hgeometry x.val).1

theorem AdaptedWindows.exists_native_family_level_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (za : { x : M // f x = a })
    (zb : { x : M // f x = b }) (α : ι → X → { x : M // f x = a }) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            (∀ j x, (α j x).val ∈ Degree.FlowCancellation.levelBasin S.flow f b) →
              ∃ β : ι → X → { x : M // f x = b },
                (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j)) ∧
                  (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                    (∀ j x,
                        Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (β j) x)) ∧
                      Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  let _ := Smale.RegularLevel.isManifold hf ha
  let _ := Smale.RegularLevel.isManifold hf hb
  dsimp only
  intro hα hαinj hαimm hpair hreach
  obtain ⟨P, hsource, -, horbit⟩ := S.exists_native_level_basin_transport hf ha hb za zb
  have hsrc (j : ι) (x : X) : α j x ∈ P.source := by
    rw [hsource]
    exact hreach j x
  let β : ι → X → { x : M // f x = b } := fun j => P ∘ α j
  have hβ (j : ι) : ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j) := by
    intro x
    exact
      (P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))).comp x
        (hα j).contMDiffAt
  have hinj (j : ι) : Function.Injective (β j) := by
    intro x y hxy
    exact hαinj j (P.toPartialEquiv.injOn (hsrc j x) (hsrc j y) hxy)
  refine
    ⟨β, hβ, fun j => (hβ j).continuous.isClosedEmbedding (hinj j), ?_, ?_, fun j x =>
      horbit (α j x) (hsrc j x)⟩
  · intro j x
    have hP := P.contMDiffOn_toFun.contMDiffAt (P.open_source.mem_nhds (hsrc j x))
    change Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (P ∘ α j) x)
    rw [mfderiv_comp x (hP.mdifferentiableAt (by simp)) ((hα j).mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv P (hsrc j x)).injective.comp (hαimm j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hiz hjz
    obtain ⟨x, hx⟩ := hiz
    obtain ⟨y, hy⟩ := hjz
    have heq : α i x = α j y := P.toPartialEquiv.injOn (hsrc i x) (hsrc j y) (hx.trans hy.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨y, heq.symm⟩

theorem AdaptedWindows.reaches_lower_of_excluded_critical_limit {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M)
    (hwindow : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∈ Set.Icc a b → q = p)
    (x : { y : M // f y = b })
    (hexcluded : ¬Filter.Tendsto (fun t => S.flow t x.val) Filter.atTop (𝓝 p)) :
    x.val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hregular := hb x.val x.property
  have hbelow : f r < a := by
    by_contra h
    have hrb : f r < b := by simpa only [x.property] using (hheights hregular).1
    have heq := hwindow r hr ⟨le_of_not_gt h, hrb.le⟩
    exact hexcluded (heq ▸ hforward)
  have habove : a < f q := by
    have hbq : b < f q := by simpa only [x.property] using (hheights hregular).2
    exact hab.trans hbq
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward habove hbelow

theorem AdaptedWindows.reaches_old_lower_of_belt_avoidance {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (D : (S.data p).UpperLevel → (S.data p).UpperLevel)
    (hforward :
      ∀ x : (S.data p).UpperLevel,
        ∀ q : M,
          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 q) ↔
            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 q))
    (x : (S.data p).UpperLevel) (hx : D x ∉ Set.range (S.data p).surgery.beltSphere) :
    x.val ∈ Degree.FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
  apply
    T.reaches_lower_of_excluded_critical_limit hf
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
      (S.data p).upper_regular p.val (S.isolated p) x
  intro h
  exact hx ((S.belt_basin_iff hf p (D x)).mp ((hforward x p.val).mp h))

theorem Degree.MorseRearrangement.exists_whole_family_avoidance {ι D Z G H H' K X Y N : Type}
    [Finite ι] [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
    {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] (a : ι → X → N)
    (ha : ∀ j, ContMDiff I J ∞ (a j)) {g : Y → N} (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) {C : Set N}
    (hC : IsClosed C) (haC : ∀ j, Disjoint (Set.range (a j)) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧
        K ⊆ Cᶜ ∧
          Nonempty (Smale.SupportedDiffeomorph.SupportedRelativeIsotopy e K C) ∧
            ∀ j, Disjoint (Set.range (e ∘ a j)) (Set.range g) := by
  obtain ⟨n, b, hb, hbrange⟩ := exists_sheetSumMap_for_finite_family a ha
  have hbC : Disjoint (Set.range b) C := by
    apply Set.disjoint_left.mpr
    intro z hz hzC
    rw [hbrange] at hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    exact Set.disjoint_left.mp (haC j) hj hzC
  obtain ⟨e, K, hK, hKC, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_fixing_closed hb hg hdim hC hbC
  refine ⟨e, K, hK, hKC, hIso, ?_⟩
  intro j
  apply Set.disjoint_left.mpr
  intro z hz hzg
  obtain ⟨x, hx⟩ := hz
  have hx' : a j x ∈ Set.range b := by
    rw [hbrange]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_range_self x⟩
  obtain ⟨w, hw⟩ := hx'
  apply Set.disjoint_left.mp hdisj _ hzg
  refine ⟨w, ?_⟩
  change e (b w) = z
  rw [hw]
  exact hx

theorem AdaptedWindows.exists_middle_family_descent {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 3)
    (α : ι → (Smale.Hemisphere.Sphere 2) → (S.data p).UpperLevel) {P : Set (S.data p).UpperLevel}
    (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ β : ι → (Smale.Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (β j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                                  (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (β j x).val) ∧
                                    ∀ j x q,
                                      Filter.Tendsto (fun t => T.flow t (β j x).val) Filter.atBot
                                          (𝓝 q) ↔
                                        Filter.Tendsto (fun t => S.flow t (α j x).val)
                                          Filter.atBot (𝓝 q) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hs := (S.data p).chart.finrank_negative_add_positive
      have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
      omega⟩
  dsimp only
  intro hα hαinj hαimm hpair
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) <
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by simp [Smale.RegularLevel.Model, hdim]
  obtain ⟨D, K, hK, -, ⟨A⟩, havoid⟩ :=
    Degree.MorseRearrangement.exists_whole_family_avoidance α hα ((S.data p).belt_smooth hf 2)
      hdim' hP hαP
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
  let u :=
    Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2 x₀
  let v :=
    Smale.SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected⟩ :=
    S.exists_relative_level_surgery_system hf hm (S.data p).upper_regular
      ((S.data p).surgery.beltSphere v) ε hε D K P hK A
  have hreach (j : ι) (x : (Smale.Hemisphere.Sphere 2)) :
    (α j x).val ∈ Degree.FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
    apply S.reaches_old_lower_of_belt_avoidance T hf p D hforward (α j x)
    intro hx
    exact Set.disjoint_left.mp (havoid j) ⟨x, rfl⟩ hx
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    T.exists_native_family_level_transport hf (S.data p).upper_regular (S.data p).lower_regular
      ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u) α hα hαinj hαimm
      hpair hreach
  refine ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j x q
  obtain ⟨t, ht⟩ := horbit j x
  rw [← ht]
  exact (MorseCancellation.flow_time_atBot_limit_iff T.flow t (α j x).val q).trans (hback (α j x) q)

theorem AdaptedWindows.exists_native_attaching_lower_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (hap : a < f p)
    (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q < f p → f q < a) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ Γ : C(Smale.Hemisphere.Sphere n, { y : M // f y = a }),
      ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
        Topology.IsClosedEmbedding Γ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
            (∀ z,
                ∃ t : ℝ,
                  S.flow t
                      ((S.data p).surgery.attachingSphere
                          (Smale.SphereCoordinates.standardParametrization
                            (S.data p).chart.NegativeCoordinates n z)).val =
                    (Γ z).val) ∧
              ∀ y : { x : M // f x = a },
                y ∈ Set.range Γ ↔
                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let e := Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates n
  let γ : C(Smale.Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    ⟨(S.data p).surgery.attachingSphere ∘ e,
      ((S.data p).attaching_smooth hf n).continuous.comp e.continuous⟩
  have hγ : ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ :=
    ((S.data p).attaching_smooth hf n).comp e.contMDiff
  have hγi : Function.Injective γ :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  have hγd : ∀ z, Function.Injective (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z) := by
    intro z
    change
      Function.Injective
        (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e)
          z)
    rw [mfderiv_comp z (((S.data p).attaching_smooth hf n).mdifferentiableAt (by simp))
        (e.contMDiff.mdifferentiableAt (by simp))]
    exact
      ((S.data p).attaching_derivative_injective hf n (e z)).comp
        (e.mfderivToContinuousLinearEquiv (by simp) z).injective
  have hreach (z : Smale.Hemisphere.Sphere n) :
    (γ z).val ∈ Degree.FlowCancellation.levelBasin S.flow f a :=
    S.attachingSphere_reaches_lower_cut hf p hap hgap (e z)
  let x₀ : Smale.Hemisphere.Sphere n := Smale.Hemisphere.point Bool.true ⟨0, by simp []⟩
  obtain ⟨D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha γ x₀ hγ hγi hγd hreach
  refine ⟨Γ, hΓ, hΓ.continuous.isClosedEmbedding hΓi, hΓd, hflow, ?_⟩
  intro y
  exact S.transported_attaching_range_iff hf p ha e e.surjective Γ hflow y

theorem AdaptedWindows.not_backward_basin_on_upper_level {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (x : (S.data p).UpperLevel) :
    ¬Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) := by
  intro hx
  obtain ⟨q, hq, r, hr, hback, _, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have heq : q = p.val := tendsto_nhds_unique hback hx
  have hh := (hheights ((S.data p).upper_regular x.val x.property)).2
  rw [heq, x.property] at hh
  exact (not_lt_of_ge (S.toSurgeryWindows.value_lt_upper p).le) hh

theorem AdaptedWindows.transported_backward_basin_image {E M X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M) (hap : a < f p)
    (α : X → { y : M // f y = a }) (β : X → { y : M // f y = b })
    (hα :
      ∀ x : { y : M // f y = a },
        x ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p))
    (horbit : ∀ z, ∃ t : ℝ, S.flow t (α z).val = (β z).val) :
    ∀ y : { x : M // f x = b },
      y ∈ Set.range β ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact
      (MorseCancellation.flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
        ((hα (α z)).mp (Set.mem_range_self z))
  · intro hy
    obtain ⟨q, hq, r, hr, _, hforward, hheights⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
        S.descent S.distinct y.val
    have hrb : f r < b := by simpa only [y.property] using (hheights (hb y.val y.property)).1
    obtain ⟨s, hs⟩ :=
      Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hy
        hforward hap (hrb.trans hab)
    let x : { z : M // f z = a } := ⟨S.flow s y.val, hs⟩
    have hx : Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) :=
      (MorseCancellation.flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hα x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancellation.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

def MorseCancellation.nativeIndexThreeAttachingSphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) : C((Smale.Hemisphere.Sphere 2), (S.data p).LowerLevel) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  exact
    (S.data p).surgery.attachingSphere.comp
      ((Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
            2).toHomeomorph :
        C((Smale.Hemisphere.Sphere 2),
          Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1))

theorem AdaptedWindows.exists_middle_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancellation.nativeMorseIndex E f p = 3) (n : ℕ)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data p).UpperLevel)
    {P : Set (S.data p).UpperLevel} (hP : IsClosed P) (hαP : ∀ j, Disjoint (Set.range (α j)) P)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ T : AdaptedWindows E f,
              (∀ q, (T.data q).chart = (S.data q).chart) ∧
                (∀ q, (T.data q).radius < ε q) ∧
                  (∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
                    (∀ x : (S.data p).UpperLevel,
                        ∀ q : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 q) ↔
                            Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        ∃ Γ : Fin (n + 1) → (Smale.Hemisphere.Sphere 2) → (S.data p).LowerLevel,
                          (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (Γ j)) ∧
                            (∀ j, Topology.IsClosedEmbedding (Γ j)) ∧
                              (∀ j x,
                                  Function.Injective
                                    (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (Γ j) x)) ∧
                                Pairwise
                                    (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) ∧
                                  (∀ x,
                                      ∃ t : ℝ,
                                        T.flow t
                                            (MorseCancellation.nativeIndexThreeAttachingSphere T p hp
                                                x).val =
                                          (Γ 0 x).val) ∧
                                    (∀ y : (S.data p).LowerLevel,
                                        y ∈ Set.range (Γ 0) ↔
                                          Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot
                                            (𝓝 p.val)) ∧
                                      (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (Γ j.succ x).val) ∧
                                        (∀ j x q,
                                            Filter.Tendsto (fun t => T.flow t (Γ j.succ x).val)
                                                Filter.atBot (𝓝 q) ↔
                                              Filter.Tendsto (fun t => S.flow t (α j x).val)
                                                Filter.atBot (𝓝 q)) ∧
                                          ∀ j q,
                                            S.toSurgeryWindows.upper p < f q →
                                              (∀ x : (S.data p).UpperLevel,
                                                  x ∈ Set.range (α j) ↔
                                                    Filter.Tendsto (fun t => S.flow t x.val)
                                                      Filter.atBot (𝓝 q)) →
                                                ∀ y : (S.data p).LowerLevel,
                                                  y ∈ Set.range (Γ j.succ) ↔
                                                    Filter.Tendsto (fun t => T.flow t y.val)
                                                      Filter.atBot (𝓝 q) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  dsimp only
  intro hα hαinj hαimm hpair
  obtain
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, hlabels⟩ :=
    S.exists_middle_family_descent hf hm hdim p hp α hP hαP ε hε hα hαinj hαimm hpair
  let _ : Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancellation.nativeMorseIndex_eq_chart (T.data p).chart).symm.trans hp⟩
  have hgap (q : Smale.ManifoldMorse.criticalPoints E f) (hqp : f q < f p) :
    f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper q).trans (S.separated q p hqp)
  obtain ⟨γ, hγ, hγe, hγi, hγflow, hγrange⟩ :=
    T.exists_native_attaching_lower_cut hf p 2 (S.data p).lower_regular
      (S.toSurgeryWindows.lower_lt_value p) hgap
  have hdisj (j : Fin n) : Disjoint (Set.range γ) (Set.range (β j)) := by
    apply Set.disjoint_left.mpr
    intro z hzγ hzβ
    obtain ⟨x, hx⟩ := hzβ
    have hb := (hγrange z).mp hzγ
    rw [← hx] at hb
    exact S.not_backward_basin_on_upper_level hf p (α j x) ((hlabels j x p.val).mp hb)
  let Γ : Fin (n + 1) → (Smale.Hemisphere.Sphere 2) → (S.data p).LowerLevel := Fin.cases γ β
  have hΓpair : Pairwise (fun i j => Disjoint (Set.range (Γ i)) (Set.range (Γ j))) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdisj j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdisj i).symm
      | succ j => exact hβpair (fun h => hij (congrArg Fin.succ h))
  refine
    ⟨T, hcharts, hradii, hgerms, hback, hprotected, Γ, ?_, ?_, ?_, hΓpair, hγflow, hγrange,
      horbit, hlabels, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hγ
    | succ j => exact hβ j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγe
    | succ j => exact hβe j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγi
    | succ j => exact hβi j
  · intro j q hq hfull
    apply
      T.transported_backward_basin_image hf
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
        (S.data p).lower_regular q hq (α j) (β j)
    · intro x
      exact (hfull x).trans (hback x q).symm
    · exact horbit j

theorem AdaptedWindows.reaches_lower_in_regular_band {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (x : { y : M // f y = a }) : x.val ∈ Degree.FlowCancellation.levelBasin S.flow f b := by
  obtain ⟨q, hq, r, hr, hback, hforward, hheights⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct x.val
  have hra : f r < a := by simpa only [x.property] using (hheights (ha x.val x.property)).1
  have haq : a < f q := by simpa only [x.property] using (hheights (ha x.val x.property)).2
  have hrb : f r < b := by
    by_contra h
    exact hgap r hr ⟨le_of_not_gt h, hra.le⟩
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hback
      hforward (hab.trans haq) hrb

theorem AdaptedWindows.exists_regular_band_family_transport {ι E M F H X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) (α : ι → X → { x : M // f x = a }) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    let _ := Smale.RegularLevel.chartedSpace hf hb
    (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) →
      (∀ j, Function.Injective (α j)) →
        (∀ j x, Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) →
          Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) →
            ∃ β : ι → X → { x : M // f x = b },
              (∀ j, ContMDiff I 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (β j)) ∧
                (∀ j, Topology.IsClosedEmbedding (β j)) ∧
                  (∀ j x,
                      Function.Injective (mfderiv I 𝓘(ℝ, Smale.RegularLevel.Model E) (β j) x)) ∧
                    Pairwise (fun i j => Disjoint (Set.range (β i)) (Set.range (β j))) ∧
                      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                        ∀ j q,
                          a < f q →
                            (∀ x : { y : M // f y = a },
                                x ∈ Set.range (α j) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 q)) →
                              ∀ y : { x : M // f x = b },
                                y ∈ Set.range (β j) ↔
                                  Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 q) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  dsimp only
  intro hα hαinj hαimm hpair
  obtain ⟨t, ht⟩ := S.reaches_lower_in_regular_band hf hab ha hgap za
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb za ⟨S.flow t za.val, ht⟩ α hα hαinj hαimm
      hpair (fun j x => S.reaches_lower_in_regular_band hf hab ha hgap (α j x))
  refine ⟨β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j q hq hfull
  exact S.transported_backward_basin_image hf hab hb q hq (α j) (β j) hfull (horbit j)

def MorseCancellation.IsNativeMiddleBasinFamily {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a }) : Prop :=
  let _ := Smale.RegularLevel.chartedSpace hf ha
  (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (α j)) ∧
    (∀ j, Topology.IsClosedEmbedding (α j)) ∧
      (∀ j x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (α j) x)) ∧
        Pairwise (fun i j => Disjoint (Set.range (α i)) (Set.range (α j))) ∧
          ∀ j y,
            y ∈ Set.range (α j) ↔
              Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 (p j).val)

theorem AdaptedWindows.exists_regular_band_middle_basin_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgap : ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, f q ∉ Set.Icc b a)
    (za : { x : M // f x = a }) {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j)) (α : Fin n → (Smale.Hemisphere.Sphere 2) → { x : M // f x = a })
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ β : Fin n → (Smale.Hemisphere.Sphere 2) → { x : M // f x = b },
      MorseCancellation.IsNativeMiddleBasinFamily S hf hb p β ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨β, hβs, hβe, hβi, hβpair, hflow, hβfull⟩ :=
    S.exists_regular_band_family_transport hf hab ha hb hgap za α hs (fun j => (he j).injective)
      hi hpair
  exact ⟨β, ⟨hβs, hβe, hβi, hβpair, fun j => hβfull j (p j).val (hp j) (hfull j)⟩, hflow⟩

theorem AdaptedWindows.exists_middle_basin_family_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hq : MorseCancellation.nativeMorseIndex E f q = 3) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data q).UpperLevel)
    (hα : MorseCancellation.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p α)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ r, 0 < ε r) :
    ∃ T : AdaptedWindows E f,
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
        (∀ r, (T.data r).radius < ε r) ∧
          (∀ r ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 r, T.field y = S.field y) ∧
            ∃ Γ : Fin (n + 1) → (Smale.Hemisphere.Sphere 2) → (S.data q).LowerLevel,
              MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular (Fin.cases q p)
                Γ := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨T, hcharts, hradii, hgerms, -, -, Γ, hΓs, hΓe, hΓi, hΓpair, -, hΓzero, -, -, hΓfull⟩ :=
    S.exists_middle_family_step hf hm hdim q hq n α isClosed_empty (fun j => Set.disjoint_empty _)
      ε hε hs (fun j => (he j).injective) hi hpair
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓs, hΓe, hΓi, hΓpair, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact hΓzero
  | succ j => exact hΓfull j (p j).val (hp j) (hfull j)

theorem AdaptedWindows.exists_middle_block_realization {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (n : ℕ) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancellation.nativeMorseIndex E f (p j) = 3)
    (horder : StrictMono (fun j => f (p j))) (habove : ∀ j, c < f (p j))
    (hblock :
      ∀ j (q : Smale.ManifoldMorse.criticalPoints E f), c < f q → f q ≤ f (p j) → q ∈ Set.range p)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    ∃ T : AdaptedWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
        (∀ q, (T.data q).radius < ε q) ∧
          (∀ q ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
            ∃ α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = c },
              MorseCancellation.IsNativeMiddleBasinFamily T hf hc p α := by
  induction n generalizing S c ε with
  |
    zero =>
    obtain ⟨T, hfield, -, hcharts, hradii⟩ :=
      MorseCancellation.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct S.smooth S.flow
        S.integral S.zero S.descent (fun q => (S.data q).chart) S.critical_model_germ ε hε
    refine ⟨T, hcharts, hradii, ?_, (fun j => Fin.elim0 j), ?_⟩
    · intro q hq
      exact Filter.Eventually.of_forall (fun y => congrFun hfield y)
    · exact
        ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
          fun j => Fin.elim0 j⟩
  | succ n ih =>
    let a := S.toSurgeryWindows.upper (p 0)
    have hpa : f (p 0) < a := S.toSurgeryWindows.value_lt_upper (p 0)
    have htail (j : Fin n) : a < f (p j.succ) :=
      (S.separated (p 0) (p j.succ) (horder (Fin.succ_pos j))).trans
        (S.toSurgeryWindows.lower_lt_value (p j.succ))
    have htailblock (j : Fin n) (q : Smale.ManifoldMorse.criticalPoints E f) (haq : a < f q)
      (hqj : f q ≤ f (p j.succ)) : q ∈ Set.range (fun i : Fin n => p i.succ) := by
      obtain ⟨i, hi⟩ := hblock j.succ q ((habove 0).trans (hpa.trans haq)) hqj
      cases i using Fin.cases with
      | zero => exact (not_lt_of_ge haq.le (hi ▸ hpa)).elim
      | succ i => exact ⟨i, hi⟩
    let δ := Real.sqrt (f (p 0) - c)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (sub_pos.mpr (habove 0))
    let η : Smale.ManifoldMorse.criticalPoints E f → ℝ := fun q =>
      Min.min (ε q) (Min.min (S.data q).radius δ)
    have hη (q : Smale.ManifoldMorse.criticalPoints E f) : 0 < η q :=
      lt_min (hε q) (lt_min (S.data q).radius_pos hδ)
    obtain ⟨T, hchartsT, hradiiT, hgermsT, α, hα⟩ :=
      ih S (S.data (p 0)).upper_regular (fun j => p j.succ) (fun j => hp j.succ)
        (fun i j hij => horder (Fin.succ_lt_succ_iff.mpr hij)) htail htailblock η hη
    have hradius : (T.data (p 0)).radius < (S.data (p 0)).radius :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hradδ : (T.data (p 0)).radius < δ :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hupper : T.toSurgeryWindows.upper (p 0) < a := by
      have hh :=
        mul_pos (sub_pos.mpr hradius)
          (add_pos (S.data (p 0)).radius_pos (T.data (p 0)).radius_pos)
      change f (p 0) + (T.data (p 0)).radius ^ 2 < f (p 0) + (S.data (p 0)).radius ^ 2
      nlinarith
    have hlower : c < T.toSurgeryWindows.lower (p 0) := by
      have hh := mul_pos (sub_pos.mpr hradδ) (add_pos hδ (T.data (p 0)).radius_pos)
      have hs : δ ^ 2 = f (p 0) - c := Real.sq_sqrt (sub_pos.mpr (habove 0)).le
      change c < f (p 0) - (T.data (p 0)).radius ^ 2
      nlinarith
    have hgapUpper :
      ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc (T.toSurgeryWindows.upper (p 0)) a := by
      intro q hq hh
      have heq :=
        S.isolated (p 0) q hq
          ⟨((S.toSurgeryWindows.lower_lt_value (p 0)).trans
                  (T.toSurgeryWindows.value_lt_upper (p 0))).le.trans
              hh.1,
            hh.2⟩
      rw [heq] at hh
      exact not_le_of_gt (T.toSurgeryWindows.value_lt_upper (p 0)) hh.1
    let _ : Fact (Module.finrank ℝ (S.data (p 0)).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hs := (S.data (p 0)).chart.finrank_negative_add_positive
        have hn := (MorseCancellation.nativeMorseIndex_eq_chart (S.data (p 0)).chart).symm.trans (hp 0)
        omega⟩
    let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
    let v :=
      Smale.SphereCoordinates.standardParametrization (S.data (p 0)).chart.PositiveCoordinates 2
        x₀
    obtain ⟨β, hβ, -⟩ :=
      T.exists_regular_band_middle_basin_family hf hupper (S.data (p 0)).upper_regular
        (T.data (p 0)).upper_regular hgapUpper ((S.data (p 0)).surgery.beltSphere v)
        (fun j => p j.succ) htail α hα
    obtain ⟨U, hchartsU, hradiiU, hgermsU, Γ, hΓ⟩ :=
      T.exists_middle_basin_family_step hf hm hdim (p 0) (hp 0) (fun j => p j.succ)
        (fun j => hupper.trans (htail j)) β hβ ε hε
    have hp_cases : Fin.cases (p 0) (fun j => p j.succ) = p := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hp_cases] at hΓ
    have hbelow (q : Smale.ManifoldMorse.criticalPoints E f) (hqp : f q < f (p 0)) : f q < c := by
      by_contra h
      have hcq : c < f q :=
        lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (fun heq => hc q.val heq q.property))
      obtain ⟨j, hj⟩ := hblock 0 q hcq hqp.le
      have hh := horder.monotone (Fin.zero_le j)
      rw [hj] at hh
      exact not_lt_of_ge hh hqp
    have hgapLower :
      ∀ q ∈ Smale.ManifoldMorse.criticalPoints E f,
        f q ∉ Set.Icc c (T.toSurgeryWindows.lower (p 0)) := by
      intro q hq hh
      exact
        not_le_of_gt (hbelow ⟨q, hq⟩ (hh.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p 0))))
          hh.1
    obtain ⟨Ω, hΩ, -⟩ :=
      U.exists_regular_band_middle_basin_family hf hlower (T.data (p 0)).lower_regular hc
        hgapLower (MorseCancellation.nativeIndexThreeAttachingSphere T (p 0) (hp 0) x₀) p
        (fun j =>
          (T.toSurgeryWindows.lower_lt_value (p 0)).trans_le (horder.monotone (Fin.zero_le j)))
        Γ hΓ
    refine ⟨U, fun q => (hchartsU q).trans (hchartsT q), hradiiU, ?_, Ω, hΩ⟩
    intro q hq
    filter_upwards [hgermsU q hq, hgermsT q hq] with y hyU hyT
    exact hyU.trans hyT

theorem MorseCancellation.unique_connection_of_distinct_minimum_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : Continuous f) (G : Flow ℝ M)
    (p r q : Smale.ManifoldMorse.criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hpr : p ≠ r) (hp : f p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
        (𝓝 q.val) ∧
      ∀ x,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val) →
            ∃ t, G t ((S.data q).surgery.attachingSphere u).val = x := by
  have hdim : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := by
    intro h
    apply hpr
    apply Subtype.ext
    exact tendsto_nhds_unique (h ▸ hu) hv
  have hbu :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atBot
      (𝓝 q.val) :=
    (hback _).mpr (Set.mem_range_self u)
  have hsingle (x : (S.data q).LowerLevel)
    (hb : Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val))
    (hp' : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 p.val)) :
    x = (S.data q).surgery.attachingSphere u := by
    obtain ⟨w, hw⟩ := (hback x).mp hb
    rcases unitSphere_eq_two_points_of_finrank_one hdim u v huv w with h | h
    · exact (congrArg (S.data q).surgery.attachingSphere h).symm.trans hw |>.symm
    · have hx : (S.data q).surgery.attachingSphere v = x := h ▸ hw
      have hrv : Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val) := hx ▸ hv
      exact False.elim (hpr (Subtype.ext (tendsto_nhds_unique hp' hrv)))
  have h :=
    Degree.FlowSuspension.unique_connection_of_level_basin_intersection G G hf
      (S.lower_lt_value q) hp id (fun _ => Iff.rfl) (fun _ => Iff.rfl)
      ((S.data q).surgery.attachingSphere u) hbu hu hsingle
  exact ⟨h.1, h.2.2⟩

def MorseCancellation.shiftedSignedMorseChart {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (k : ℝ) :
    Smale.ManifoldMorse.SignedMorseChart (E := E) (fun x => f x + k) p
    where
  weights := c.weights
  signs := c.signs
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation x hx := by rw [c.equation x hx]; ring
  inverse_equation z hz := by rw [c.inverse_equation z hz]; ring

theorem MorseCancellation.isMorseAt_add_const {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : Smale.ManifoldMorse.IsMorseAt E f p) (k : ℝ) :
    Smale.ManifoldMorse.IsMorseAt E (fun x => f x + k) p := by
  obtain ⟨e, he, hp, hgood⟩ := hm
  have hd : fderiv ℝ ((fun x => f x + k) ∘ e.symm) = fderiv ℝ (f ∘ e.symm) := by
    funext z
    exact fderiv_add_const k
  refine ⟨e, he, hp, ?_⟩
  rw [hd]
  exact hgood

theorem MorseCancellation.isMorseAt_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hm : Smale.ManifoldMorse.IsMorseAt E f p) {k : ℝ} (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    Smale.ManifoldMorse.IsMorseAt E g p :=
  Degree.MorseCancellationPreservation.isMorseAt_of_same_germ (isMorseAt_add_const hm k) hgerm

theorem MorseCancellation.nativeMorseIndex_add_const {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (k : ℝ) :
    nativeMorseIndex E (fun x => f x + k) p = nativeMorseIndex E f p := by
  rw [nativeMorseIndex_eq_chart (shiftedSignedMorseChart c k), nativeMorseIndex_eq_chart c]
  rfl

theorem MorseCancellation.nativeMorseIndex_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) : nativeMorseIndex E g p = nativeMorseIndex E f p :=
  (nativeMorseIndex_congr_germ hgerm).trans (nativeMorseIndex_add_const c k)

theorem MorseCancellation.mfderiv_of_add_const_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p) {k : ℝ} (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g p = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p := by
  calc
    _ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun x => f x + k) p : E →L[ℝ] ℝ) := hgerm.mfderiv_eq
    _ = _ := by
      have hs : mvfderiv 𝓘(ℝ, E) (fun x => f x + k) p = mvfderiv 𝓘(ℝ, E) f p := by
        rw [mvfderiv_fun_add hf mdifferentiableAt_const, mvfderiv_const, add_zero]
      exact hs

theorem MorseCancellation.exists_signed_morse_chart_of_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hgerm : g =ᶠ[𝓝 p] f) :
    ∃ d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hgerm
  let d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p :=
    { weights := c.weights
      signs := c.signs
      chart := Smale.PartialChart.restrictSource c.chart hU
      mem_source := ⟨c.mem_source, hpU⟩
      center := c.center
      equation := by
        intro x hx
        have hxs : x ∈ c.chart.source ∩ U := hx
        have hxeq : g x = f x := hUsub hxs.2
        change g x = g p + ∑ i, c.weights i * (c.chart x i) ^ 2
        rw [hxeq, hgerm.self_of_nhds]
        exact c.equation x hxs.1
      inverse_equation := by
        intro z hz
        have hzs : z ∈ c.chart.target ∩ c.chart.symm ⁻¹' U := hz
        have hzeq : g (c.chart.symm z) = f (c.chart.symm z) := hUsub hzs.2
        change g (c.chart.symm z) = g p + ∑ i, c.weights i * z i ^ 2
        rw [hzeq, hgerm.self_of_nhds]
        exact c.inverse_equation z hzs.1 }
  exact ⟨d, rfl⟩

theorem MorseCancellation.exists_signed_morse_chart_of_shift_germ_preserving_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {k : ℝ}
    (hgerm : g =ᶠ[𝓝 p] fun x => f x + k) :
    ∃ d : Smale.ManifoldMorse.SignedMorseChart (E := E) g p, d.descentField = c.descentField := by
  obtain ⟨d, hd⟩ :=
    exists_signed_morse_chart_of_germ_preserving_field (shiftedSignedMorseChart c k) hgerm
  exact ⟨d, hd⟩

theorem Degree.FlowCancellation.levelBasin_eq_of_orbit_level_bridge {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ) (a b : ℝ) (D : X → X)
    (hlevel : D '' {x | f x = a} = {x | f x = b}) (horbit : ∀ x, ∃ t, F t x = D x) :
    levelBasin F f a = levelBasin F f b := by
  ext x
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := horbit (F s x)
    have hDy : f (D (F s x)) = b := by
      have hh : D (F s x) ∈ D '' {y | f y = a} := Set.mem_image_of_mem D hs
      rw [hlevel] at hh
      exact hh
    exact ⟨t + s, by rw [F.map_add, ht]; exact hDy⟩
  · rintro ⟨s, hs⟩
    have hy : F s x ∈ D '' {y | f y = a} := by rw [hlevel]; exact hs
    obtain ⟨y, hy, heq⟩ := hy
    change f y = a at hy
    obtain ⟨t, ht⟩ := horbit y
    have hyB : y ∈ levelBasin F f a := ⟨0, by simpa only [F.map_zero_apply] using hy⟩
    have hh := (levelBasin_flow_iff F f a t y).mpr hyB
    rw [ht, heq] at hh
    exact (levelBasin_flow_iff F f a s x).mp hh

theorem Degree.FlowCancellation.levelBasin_eq_of_regular_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    levelBasin F f a = levelBasin F f b := by
  obtain ⟨D, hlevel, -, horbit⟩ :=
    Degree.FlowTimeChange.exists_orbit_preserving_ambient_band_bridge hf hV hdesc F hF hab hband
  exact levelBasin_eq_of_orbit_level_bridge F f a b D hlevel horbit

theorem MorseCancellation.image_flow_invariant_section {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B) (ι : A → X) (κ : B → X)
    (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x)) {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    e '' {x | P (ι x)} = {y | P (κ y)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := horbit x
    have hh := (hP t (ι x)).mpr hx
    rwa [ht] at hh
  · intro hy
    obtain ⟨t, ht⟩ := horbit (e.symm y)
    have heq : e (e.symm y) = y := e.apply_symm_apply y
    rw [heq] at ht
    refine ⟨e.symm y, ?_, heq⟩
    apply (hP t (ι (e.symm y))).mp
    rwa [ht]

theorem MorseCancellation.isCompact_flow_invariant_section_iff {X A B : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B] (F : Flow ℝ X) (e : A ≃ₜ B) (ι : A → X) (κ : B → X)
    (horbit : ∀ x, ∃ t, F t (ι x) = κ (e x)) {P : X → Prop} (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {y : B | P (κ y)} ↔ IsCompact {x : A | P (ι x)} := by
  rw [← image_flow_invariant_section F e ι κ horbit hP]
  exact e.isCompact_image

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.isCompact_native_belt_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact
      {x : { y : M // f y = f p + r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} := by
  have heq :
    {x : { y : M // f y = f p + r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} =
      Set.range (c.beltCoreMap r hr hblock) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_range, Subtype.ext_iff] using
      native_belt_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.beltCoreMap r hr hblock).continuous

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.isCompact_native_attaching_basin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsCompact
      {x : { y : M // f y = f p - r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} := by
  have heq :
    {x : { y : M // f y = f p - r ^ 2 } |
        Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} =
      Set.range (c.attachingCoreMap r hr hblock) := by
    ext x
    simpa only [Set.mem_ofPred_eq, Set.mem_range, Subtype.ext_iff] using
      native_attaching_core_basin_iff c hf hV F hF r hr hblock hfield hboundary x.property
  rw [heq]
  exact isCompact_range (c.attachingCoreMap r hr hblock).continuous

theorem Degree.FlowCancellation.isCompact_invariant_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) {P : M → Prop}
    (hP : ∀ t x, P (F t x) ↔ P x) :
    IsCompact {x : { y : M // f y = b } | P (x : M)} ↔
      IsCompact {x : { y : M // f y = a } | P (x : M)} := by
  have ha : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨le_rfl, hab⟩)
  have hb : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hband x (by rw [hx]; exact ⟨hab, le_rfl⟩)
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨D, e, -, he, horbit⟩ :=
    Degree.FlowTimeChange.exists_orbit_preserving_native_band_bridge hf hV hdesc F hF hab hband ha
      hb
  apply
    MorseCancellation.isCompact_flow_invariant_section_iff F e.toHomeomorph Subtype.val Subtype.val _ hP
  intro x
  obtain ⟨t, ht⟩ := horbit x
  exact ⟨t, ht.trans (he x).symm⟩

theorem Degree.FlowCancellation.isCompact_forward_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact
        {x : { y : M // f y = b } | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} ↔
      IsCompact
        {x : { y : M // f y = a } | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband (P := fun x =>
    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (fun t x => MorseCancellation.flow_time_atTop_limit_iff F t x p)

theorem Degree.FlowCancellation.isCompact_backward_section_iff_of_regular_band {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M) :
    IsCompact
        {x : { y : M // f y = b } | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} ↔
      IsCompact
        {x : { y : M // f y = a } | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 p)} :=
  isCompact_invariant_section_iff_of_regular_band hf hV hdesc F hF hab hband (P := fun x =>
    Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (fun t x => MorseCancellation.flow_time_atBot_limit_iff F t x p)

def Degree.MorseRearrangement.nativeCylinderWeight {Z H N E M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H} [TopologicalSpace N]
    [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (θ : N → ℝ)
    (x : M) : ℝ :=
  θ (A.symm x).1

theorem Degree.MorseRearrangement.contMDiffOn_nativeCylinderWeight {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {θ : N → ℝ}
    (hθ : ContMDiff I 𝓘(ℝ, ℝ) ∞ θ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (nativeCylinderWeight A θ) A.target :=
  hθ.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn A.contMDiffOn_invFun)

theorem Degree.MorseRearrangement.nativeCylinderWeight_mem_Icc {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) {θ : N → ℝ}
    (hθ : ∀ z, θ z ∈ Set.Icc (0 : ℝ) 1) (x : M) :
    nativeCylinderWeight A θ x ∈ Set.Icc (0 : ℝ) 1 :=
  hθ _

theorem Degree.MorseRearrangement.native_cylinder_flow_coordinates {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (hsource : A.source = Set.univ)
    (F : Flow ℝ M) (ι : N → M) (hformula : ∀ u, A u = F u.2 (ι u.1)) {x : M} (hx : x ∈ A.target)
    (t : ℝ) : A.symm (F t x) = ((A.symm x).1, t + (A.symm x).2) := by
  have hright : A (A.symm x) = x := A.right_inv' hx
  have hexpr : F t x = A ((A.symm x).1, t + (A.symm x).2) := by
    calc
      F t x = F t (A (A.symm x)) := congrArg (F t) hright.symm
      _ = F (t + (A.symm x).2) (ι (A.symm x).1) := by rw [hformula, ← F.map_add]
      _ = A ((A.symm x).1, t + (A.symm x).2) := (hformula ((A.symm x).1, t + (A.symm x).2)).symm
  rw [hexpr]
  exact A.left_inv' (by rw [hsource]; trivial)

theorem Degree.MorseRearrangement.nativeCylinderWeight_flow {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (hsource : A.source = Set.univ)
    (F : Flow ℝ M) (ι : N → M) (hformula : ∀ u, A u = F u.2 (ι u.1)) (θ : N → ℝ) {x : M}
    (hx : x ∈ A.target) (t : ℝ) : nativeCylinderWeight A θ (F t x) = nativeCylinderWeight A θ x :=
  by
  unfold nativeCylinderWeight
  rw [native_cylinder_flow_coordinates A hsource F ι hformula hx t]

theorem Degree.MorseRearrangement.exists_native_cylinder_plateau_weight {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace H]
    {I : ModelWithCorners ℝ Z H} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [T2Space N] [CompactSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = Set.univ) (F : Flow ℝ M) (ι : N → M)
    (hformula : ∀ u, A u = F u.2 (ι u.1)) {S₀ S₁ : Set N} (hS₀ : IsClosed S₀) (hS₁ : IsClosed S₁)
    (hdisj : Disjoint S₀ S₁) :
    ∃ w : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w A.target ∧
        (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x ∈ A.target, ∀ t, w (F t x) = w x) ∧
            (∀ x ∈ A.target, (A.symm x).1 ∈ S₀ → w =ᶠ[𝓝 x] fun _ => 0) ∧
              (∀ x ∈ A.target, (A.symm x).1 ∈ S₁ → w =ᶠ[𝓝 x] fun _ => 1) := by
  obtain ⟨θ, hθ₀, hθ₁, hθrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I hS₀ hS₁ hdisj (n := ⊤)
  refine
    ⟨nativeCylinderWeight A θ, contMDiffOn_nativeCylinderWeight A θ.contMDiff,
      nativeCylinderWeight_mem_Icc A hθrange, fun x hx t =>
      nativeCylinderWeight_flow A hsource F ι hformula θ hx t, ?_, ?_⟩
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 0 := hθ₀.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 1 := hθ₁.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.eventually_nonzero_positive_coordinate_on_upper_level_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : f p < a) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → (c.splitChart x).2 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_negative_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.1 hzero
  have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).ge_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.eventually_nonzero_negative_coordinate_on_lower_level_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : a < f p) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → (c.splitChart x).1 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_positive_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.2 hzero
  have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).le_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.eventually_constant_basin_weight_of_belt_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {a k : ℝ} (ha : f p < a) {w : M → ℝ}
    (hinv : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) {U : Set M}
    (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p + r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_positive_coordinate_on_upper_level_basin c hf hV F hF hmono
      heq ha,
    eventually_backward_exit_in_belt_neighborhood c hV F hF hr hblock hfield hU hcore] with x hne
    hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.eventually_constant_basin_weight_of_attaching_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {a k : ℝ} (ha : a < f p) {w : M → ℝ}
    (hinv : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) {U : Set M}
    (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p - r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_negative_coordinate_on_lower_level_basin c hf hV F hF hmono
      heq ha,
    eventually_forward_exit_in_attaching_neighborhood c hV F hF hr hblock hfield hU hcore] with x
    hne hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

theorem Degree.MorseRearrangement.height_side_of_not_levelBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a : ℝ} {x : X}
    (hx : x ∉ Degree.FlowCancellation.levelBasin F f a) (t : ℝ) : f (F t x) < a ↔ f x < a := by
  have hc : Continuous (fun s : ℝ => f (F s x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  have hside (s u : ℝ) (hs : f (F s x) < a) : f (F u x) < a := by
    by_contra hu
    obtain ⟨v, hv⟩ :=
      intermediate_value_univ s u hc
        (show a ∈ Set.Icc (f (F s x)) (f (F u x)) from ⟨hs.le, le_of_not_gt hu⟩)
    exact hx ⟨v, hv⟩
  constructor
  · intro ht
    simpa only [F.map_zero_apply] using hside t 0 ht
  · intro hx
    exact hside 0 t (by simpa only [F.map_zero_apply] using hx)

attribute [local instance 100] Classical.propDecidable in
def Degree.MorseRearrangement.extendedBasinWeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (a : ℝ) (w : X → ℝ) (x : X) : ℝ :=
  if x ∈ Degree.FlowCancellation.levelBasin F f a then w x else if f x < a then 1 else 0

theorem Degree.MorseRearrangement.extendedBasinWeight_eq {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ) {x : X}
    (hx : x ∈ Degree.FlowCancellation.levelBasin F f a) : extendedBasinWeight F f a w x = w x := by
  classical simp only [extendedBasinWeight, if_pos hx]

theorem Degree.MorseRearrangement.extendedBasinWeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) (a : ℝ) (w : X → ℝ)
    (hinv : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) (x : X)
    (t : ℝ) : extendedBasinWeight F f a w (F t x) = extendedBasinWeight F f a w x := by
  classical
  by_cases hx : x ∈ Degree.FlowCancellation.levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _
        ((Degree.FlowCancellation.levelBasin_flow_iff F f a t x).mpr hx),
      extendedBasinWeight_eq _ _ _ _ hx]
    exact hinv x hx t
  · have htx : F t x ∉ Degree.FlowCancellation.levelBasin F f a := fun h =>
      hx ((Degree.FlowCancellation.levelBasin_flow_iff F f a t x).mp h)
    simp only [extendedBasinWeight, if_neg hx, if_neg htx,
      height_side_of_not_levelBasin F hf hx t]

theorem Degree.MorseRearrangement.extendedBasinWeight_mem_Icc {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ)
    (hw : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, w x ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    extendedBasinWeight F f a w x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ Degree.FlowCancellation.levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _ hx]
    exact hw x hx
  · simp only [extendedBasinWeight, if_neg hx]
    split_ifs <;> norm_num

theorem Degree.MorseRearrangement.extendedBasinWeight_lower_germ {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : f p < a)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 1) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 1 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, f x < a := hf (eventually_lt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ Degree.FlowCancellation.levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, if_neg hbasin, if_pos hfx]

theorem Degree.MorseRearrangement.extendedBasinWeight_upper_germ {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : a < f p)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 0) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 0 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, a < f x := hf (eventually_gt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ Degree.FlowCancellation.levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, if_neg hbasin, if_neg (not_lt_of_gt hfx)]

theorem Degree.MorseRearrangement.constant_germ_of_endpoint_limit {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {w : X → ℝ} (hinv : ∀ x t, w (F t x) = w x) {p x : X} {k : ℝ} {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p))
    (hgerm : w =ᶠ[𝓝 p] fun _ => k) : w =ᶠ[𝓝 x] fun _ => k := by
  obtain ⟨t, ht⟩ := (hlim.eventually (eventually_eventually_nhds.mpr hgerm)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (hinv y t).symm.trans hy

theorem Degree.MorseRearrangement.pair_band_basin_complement {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {S : Set X}
    (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q : X} {l a u : ℝ} (hla : l < a)
    (hau : a < u) (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Set.Icc l u → z = p ∨ z = q) {x : X} (hx : f x ∈ Set.Icc l u)
    (hnot : x ∉ Degree.FlowCancellation.levelBasin F f a) :
    (f x < a ∧ Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) ∨
      (a < f x ∧ Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 q)) := by
  obtain ⟨r, hr, s, hs, hrlim, hslim, -⟩ :=
    Degree.FlowCancellation.exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f r)) :=
    hf.continuousAt.tendsto.comp hrlim
  have hsheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f s)) :=
    hf.continuousAt.tendsto.comp hslim
  by_cases hxa : f x < a
  · have hrle : f r ≤ a :=
      isClosed_Iic.mem_of_tendsto hrheight
        (Filter.Eventually.of_forall
          (fun t => ((height_side_of_not_levelBasin F hf hnot t).mpr hxa).le))
    have hxr : f x ≤ f r := by
      simpa only [F.map_zero_apply] using (hmono x).ge_of_tendsto hrheight 0
    have hrp : r = p :=
      (hpair r hr ⟨hx.1.trans hxr, hrle.trans hau.le⟩).resolve_right
        (by
          intro heq
          rw [heq] at hrle
          exact (not_le_of_gt hq) hrle)
    exact Or.inl ⟨hxa, by simpa only [hrp] using hrlim⟩
  · have hneq : f x ≠ a := fun heq => hnot ⟨0, by simpa only [F.map_zero_apply] using heq⟩
    have hax : a < f x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm hneq)
    have hsge : a ≤ f s :=
      isClosed_Ici.mem_of_tendsto hsheight
        (Filter.Eventually.of_forall
          (fun t =>
            le_of_not_gt (fun ht => hxa ((height_side_of_not_levelBasin F hf hnot t).mp ht))))
    have hsx : f s ≤ f x := by
      simpa only [F.map_zero_apply] using (hmono x).le_of_tendsto hsheight 0
    have hsq : s = q :=
      (hpair s hs ⟨hla.le.trans hsge, hsx.trans hx.2⟩).resolve_left
        (by
          intro heq
          rw [heq] at hsge
          exact (not_le_of_gt hp) hsge)
    exact Or.inr ⟨hax, by simpa only [hsq] using hslim⟩

theorem Degree.MorseRearrangement.contMDiffOn_extendedBasinWeight_pair_band {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] (F : Flow ℝ M) {f : M → ℝ}
    (hf : Continuous f) {S : Set M} (hinj : Set.InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q : M} {l a u : ℝ} (hla : l < a)
    (hau : a < u) (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hB : IsOpen (Degree.FlowCancellation.levelBasin F f a)) {w : M → ℝ}
    (hw : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ w (Degree.FlowCancellation.levelBasin F f a))
    (hstationary : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x)
    (hpw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 1)
    (hqw : ∀ᶠ x in 𝓝 q, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 0) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (extendedBasinWeight F f a w) (f ⁻¹' Set.Icc l u) := by
  have hpgerm := extendedBasinWeight_lower_germ F hf.continuousAt hp hpw
  have hqgerm := extendedBasinWeight_upper_germ F hf.continuousAt hq hqw
  have hinvariant (x : M) (t : ℝ) := extendedBasinWeight_flow F hf a w hstationary x t
  intro x hx
  by_cases hxB : x ∈ Degree.FlowCancellation.levelBasin F f a
  · have heq : extendedBasinWeight F f a w =ᶠ[𝓝 x] w := by
      filter_upwards [hB.mem_nhds hxB] with y hy
      exact extendedBasinWeight_eq F f a w hy
    exact (((hw x hxB).contMDiffAt (hB.mem_nhds hxB)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · rcases pair_band_basin_complement F hf hinj hmono hstrict hla hau hp hq hpair hx hxB with
      ⟨-, hlim⟩ | ⟨-, hlim⟩
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hpgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hqgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt

attribute [local instance 100] Classical.propDecidable in
theorem Degree.MorseRearrangement.exists_stationary_pair_weight {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {p q : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) {rp rq l a u : ℝ} (hrp : 0 < rp)
    (hrq : 0 < rq) (hla : l < a) (hau : a < u)
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hbp :
      Metric.closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
          Metric.closedBall (0 : cp.PositiveCoordinates) (2 * rp) ⊆
        cp.splitChart.target)
    (hbq :
      Metric.closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
          Metric.closedBall (0 : cq.PositiveCoordinates) (2 * rq) ⊆
        cq.splitChart.target)
    (hfp :
      ∀
        z ∈
          Metric.closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
            Metric.closedBall (0 : cp.PositiveCoordinates) (2 * rp),
        ∀ᶠ y in 𝓝 (cp.splitChart.symm z), V y = cp.descentField y)
    (hfq :
      ∀
        z ∈
          Metric.closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
            Metric.closedBall (0 : cq.PositiveCoordinates) (2 * rq),
        ∀ᶠ y in 𝓝 (cq.splitChart.symm z), V y = cq.descentField y)
    (hpa : f p + rp ^ 2 ≤ a) (haq : a ≤ f q - rq ^ 2)
    (hbandp : ∀ x, f x ∈ Set.Icc (f p + rp ^ 2) a → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hbandq : ∀ x, f x ∈ Set.Icc a (f q - rq ^ 2) → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))) :
    ∃ W : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ W (f ⁻¹' Set.Icc l u) ∧
        (∀ x, W x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x t, W (F t x) = W x) ∧ (W =ᶠ[𝓝 p] fun _ => 1) ∧ (W =ᶠ[𝓝 q] fun _ => 0) := by
  have hpa' : f p < a := by nlinarith [sq_pos_of_pos hrp]
  have haq' : a < f q := by nlinarith [sq_pos_of_pos hrq]
  have hreg : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hbandp x (by rw [hx]; exact ⟨hpa, le_rfl⟩)
  have hboundp : ∀ x, f x = f p + rp ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandp x (by rw [hx]; exact ⟨le_rfl, hpa⟩))
  have hboundq : ∀ x, f x = f q - rq ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandq x (by rw [hx]; exact ⟨haq, le_rfl⟩))
  let L := { x : M // f x = a }
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  let : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let S₀ : Set L := {x | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 q)}
  let S₁ : Set L := {x | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)}
  have hS₁ : IsCompact S₁ :=
    (Degree.FlowCancellation.isCompact_forward_section_iff_of_regular_band hf hV hdesc F hF hpa
          hbandp p).mpr
      (MorseCancellation.isCompact_native_belt_basin cp hf hV F hF rp hrp hbp hfp hboundp)
  have hS₀ : IsCompact S₀ :=
    (Degree.FlowCancellation.isCompact_backward_section_iff_of_regular_band hf hV hdesc F hF haq
          hbandq q).mp
      (MorseCancellation.isCompact_native_attaching_basin cq hf hV F hF rq hrq hbq hfq hboundq)
  have hdisj : Disjoint S₀ S₁ :=
    Set.disjoint_left.mpr (fun x hx₀ hx₁ => hnoconnection x ⟨hx₀, hx₁⟩)
  obtain ⟨z, hz⟩ := intermediate_value_univ p q hf.continuous ⟨hpa'.le, haq'.le⟩
  obtain ⟨A, hAsource, hAtarget, hAformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg hV F hF
      (fun x hx => hdesc x (hreg x hx)) (⟨z, hz⟩ : L)
  obtain ⟨w, hw, hwrange, hwinv, hw₀, hw₁⟩ :=
    exists_native_cylinder_plateau_weight A hAsource F Subtype.val hAformula hS₀.isClosed
      hS₁.isClosed hdisj
  have hmono := Smale.FlowConstruction.antitone_flow_height hf F hF hzero hdesc
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hbasinp :=
    Degree.FlowCancellation.levelBasin_eq_of_regular_band hf hV hdesc F hF hpa hbandp
  have hbasinq :=
    Degree.FlowCancellation.levelBasin_eq_of_regular_band hf hV hdesc F hF haq hbandq
  have hcorep (v : Smale.PuncturedHandle.UnitSphere cp.PositiveCoordinates) :
    w =ᶠ[𝓝 (cp.beltCoreMap rp hrp hbp v : M)] fun _ => 1 := by
    let x : M := cp.beltCoreMap rp hrp hbp v
    have hx : x ∈ A.target := by
      rw [hAtarget, ← hbasinp]
      exact ⟨0, by simpa only [F.map_zero_apply] using (cp.beltCoreMap rp hrp hbp v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₁ x hx
    have hh := MorseCancellation.native_belt_core_forward_limit cp hV₁ F hF rp hrp hbp hfp v
    apply (MorseCancellation.flow_time_atTop_limit_iff F (A.symm x).2 ((A.symm x).1 : M) p).mp
    rw [hmap]
    exact hh
  have hcoreq (v : Smale.PuncturedHandle.UnitSphere cq.NegativeCoordinates) :
    w =ᶠ[𝓝 (cq.attachingCoreMap rq hrq hbq v : M)] fun _ => 0 := by
    let x : M := cq.attachingCoreMap rq hrq hbq v
    have hx : x ∈ A.target := by
      rw [hAtarget, hbasinq]
      exact
        ⟨0, by simpa only [F.map_zero_apply] using (cq.attachingCoreMap rq hrq hbq v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₀ x hx
    have hh := MorseCancellation.native_attaching_core_backward_limit cq hV₁ F hF rq hrq hbq hfq v
    apply (MorseCancellation.flow_time_atBot_limit_iff F (A.symm x).2 ((A.symm x).1 : M) q).mp
    rw [hmap]
    exact hh
  have hstationary : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t, w (F t x) = w x := by
    simpa only [hAtarget] using hwinv
  have hpw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 1 :=
    MorseCancellation.eventually_constant_basin_weight_of_belt_neighborhood cp hf.continuous hV₁ F hF
      hmono hrp hbp hfp hpa' hstationary (U := interior {x | w x = 1}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcorep v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 1}) hx)
  have hqw : ∀ᶠ x in 𝓝 q, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 0 :=
    MorseCancellation.eventually_constant_basin_weight_of_attaching_neighborhood cq hf.continuous hV₁ F
      hF hmono hrq hbq hfq haq' hstationary (U := interior {x | w x = 0}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcoreq v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 0}) hx)
  have hB : IsOpen (Degree.FlowCancellation.levelBasin F f a) := hAtarget ▸ A.open_target
  have hwB : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w (Degree.FlowCancellation.levelBasin F f a) :=
    hAtarget ▸ hw
  refine
    ⟨extendedBasinWeight F f a w, ?_, extendedBasinWeight_mem_Icc F f a w (fun x _ => hwrange x),
      extendedBasinWeight_flow F hf.continuous a w hstationary,
      extendedBasinWeight_lower_germ F hf.continuous.continuousAt hpa' hpw,
      extendedBasinWeight_upper_germ F hf.continuous.continuousAt haq' hqw⟩
  exact
    contMDiffOn_extendedBasinWeight_pair_band F hf.continuous hinj hmono
      (fun x hx => Smale.FlowConstruction.strictAnti_flow_height hf hV₁ F hF hzero hdesc hx) hla
      hau hpa' haq' hpair hB hwB hstationary hpw hqw

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_small_native_morse_field_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ,
      0 < r ∧
        r ^ 2 < ε ∧
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
              c.splitChart.target ∧
            ∀
              z ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
              ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  obtain ⟨R, hR, hblock, hfield⟩ := exists_native_morse_field_block c heq
  obtain ⟨r, hr, hsmall⟩ :=
    exists_between (lt_min (half_pos hR) (lt_min hε (by norm_num : (0 : ℝ) < 1)))
  have h2r : 2 * r ≤ R := by linarith [hsmall.trans_le (min_le_left _ _)]
  have hrε : r < ε := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hr1 : r < 1 := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hr2 : r ^ 2 < ε := lt_trans (by nlinarith : r ^ 2 < r) hrε
  have hsub :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) R :=
    fun z hz =>
    ⟨Metric.closedBall_subset_closedBall h2r hz.1, Metric.closedBall_subset_closedBall h2r hz.2⟩
  exact ⟨r, hr, hr2, hsub.trans hblock, fun z hz => hfield z (hsub hz)⟩

theorem Degree.MorseRearrangement.blended_height_exterior_germ {M : Type*} [TopologicalSpace M]
    {f θ : M → ℝ} {P Q : ℝ → ℝ} {l u : ℝ} (hf : Continuous f)
    (hP : ∀ s ∉ Set.Ioo l u, P =ᶠ[𝓝 s] id) (hQ : ∀ s ∉ Set.Ioo l u, Q =ᶠ[𝓝 s] id) {x : M}
    (hx : f x ∉ Set.Ioo l u) : (fun y => blendHeight (θ y) P Q (f y)) =ᶠ[𝓝 x] f := by
  filter_upwards [hf.continuousAt.tendsto.eventually (hP _ hx),
    hf.continuousAt.tendsto.eventually (hQ _ hx)] with y hyP hyQ
  exact blendHeight_fixed hyP hyQ _

theorem Degree.MorseRearrangement.contMDiff_globally_blended_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f θ : M → ℝ}
    {P Q : ℝ → ℝ} {l u : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Set.Icc l u)) (hP : ContDiff ℝ ∞ P)
    (hQ : ContDiff ℝ ∞ Q) (hPfix : ∀ s ∉ Set.Ioo l u, P =ᶠ[𝓝 s] id)
    (hQfix : ∀ s ∉ Set.Ioo l u, Q =ᶠ[𝓝 s] id) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)) := by
  intro x
  by_cases hx : f x ∈ Set.Ioo l u
  · have hnhds : f ⁻¹' Set.Icc l u ∈ 𝓝 x :=
      Filter.mem_of_superset ((isOpen_Ioo.preimage hf.continuous).mem_nhds hx)
        (fun _ hy => ⟨hy.1.le, hy.2.le⟩)
    have hw := (hθ x ⟨hx.1.le, hx.2.le⟩).contMDiffAt hnhds
    exact
      (hw.mul (hP.contMDiff.contMDiffAt.comp x (hf x))).add
        ((contMDiffAt_const.sub hw).mul (hQ.contMDiff.contMDiffAt.comp x (hf x)))
  · exact (hf x).congr_of_eventuallyEq (blended_height_exterior_germ hf.continuous hPfix hQfix hx)

theorem Degree.MorseRearrangement.blended_height_one_translation_germ {M : Type*}
    [TopologicalSpace M] {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ} (hf : ContinuousAt f p)
    (hθ : θ =ᶠ[𝓝 p] fun _ => 1) (hP : P =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hP] with x hx hPx
  rw [hx, blendHeight_one]
  exact hPx

theorem Degree.MorseRearrangement.blended_height_zero_translation_germ {M : Type*}
    [TopologicalSpace M] {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ} (hf : ContinuousAt f p)
    (hθ : θ =ᶠ[𝓝 p] fun _ => 0) (hQ : Q =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hQ] with x hx hQx
  rw [hx, blendHeight_zero]
  exact hQx

theorem Degree.MorseRearrangement.blended_height_directional_derivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f θ : M → ℝ}
    {P Q : ℝ → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)))
    (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (hθ : ∀ x t, θ (F t x) = θ x)
    (x : M) :
    mvfderiv 𝓘(ℝ, E) (fun y => blendHeight (θ y) P Q (f y)) x (V x) =
      (θ x * deriv P (f x) + (1 - θ x) * deriv Q (f x)) * mvfderiv 𝓘(ℝ, E) f x (V x) := by
  have hw : HasDerivAt (fun t => θ (F t x)) 0 0 := by
    have heq : (fun t => θ (F t x)) = fun _ => θ x := funext (hθ x)
    rw [heq]
    exact hasDerivAt_const _ _
  have hdf := Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hF x) 0
  have hdg := Smale.FlowConstruction.hasDerivAt_comp_integralCurve hg (hF x) 0
  have hh := hasDerivAt_blended_height hdf hw (hP _).hasDerivAt (hQ _).hasDerivAt
  have heq := hdg.unique hh
  have hdf0 := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  have hdg0 :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) y (V y))
      (F.map_zero_apply x)
  change
    mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) (F 0 x) (V (F 0 x)) =
      (θ (F 0 x) * deriv P (f (F 0 x)) + (1 - θ (F 0 x)) * deriv Q (f (F 0 x))) *
        mvfderiv 𝓘(ℝ, E) f (F 0 x) (V (F 0 x)) at heq
  rw [hdg0, hdf0, F.map_zero_apply] at heq
  exact heq

theorem Degree.MorseRearrangement.exists_rearranged_morse_function_of_stationary_weight
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f θ : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p q : M} {l u p' q' : ℝ} (hp : f p ∈ Set.Ioo l u) (hq : f q ∈ Set.Ioo l u)
    (hp' : p' ∈ Set.Ioo l u) (hq' : q' ∈ Set.Ioo l u)
    (hpair : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Ioo l u → x = p ∨ x = q)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Set.Icc l u))
    (hθrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) (hθinv : ∀ x t, θ (F t x) = θ x)
    (hpgerm : θ =ᶠ[𝓝 p] fun _ => 1) (hqgerm : θ =ᶠ[𝓝 q] fun _ => 0) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            g p = p' ∧
              g q = q' ∧
                (∀ x,
                    x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                  (∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f) ∧
                    (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
                      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
                          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k) := by
  obtain ⟨P, -, hPtrans, -, -, hPpos, hPfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hp hp'
  obtain ⟨Q, -, hQtrans, -, -, hQpos, hQfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hq hq'
  let g : M → ℝ := fun x => blendHeight (θ x) P Q (f x)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_globally_blended_height hf hθ P.contMDiff.contDiff Q.contMDiff.contDiff hPfix hQfix
  have hgp : g =ᶠ[𝓝 p] fun x => f x + (p' - f p) :=
    blended_height_one_translation_germ hf.continuous.continuousAt hpgerm hPtrans
  have hgq : g =ᶠ[𝓝 q] fun x => f x + (q' - f q) :=
    blended_height_zero_translation_germ hf.continuous.continuousAt hqgerm hQtrans
  have hexterior (x : M) (hx : f x ∉ Set.Ioo l u) : g =ᶠ[𝓝 x] f :=
    blended_height_exterior_germ hf.continuous hPfix hQfix hx
  have hothers (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f) (hxp : x ≠ p)
    (hxq : x ≠ q) : g =ᶠ[𝓝 x] f := hexterior x (fun hb => (hpair x hx hb).elim hxp hxq)
  have hkeep (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k := by
    by_cases hxp : x = p
    · subst x
      exact ⟨p' - f p, hgp⟩
    by_cases hxq : x = q
    · subst x
      exact ⟨q' - f q, hgq⟩
    exact ⟨0, by simpa only [add_zero] using hothers x hx hxp hxq⟩
  have hdescent (x : M) (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) g x (V x) < 0 := by
    rw [blended_height_directional_derivative hf hg
        (P.contMDiff.contDiff.differentiable (by simp))
        (Q.contMDiff.contDiff.differentiable (by simp)) F hF hθinv x]
    exact
      mul_neg_of_pos_of_neg (positive_blended_slope (hθrange x) (hPpos _) (hQpos _)) (hdesc x hx)
  have hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      exact Degree.FlowCancellation.not_critical_of_directional_neg (hdescent x hnot) hx
    · intro hx
      obtain ⟨k, hk⟩ := hkeep x hx
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [MorseCancellation.mfderiv_of_add_const_germ (hf.mdifferentiableAt (by simp)) hk]
      exact hx
  have hmg : Smale.ManifoldMorse.IsMorse E g := by
    intro x
    by_cases hx : x ∈ Smale.ManifoldMorse.criticalPoints E f
    · obtain ⟨k, hk⟩ := hkeep x hx
      exact MorseCancellation.isMorseAt_of_add_const_germ (hm x) hk
    · have hreg : x ∉ Smale.ManifoldMorse.criticalPoints E g := by rwa [hcrit]
      exact Degree.MorseCancellationPreservation.isMorseAt_of_regular hg hreg
  refine ⟨g, hg, hmg, hcrit, ?_, ?_, hdescent, hexterior, hgp, hgq, hothers, hkeep⟩
  · have hh := hgp.self_of_nhds
    dsimp only at hh
    linarith
  · have hh := hgq.self_of_nhds
    dsimp only at hh
    linarith

theorem Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {p q : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q)
    (hfp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (hfq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y)
    {l u p' q' : ℝ} (hp : f p ∈ Set.Ioo l u) (hq : f q ∈ Set.Ioo l u) (hpq : f p < f q)
    (hp' : p' ∈ Set.Ioo l u) (hq' : q' ∈ Set.Ioo l u)
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            g p = p' ∧
              g q = q' ∧
                (∀ x,
                    x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                  (∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f) ∧
                    (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
                      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
                          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            MorseCancellation.nativeMorseIndex E g x =
                              MorseCancellation.nativeMorseIndex E f x) := by
  obtain ⟨a, hpa, haq⟩ := exists_between hpq
  obtain ⟨rp, hrp, hrpa, hbp, hfieldp⟩ :=
    MorseCancellation.exists_small_native_morse_field_block cp hfp (sub_pos.mpr hpa)
  obtain ⟨rq, hrq, hrqa, hbq, hfieldq⟩ :=
    MorseCancellation.exists_small_native_morse_field_block cq hfq (sub_pos.mpr haq)
  have hpa' : f p + rp ^ 2 ≤ a := by linarith
  have haq' : a ≤ f q - rq ^ 2 := by linarith
  have hregular (x : M) (hx : f x ∈ Set.Ioo (f p) (f q)) :
    x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro hcrit
    rcases hpair x hcrit ⟨hp.1.le.trans hx.1.le, hx.2.le.trans hq.2.le⟩ with heq | heq
    · rw [heq] at hx
      exact lt_irrefl _ hx.1
    · rw [heq] at hx
      exact lt_irrefl _ hx.2
  have hbandp :
    ∀ x, f x ∈ Set.Icc (f p + rp ^ 2) a → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨by nlinarith [hx.1, sq_pos_of_pos hrp], hx.2.trans_lt haq⟩
  have hbandq :
    ∀ x, f x ∈ Set.Icc a (f q - rq ^ 2) → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨hpa.trans_le hx.1, by nlinarith [hx.2, sq_pos_of_pos hrq]⟩
  obtain ⟨W, hW, hWrange, hWinv, hWp, hWq⟩ :=
    exists_stationary_pair_weight hf hV F hF hzero hdesc hinj cp cq hrp hrq (hp.1.trans hpa)
      (haq.trans hq.2) hpair hbp hbq hfieldp hfieldq hpa' haq' hbandp hbandq hnoconnection
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, -⟩ :=
    exists_rearranged_morse_function_of_stationary_weight hf hm F hF hdesc hp hq hp' hq'
      (fun x hx hband => hpair x hx ⟨hband.1.le, hband.2.le⟩) hW hWrange hWinv hWp hWq
  refine ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact MorseCancellation.nativeMorseIndex_of_add_const_germ cp hpgerm
  by_cases hxq : x = q
  · subst x
    exact MorseCancellation.nativeMorseIndex_of_add_const_germ cq hqgerm
  exact MorseCancellation.nativeMorseIndex_congr_germ (hothers x hx hxp hxq)

theorem MorseCancellation.injOn_of_exchanged_values {X Y : Type*} {f g : X → Y} {S : Set X} {p q : X}
    (hinj : Set.InjOn f S) (hp : p ∈ S) (hq : q ∈ S) (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ S, x ≠ p → x ≠ q → g x = f x) : Set.InjOn g S := by
  classical
  have hform (x : X) (hx : x ∈ S) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hothers x hx hxp hxq
  have hmaps : Set.MapsTo (Equiv.swap p q) S S := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hq
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hp
    simpa only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hx
  intro x hx y hy hxy
  apply (Equiv.swap p q).injective
  apply hinj (hmaps hx) (hmaps hy)
  rw [← hform x hx, ← hform y hy]
  exact hxy

theorem MorseCancellation.nativeMorseCount_eq_of_preserved_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x)
    (k : ℕ) : nativeMorseCount E g k = nativeMorseCount E f k := by
  have heq :
    {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g x = k} =
      {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k} := by
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hcrit]
    by_cases hx : x ∈ Smale.ManifoldMorse.criticalPoints E f
    · rw [hindex x hx]
    · simp only [hx, false_and]
  exact congrArg Set.ncard heq

theorem MorseCancellation.adapted_surgery_system_after_value_exchange {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : AdaptedWindows E f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g) (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) :
    Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hinj : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values S.distinct hp hq hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  exact ⟨hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

theorem MorseCancellation.exists_flow_preserving_value_exchange {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                      x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
                    (∀ x,
                        x ∉ Smale.ManifoldMorse.criticalPoints E g →
                          mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                      (∀ x ∈ Smale.ManifoldMorse.criticalPoints E g,
                          ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
                          ∀ k, nativeMorseCount E g k = nativeMorseCount E f k := by
  obtain ⟨S⟩ := Smale.ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels p p.property
  obtain ⟨cq, hcq⟩ := hmodels q q.property
  have hp : f p ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨S.lower_lt_value p, hpq.trans (S.value_lt_upper q)⟩
  have hq : f q ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨(S.lower_lt_value p).trans hpq, S.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, -, hpgerm, hqgerm, hothers, hindices⟩ :=
    Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV F hF hzero
      hdesc hinj cp cq hcp hcq hp hq hpq hq hp (surgery_pair_band_isolation S p q hconsecutive)
      hnoconnection
  have hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values hinj p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels :
    ∀ x ∈ Smale.ManifoldMorse.criticalPoints E g,
      ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    rw [hcrit] at hx
    by_cases hxp : x = p.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cp hpgerm
      exact ⟨c, hc ▸ hcp⟩
    by_cases hxq : x = q.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cq hqgerm
      exact ⟨c, hc ▸ hcq⟩
    obtain ⟨c, hc⟩ := hmodels x hx
    obtain ⟨d, hd⟩ := exists_signed_morse_chart_of_germ_preserving_field c (hothers x hx hxp hxq)
    exact ⟨d, hd ▸ hc⟩
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, (fun x hx => hdescent x (hcrit ▸ hx)),
      hnewmodels, hindices, nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

attribute [local instance 100] Classical.propDecidable in
def Degree.MorseRearrangement.upperValueRank {X : Type*} [Fintype X] (h : X → ℝ) (x : X) : ℕ :=
  (Finset.univ.filter (fun y => h x < h y)).card

def Degree.MorseRearrangement.finiteIndexDisorder {X : Type*} [Fintype X] (h : X → ℝ)
    (w : X → ℕ) : ℕ :=
  ∑ x, w x * upperValueRank h x

theorem Degree.MorseRearrangement.upperValueRank_comp_equiv {X : Type*} [Fintype X] {Y : Type*}
    [Fintype Y] (h : Y → ℝ) (e : X ≃ Y) (x : X) :
    upperValueRank (h ∘ e) x = upperValueRank h (e x) := by
  classical
  unfold upperValueRank
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem Degree.MorseRearrangement.finiteIndexDisorder_comp_equiv {X : Type*} [Fintype X]
    {Y : Type*} [Fintype Y] (h : Y → ℝ) (w : Y → ℕ) (e : X ≃ Y) :
    finiteIndexDisorder (h ∘ e) (w ∘ e) = finiteIndexDisorder h w := by
  classical
  unfold finiteIndexDisorder
  calc
    _ = ∑ x, w (e x) * upperValueRank h (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [upperValueRank_comp_equiv]
      rfl
    _ = _ := e.sum_comp (fun y => w y * upperValueRank h y)

theorem Degree.MorseRearrangement.upperValueRank_consecutive {X : Type*} [Fintype X] {h : X → ℝ}
    (hi : Function.Injective h) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) :
    upperValueRank h p = upperValueRank h q + 1 := by
  classical
  have hset :
    Finset.univ.filter (fun x => h p < h x) =
      Insert.insert q (Finset.univ.filter (fun x => h q < h x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxq : x = q
      · exact Or.inl hxq
      · apply Or.inr
        by_contra hnot
        have hlt : h x < h q := lt_of_le_of_ne (le_of_not_gt hnot) (fun heq => hxq (hi heq))
        exact hconsecutive x ⟨hx, hlt⟩
    · rintro (rfl | hx)
      · exact hpq
      · exact hpq.trans hx
  unfold upperValueRank
  rw [hset, Finset.card_insert_of_notMem (by simp)]

attribute [local instance 100] Classical.propDecidable in
theorem Degree.MorseRearrangement.sum_erase_two_nat {X : Type*} [Fintype X] (v : X → ℕ) {p q : X}
    (hpq : p ≠ q) : ∑ x, v x = (∑ x ∈ (Finset.univ.erase p).erase q, v x) + v p + v q := by
  classical
  have hp := Finset.sum_erase_add (s := Finset.univ) v (Finset.mem_univ p)
  have hq :=
    Finset.sum_erase_add (s := Finset.univ.erase p) v
      (by simp [Ne.symm hpq] : q ∈ Finset.univ.erase p)
  omega

attribute [local instance 100] Classical.propDecidable in
theorem Degree.MorseRearrangement.weighted_sum_swap_identity {X : Type*} [Fintype X] (w v : X → ℕ)
    {p q : X} (hpq : p ≠ q) :
    (∑ x, w x * v (Equiv.swap p q x)) + w p * v p + w q * v q =
      (∑ x, w x * v x) + w p * v q + w q * v p := by
  classical
  have hnew := sum_erase_two_nat (fun x => w x * v (Equiv.swap p q x)) hpq
  have hold := sum_erase_two_nat (fun x => w x * v x) hpq
  have hrest :
    (∑ x ∈ (Finset.univ.erase p).erase q, w x * v (Equiv.swap p q x)) =
      ∑ x ∈ (Finset.univ.erase p).erase q, w x * v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxq := (Finset.mem_erase.mp hx).1
    have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp only [Equiv.swap_apply_def, if_neg hxp, if_neg hxq]
  rw [hrest] at hnew
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hnew
  omega

attribute [local instance 100] Classical.propDecidable in
theorem Degree.MorseRearrangement.finiteIndexDisorder_swap_lt {X : Type*} [Fintype X] {h : X → ℝ}
    (hi : Function.Injective h) (w : X → ℕ) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) (hw : w q < w p) :
    finiteIndexDisorder (h ∘ Equiv.swap p q) w < finiteIndexDisorder h w := by
  classical
  have hne : p ≠ q := fun heq => (ne_of_lt hpq) (congrArg h heq)
  have hrank := upperValueRank_consecutive hi hpq hconsecutive
  have hid := weighted_sum_swap_identity w (upperValueRank h) hne
  have hnew :
    finiteIndexDisorder (h ∘ Equiv.swap p q) w = ∑ x, w x * upperValueRank h (Equiv.swap p q x) :=
    by
    unfold finiteIndexDisorder
    apply Finset.sum_congr rfl
    intro x _
    rw [upperValueRank_comp_equiv]
  rw [hrank] at hid
  simp only [Nat.mul_add, Nat.mul_one] at hid
  change _ < ∑ x, w x * upperValueRank h x
  rw [hnew]
  omega

theorem Degree.MorseRearrangement.exists_adjacent_index_inversion {X : Type*} [Finite X]
    {h : X → ℝ} (hi : Function.Injective h) (w : X → ℕ) (hnot : ¬∀ x y, h x < h y → w x ≤ w y) :
    ∃ p q, h p < h q ∧ (∀ x, ¬(h p < h x ∧ h x < h q)) ∧ w q < w p := by
  classical
  let := Fintype.ofFinite X
  let _ : LinearOrder X := LinearOrder.lift' h hi
  let _ : LocallyFiniteOrder X := Fintype.toLocallyFiniteOrder
  have hnotmono : ¬Monotone w := by
    intro hm
    apply hnot
    intro x y hxy
    exact hm (show x ≤ y from hxy.le)
  have hnotadj : ¬∀ x y : X, x ⋖ y → w x ≤ w y := by
    intro hadj
    exact hnotmono ((monotone_iff_forall_covBy w).mpr hadj)
  simp only [Classical.not_forall, not_le] at hnotadj
  obtain ⟨p, q, hcover, hweights⟩ := hnotadj
  exact ⟨p, q, hcover.lt, fun x hx => hcover.2 hx.1 hx.2, hweights⟩

theorem Degree.MorseRearrangement.exists_consecutive_below_of_intermediate {X : Type*} [Finite X]
    {h : X → ℝ} {p q : X} (hintermediate : ∃ x, h p < h x ∧ h x < h q) :
    ∃ r, h p < h r ∧ h r < h q ∧ ∀ x, ¬(h r < h x ∧ h x < h q) := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨w, hpw, hwq⟩ := hintermediate
  let K := Finset.univ.filter (fun x => h x < h q)
  have hw : w ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwq⟩
  obtain ⟨r, hr, hmax⟩ := K.exists_max_image h ⟨w, hw⟩
  refine ⟨r, hpw.trans_le (hmax w hw), (Finset.mem_filter.mp hr).2, ?_⟩
  intro x hx
  exact (not_lt_of_ge (hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩))) hx.1

def Degree.MorseRearrangement.beforeValueRank {X : Type*} [Fintype X] (h : X → ℝ) (q : X) : ℕ :=
  upperValueRank (fun x => -h x) q

attribute [local instance 100] Classical.propDecidable in
theorem Degree.MorseRearrangement.beforeValueRank_exchange_lt {X : Type*} [Fintype X]
    {h g : X → ℝ} (hi : Function.Injective h) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) (hgp : g p = h q) (hgq : g q = h p)
    (hothers : ∀ x, x ≠ p → x ≠ q → g x = h x) : beforeValueRank g q < beforeValueRank h q := by
  classical
  have hform : (fun x => -g x) = (fun x => -h x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_left, hgp]
    by_cases hxq : x = q
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_right, hgq]
    simp only [Function.comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq,
      hothers x hxp hxq]
  have hnew : beforeValueRank g q = beforeValueRank h p := by
    unfold beforeValueRank
    rw [hform, upperValueRank_comp_equiv, Equiv.swap_apply_right]
  have hneg : Function.Injective (fun x => -h x) := fun x y hxy => hi (neg_injective hxy)
  have hgap : beforeValueRank h q = beforeValueRank h p + 1 := by
    apply upperValueRank_consecutive hneg (neg_lt_neg hpq)
    intro x hx
    exact hconsecutive x ⟨neg_lt_neg_iff.mp hx.2, neg_lt_neg_iff.mp hx.1⟩
  omega

theorem MorseCancellation.exists_flow_preserving_consecutive_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f₀ : M → ℝ}
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : Smale.ManifoldMorse.IsMorse E f₀)
    (hinj₀ : Set.InjOn f₀ (Smale.ManifoldMorse.criticalPoints E f₀))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : Smale.ManifoldMorse.criticalPoints E f₀) (hrp : f₀ r < f₀ p) (hpq : f₀ p < f₀ q)
    (hnoconnection :
      ∀ j : Smale.ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val))) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ z : Smale.ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q)) ∧
                      (∀ x,
                          x ∉ Smale.ManifoldMorse.criticalPoints E f →
                            mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
                              ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                          ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x := by
  classical
  let _ := (Smale.ManifoldMorse.finite_criticalPoints hf₀ hm₀).fintype
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ x,
                        x ∉ Smale.ManifoldMorse.criticalPoints E f →
                          mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                      (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                          ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
                          Degree.MorseRearrangement.beforeValueRank
                              (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) q =
                            n
  have hex : ∃ n, P n :=
    ⟨Degree.MorseRearrangement.beforeValueRank
        (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f₀ x) q,
      f₀, hf₀, hm₀, rfl, hinj₀, rfl, rfl, hpq, hdesc₀, hmodels₀, fun _ _ => rfl, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hdesc, hmodels, hindices, hrank⟩ :=
    Nat.find_spec hex
  have hconsecutive : ∀ z : Smale.ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hpz, hzq, hbefore⟩ :=
      Degree.MorseRearrangement.exists_consecutive_below_of_intermediate (h :=
        fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) (p := p) (q := q) hnot
    have hzp : z.val ≠ p.val := fun h => (ne_of_lt hpz) (congrArg f h).symm
    have hzq' : z.val ≠ q.val := fun h => (ne_of_lt hzq) (congrArg f h)
    have hzr : z.val ≠ r.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      exact (not_lt_of_gt hpz) (by simpa only [h] using hrp')
    let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, by rw [hcrit]; exact z.property⟩
    let qf : Smale.ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
    have hbeforef : ∀ s : Smale.ManifoldMorse.criticalPoints E f, ¬(f zf < f s ∧ f s < f qf) := by
      intro s hs
      exact hbefore ⟨s.val, by rw [← hcrit]; exact s.property⟩ hs
    obtain ⟨g, hg, hmg, hcritg, hinjg, hgz, hgq, hothers, hdescg, hmodelsg, hindicesg, -⟩ :=
      exists_flow_preserving_value_exchange hf hm hinj hV F hF (fun x hx => hzero x (hcrit ▸ hx))
        hdesc hmodels zf qf hzq hbeforef
        (hnoconnection z (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)) (fun h => hzr (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ Smale.ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact p.property
    have hrcrit : r.val ∈ Smale.ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact r.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hfpq) (congrArg f h)
    have hrq' : r.val ≠ q.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      have hlt : f r < f q := hrp'.trans hfpq
      exact (ne_of_lt hlt) (congrArg f h)
    have hgp : g p = f p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hgr : g r = f r := (hothers r hrcrit hzr.symm hrq').self_of_nhds
    have hidxg₀ (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hdecrease :
      Degree.MorseRearrangement.beforeValueRank
          (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => g x) q <
        Degree.MorseRearrangement.beforeValueRank
          (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) q := by
      apply
        Degree.MorseRearrangement.beforeValueRank_exchange_lt (h :=
          fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) (g :=
          fun x : Smale.ManifoldMorse.criticalPoints E f₀ => g x) (p := z) (q := q)
          (fun x y h =>
            Subtype.ext
              (hinj (by rw [hcrit]; exact x.property) (by rw [hcrit]; exact y.property) h))
          hzq hbefore hgz hgq
      intro x hxz hxq
      exact
        (hothers x (by rw [hcrit]; exact x.property) (fun h => hxz (Subtype.ext h))
            (fun h => hxq (Subtype.ext h))).self_of_nhds
    have hminimal :=
      Nat.find_min' hex
        ⟨g, hg, hmg, hcritg.trans hcrit, hinjg, hgp.trans hfp, hgr.trans hfr,
          (by rw [hgp, hgq]; exact hpz), hdescg, hmodelsg, hidxg₀, rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hconsecutive, hdesc, hmodels, hindices⟩

theorem MorseCancellation.isOpen_forward_basin_of_native_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodel : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)} := by
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hindex
  obtain ⟨r, hr, -, hbasin⟩ :=
    exists_descending_morse_basin_block c hf (hV.of_le (by simp)) F hF hzero hdesc hmodel
  have hnear : ∀ᶠ y in 𝓝 p, Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) := by
    filter_upwards [morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (flow_time_atTop_limit_iff F t y p).mp hy

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_unique_zero_one_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p q z : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hindexp : nativeMorseIndex E f p = 0)
    (hindexq : nativeMorseIndex E f q = 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {l u : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc l u → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f := by
  have hp0 : Module.finrank ℝ cp.NegativeCoordinates = 0 :=
    (nativeMorseIndex_eq_chart cp).symm.trans hindexp
  have hq1 : Module.finrank ℝ cq.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart cq).symm.trans hindexq
  have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by
    have h := cq.finrank_negative_add_positive
    omega
  have hindex :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    have h :
      Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
      omega
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using h
  have hbasin : ∀ᶠ x in 𝓝 z, Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) :=
    (isOpen_forward_basin_of_native_index_zero cp hf hV F hF hzero hdesc heqp hp0).mem_nhds hp
  have htrans :
    Smale.NativeTransversality.At 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) (fun x : M => x) z z :=
    by
    intro _ w
    refine ⟨(0, w), ?_⟩
    change
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) z 0 +
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : M => x) z w =
        w
    rw [map_zero, zero_add]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w = w
    rw [mfderiv_id]
    rfl
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V hV hzero hdesc F
      hF hinj hpc hqc hpq hl hu hpair hp hq hunique heqp heqq (S := fun _ : M => z) (T :=
      fun x : M => x) mdifferentiableAt_const mdifferentiableAt_id rfl rfl
      (Filter.Eventually.of_forall (fun _ => hq)) hbasin htrans

def Smale.EmbeddedCellAttachment.oldHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology D.old k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.oldNeighborhood k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv D.oldHomotopyEquiv k

def Smale.EmbeddedCellAttachment.overlapHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(D.oldNeighborhood ∩ D.diskPatch)) k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv D.overlapSphereEquiv k

def Smale.EmbeddedCellAttachment.attachingHomologyMap {N X : Type} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.old k :=
  SingularMayerVietoris.singularHomologyMap D.attachingSphere k

def Smale.EmbeddedCellAttachment.oldHomologyMap {N X : Type} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology D.old k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X k :=
  SingularMayerVietoris.singularHomologyMap (SingularMayerVietoris.subtypeInclusion D.old) k

def Smale.EmbeddedCellAttachment.cellConnectingMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (D.overlapHomologyEquiv k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k)

theorem Smale.EmbeddedCellAttachment.diskPatch_homology_subsingleton {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology D.diskPatch k) := by
  let := D.diskPatch_contractible
  exact PeriodTorusHigherHomology.contractible_homology_subsingleton D.diskPatch k hk

theorem Smale.EmbeddedCellAttachment.coverLeft_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    (D.oldHomologyEquiv k).symm
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k a)).1 =
      D.attachingHomologyMap k a := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap D.oldRetraction k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          k (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap D.attachingSphere k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap (D.overlapOldMap.comp D.overlapSphereEquiv.toFun) k
        a =
      _
  rw [D.overlapOldMap_comp_sphere]

theorem Smale.EmbeddedCellAttachment.coverRight_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology D.old k) :
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
        (D.oldHomologyEquiv k a, 0) =
      D.oldHomologyMap k a := by
  rw [SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) k
        (SingularMayerVietoris.singularHomologyMap D.oldInclusion k a) =
      SingularMayerVietoris.singularHomologyMap (SingularMayerVietoris.subtypeInclusion D.old) k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

theorem Smale.EmbeddedCellAttachment.coverLeft_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
        (D.overlapHomologyEquiv k a) =
      (D.oldHomologyEquiv k (D.attachingHomologyMap k a), 0) := by
  let := D.diskPatch_homology_subsingleton k hk
  apply Prod.ext
  · exact (D.oldHomologyEquiv k).symm_apply_eq.mp (D.coverLeft_old k a)
  · exact Subsingleton.elim _ _

theorem Smale.EmbeddedCellAttachment.coverRight_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0)
    (b :
      SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
        SingularMayerVietoris.SingularHomology D.diskPatch k) :
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k b =
      D.oldHomologyMap k ((D.oldHomologyEquiv k).symm b.1) := by
  let := D.diskPatch_homology_subsingleton k hk
  have hb : (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) = b :=
    Prod.ext ((D.oldHomologyEquiv k).apply_symm_apply b.1) (Subsingleton.elim _ _)
  calc
    _ =
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) :=
      congrArg (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) hb.symm
    _ = _ := D.coverRight_old k _

theorem Smale.EmbeddedCellAttachment.cellConnecting_eq_zero_iff {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    D.cellConnectingMap k a = 0 ↔
      SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
          D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k a =
        0 := by
  change (D.overlapHomologyEquiv k).symm _ = 0 ↔ _ = 0
  constructor
  · intro h
    exact (D.overlapHomologyEquiv k).symm.injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem Smale.EmbeddedCellAttachment.range_coverRight {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) =
      LinearMap.range (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k).symm b.1, (D.coverRight_formula k hk b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k b, 0), D.coverRight_old k b⟩

theorem Smale.EmbeddedCellAttachment.cell_exact_at_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.attachingHomologyMap k) = LinearMap.ker (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch k)
        (D.overlapHomologyEquiv k s)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k s)) =
        0 at hzero
    rw [D.coverLeft_formula k hk, D.coverRight_old] at hzero
    exact hzero
  · intro ha
    have hpair :
      (D.oldHomologyEquiv k a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
            (D.oldHomologyEquiv k a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover k] at hpair
    obtain ⟨c, hc⟩ := hpair
    refine ⟨(D.overlapHomologyEquiv k).symm c, ?_⟩
    have hc' :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm c)) =
        (D.oldHomologyEquiv k a, 0) := by
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    rw [D.coverLeft_formula k hk] at hc'
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        hc'
    exact (D.oldHomologyEquiv k).injective heq

theorem Smale.EmbeddedCellAttachment.cell_exact_at_ambient {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    LinearMap.range (D.oldHomologyMap (k + 1)) = LinearMap.ker (D.cellConnectingMap k) := by
  rw [← D.range_coverRight (k + 1) (Nat.succ_ne_zero k),
    SingularMayerVietoris.exact_at_ambient D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover k]
  ext a
  exact (D.cellConnecting_eq_zero_iff k a).symm

theorem Smale.EmbeddedCellAttachment.mem_range_cellConnecting {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    a ∈ LinearMap.range (D.cellConnectingMap k) ↔
      D.overlapHomologyEquiv k a ∈
        LinearMap.range
          (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
            D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change _ = D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm _)
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (D.overlapHomologyEquiv k).symm _ = a
    rw [hx, LinearEquiv.symm_apply_apply]

theorem Smale.EmbeddedCellAttachment.coverLeft_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k a) =
        0 ↔
      D.attachingHomologyMap k a = 0 := by
  rw [D.coverLeft_formula k hk]
  constructor
  · intro h
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        h
    exact (D.oldHomologyEquiv k).injective (heq.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]
    rfl

theorem Smale.EmbeddedCellAttachment.cell_exact_at_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.cellConnectingMap k) = LinearMap.ker (D.attachingHomologyMap k) := by
  ext a
  rw [D.mem_range_cellConnecting k,
    SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k]
  exact D.coverLeft_eq_zero_iff k hk a

theorem Smale.EmbeddedCellAttachment.cellConnecting_zero_apply {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)]
    (a : SingularMayerVietoris.SingularHomology X 1) : D.cellConnectingMap 0 a = 0 := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  have hc :
    D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a) ∈
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    rw [←
      SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
        D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0]
    exact (D.mem_range_cellConnecting 0 _).mp ⟨a, rfl⟩
  change
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
        (D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a)) =
      0 at hc
  have h := congrArg Prod.snd hc
  rw [SingularMayerVietoris.leftHomologyMap_apply] at h
  have hz : SingularMayerVietoris.singularHomologyMap q 0 (D.cellConnectingMap 0 a) = 0 := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact neg_eq_zero.mp h
  apply SphereHomology.singularHomologyMap_zero_injective q
  exact hz.trans (map_zero _).symm

theorem MorseCancellation.cell_oldHomologyMap_zero_injective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Injective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpair :
    (D.oldHomologyEquiv 0 a, 0) ∈
      LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.oldHomologyEquiv 0 a, 0) =
        0
    rw [D.coverRight_old]
    exact ha
  rw [←
    SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover 0] at hpair
  obtain ⟨c, hc⟩ := hpair
  have hq :
    SingularMayerVietoris.singularHomologyMap q 0 ((D.overlapHomologyEquiv 0).symm c) = 0 := by
    have h := congrArg Prod.snd hc
    rw [SingularMayerVietoris.leftHomologyMap_apply] at h
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
    change
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
          (D.overlapHomologyEquiv 0 ((D.overlapHomologyEquiv 0).symm c)) =
        0
    rw [LinearEquiv.apply_symm_apply]
    exact neg_eq_zero.mp h
  have hz : (D.overlapHomologyEquiv 0).symm c = 0 :=
    SphereHomology.singularHomologyMap_zero_injective q (hq.trans (map_zero _).symm)
  have hc0 : c = 0 := by
    apply (D.overlapHomologyEquiv 0).symm.injective
    exact hz.trans (map_zero _).symm
  rw [hc0, map_zero] at hc
  apply (D.oldHomologyEquiv 0).injective
  exact (congrArg Prod.fst hc).symm.trans (map_zero _).symm

theorem MorseCancellation.cell_oldHomologyMap_zero_surjective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Surjective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  intro a
  obtain ⟨⟨b, c⟩, hbc⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover a
  obtain ⟨z, hz⟩ := SphereHomology.singularHomologyMap_zero_surjective q c
  let v := D.overlapHomologyEquiv 0 z
  have hv :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
        v =
      c := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at hz
    exact hz
  have hzero :=
    LinearMap.congr_fun
      (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0) v
  change
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0 v) =
      0 at hzero
  rw [SingularMayerVietoris.leftHomologyMap_apply, SingularMayerVietoris.rightHomologyMap_apply,
    map_neg, hv] at hzero
  have hrel :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) 0
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          0 v) =
      SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.diskPatch) 0 c := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hzero
  refine
    ⟨(D.oldHomologyEquiv 0).symm
        (b +
          SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.inclusion Set.inter_subset_left) 0 v),
      ?_⟩
  rw [← D.coverRight_old, LinearEquiv.apply_symm_apply,
    SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero, map_add, hrel]
  exact hbc

theorem MorseCancellation.cell_oldHomologyMap_zero_bijective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Bijective (D.oldHomologyMap 0) :=
  ⟨cell_oldHomologyMap_zero_injective D, cell_oldHomologyMap_zero_surjective D⟩

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.componentChainWeight {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains X 0 →ₗ[ℤ] ℤ :=
  FirstHurewicz.chainLift X 0 (fun σ => if Joined x (σ (stdSimplex.vertex 0)) then 1 else 0)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.componentChainWeight_point {X : Type} [TopologicalSpace X] (x y : X) :
    componentChainWeight x (FirstHurewicz.pointChain y) = if Joined x y then 1 else 0 := by
  exact FirstHurewicz.chainLift_simplex X 0 _ _

theorem MorseCancellation.componentChainWeight_boundary {X : Type} [TopologicalSpace X] (x : X)
    (b : FirstHurewicz.Chains X 1) : componentChainWeight x (FirstHurewicz.boundaryOne X b) = 0 :=
  by
  classical
  have heq : (componentChainWeight x).comp (FirstHurewicz.boundaryOne X) = 0 := by
    apply FirstHurewicz.chainMap_ext X 1
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, FirstHurewicz.boundaryOne_simplex,
      map_sub, componentChainWeight, FirstHurewicz.chainLift_simplex, ContinuousMap.comp_apply,
      FirstHurewicz.simplexFace_zero_zero, FirstHurewicz.simplexFace_zero_one]
    have hp : Joined (σ (stdSimplex.vertex 0)) (σ (stdSimplex.vertex 1)) :=
      ⟨FirstHurewicz.simplexPath σ⟩
    have hi : Joined x (σ (stdSimplex.vertex 1)) ↔ Joined x (σ (stdSimplex.vertex 0)) :=
      ⟨fun h => h.trans hp.symm, fun h => h.trans hp⟩
    rw [hi, sub_self]
  exact LinearMap.congr_fun heq b

theorem MorseCancellation.pointClass_eq_iff_joined {X : Type} [TopologicalSpace X] (x y : X) :
    PeriodTorusHigherHomology.pointClass x = PeriodTorusHigherHomology.pointClass y ↔
      Joined x y := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨b, hb⟩ :=
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 0
            (PeriodTorusHigherHomology.pointCycle x) (PeriodTorusHigherHomology.pointCycle y)).mp
        h
    have he := congrArg (componentChainWeight x) hb
    change
      componentChainWeight x (FirstHurewicz.boundaryOne X b) =
        componentChainWeight x (FirstHurewicz.pointChain x - FirstHurewicz.pointChain y) at he
    rw [componentChainWeight_boundary, map_sub, componentChainWeight_point,
      componentChainWeight_point, if_pos (Joined.refl x), if_neg hn] at he
    norm_num at he
  · rintro ⟨p⟩
    apply
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 0
          (PeriodTorusHigherHomology.pointCycle x) (PeriodTorusHigherHomology.pointCycle y)).mpr
    exact ⟨FirstHurewicz.pathChain p.symm, FirstHurewicz.boundaryOne_pathChain p.symm⟩

theorem MorseCancellation.joined_iff_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) (x y : X) :
    Joined (f x) (f y) ↔ Joined x y := by
  rw [← pointClass_eq_iff_joined, ← pointClass_eq_iff_joined, ←
    PeriodTorusHigherHomology.singularHomologyMap_pointClass f, ←
    PeriodTorusHigherHomology.singularHomologyMap_pointClass f, hf.eq_iff]

theorem MorseCancellation.pathConnectedSpace_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [PathConnectedSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) :
    PathConnectedSpace X := by
  exact
    ⟨inferInstance, fun x y =>
      (joined_iff_of_homologyZero_injective f hf x y).mp (PathConnectedSpace.joined (f x) (f y))⟩

theorem MorseCancellation.pathConnectedSpace_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  let : Nonempty X := ⟨e.invFun (Classical.arbitrary Y)⟩
  exact
    pathConnectedSpace_of_homologyZero_injective e.toFun
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0).injective

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (d.coreCellPresentation hf).old k :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv (d.cellOldHomeomorph hf) k

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (d.coreUnionHomotopyEquiv hf) k

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.morseConnectingMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k :=
  ((d.coreCellPresentation hf).cellConnectingMap k).comp
    (d.cellTotalHomologyEquiv hf (k + 1)).symm.toLinearMap

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :
    (d.coreCellPresentation hf).attachingHomologyMap k a =
      d.cellOldHomologyEquiv hf k (d.coreBoundaryHomologyMap k a) := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).attachingSphere k a =
      SingularMayerVietoris.singularHomologyMap (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k a)
  rw [d.coreCell_attaching_eq, PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.cellOldHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) :
    d.cellTotalHomologyEquiv hf k
        ((d.coreCellPresentation hf).oldHomologyMap k (d.cellOldHomologyEquiv hf k a)) =
      d.lowerRealizationHomologyMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (d.coreCellPresentation hf).old) k
          (SingularMayerVietoris.singularHomologyMap
            (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.morseConnecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) (k + 1)) :
    d.morseConnectingMap hf k (d.cellTotalHomologyEquiv hf (k + 1) a) =
      (d.coreCellPresentation hf).cellConnectingMap k a := by
  change
    (d.coreCellPresentation hf).cellConnectingMap k
        ((d.cellTotalHomologyEquiv hf (k + 1)).symm (d.cellTotalHomologyEquiv hf (k + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.coreBoundaryHomologyMap k) =
      LinearMap.ker (d.lowerRealizationHomologyMap k) := by
  refine
    Smale.HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
      (d.cellOldHomologyEquiv hf k).symm (d.cellTotalHomologyEquiv hf k)
      ((d.coreCellPresentation hf).attachingHomologyMap k)
      ((d.coreCellPresentation hf).oldHomologyMap k) (d.coreBoundaryHomologyMap k)
      (d.lowerRealizationHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_old k hk)
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have h := d.cellOldHomology_compare hf k ((d.cellOldHomologyEquiv hf k).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) =
      LinearMap.ker (d.morseConnectingMap hf k) := by
  refine
    Smale.HomologyTransport.exact_of_equivalences (d.cellOldHomologyEquiv hf (k + 1)).symm
      (d.cellTotalHomologyEquiv hf (k + 1)) (LinearEquiv.refl ℤ _)
      ((d.coreCellPresentation hf).oldHomologyMap (k + 1))
      ((d.coreCellPresentation hf).cellConnectingMap k) (d.lowerRealizationHomologyMap (k + 1))
      (d.morseConnectingMap hf k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_ambient k)
  · intro a
    have h := d.cellOldHomology_compare hf (k + 1) ((d.cellOldHomologyEquiv hf (k + 1)).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact d.morseConnecting_compare hf k

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.morseConnectingMap hf k) = LinearMap.ker (d.coreBoundaryHomologyMap k) := by
  refine
    Smale.HomologyTransport.exact_of_equivalences (d.cellTotalHomologyEquiv hf (k + 1))
      (LinearEquiv.refl ℤ _) (d.cellOldHomologyEquiv hf k).symm
      ((d.coreCellPresentation hf).cellConnectingMap k)
      ((d.coreCellPresentation hf).attachingHomologyMap k) (d.morseConnectingMap hf k)
      (d.coreBoundaryHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_sphere k hk)
  · exact d.morseConnecting_compare hf k
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)]
    [Subsingleton
        (SingularMayerVietoris.SingularHomology
          (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  have hall :
    ∀ a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k, a = 0 :=
    by
    intro a
    have ha : a ∈ LinearMap.ker (d.lowerRealizationHomologyMap k) := Subsingleton.elim _ _
    rw [← d.morse_exact_at_lower hf k hk] at ha
    obtain ⟨s, hs⟩ := ha
    have hs0 : s = 0 := Subsingleton.elim _ _
    rw [hs0, map_zero] at hs
    exact hs.symm
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

theorem Smale.ManifoldMorse.MorseSurgeryData.attachingSphere_pathConnected {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    PathConnectedSpace (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by omega)) _ zero_le_one)

theorem Smale.ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :
    d.morseConnectingMap hf 0 a = 0 := by
  let := d.attachingSphere_pathConnected hindex
  exact (d.coreCellPresentation hf).cellConnecting_zero_apply _

theorem Smale.ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Surjective (d.lowerRealizationHomologyMap 1) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 0) :=
    d.morseConnecting_zero_apply hf hindex a
  rw [← d.morse_exact_at_upper hf 0] at ha
  exact ha

theorem Smale.ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :=
  (d.lowerRealization_one_surjective hf hindex).subsingleton

theorem MorseCancellation.native_lowerRealization_zero_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Bijective (d.lowerRealizationHomologyMap 0) := by
  let := d.attachingSphere_pathConnected hindex
  have hi := cell_oldHomologyMap_zero_bijective (d.coreCellPresentation hf)
  have heq :
    d.lowerRealizationHomologyMap 0 =
      (d.cellTotalHomologyEquiv hf 0).toLinearMap.comp
        (((d.coreCellPresentation hf).oldHomologyMap 0).comp
          (d.cellOldHomologyEquiv hf 0).toLinearMap) := by
    ext a
    exact (d.cellOldHomology_compare hf 0 a).symm
  rw [heq]
  exact
    (d.cellTotalHomologyEquiv hf 0).bijective.comp
      (hi.comp (d.cellOldHomologyEquiv hf 0).bijective)

theorem MorseCancellation.native_lower_pathConnected_of_upper {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let := d.attachingSphere_pathConnected hindex
  let : Nonempty { z : M // f z ≤ f p - d.radius ^ 2 } :=
    ⟨d.coreBoundaryMap (Classical.arbitrary (Metric.sphere (0 : d.chart.NegativeCoordinates) 1))⟩
  exact
    pathConnectedSpace_of_homologyZero_injective d.realizedLowerInclusion
      (native_lowerRealization_zero_bijective d hf hindex).1

def Smale.ManifoldMorse.SurgeryWindows.values {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) : Finset ℝ :=
  (S.finite.image f).toFinset

def Smale.ManifoldMorse.SurgeryWindows.count {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) : ℕ :=
  S.values.card

def Smale.ManifoldMorse.SurgeryWindows.point {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) :
    Fin S.count ≃ Smale.ManifoldMorse.criticalPoints E f :=
  ((S.values.orderIsoOfFin rfl).toEquiv.trans
        (Equiv.setCongr (S.finite.image f).coe_toFinset)).trans
    (Equiv.Set.imageOfInjOn f (Smale.ManifoldMorse.criticalPoints E f) S.distinct).symm

theorem Smale.ManifoldMorse.SurgeryWindows.point_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i : Fin S.count) :
    f (S.point i) = S.values.orderEmbOfFin rfl i := by
  let e := Equiv.Set.imageOfInjOn f (Smale.ManifoldMorse.criticalPoints E f) S.distinct
  let v : f '' Smale.ManifoldMorse.criticalPoints E f :=
    Equiv.setCongr (S.finite.image f).coe_toFinset (S.values.orderIsoOfFin rfl i)
  have h :=
    congrArg (fun x : f '' Smale.ManifoldMorse.criticalPoints E f => (x : ℝ))
      (e.apply_symm_apply v)
  exact h

theorem Smale.ManifoldMorse.SurgeryWindows.point_strictMono {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) :
    StrictMono (fun i : Fin S.count => f (S.point i)) := by
  intro i j hij
  change f (S.point i) < f (S.point j)
  rw [S.point_value, S.point_value]
  exact (S.values.orderEmbOfFin rfl).strictMono hij

theorem Smale.ManifoldMorse.SurgeryWindows.point_consecutive {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f (S.point i) < f r ∧ f r < f (S.point j)) := by
  intro r hr
  obtain ⟨k, rfl⟩ := S.point.surjective r
  have hik : i < k := S.point_strictMono.lt_iff_lt.mp hr.1
  have hkj : k < j := S.point_strictMono.lt_iff_lt.mp hr.2
  have hik' : i.val < k.val := hik
  have hkj' : k.val < j.val := hkj
  omega

theorem Smale.ManifoldMorse.SurgeryWindows.ordered_windows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i < j) :
    S.upper (S.point i) < S.lower (S.point j) :=
  S.upper_lt_lower _ _ (S.point_strictMono hij)

theorem Smale.ManifoldMorse.SurgeryWindows.consecutive_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ x,
      f x ∈ Set.Icc (S.upper (S.point i)) (S.lower (S.point j)) →
        x ∉ Smale.ManifoldMorse.criticalPoints E f :=
  S.regular_between _ _ (S.point_consecutive i j hij)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SurgeryWindows.exists_consecutiveBandBridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i j : Fin S.count)
    (hij : i.val + 1 = j.val) :
    letI := Smale.RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := Smale.RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data (S.point i)).UpperLevel (S.data (S.point j)).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper (S.point i)} = {x : M | f x ≤ S.lower (S.point j)} ∧
          ∀ x : (S.data (S.point i)).UpperLevel, (b x : M) = D x := by
  have hlt : i < j := by change i.val < j.val; omega
  exact S.exists_bandBridge hf _ _ (S.point_strictMono hlt) (S.point_consecutive i j hij)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.negative_eq_zero_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p)
    (u : c.NegativeCoordinates) : u = 0 := by
  by_contra hu
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨U, hUmin, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmin
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.NegativeCoordinates := (r / ‖u‖) • u
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖u‖) • u from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint :=
    hblock
      (show (z, (0 : c.PositiveCoordinates)) ∈ Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r from
        ⟨mem_closedBall_zero_iff.mpr hz.le, by
          simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le⟩)
  have hh := hUmin hpoint.2
  change f p ≤ f (c.splitChart.symm (z, (0 : c.PositiveCoordinates))) at hh
  rw [c.splitChart_inverse_equation hpoint.1, hz, norm_zero] at hh
  nlinarith [sq_pos_of_pos hr]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.subsingleton_negative_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Subsingleton c.NegativeCoordinates :=
  ⟨fun u v =>
    (c.negative_eq_zero_of_localMin hmin u).trans (c.negative_eq_zero_of_localMin hmin v).symm⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.positive_eq_zero_of_localMax {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmax : IsLocalMax f p)
    (v : c.PositiveCoordinates) : v = 0 := by
  by_contra hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨U, hUmax, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmax
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.PositiveCoordinates := (r / ‖v‖) • v
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖v‖) • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint :=
    hblock
      (show ((0 : c.NegativeCoordinates), z) ∈ Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r from
        ⟨by simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le,
          mem_closedBall_zero_iff.mpr hz.le⟩)
  have hh := hUmax hpoint.2
  change f (c.splitChart.symm ((0 : c.NegativeCoordinates), z)) ≤ f p at hh
  rw [c.splitChart_inverse_equation hpoint.1, norm_zero, hz] at hh
  nlinarith [sq_pos_of_pos hr]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.subsingleton_positive_of_localMax {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmax : IsLocalMax f p) :
    Subsingleton c.PositiveCoordinates :=
  ⟨fun u v =>
    (c.positive_eq_zero_of_localMax hmax u).trans (c.positive_eq_zero_of_localMax hmax v).symm⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.exists_minimum_disk_sublevel_with_height
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ ρ > (0 : ℝ),
      f p + ρ ^ 2 < b ∧
        ∃ e : Smale.MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ { x : M // f x ≤ f p + ρ ^ 2 },
          ∀ v, f (e v).1 = f p + ρ ^ 2 * ‖(v : c.PositiveCoordinates)‖ ^ 2 := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  let : Subsingleton c.NegativeCoordinates := c.subsingleton_negative_of_localMin hmin
  obtain ⟨R, hR, hblockR⟩ := c.exists_closed_productBlock
  obtain ⟨ε, hε, hsublevel⟩ :=
    Smale.exists_small_sublevel_subset hf hunique c.splitChart.open_source c.splitChart_mem_source
  let δ := Min.min ε (b - f p)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hb)
  let ρ := Min.min (R / 2) (Min.min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ ≤ R / 2 := min_le_left _ _
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  have hsqε : ρ ^ 2 < ε := hρsq.trans_le (min_le_left _ _)
  have hsqb : ρ ^ 2 < b - f p := hρsq.trans_le (min_le_right _ _)
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target := by
    intro z hz
    have hr : 2 * ρ ≤ R := by linarith
    exact
      hblockR
        ⟨Metric.closedBall_subset_closedBall hr hz.1, Metric.closedBall_subset_closedBall hr hz.2⟩
  let z₀ : Smale.MorseHandle.UnitDisk c.NegativeCoordinates := ⟨0, by simp⟩
  let h : C(Smale.MorseHandle.UnitDisk c.PositiveCoordinates, { x : M // f x ≤ f p + ρ ^ 2 }) :=
    { toFun := fun v =>
        ⟨c.attachingHandleMap ρ hρ hblock (z₀, v), c.attachingHandleMap_upper ρ hρ hblock (z₀, v)⟩
      continuous_toFun :=
        ((c.attachingHandleMap ρ hρ hblock).continuous.comp
              (continuous_const.prodMk continuous_id)).subtype_mk
          _ }
  have hinj : Function.Injective h := by
    intro v w hvw
    have heq := c.attachingHandleMap_injective ρ hρ hblock (congrArg Subtype.val hvw)
    exact congrArg Prod.snd heq
  have hsurj : Function.Surjective h := by
    intro y
    have hyS : y.1 ∈ c.splitChart.source :=
      hsublevel
        (show f y.1 ≤ f p + ε from by
          have hy := y.2
          linarith)
    have heq := c.splitChart_equation hyS
    have hnegative : (c.splitChart y.1).1 = 0 := Subsingleton.elim _ _
    rw [hnegative, norm_zero] at heq
    have hypos : ‖(c.splitChart y.1).2‖ ≤ ρ := by
      have hy := y.2
      nlinarith [norm_nonneg (c.splitChart y.1).2]
    have hylower : f p - ρ ^ 2 ≤ f y.1 := by
      have hy := hglobal y.1
      linarith [sq_nonneg ρ]
    obtain ⟨⟨u, v⟩, huv⟩ :=
      (c.mem_range_attachingHandleMap_iff_inequalities ρ hρ hblock hyS).mpr ⟨hypos, hylower⟩
    have hu : u = z₀ := Subsingleton.elim _ _
    subst u
    exact ⟨v, Subtype.ext huv⟩
  refine ⟨ρ, hρ, by linarith, ?_⟩
  refine
    ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h ⟨hinj, hsurj⟩) h.continuous, ?_⟩
  intro v
  change f (c.attachingHandleMap ρ hρ hblock (z₀, v)) = _
  rw [c.attachingHandleMap_quadratic]
  change
    f p +
        (-‖(ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) •
                  (0 : c.NegativeCoordinates)‖ ^
              2 +
          ‖ρ • (v : c.PositiveCoordinates)‖ ^ 2) =
      _
  simp only [smul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_add,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.finrank_positive_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Module.finrank ℝ c.PositiveCoordinates = Module.finrank ℝ E := by
  let : Unique c.NegativeCoordinates :=
    { default := 0, uniq := c.negative_eq_zero_of_localMin hmin }
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] c.PositiveCoordinates :=
    (Smale.MorseHandle.splitLinearEquiv c.weights).trans
      (LinearEquiv.uniqueProd (R := ℝ) (M := c.PositiveCoordinates) (M₂ := c.NegativeCoordinates))
  simpa using e.finrank_eq.symm

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.minimumPositiveIsometry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    c.PositiveCoordinates ≃ₗᵢ[ℝ] Smale.Hemisphere.Ambient (Module.finrank ℝ E) :=
  (stdOrthonormalBasis ℝ c.PositiveCoordinates).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (c.finrank_positive_of_localMin hmin)))

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.SignedMorseChart.minimumDiskHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Smale.MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ
      Smale.Hemisphere.Ball (Module.finrank ℝ E) :=
  (c.minimumPositiveIsometry hmin).toHomeomorph.subtype (p := fun x => x ∈ Metric.closedBall 0 1)
    (q := fun x => x ∈ Metric.closedBall 0 1)
    (fun x => by
      simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.coe_toHomeomorph,
        LinearIsometryEquiv.norm_map])

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.norm_minimumDiskHomeomorph_symm {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p)
    (v : Smale.Hemisphere.Ball (Module.finrank ℝ E)) :
    ‖((c.minimumDiskHomeomorph hmin).symm v : c.PositiveCoordinates)‖ =
      ‖(v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ := by
  change
    ‖(c.minimumPositiveIsometry hmin).symm (v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ =
      _
  exact (c.minimumPositiveIsometry hmin).symm.norm_map _

def Smale.Hemisphere.tail {n : ℕ} (y : Sphere n) : Ambient n :=
  WithLp.toLp 2 (fun i => (y : Ambient (n + 1)) i.succ)

theorem Smale.Hemisphere.head_sq_add_tail_norm_sq {n : ℕ} (y : Sphere n) :
    (y : Ambient (n + 1)) 0 ^ 2 + ‖tail y‖ ^ 2 = 1 := by
  have hy : ‖(y : Ambient (n + 1))‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp y.property]
    exact one_pow 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hy
  rw [EuclideanSpace.real_norm_sq_eq]
  exact hy

theorem Smale.Hemisphere.tail_mem_ball {n : ℕ} (y : Sphere n) :
    tail y ∈ Metric.closedBall (0 : Ambient n) 1 := by
  rw [mem_closedBall_zero_iff]
  have hy := head_sq_add_tail_norm_sq y
  nlinarith [sq_nonneg ((y : Ambient (n + 1)) 0), norm_nonneg (tail y)]

def Smale.Hemisphere.disk {n : ℕ} (y : Sphere n) : Ball n :=
  ⟨tail y, tail_mem_ball y⟩

theorem Smale.Hemisphere.radius_disk {n : ℕ} (y : Sphere n) :
    radius (disk y) = |(y : Ambient (n + 1)) 0| := by
  have hy := head_sq_add_tail_norm_sq y
  have hs : 1 - ‖tail y‖ ^ 2 = (y : Ambient (n + 1)) 0 ^ 2 := by linarith
  change Real.sqrt (1 - ‖tail y‖ ^ 2) = _
  rw [hs, Real.sqrt_sq_eq_abs]

theorem Smale.Hemisphere.point_disk_of_nonneg {n : ℕ} (y : Sphere n)
    (hy : 0 ≤ (y : Ambient (n + 1)) 0) : point Bool.true (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonneg hy]
  · rfl

theorem Smale.Hemisphere.point_disk_of_nonpos {n : ℕ} (y : Sphere n)
    (hy : (y : Ambient (n + 1)) 0 ≤ 0) : point Bool.false (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonpos hy]
  · rfl

theorem Smale.Hemisphere.point_jointly_surjective {n : ℕ} (y : Sphere n) : ∃ b x, point b x = y :=
  by
  rcases le_total 0 ((y : Ambient (n + 1)) 0) with hy | hy
  · exact ⟨Bool.true, disk y, point_disk_of_nonneg y hy⟩
  · exact ⟨Bool.false, disk y, point_disk_of_nonpos y hy⟩

def Smale.DiskDouble.hemisphereMap (n : ℕ) :
    Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n → Smale.Hemisphere.Sphere n :=
  Sum.elim (Smale.Hemisphere.point Bool.false) (Smale.Hemisphere.point Bool.true)

theorem Smale.DiskDouble.continuous_hemisphereMap (n : ℕ) : Continuous (hemisphereMap n) :=
  continuous_sum_dom.mpr
    ⟨Smale.Hemisphere.continuous_point Bool.false, Smale.Hemisphere.continuous_point Bool.true⟩

theorem Smale.DiskDouble.hemisphereMap_respects (n : ℕ)
    (x y : Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n)
    (h : Smale.DiskDouble.Rel (Homeomorph.refl (Boundary (Smale.Hemisphere.Ambient n))) x y) :
    hemisphereMap n x = hemisphereMap n y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y =>
      obtain ⟨z, rfl, rfl⟩ := h
      exact Smale.Hemisphere.point_boundary z
  | inr x => cases y <;> exact h.elim

def Smale.DiskDouble.sphereMap (n : ℕ) :
    Space (Homeomorph.refl (Boundary (Smale.Hemisphere.Ambient n))) → Smale.Hemisphere.Sphere n :=
  Quot.lift (hemisphereMap n) (hemisphereMap_respects n)

theorem Smale.DiskDouble.continuous_sphereMap (n : ℕ) : Continuous (sphereMap n) :=
  continuous_quot_lift (hemisphereMap_respects n) (continuous_hemisphereMap n)

theorem Smale.DiskDouble.sphereMap_injective (n : ℕ) : Function.Injective (sphereMap n) := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := Smale.Hemisphere.point_injective Bool.false h
          subst y
          rfl
        | inr y => exact Quot.sound ((Smale.Hemisphere.point_false_eq_true_iff x y).mp h)
      | inr x =>
        cases y with
        | inl y =>
          exact (Quot.sound ((Smale.Hemisphere.point_false_eq_true_iff y x).mp h.symm)).symm
        | inr y =>
          have hxy := Smale.Hemisphere.point_injective Bool.true h
          subst y
          rfl

theorem Smale.DiskDouble.sphereMap_surjective (n : ℕ) : Function.Surjective (sphereMap n) := by
  intro y
  obtain ⟨b, x, hx⟩ := Smale.Hemisphere.point_jointly_surjective y
  cases b
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr x), hx⟩

def Smale.DiskDouble.homeomorphSphere (n : ℕ) :
    Space (Homeomorph.refl (Boundary (Smale.Hemisphere.Ambient n))) ≃ₜ
      Smale.Hemisphere.Sphere n :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (sphereMap n) ⟨sphereMap_injective n, sphereMap_surjective n⟩)
    (continuous_sphereMap n)

def Smale.DiskDouble.twistedHomeomorphSphere (n : ℕ)
    (e : Boundary (Smale.Hemisphere.Ambient n) ≃ₜ Boundary (Smale.Hemisphere.Ambient n)) :
    Space e ≃ₜ Smale.Hemisphere.Sphere n :=
  (homeomorphUntwisted e).trans (homeomorphSphere n)

structure Smale.TwoDiskDecomposition (n : ℕ) (M : Type*) [TopologicalSpace M] where
  boundaryEquiv :
    DiskDouble.Boundary (Hemisphere.Ambient n) ≃ₜ DiskDouble.Boundary (Hemisphere.Ambient n)
  left : C(Hemisphere.Ball n, M)
  right : C(Hemisphere.Ball n, M)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  covers : ∀ p : M, (∃ x, left x = p) ∨ ∃ y, right y = p
  overlap :
    ∀ x y,
      left x = right y ↔
        ∃ z : DiskDouble.Boundary (Hemisphere.Ambient n),
          x = DiskDouble.boundary (Hemisphere.Ambient n) z ∧
            y = DiskDouble.boundary (Hemisphere.Ambient n) (boundaryEquiv z)

def Smale.TwoDiskDecomposition.sumMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) :
    Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n → M :=
  Sum.elim d.left d.right

theorem Smale.TwoDiskDecomposition.continuous_sumMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Continuous d.sumMap :=
  continuous_sum_dom.mpr ⟨d.left.continuous, d.right.continuous⟩

theorem Smale.TwoDiskDecomposition.sumMap_respects {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) (x y : Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n)
    (h : Smale.DiskDouble.Rel d.boundaryEquiv x y) : d.sumMap x = d.sumMap y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y => exact (d.overlap x y).mpr h
  | inr x => cases y <;> exact h.elim

def Smale.TwoDiskDecomposition.quotientMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Smale.DiskDouble.Space d.boundaryEquiv → M :=
  Quot.lift d.sumMap d.sumMap_respects

theorem Smale.TwoDiskDecomposition.continuous_quotientMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Continuous d.quotientMap :=
  continuous_quot_lift d.sumMap_respects d.continuous_sumMap

theorem Smale.TwoDiskDecomposition.quotientMap_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Function.Injective d.quotientMap := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := d.left_injective h
          subst y
          rfl
        | inr y => exact Quot.sound ((d.overlap x y).mp h)
      | inr x =>
        cases y with
        | inl y => exact (Quot.sound ((d.overlap y x).mp h.symm)).symm
        | inr y =>
          have hxy := d.right_injective h
          subst y
          rfl

theorem Smale.TwoDiskDecomposition.quotientMap_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Function.Surjective d.quotientMap := by
  intro p
  rcases d.covers p with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr y), hy⟩

def Smale.TwoDiskDecomposition.quotientHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) [T2Space M] :
    Smale.DiskDouble.Space d.boundaryEquiv ≃ₜ M :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective d.quotientMap ⟨d.quotientMap_injective, d.quotientMap_surjective⟩)
    d.continuous_quotientMap

def Smale.TwoDiskDecomposition.homeomorphSphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) [T2Space M] : M ≃ₜ Smale.Hemisphere.Sphere n :=
  d.quotientHomeomorph.symm.trans (Smale.DiskDouble.twistedHomeomorphSphere n d.boundaryEquiv)

structure Smale.SublevelDisk (n : ℕ) {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  homeomorph : Hemisphere.Ball n ≃ₜ { x : M // f x ≤ a }
  boundary_iff : ∀ v, f (homeomorph v).1 = a ↔ ‖(v : Hemisphere.Ambient n)‖ = 1

def Smale.SublevelDisk.map {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.SublevelDisk n f a) : C(Smale.Hemisphere.Ball n, M)
    where
  toFun v := (d.homeomorph v).1
  continuous_toFun := continuous_subtype_val.comp d.homeomorph.continuous

theorem Smale.SublevelDisk.map_injective {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} (d : Smale.SublevelDisk n f a) : Function.Injective d.map := by
  intro v w h
  exact d.homeomorph.injective (Subtype.ext h)

def Smale.SublevelDisk.boundaryMap {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.SublevelDisk n f a) :
    C(Smale.DiskDouble.Boundary (Smale.Hemisphere.Ambient n), { x : M // f x = a })
    where
  toFun
    z :=
    ⟨d.map (Smale.DiskDouble.boundary _ z),
      (d.boundary_iff _).mpr
        (by simpa only [Smale.DiskDouble.boundary, mem_sphere_zero_iff_norm] using z.2)⟩
  continuous_toFun :=
    (d.map.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun z => Metric.sphere_subset_closedBall z.2))).subtype_mk
      _

theorem Smale.SublevelDisk.boundaryMap_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a : ℝ} (d : Smale.SublevelDisk n f a) : Function.Injective d.boundaryMap := by
  intro z w h
  have heq : d.map (Smale.DiskDouble.boundary _ z) = d.map (Smale.DiskDouble.boundary _ w) :=
    congrArg (fun y : { x : M // f x = a } => y.1) h
  have h' := d.map_injective heq
  apply Subtype.ext
  exact congrArg (fun v : Smale.Hemisphere.Ball n => (v : Smale.Hemisphere.Ambient n)) h'

theorem Smale.SublevelDisk.boundaryMap_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a : ℝ} (d : Smale.SublevelDisk n f a) : Function.Surjective d.boundaryMap := by
  intro y
  let v := d.homeomorph.symm ⟨y.1, y.2.le⟩
  have hv : (d.homeomorph v).1 = y.1 :=
    congrArg Subtype.val (d.homeomorph.apply_symm_apply ⟨y.1, y.2.le⟩)
  have hnorm : ‖(v : Smale.Hemisphere.Ambient n)‖ = 1 :=
    (d.boundary_iff v).mp (by rw [hv]; exact y.2)
  let z : Smale.DiskDouble.Boundary (Smale.Hemisphere.Ambient n) :=
    ⟨v.1, mem_sphere_zero_iff_norm.mpr hnorm⟩
  refine ⟨z, Subtype.ext ?_⟩
  exact hv

def Smale.SublevelDisk.boundaryHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} (d : Smale.SublevelDisk n f a) [T2Space M] :
    Smale.DiskDouble.Boundary (Smale.Hemisphere.Ambient n) ≃ₜ { x : M // f x = a } :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective d.boundaryMap ⟨d.boundaryMap_injective, d.boundaryMap_surjective⟩)
    d.boundaryMap.continuous

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SignedMorseChart.exists_minimumSublevelDisk {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ a ∈ Set.Ioo (f p) b, Nonempty (Smale.SublevelDisk (Module.finrank ℝ E) f a) := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  obtain ⟨ρ, hρ, hab, e, he⟩ := exists_minimum_disk_sublevel_with_height c hf hunique hb
  let d := (c.minimumDiskHomeomorph hmin).symm.trans e
  have hd (v : Smale.Hemisphere.Ball (Module.finrank ℝ E)) :
    f (d v).1 = f p + ρ ^ 2 * ‖(v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 := by
    change f (e ((c.minimumDiskHomeomorph hmin).symm v)).1 = _
    rw [he, c.norm_minimumDiskHomeomorph_symm]
  refine ⟨f p + ρ ^ 2, ⟨by linarith [sq_pos_of_pos hρ], hab⟩, ⟨⟨d, ?_⟩⟩⟩
  intro v
  rw [hd]
  constructor
  · intro h
    have hs : ‖(v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 = 1 :=
      mul_left_cancel₀ (pow_ne_zero 2 hρ.ne') (by linarith)
    nlinarith [norm_nonneg (v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))]
  · intro h
    rw [h, one_pow, mul_one]

theorem Smale.FlowConstruction.exists_regularSublevelHomeomorph_with_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Set.Icc c (Max.max a b) → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ e : { x : M // f x ≤ a } ≃ₜ { x : M // f x ≤ b }, ∀ x, f (e x).1 = b ↔ f x.1 = a := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  refine
    ⟨regularSublevelHomeomorphOfFlow F hF hf.continuous hca hcb (le_max_left a b)
        (le_max_right a b),
      ?_⟩
  exact
    regularSublevelHomeomorphOfFlow_level_iff F hF hf.continuous hca hcb (le_max_left a b)
      (le_max_right a b)

def Smale.SublevelDisk.transport {M : Type*} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {a b : ℝ}
    (d : Smale.SublevelDisk n f a) (e : { x : M // f x ≤ a } ≃ₜ { x : M // f x ≤ b })
    (he : ∀ x, f (e x).1 = b ↔ f x.1 = a) : Smale.SublevelDisk n f b
    where
  homeomorph := d.homeomorph.trans e
  boundary_iff v := (he (d.homeomorph v)).trans (d.boundary_iff v)

theorem Smale.FlowConstruction.nonempty_regularSublevelDisk {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {n : ℕ} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Set.Icc c (Max.max a b) → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (d : Smale.SublevelDisk n f a) : Nonempty (Smale.SublevelDisk n f b) := by
  obtain ⟨e, he⟩ := exists_regularSublevelHomeomorph_with_level hf hca hcb hband
  exact ⟨d.transport e he⟩

theorem Smale.ManifoldMorse.SignedMorseChart.nonempty_sublevelDisk_before_next_critical
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b)
    (hregular : ∀ x, f p < f x → f x ≤ b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    Nonempty (Smale.SublevelDisk (Module.finrank ℝ E) f b) := by
  obtain ⟨a, ha, ⟨d⟩⟩ := c.exists_minimumSublevelDisk hf.continuous hunique hb
  obtain ⟨l, hpl, hla⟩ := exists_between ha.1
  apply Smale.FlowConstruction.nonempty_regularSublevelDisk hf hla (hla.trans ha.2) _ d
  intro x hx
  apply hregular x (hpl.trans_le hx.1)
  exact hx.2.trans (max_le ha.2.le le_rfl)

def Smale.ManifoldMorse.SurgeryWindows.first {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count) :
    Smale.ManifoldMorse.criticalPoints E f :=
  S.point ⟨0, h⟩

def Smale.ManifoldMorse.SurgeryWindows.last {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count) :
    Smale.ManifoldMorse.criticalPoints E f :=
  S.point ⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩

theorem Smale.ManifoldMorse.SurgeryWindows.value_first_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count)
    (p : Smale.ManifoldMorse.criticalPoints E f) : f (S.first h) ≤ f p := by
  have hle : (⟨0, h⟩ : Fin S.count) ≤ S.point.symm p := Nat.zero_le _
  simpa only [first, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

theorem Smale.ManifoldMorse.SurgeryWindows.value_le_last {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count)
    (p : Smale.ManifoldMorse.criticalPoints E f) : f p ≤ f (S.last h) := by
  have hle : S.point.symm p ≤ (⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩ : Fin S.count) :=
    Nat.le_sub_one_of_lt (S.point.symm p).isLt
  simpa only [last, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

theorem Smale.ManifoldMorse.SurgeryWindows.count_pos {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [Nonempty M] : 0 < S.count := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun x => hmin (Set.mem_univ x)))
  exact lt_of_le_of_lt (Nat.zero_le _) (S.point.symm ⟨p, hp⟩).isLt

theorem Smale.ManifoldMorse.SurgeryWindows.first_globalMin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) : f (S.first h) ≤ f x := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hmin (Set.mem_univ y)))
  exact (S.value_first_le h ⟨p, hp⟩).trans (hmin (Set.mem_univ x))

theorem Smale.ManifoldMorse.SurgeryWindows.last_globalMax {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) : f x ≤ f (S.last h) := by
  obtain ⟨p, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMax hf
      (Filter.Eventually.of_forall (fun y => hmax (Set.mem_univ y)))
  exact (hmax (Set.mem_univ x)).trans (S.value_le_last h ⟨p, hp⟩)

theorem Smale.ManifoldMorse.SurgeryWindows.unique_first {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) (hx : f x ≤ f (S.first h)) :
    x = (S.first h).val := by
  have hxcrit : x ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hx.trans (S.first_globalMin hf h y)))
  exact S.distinct hxcrit (S.first h).property (le_antisymm hx (S.first_globalMin hf h x))

theorem Smale.ManifoldMorse.SurgeryWindows.last_upper_univ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    {x : M | f x ≤ S.upper (S.last h)} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (S.last_globalMax hf h x).trans (S.value_lt_upper (S.last h)).le

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SurgeryWindows.first_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.first h)).chart.NegativeCoordinates = 0 := by
  let :=
    (S.data (S.first h)).chart.subsingleton_negative_of_localMin
      (Filter.Eventually.of_forall (S.first_globalMin hf h))
  exact Module.finrank_zero_of_subsingleton

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SurgeryWindows.last_index_dimension {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.last h)).chart.NegativeCoordinates = Module.finrank ℝ E := by
  let :=
    (S.data (S.last h)).chart.subsingleton_positive_of_localMax
      (Filter.Eventually.of_forall (S.last_globalMax hf h))
  have hz : Module.finrank ℝ (S.data (S.last h)).chart.PositiveCoordinates = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [hz, add_zero] using (S.data (S.last h)).chart.finrank_negative_add_positive

theorem Smale.ManifoldMorse.SurgeryWindows.nonempty_firstSublevelDisk {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [FiniteDimensional ℝ E] [T2Space M] (h : 0 < S.count) :
    Nonempty (Smale.SublevelDisk (Module.finrank ℝ E) f (S.upper (S.first h))) := by
  apply
    (S.data (S.first h)).chart.nonempty_sublevelDisk_before_next_critical hf (S.unique_first hf h)
      (S.value_lt_upper (S.first h))
  intro x hxlo hxhi hxcrit
  have hxlower : S.lower (S.first h) ≤ f x := (S.lower_lt_value (S.first h)).le.trans hxlo.le
  have hxp := S.isolated (S.first h) x hxcrit ⟨hxlower, hxhi⟩
  rw [hxp] at hxlo
  exact lt_irrefl _ hxlo

theorem Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ e : { x : M // f x ≤ a } ≃ₕ { x : M // f x ≤ b }, ∀ x, (e x).1 = x.1 := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularSublevelHomotopyEquivOfFlow F hF hf.continuous hab, fun _ => rfl⟩

theorem MorseCancellation.ordered_upper_pathConnected_of_later_transfers {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (htransfer :
      ∀ j : Fin S.count,
        i.val < j.val →
          PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
            PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) :
    PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
  have hall :
    ∀ k : ℕ,
      ∀ i : Fin S.count,
        S.count - 1 - i.val = k →
          (∀ j : Fin S.count,
              i.val < j.val →
                PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
                  PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) →
            PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki hindices
      have hpos : 0 < S.count := (Nat.zero_le i.val).trans_lt i.isLt
      by_cases hlast : i.val = S.count - 1
      · have hi : S.point i = S.last hpos := congrArg S.point (Fin.ext hlast)
        have hset : {x : M | f x ≤ S.upper (S.point i)} = Set.univ := by
          rw [hi]
          exact S.last_upper_univ hf hpos
        have hp : IsPathConnected {x : M | f x ≤ S.upper (S.point i)} :=
          hset.symm ▸ isPathConnected_univ
        exact isPathConnected_iff_pathConnectedSpace.mp hp
      · have hjlt : i.val + 1 < S.count := by omega
        let j : Fin S.count := ⟨i.val + 1, hjlt⟩
        have hjmeasure : S.count - 1 - j.val < k := by
          dsimp [j]
          omega
        have hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } :=
          ih _ hjmeasure j rfl (fun q hq => hindices q (by dsimp [j] at hq; omega))
        let : PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) } :=
          hindices j (by dsimp [j]; omega) hupper
        have hij : i < j := by change i.val < i.val + 1; omega
        obtain ⟨e, -⟩ :=
          Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv hf
            (S.ordered_windows i j hij).le (S.consecutive_regular i j rfl)
        exact pathConnectedSpace_of_homotopyEquiv e
  exact hall _ i rfl htransfer

theorem MorseCancellation.cell_old_empty_of_empty_boundary {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] [PreconnectedSpace X]
    (D : Smale.EmbeddedCellAttachment N X) [IsEmpty (Metric.sphere (0 : N) 1)] : D.old = ∅ := by
  have hdisjoint (z : Smale.MorseHandle.UnitDisk N) : D.cell z ∉ D.old := by
    intro hz
    exact
      isEmptyElim
        (⟨z.val, mem_sphere_zero_iff_norm.mpr ((D.boundary z).mp hz)⟩ : Metric.sphere (0 : N) 1)
  have heq : D.old = (Set.range D.cell)ᶜ := by
    ext x
    constructor
    · intro hx ⟨z, hz⟩
      exact hdisjoint z (hz ▸ hx)
    · intro hx
      have hc : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
      exact hc.resolve_right hx
  have hc : IsClopen D.old := ⟨D.old_closed, heq.symm ▸ D.cell_closed.isClosed_range.isOpen_compl⟩
  rcases isClopen_iff.mp hc with h | h
  · exact h
  · let z : Smale.MorseHandle.UnitDisk N := ⟨0, by simp⟩
    exact False.elim (hdisjoint z (h ▸ Set.mem_univ _))

theorem MorseCancellation.native_zero_handle_lower_isEmpty {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    IsEmpty { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : Subsingleton d.chart.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ d.chart.NegativeCoordinates).mp hindex
  let : IsEmpty (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
    ⟨fun v => by
      have h := mem_sphere_zero_iff_norm.mp v.property
      rw [Subsingleton.elim v.val 0, norm_zero] at h
      norm_num at h⟩
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  have he := cell_old_empty_of_empty_boundary (d.coreCellPresentation hf)
  refine ⟨fun x => ?_⟩
  have hx := (d.cellOldHomeomorph hf x).property
  exact (Set.eq_empty_iff_forall_notMem.mp he) _ hx

theorem Smale.SublevelDisk.circle_nullhomotopies {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} (d : Smale.SublevelDisk (n + 1) f a) (hn : 1 < n) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = a }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let e : Smale.Hemisphere.Sphere n ≃ₜ { x : M // f x = a } := d.boundaryHomeomorph
  let forward : C(Smale.Hemisphere.Sphere n, { x : M // f x = a }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = a }, Smale.Hemisphere.Sphere n) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := NoExotic.sphere_sphere_nullhomotopic hn (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

def Smale.FlowConstruction.regularLevelHomeomorphOfFlow {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (hab : a ≤ b) (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) :
    { x : M // f x = a } ≃ₜ { x : M // f x = b } := by
  have hup (x : { x : M // f x = a }) : f (F (b - a) x) = b := by
    have hs : f x ∈ Set.Icc a b := by rw [x.property]; exact ⟨le_rfl, hab⟩
    have ht : f x + (b - a) ∈ Set.Icc a b := by
      rw [x.property, add_sub_cancel]
      exact ⟨hab, le_rfl⟩
    simpa only [x.property, add_sub_cancel] using hF x (b - a) hs ht
  have hdown (y : { x : M // f x = b }) : f (F (a - b) y) = a := by
    have hs : f y ∈ Set.Icc a b := by rw [y.property]; exact ⟨hab, le_rfl⟩
    have ht : f y + (a - b) ∈ Set.Icc a b := by
      rw [y.property, add_sub_cancel]
      exact ⟨le_rfl, hab⟩
    simpa only [y.property, add_sub_cancel] using hF y (a - b) hs ht
  refine
    { toFun := fun x => ⟨F (b - a) x, hup x⟩
      invFun := fun y => ⟨F (a - b) y, hdown y⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _
      continuous_invFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _ }
  · intro x
    apply Subtype.ext
    change F (a - b) (F (b - a) x) = x
    rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
  · intro y
    apply Subtype.ext
    change F (b - a) (F (a - b) y) = y
    rw [← F.map_add, show b - a + (a - b) = 0 by ring, F.map_zero_apply]

theorem Smale.FlowConstruction.nonempty_regularLevelHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    Nonempty ({ x : M // f x = a } ≃ₜ { x : M // f x = b }) := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularLevelHomeomorphOfFlow hab F hF⟩

theorem Smale.FlowConstruction.circle_nullhomotopies_regular_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = a }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = b }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  obtain ⟨e⟩ := nonempty_regularLevelHomeomorph hf hab hband
  let forward : C({ x : M // f x = a }, { x : M // f x = b }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = b }, { x : M // f x = a }) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := hnull (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val →
            Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, (S.data (S.point j)).LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          ∀ g : C(Smale.Hemisphere.Sphere 1, (S.data (S.point ⟨n, hn⟩)).UpperLevel),
            ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : Smale.SublevelDisk 6 f (S.upper (S.first hn)) := hdim ▸ d
      exact d'.circle_nullhomotopies (n := 5) (by norm_num)
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      have hprev := ih hn' (by omega)
      have hlt : (⟨n, hn'⟩ : Fin S.count) < ⟨n + 1, hn⟩ := Nat.lt_succ_self n
      have hlow :
        ∀ g : C(Smale.Hemisphere.Sphere 1, (S.data (S.point ⟨n + 1, hn⟩)).LowerLevel),
          ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
        Smale.FlowConstruction.circle_nullhomotopies_regular_level hf
          (S.ordered_windows _ _ hlt).le (S.consecutive_regular _ _ rfl) hprev
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with htwo | hthree
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 1 + 1) :=
          ⟨htwo⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 1 (by norm_num) (by omega)
            hlow
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) :=
          ⟨hthree⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 2 (by norm_num) (by omega)
            hlow
  have hprev : j.val - 1 < S.count := by omega
  have hprevj : (⟨j.val - 1, hprev⟩ : Fin S.count) < j := by
    change j.val - 1 < j.val
    omega
  exact
    Smale.FlowConstruction.circle_nullhomotopies_regular_level hf
      (S.ordered_windows _ _ hprevj).le
      (S.consecutive_regular _ _ (by change j.val - 1 + 1 = j.val; omega))
      (hupper (j.val - 1) hprev hprevj)

theorem MorseCancellation.native_index_zero_point_unique {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hn : 0 < S.count) (hcount : nativeMorseCount E f 0 = 1) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f z = 0 → z = (S.first hn).val := by
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  change
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hcount
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hfirstmem :
    (S.first hn).val ∈
      {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨(S.first hn).property, hfirst⟩
  rw [hz₀, Set.mem_singleton_iff] at hfirstmem
  intro z hz hi
  have hzmem :
    z ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨hz, hi⟩
  rw [hz₀, Set.mem_singleton_iff] at hzmem
  exact hzmem.trans hfirstmem.symm

theorem MorseCancellation.native_index_one_excluded {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hcount : nativeMorseCount E f 1 = 0) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 1 := by
  have hfinite :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.lower_circle_nullhomotopies_of_ordered_native_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hpindex : nativeMorseIndex E f p = 2) (hzero : nativeMorseCount E f 0 = 1)
    (hone : nativeMorseCount E f 1 = 0)
    (horder :
      ∀ r : Smale.ManifoldMorse.criticalPoints E f, f r < f p → nativeMorseIndex E f r ≤ 2) :
    ∀ γ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨j, rfl⟩ := S.point.surjective p
  have hn : 0 < S.count := (Nat.zero_le j.val).trans_lt j.isLt
  have hpnotfirst : S.point j ≠ S.first hn := by
    intro hpfirst
    have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
      (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
    rw [hpfirst] at hpindex
    omega
  have hj : 0 < j.val := by
    by_contra hj
    have hj0 : j.val = 0 := by omega
    have heq : S.point j = S.first hn := congrArg S.point (Fin.ext hj0)
    exact hpnotfirst heq
  have hmiddle (i : Fin S.count) (hi : 0 < i.val) (hij : i.val < j.val) :
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 := by
    have hvalues : f (S.point i) < f (S.point j) := S.point_strictMono (show i < j from hij)
    have hle := horder (S.point i) hvalues
    have hne0 : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hindex
      have heq : (S.point i).val = (S.first hn).val :=
        native_index_zero_point_unique S hf hn hzero _ (S.point i).property hindex
      have heq' : S.point i = S.point ⟨0, hn⟩ := Subtype.ext heq
      have hival := congrArg Fin.val (S.point.injective heq')
      change i.val = 0 at hival
      omega
    have hne1 := native_index_one_excluded S hone _ (S.point i).property
    have hindex : nativeMorseIndex E f (S.point i) = 2 := by omega
    exact Or.inl ((nativeMorseIndex_eq_chart (S.data (S.point i)).chart).symm.trans hindex)
  exact S.lower_circle_nullhomotopies_of_middle_indices hf hdim j hj hmiddle

def MorseCancellation.zeroChainCycle {X : Type} [TopologicalSpace X] :
    FirstHurewicz.Chains X 0 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 0
    where
  toFun
    z :=
    SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 0 z
      (by
        have h := (FirstHurewicz.singularComplex X).shape 0 0 (by simp)
        exact congrArg (fun f => f.hom z) h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def MorseCancellation.zeroChainClass {X : Type} [TopologicalSpace X] :
    FirstHurewicz.Chains X 0 →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 0 :=
  (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 0).comp
    zeroChainCycle

theorem MorseCancellation.zeroChainClass_surjective {X : Type} [TopologicalSpace X] :
    Function.Surjective (zeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 0
      a
  exact ⟨c.val, rfl⟩

theorem MorseCancellation.homologyZero_linearMap_ext {X : Type} [TopologicalSpace X] {A : Type}
    [AddCommGroup A] [Module ℤ A] {L K : SingularMayerVietoris.SingularHomology X 0 →ₗ[ℤ] A}
    (h :
      ∀ x : X,
        L (PeriodTorusHigherHomology.pointClass x) = K (PeriodTorusHigherHomology.pointClass x)) :
    L = K := by
  have heq : L.comp zeroChainClass = K.comp zeroChainClass := by
    apply FirstHurewicz.chainMap_ext X 0
    intro σ
    have hσ : σ = ContinuousMap.const (FirstHurewicz.Simplex 0) (σ (stdSimplex.vertex 0)) := by
      ext t
      exact congrArg σ (FirstHurewicz.simplexZero_eq_vertex t)
    rw [hσ]
    exact h _
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := zeroChainClass_surjective a
  exact LinearMap.congr_fun heq z

def MorseCancellation.cellDiskBoundaryHomologyMap {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.diskPatch 0 :=
  SingularMayerVietoris.singularHomologyMap
    ((ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun) 0

theorem MorseCancellation.cell_oldHomologyMap_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (a : SingularMayerVietoris.SingularHomology D.old 0) :
    D.oldHomologyMap 0 a = 0 ↔
      ∃ z : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0,
        D.attachingHomologyMap 0 z = a ∧ cellDiskBoundaryHomologyMap D z = 0 := by
  constructor
  · intro ha
    have hp :
      (D.oldHomologyEquiv 0 a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.oldHomologyEquiv 0 a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover 0] at hp
    obtain ⟨c, hc⟩ := hp
    let z := (D.overlapHomologyEquiv 0).symm c
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      dsimp [z]
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    refine ⟨z, ?_, ?_⟩
    · rw [← D.coverLeft_old, hL, LinearEquiv.symm_apply_apply]
    · have hs := congrArg Prod.snd hL
      rw [SingularMayerVietoris.leftHomologyMap_apply] at hs
      change SingularMayerVietoris.singularHomologyMap _ 0 z = 0
      rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
      exact neg_eq_zero.mp hs
  · rintro ⟨z, hza, hz⟩
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      apply Prod.ext
      · exact (D.oldHomologyEquiv 0).symm_apply_eq.mp ((D.coverLeft_old 0 z).trans hza)
      · rw [SingularMayerVietoris.leftHomologyMap_apply]
        rw [cellDiskBoundaryHomologyMap, PeriodTorusHigherHomology.singularHomologyMap_comp] at hz
        exact neg_eq_zero.mpr hz
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0)
        (D.overlapHomologyEquiv 0 z)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.overlapHomologyEquiv 0 z)) =
        0 at hzero
    rw [hL, D.coverRight_old] at hzero
    exact hzero

theorem MorseCancellation.cell_oldHomologyMap_injective_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) :
    Function.Injective (D.oldHomologyMap 0) := by
  let c : C(D.diskPatch, D.old) := ContinuousMap.const _ p
  have heq :
    D.attachingHomologyMap 0 =
      (SingularMayerVietoris.singularHomologyMap c 0).comp (cellDiskBoundaryHomologyMap D) := by
    apply homologyZero_linearMap_ext
    intro u
    change
      SingularMayerVietoris.singularHomologyMap D.attachingSphere 0
          (PeriodTorusHigherHomology.pointClass u) =
        SingularMayerVietoris.singularHomologyMap c 0
          (SingularMayerVietoris.singularHomologyMap _ 0 (PeriodTorusHigherHomology.pointClass u))
    rw [PeriodTorusHigherHomology.singularHomologyMap_pointClass,
      PeriodTorusHigherHomology.singularHomologyMap_pointClass,
      PeriodTorusHigherHomology.singularHomologyMap_pointClass]
    exact (pointClass_eq_iff_joined _ _).mpr (hcomponent u)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨z, hza, hz⟩ := (cell_oldHomologyMap_zero_iff D a).mp ha
  rw [← hza, heq, LinearMap.comp_apply, hz, map_zero]

theorem MorseCancellation.cell_old_pathConnected_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) [PathConnectedSpace X] (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) : PathConnectedSpace D.old := by
  let : Nonempty D.old := ⟨p⟩
  exact
    pathConnectedSpace_of_homologyZero_injective (SingularMayerVietoris.subtypeInclusion D.old)
      (cell_oldHomologyMap_injective_of_attaching_component D p hcomponent)

theorem MorseCancellation.native_lower_pathConnected_of_attaching_component {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (a : { z : M // f z ≤ f p - d.radius ^ 2 }) (hcomponent : ∀ u, Joined (d.coreBoundaryMap u) a)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    cell_old_pathConnected_of_attaching_component (d.coreCellPresentation hf)
      (d.cellOldHomeomorph hf a)
      (fun u => by
        rw [d.coreCell_attaching_eq]
        exact (hcomponent u).map (d.cellOldHomeomorph hf).continuous)
  exact pathConnectedSpace_of_homotopyEquiv (d.cellOldHomeomorph hf).toHomotopyEquiv

theorem MorseCancellation.native_attaching_component_of_pairwise_joined {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hjoined : ∀ u v, Joined (d.coreBoundaryMap u) (d.coreBoundaryMap v)) :
    ∃ a : { z : M // f z ≤ f p - d.radius ^ 2 }, ∀ u, Joined (d.coreBoundaryMap u) a := by
  let : Nontrivial d.chart.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : d.chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact ⟨d.coreBoundaryMap ⟨v, hv⟩, fun u => hjoined u ⟨v, hv⟩⟩

theorem MorseCancellation.native_minimum_count_one_of_one_handle_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcomponents :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f p = 1 →
          ∃ a : { z : M // f z ≤ f p - (S.data p).radius ^ 2 },
            ∀ u, Joined ((S.data p).coreBoundaryMap u) a) :
    nativeMorseCount E f 0 = 1 := by
  classical
  have hn := S.count_pos hf
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => nativeMorseIndex E f (S.point i) = 0)
  have hK : K.Nonempty := ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩⟩
  let j : Fin S.count := K.max' hK
  have hjzero : nativeMorseIndex E f (S.point j) = 0 := (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have htail (i : Fin S.count) (hji : j.val < i.val)
    (hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) }) :
    PathConnectedSpace { x : M // f x ≤ S.lower (S.point i) } := by
    let : PathConnectedSpace { x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2 } :=
      hupper
    have hne : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hi
      have hm : i.val ≤ j.val := hmax i hi
      omega
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · obtain ⟨a, ha⟩ := hcomponents (S.point i) hone
      exact
        native_lower_pathConnected_of_attaching_component (S.data (S.point i)) hf.continuous a ha
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace { x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2 } :=
    ordered_upper_pathConnected_of_later_transfers S hf j htail
  let : IsEmpty { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 } :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  have hjfirst : j.val = 0 := by
    by_contra hj
    have hlt : (⟨0, hn⟩ : Fin S.count) < j := by change 0 < j.val; omega
    have hbelow : f (S.first hn) ≤ S.lower (S.point j) :=
      (S.value_lt_upper (S.first hn)).le.trans (S.ordered_windows _ _ hlt).le
    exact
      isEmptyElim
        (⟨S.first hn, hbelow⟩ :
          { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 })
  have hset :
    {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} =
      {(S.first hn).val} := by
    ext x
    constructor
    · rintro ⟨hx, hi⟩
      obtain ⟨i, he⟩ := S.point.surjective ⟨x, hx⟩
      have hi0 : nativeMorseIndex E f (S.point i) = 0 := by simpa only [he] using hi
      have hle : i.val ≤ j.val := hmax i hi0
      have hi0' : i.val = 0 := by omega
      have hip : S.point i = S.first hn := congrArg S.point (Fin.ext hi0')
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (he.symm.trans hip))
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ ⟨(S.first hn).property, hfirst⟩
  exact Set.ncard_eq_one.mpr ⟨(S.first hn).val, hset⟩

theorem MorseCancellation.exists_native_one_handle_joining_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : nativeMorseCount E f 0 ≠ 1) :
    ∃ p : Smale.ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f p = 1 ∧
        ∃ u v, ¬Joined ((S.data p).coreBoundaryMap u) ((S.data p).coreBoundaryMap v) := by
  classical
  by_contra h
  apply hmin
  apply native_minimum_count_one_of_one_handle_components S hf
  intro p hp
  have hindex : 0 < Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rw [← nativeMorseIndex_eq_chart (S.data p).chart, hp]
    exact zero_lt_one
  apply native_attaching_component_of_pairwise_joined (S.data p) hindex
  intro u v
  by_contra huv
  exact h ⟨p, hp, u, v, huv⟩

theorem MorseCancellation.cancel_realized_higher_minimum {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f₀ : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : Smale.ManifoldMorse.IsMorse E f₀) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : Smale.ManifoldMorse.criticalPoints E f₀) (hpzero : nativeMorseIndex E f₀ p = 0)
    (hqone : nativeMorseIndex E f₀ q = 1) (hrp : f₀ r < f₀ p) (hp : f₀ p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val))
    (hnoconnection :
      ∀ j : Smale.ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 j.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f₀).ncard := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => f₀ x.val) h).symm
  obtain ⟨hzback, hunique⟩ :=
    unique_connection_of_distinct_minimum_branches S hf₀.continuous G p r q hqone hpr hp u v hback
      hu hv
  obtain ⟨f, hf, hm, hcrit, hinj, -, -, hpq, hconsecutive, hdesc, hmodels, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf₀ hm₀ S.distinct hV G hG hzero hdesc₀ hmodels₀ p r q
      hrp (hp.trans (S.lower_lt_value q)) hnoconnection
  let pf : Smale.ManifoldMorse.criticalPoints E f := ⟨p.val, by rw [hcrit]; exact p.property⟩
  let qf : Smale.ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
  have hconsecutivef : ∀ z : Smale.ManifoldMorse.criticalPoints E f, ¬(f pf < f z ∧ f z < f qf) :=
    by
    intro z hz
    exact hconsecutive ⟨z.val, by rw [← hcrit]; exact z.property⟩ hz
  obtain ⟨T⟩ := Smale.ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels pf pf.property
  obtain ⟨cq, hcq⟩ := hmodels qf qf.property
  obtain ⟨g, hg, hmg, hcard, hcritg, hexterior⟩ :=
    cancel_unique_zero_one_connection cp cq hf hm ((hindices p p.property).trans hpzero)
      ((hindices q q.property).trans hqone) hV G hG (fun x hx => hzero x (hcrit ▸ hx)) hdesc hinj
      pf.property qf.property hpq (T.lower_lt_value pf) (T.value_lt_upper qf)
      (surgery_pair_band_isolation T pf qf hconsecutivef) hu hzback hunique hcp hcq
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation T pf qf hconsecutivef)
      hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinj (fun x hx => ((hcritg x).mp hx).1) hkeep
  exact ⟨g, hg, hmg, hinjg, hcard.trans (congrArg Set.ncard hcrit)⟩

theorem MorseCancellation.exists_excellent_morse_reduction_of_multiple_minima {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f₀ : M → ℝ} (S : AdaptedWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : Smale.ManifoldMorse.IsMorse E f₀)
    (hmin : nativeMorseCount E f₀ 0 ≠ 1) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f₀).ncard := by
  obtain ⟨q, hqone, u, v, hnot⟩ :=
    exists_native_one_handle_joining_components S.toSurgeryWindows hf₀ hmin
  obtain
    ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr, hp, hr, hback, hu, hv, -,
      hnoconnection⟩ :=
    S.realize_one_handle_minimum_branches hf₀ q hqone u v hnot
  have hmodels (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f₀) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f₀ x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(S.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, S.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hne : f₀ p ≠ f₀ r := fun h => hpr (Subtype.ext (S.distinct p.property r.property h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels r p q
        hrzero hqone hlt hr v u hback hv hu (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels p r q
        hpzero hqone hgt hp u v hback hu hv hnoconnection

theorem MorseCancellation.isMorseAt_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : Smale.ManifoldMorse.IsMorseAt E f p) :
    Smale.ManifoldMorse.IsMorseAt E (fun x => -f x) p := by
  obtain ⟨e, he, hp, hregular | hH⟩ := hm
  · refine ⟨e, he, hp, Or.inl ?_⟩
    change fderiv ℝ (fun x => -f (e.symm x)) (e p) ≠ 0
    rw [fderiv_fun_neg, neg_ne_zero]
    exact hregular
  · refine ⟨e, he, hp, Or.inr ?_⟩
    have hd : fderiv ℝ ((fun x => -f x) ∘ e.symm) = fun z => -fderiv ℝ (f ∘ e.symm) z := by
      funext z
      exact fderiv_fun_neg
    rw [hd, fderiv_fun_neg]
    change Function.Bijective (fun v => -(fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p) v))
    exact neg_bijective.comp hH

theorem MorseCancellation.isMorse_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} (hm : Smale.ManifoldMorse.IsMorse E f) :
    Smale.ManifoldMorse.IsMorse E (fun x => -f x) := fun x => isMorseAt_neg (hm x)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.negative_finrank_neg_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.neg.NegativeCoordinates = Module.finrank ℝ c.PositiveCoordinates := by
  simp only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.ManifoldMorse.SignedMorseChart.PositiveCoordinates, Smale.MorseHandle.NegativeSpace,
    Smale.MorseHandle.PositiveSpace, finrank_euclideanSpace]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change -c.weights i = -1 ↔ c.weights i ≠ -1
  rcases c.signs i with h | h <;> norm_num [h]

theorem MorseCancellation.nativeMorseIndex_neg_add {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E (fun x => -f x) p + nativeMorseIndex E f p = Module.finrank ℝ E := by
  rw [nativeMorseIndex_eq_chart c.neg, nativeMorseIndex_eq_chart c, negative_finrank_neg_chart]
  exact (Nat.add_comm _ _).trans c.finrank_negative_add_positive

theorem MorseCancellation.nativeMorseCount_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) :
    nativeMorseCount E (fun x => -f x) (Module.finrank ℝ E - k) = nativeMorseCount E f k := by
  unfold nativeMorseCount
  congr 1
  ext z
  rw [Smale.ManifoldMorse.criticalPoints_neg]
  change
    (z ∈ Smale.ManifoldMorse.criticalPoints E f ∧
        nativeMorseIndex E (fun x => -f x) z = Module.finrank ℝ E - k) ↔
      (z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k)
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := Smale.ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := Smale.ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩

theorem MorseCancellation.exists_minimal_excellent_morse_system (E : Type*) (M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            ∀ g : M → ℝ,
              ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                Smale.ManifoldMorse.IsMorse E g →
                  Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                    (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                      (Smale.ManifoldMorse.criticalPoints E g).ncard := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
            (Smale.ManifoldMorse.criticalPoints E f).ncard = n
  obtain ⟨f₀, hf₀, hm₀, -, hinj₀⟩ :=
    Smale.ManifoldMorse.exists_morse_function_with_distinct_critical_values E M
  have hex : ∃ n, P n :=
    ⟨(Smale.ManifoldMorse.criticalPoints E f₀).ncard, f₀, hf₀, hm₀, hinj₀, rfl⟩
  obtain ⟨f, hf, hm, hinj, hcard⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  refine ⟨f, hf, hm, S, ?_⟩
  intro g hg hmg hinjg
  rw [hcard]
  exact Nat.find_min' hex ⟨g, hg, hmg, hinjg, rfl⟩

theorem MorseCancellation.minimal_excellent_morse_forbids_pair_removal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ}
    (hminimal :
      ∀ h : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
          Smale.ManifoldMorse.IsMorse E h →
            Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E h).ncard)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g)) :
    (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 ≠
      (Smale.ManifoldMorse.criticalPoints E f).ncard := by
  have hle := hminimal g hg hmg hinjg
  omega

theorem MorseCancellation.distinct_critical_values_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) :
    Set.InjOn (fun x => -f x) (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)) := by
  rw [Smale.ManifoldMorse.criticalPoints_neg]
  intro x hx y hy hxy
  exact hinj hx hy (neg_injective hxy)

theorem MorseCancellation.minimal_excellent_morse_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        Smale.ManifoldMorse.IsMorse E g →
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
            (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)).ncard ≤
              (Smale.ManifoldMorse.criticalPoints E g).ncard := by
  intro g hg hmg hinjg
  have hh :=
    hminimal (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
  simpa only [Smale.ManifoldMorse.criticalPoints_neg] using hh

theorem Smale.FiniteSignedCancellation.opposite_signs_distinct {a b : SignType} (h : a * b = -1) :
    a ≠ b := by cases a <;> cases b <;> simp_all

theorem Smale.FiniteSignedCancellation.cast_add_eq_zero_of_opposite {a b : SignType}
    (h : a * b = -1) : (a : ℤ) + (b : ℤ) = 0 := by cases a <;> cases b <;> simp_all

theorem Smale.FiniteSignedCancellation.sum_sdiff_pair {X : Type*} [DecidableEq X] (s : Finset X)
    (σ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1) :
    ∑ z ∈ s \ { x, y }, (σ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  classical
  have hne : x ≠ y := fun h => opposite_signs_distinct hxy (congrArg σ h)
  have hsub : ({ x, y } : Finset X) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  have hsum : ∑ z ∈ ({ x, y } : Finset X), (σ z : ℤ) = 0 := by
    rw [Finset.sum_pair hne]
    exact cast_add_eq_zero_of_opposite hxy
  have h := Finset.sum_sdiff (f := fun z => (σ z : ℤ)) hsub
  simpa only [hsum, add_zero] using h

theorem Smale.FiniteSignedCancellation.sum_sdiff_pair_of_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (σ τ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1)
    (heq : ∀ z ∈ s \ { x, y }, τ z = σ z) : ∑ z ∈ s \ { x, y }, (τ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  calc
    _ = ∑ z ∈ s \ { x, y }, (σ z : ℤ) :=
      Finset.sum_congr rfl (fun z hz => congrArg (fun a : SignType => (a : ℤ)) (heq z hz))
    _ = _ := sum_sdiff_pair s σ hx hy hxy

theorem Smale.FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite {X : Type*}
    (s : Finset X) (σ : X → SignType) (hunit : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hno : ∀ x ∈ s, ∀ y ∈ s, σ x * σ y ≠ -1) : s.card = (∑ x ∈ s, (σ x : ℤ)).natAbs := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have heq (y : X) (hy : y ∈ s) : σ y = σ x := by
    rcases hunit x hx with hxp | hxn <;> rcases hunit y hy with hyp | hyn
    · exact hyp.trans hxp.symm
    · exact (hno x hx y hy (by rw [hxp, hyn]; simp)).elim
    · exact (hno x hx y hy (by rw [hxn, hyp]; simp)).elim
    · exact hyn.trans hxn.symm
  have hsum : (∑ y ∈ s, (σ y : ℤ)) = ∑ _ ∈ s, (σ x : ℤ) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [heq y hy]
  rw [hsum]
  rcases hunit x hx with hp | hn
  · simp [hp]
  · simp [hn]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (P : Finset (Smale.Hemisphere.Sphere 2)) (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Smale.Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) (x y : Smale.Hemisphere.Sphere 2)
    (hx : x ∈ P) (hy : y ∈ P)
    (hxy : D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ z, g' z = e (g z)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              ((P \ { x, y } : Finset (Smale.Hemisphere.Sphere 2)) :
                    Set (Smale.Hemisphere.Sphere 2)) =
                  D.beltIntersectionPoints 2 g' ∧
                (∀ z ∈ P \ { x, y }, (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 z] g) ∧
                  (∑ z ∈ P \ { x, y }, (D.beltIntersectionSign 2 r g' z : ℤ)) =
                    ∑ z ∈ P, (D.beltIntersectionSign 2 r g z : ℤ) := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  have hxB : x ∈ D.beltIntersectionPoints 2 g := hP ▸ hx
  have hyB : y ∈ D.beltIntersectionPoints 2 g := hP ▸ hy
  obtain ⟨e, g', hiso, heq, hg', hinj', hi', ht', hpoints, hgerm, hsign⟩ :=
    D.exists_signed_belt_cancellation_step hf hdim hindex hnull r g hg hinj hi ht x y hxB hyB hxy
  have hP' :
    ((P \ { x, y } : Finset (Smale.Hemisphere.Sphere 2)) : Set (Smale.Hemisphere.Sphere 2)) =
      D.beltIntersectionPoints 2 g' := by
    rw [hpoints, ← hP]
    simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
  have hmem (z : Smale.Hemisphere.Sphere 2) (hz : z ∈ P \ { x, y }) :
    z ∈ D.beltIntersectionPoints 2 g' := hP' ▸ hz
  refine ⟨e, g', hiso, heq, ⟨hg', hinj', hi', ht'⟩, hP', ?_, ?_⟩
  · exact fun z hz => hgerm z (hmem z hz)
  · exact
      Smale.FiniteSignedCancellation.sum_sdiff_pair_of_eq P (D.beltIntersectionSign 2 r g)
        (D.beltIntersectionSign 2 r g') (x := x) (y := y) hx hy hxy
        (fun z hz => hsign z (hmem z hz))

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (P : Finset (Smale.Hemisphere.Sphere 2)) (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Smale.Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        ∃ P' : Finset (Smale.Hemisphere.Sphere 2),
          Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g' x = e (g x)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                (P' : Set (Smale.Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g' ∧
                  P' ⊆ P ∧
                    (∀ x ∈ P', (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                      (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)) =
                          ∑ x ∈ P, (D.beltIntersectionSign 2 r g x : ℤ) ∧
                        ∀ x ∈ P',
                          ∀ y ∈ P',
                            D.beltIntersectionSign 2 r g' x * D.beltIntersectionSign 2 r g' y ≠
                              -1 := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  induction P using Finset.strongInductionOn generalizing g with
  | _ P
    ih =>
    by_cases hpair :
      ∃ x ∈ P, ∃ y ∈ P, D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
      obtain ⟨e₁, g₁, hiso₁, heq₁, hgood₁, hR, hgerm₁, hsum₁⟩ :=
        D.exists_finite_belt_cancellation_step hf hdim hindex hnull r P g hP hgood x y hx hy hxy
      let R : Finset (Smale.Hemisphere.Sphere 2) := P \ { x, y }
      have hsubpair : ({ x, y } : Finset (Smale.Hemisphere.Sphere 2)) ⊆ P := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_singleton.mp hz ▸ hy
      have hRlt : R ⊂ P := Finset.sdiff_ssubset hsubpair ⟨x, by simp⟩
      obtain ⟨e₂, g₂, P₂, hiso₂, heq₂, hgood₂, hP₂, hsub₂, hgerm₂, hsum₂, hno₂⟩ :=
        ih R hRlt g₁ hR hgood₁
      refine
        ⟨e₁.trans e₂, g₂, P₂, hiso₁.trans hiso₂, ?_, hgood₂, hP₂, hsub₂.trans Finset.sdiff_subset,
          ?_, hsum₂.trans hsum₁, hno₂⟩
      · intro z
        change g₂ z = e₂ (e₁ (g z))
        rw [heq₂, heq₁]
      · intro z hz
        exact (hgerm₂ z hz).trans (hgerm₁ z (hsub₂ hz))
    · refine
        ⟨Diffeomorph.refl _ _ _, g, P, Smale.SupportedDiffeomorph.isotopicToIdentity_refl,
          fun _ => rfl, hgood, hP, fun _ hx => hx, fun _ _ => Filter.EventuallyEq.refl _ _, rfl,
          ?_⟩
      intro x hx y hy hxy
      exact hpair ⟨x, hx, y, hy, hxy⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ x, g' x = e (g x)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              D.beltIntersectionPoints 2 g' ⊆ D.beltIntersectionPoints 2 g ∧
                (∀ x ∈ D.beltIntersectionPoints 2 g',
                    (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                  (∀ hfin' : (D.beltIntersectionPoints 2 g').Finite,
                      D.beltIntersectionCount 2 r g' hfin' =
                        D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)) ∧
                    (D.beltIntersectionPoints 2 g').ncard =
                      (D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex
                            hgood)).natAbs := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let hfin := D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood
  obtain ⟨e, g', P', hiso, heq, hgood', hP', hsub, hgerm, hsum, hno⟩ :=
    D.exists_finite_belt_reduction hf hdim hindex hnull r hfin.toFinset g hfin.coe_toFinset hgood
  have hunit :
    ∀ x ∈ P', D.beltIntersectionSign 2 r g' x = 1 ∨ D.beltIntersectionSign 2 r g' x = -1 := by
    obtain ⟨hg', _, _, ht'⟩ := hgood'
    intro x hx
    exact D.beltIntersectionSign_unit hf 3 2 hindex r g' hg' ht' x (hP' ▸ hx)
  have hmem (x : Smale.Hemisphere.Sphere 2) (hx : x ∈ D.beltIntersectionPoints 2 g') : x ∈ P' := by
    change x ∈ (P' : Set (Smale.Hemisphere.Sphere 2))
    rw [hP']
    exact hx
  refine ⟨e, g', hiso, heq, hgood', ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ P' := hmem x hx
    exact hfin.mem_toFinset.mp (hsub hxP)
  · intro x hx
    exact hgerm x (hmem x hx)
  · intro hfin'
    have hPfin : hfin'.toFinset = P' := by
      apply Finset.coe_injective
      exact hfin'.coe_toFinset.trans hP'.symm
    change (∑ x ∈ hfin'.toFinset, (D.beltIntersectionSign 2 r g' x : ℤ)) = _
    rw [hPfin]
    exact hsum
  · calc
      (D.beltIntersectionPoints 2 g').ncard = P'.card := by rw [← hP', Set.ncard_coe_finset]
      _ = (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)).natAbs :=
        (Smale.FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite P'
          (D.beltIntersectionSign 2 r g') hunit hno)
      _ = _ := congrArg Int.natAbs hsum

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (hcount :
      (D.beltIntersectionCount 2 r g
            (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs =
        1) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        ∃ x : Smale.Hemisphere.Sphere 2,
          Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ y, g' y = e (g y)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                D.beltIntersectionPoints 2 g' = { x } ∧
                  Set.range g' ∩ Set.range D.surgery.beltSphere = {g' x} := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    D.exists_minimal_signed_belt_sphere hf hdim hindex hnull r g hgood
  have hone : (D.beltIntersectionPoints 2 g').ncard = 1 := hsize.trans hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage :
    g' '' D.beltIntersectionPoints 2 g' = Set.range g' ∩ Set.range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' Set.range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  rw [← himage, hx, Set.image_singleton]

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.remove_connections_of_index_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (n m : ℕ) (hqindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)
    (hppos : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1)
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1) := ⟨hqindex⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1) := ⟨hppos⟩
  obtain ⟨D, b, -, hb, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  have horbit' (x : (S.data p).UpperLevel) : ∃ t, S.flow t x = (b x : M) := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, ht.trans (hb x).symm⟩
  let α := (S.data p).transportedAttachingSphere (S.data q) n b.toHomeomorph
  have hα : ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf n b
  have hB := (S.data p).belt_smooth hf m
  have hdim :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) <
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace, Fintype.card_fin]
    have hh := (S.data p).chart.finrank_negative_add_positive
    omega
  obtain ⟨e, he, hdisjoint⟩ :=
    Degree.MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension hα hB hdim
  have hbasins :
    ∀ x : (S.data p).UpperLevel,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t (e x)) Filter.atTop (𝓝 p.val)) := by
    rintro x ⟨hxq, hxp⟩
    obtain ⟨v, hv⟩ := (S.transported_attaching_basin_iff hf p q n b.toHomeomorph horbit' x).mp hxq
    have hB := (S.belt_basin_iff hf p (e x)).mp hxp
    have hαx : e x ∈ Set.range (e ∘ α) := ⟨v, congrArg e hv⟩
    exact Set.disjoint_left.mp hdisjoint hαx hB
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  let z : (S.data p).UpperLevel := α (Classical.arbitrary (Smale.Hemisphere.Sphere n))
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hac hcb
      (MorseCancellation.surgery_pair_inner_band_regular p q hconsecutive hpa hbq)
      (S.data p).upper_regular z e he
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val e
      (fun x => (hgeometry x).2.1) (fun x => (hgeometry x).2.2) hend hleft hright
  refine ⟨V, G, hV, hG, fun x hx => (hzeros x).mpr (S.zero x hx), hneg, hgerms, ?_⟩
  exact
    Degree.FlowSuspension.no_connection_of_level_basin_disjointness S.flow G hf.continuous hqc hpc
      e (fun x => hback x q.val) (fun x => hforward x p.val) hbasins

theorem MorseCancellation.unitSphere_isEmpty_of_finrank_zero {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] (hA : Module.finrank ℝ A = 0) :
    IsEmpty (Smale.PuncturedHandle.UnitSphere A) := by
  let _ : Subsingleton A := (Module.finrank_eq_zero_iff_of_free ℝ A).mp hA
  refine ⟨fun v => ?_⟩
  have hh := mem_sphere_zero_iff_norm.mp v.property
  rw [Subsingleton.elim (v : A) 0, norm_zero] at hh
  norm_num at hh

theorem AdaptedWindows.no_connection_of_upper_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ := MorseCancellation.unitSphere_isEmpty_of_finrank_zero hqzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hxq hxp
      (S.toSurgeryWindows.lower_lt_value q)
      ((S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq))
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hlim : Filter.Tendsto (fun s => S.flow s (y : M)) Filter.atBot (𝓝 q.val) :=
    (MorseCancellation.flow_time_atBot_limit_iff S.flow t x q.val).mpr hxq
  obtain ⟨v, -⟩ := (S.attaching_basin_iff hf q y).mp hlim
  exact isEmptyElim v

theorem AdaptedWindows.no_connection_of_lower_positive_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ := MorseCancellation.unitSphere_isEmpty_of_finrank_zero hpzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hxq hxp
      ((S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q))
      (S.toSurgeryWindows.value_lt_upper p)
  let y : (S.data p).UpperLevel := ⟨S.flow t x, ht⟩
  have hlim : Filter.Tendsto (fun s => S.flow s (y : M)) Filter.atTop (𝓝 p.val) :=
    (MorseCancellation.flow_time_atTop_limit_iff S.flow t x p.val).mpr hxp
  obtain ⟨v, -⟩ := (S.belt_basin_iff hf p y).mp hlim
  exact isEmptyElim v

theorem AdaptedWindows.remove_connections_of_nonincreasing_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  by_cases hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_upper_index_zero hf p q hpq hqzero⟩
  by_cases hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_lower_positive_zero hf p q hpq hpzero⟩
  exact
    S.remove_connections_of_index_le hf p q hpq hconsecutive
      (Module.finrank ℝ (S.data q).chart.NegativeCoordinates - 1)
      (Module.finrank ℝ (S.data p).chart.PositiveCoordinates - 1) (by omega) (by omega) hle

theorem AdaptedWindows.exchange_nonincreasing_native_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle : MorseCancellation.nativeMorseIndex E f q ≤ MorseCancellation.nativeMorseIndex E f p) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            g p = f q ∧
              g q = f p ∧
                (∀ z,
                    f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                      g =ᶠ[𝓝 z] f) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                    Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
                      Nonempty (AdaptedWindows E g) ∧
                        (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                            MorseCancellation.nativeMorseIndex E g z =
                              MorseCancellation.nativeMorseIndex E f z) ∧
                          ∀ k,
                            MorseCancellation.nativeMorseCount E g k =
                              MorseCancellation.nativeMorseCount E f k := by
  have hle' :
    Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rwa [MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart,
      MorseCancellation.nativeMorseIndex_eq_chart (S.data p).chart] at hle
  obtain ⟨V, G, hV, hG, hzeros, hneg, hgerms, hnoconnection⟩ :=
    S.remove_connections_of_nonincreasing_indices hf p q hpq hconsecutive hle'
  have hpgerm : ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p p.property, S.critical_model_germ p] with y hy hmodel
    exact hy.trans hmodel
  have hqgerm : ∀ᶠ y in 𝓝 q.val, V y = (S.data q).chart.descentField y := by
    filter_upwards [hgerms q q.property, S.critical_model_germ q] with y hy hmodel
    exact hy.trans hmodel
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, -, hexterior, -, -, hothers, hindices⟩ :=
    Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV G hG hzeros
      hneg S.distinct (S.data p).chart (S.data q).chart hpgerm hqgerm hpband hqband hpq hqband
      hpband (MorseCancellation.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive)
      hnoconnection
  obtain ⟨hinj, hnew⟩ :=
    MorseCancellation.adapted_surgery_system_after_value_exchange S hg hmg p.property q.property hcrit
      hgp hgq hothers
  exact
    ⟨g, hg, hmg, hcrit, hgp, hgq, hexterior, hothers, hinj, hnew, hindices,
      MorseCancellation.nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

attribute [local instance 100] Classical.propDecidable in
def MorseCancellation.nativeIndexDisorder (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : ℕ :=
  if hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite then
    let _ := hfinite.fintype
    Degree.MorseRearrangement.finiteIndexDisorder
      (fun x : Smale.ManifoldMorse.criticalPoints E f => f x)
      (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x)
  else 0

theorem MorseCancellation.nativeIndexDisorder_eq_of_finite {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite) :
    letI := hfinite.fintype
    nativeIndexDisorder E f =
      Degree.MorseRearrangement.finiteIndexDisorder
        (fun x : Smale.ManifoldMorse.criticalPoints E f => f x)
        (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical simp only [nativeIndexDisorder, dif_pos hfinite]

theorem MorseCancellation.nativeIndexDisorder_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    letI := hfinite.fintype
    nativeIndexDisorder E g =
      Degree.MorseRearrangement.finiteIndexDisorder
        (fun x : Smale.ManifoldMorse.criticalPoints E f => g x)
        (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical
  let _ := hfinite.fintype
  have hgfinite : (Smale.ManifoldMorse.criticalPoints E g).Finite := hcrit.symm ▸ hfinite
  let _ := hgfinite.fintype
  let e : Smale.ManifoldMorse.criticalPoints E f ≃ Smale.ManifoldMorse.criticalPoints E g :=
    Equiv.setCongr hcrit.symm
  rw [nativeIndexDisorder_eq_of_finite hgfinite]
  rw [←
    Degree.MorseRearrangement.finiteIndexDisorder_comp_equiv
      (fun x : Smale.ManifoldMorse.criticalPoints E g => g x)
      (fun x : Smale.ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) e]
  have hw :
    ((fun x : Smale.ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) ∘ e) =
      fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x := by
    funext x
    exact hindex x x.property
  rw [hw]
  rfl

theorem MorseCancellation.nativeIndexDisorder_exchange_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hindexlt : nativeMorseIndex E f q < nativeMorseIndex E f p)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f)
    (hindex :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    nativeIndexDisorder E g < nativeIndexDisorder E f := by
  classical
  let _ : DecidableEq (Smale.ManifoldMorse.criticalPoints E f) := fun a b =>
    Classical.propDecidable (a = b)
  let _ := hfinite.fintype
  have hform :
    (fun x : Smale.ManifoldMorse.criticalPoints E f => g x) =
      (fun x : Smale.ManifoldMorse.criticalPoints E f => f x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_right] using hgq
    have hh :=
      (hothers x x.property (fun h => hxp (Subtype.ext h))
          (fun h => hxq (Subtype.ext h))).self_of_nhds
    simpa only [Function.comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hh
  rw [nativeIndexDisorder_transport hfinite hcrit hindex,
    nativeIndexDisorder_eq_of_finite hfinite, hform]
  have hi : Function.Injective (fun x : Smale.ManifoldMorse.criticalPoints E f => f x) :=
    fun x y h => Subtype.ext (hinj x.property y.property h)
  exact
    Degree.MorseRearrangement.finiteIndexDisorder_swap_lt (h :=
      fun x : Smale.ManifoldMorse.criticalPoints E f => f x) hi
      (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) (p := p) (q := q)
      hpq hconsecutive hindexlt

theorem MorseCancellation.exists_index_ordered_morse_system_preserving_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f₀ : M → ℝ} (S₀ : AdaptedWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : Smale.ManifoldMorse.IsMorse E f₀) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              ∃ _ : AdaptedWindows E f,
                (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                    f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
                  ∀ k, nativeMorseCount E f k = nativeMorseCount E f₀ k := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧ nativeIndexDisorder E f = n
  have hex : ∃ n, P n :=
    ⟨nativeIndexDisorder E f₀, f₀, hf₀, hm₀, rfl, fun _ _ => rfl, S₀.distinct, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hindices, hinj, hdisorder⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  have horder :
    ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
      f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q := by
    by_contra hnot
    let _ := S.finite.fintype
    obtain ⟨p, q, hpq, hconsecutive, hinversion⟩ :=
      Degree.MorseRearrangement.exists_adjacent_index_inversion (h :=
        fun x : Smale.ManifoldMorse.criticalPoints E f => f x)
        (fun x y h => Subtype.ext (hinj x.property y.property h))
        (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) hnot
    obtain ⟨g, hg, hmg, hcritg, hgp, hgq, -, hothers, hinjg, -, hindicesg, -⟩ :=
      S.exchange_nonincreasing_native_indices hf hm p q hpq hconsecutive hinversion.le
    have hdecrease : nativeIndexDisorder E g < nativeIndexDisorder E f :=
      nativeIndexDisorder_exchange_lt S.finite hinj p q hpq hconsecutive hinversion hcritg hgp hgq
        hothers hindicesg
    have hindicesg₀ (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hminimal := Nat.find_min' hex ⟨g, hg, hmg, hcritg.trans hcrit, hindicesg₀, hinjg, rfl⟩
    rw [← hdisorder] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact
    ⟨f, hf, hm, hcrit, hindices, S, horder,
      nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

theorem MorseCancellation.minimal_excellent_morse_minimum_count_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 := by
  by_contra hmin
  obtain ⟨g, hg, hmg, hinjg, hcount⟩ :=
    exists_excellent_morse_reduction_of_multiple_minima S hf hm hmin
  exact minimal_excellent_morse_forbids_pair_removal hminimal hg hmg hinjg hcount

theorem MorseCancellation.minimal_excellent_morse_extreme_counts_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 := by
  refine ⟨minimal_excellent_morse_minimum_count_one S hf hm hminimal, ?_⟩
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have hmin :=
    minimal_excellent_morse_minimum_count_one T hf.neg (isMorse_neg hm)
      (minimal_excellent_morse_neg hminimal)
  have hcounts := nativeMorseCount_neg hf hm (le_refl (Module.finrank ℝ E))
  rw [Nat.sub_self] at hcounts
  exact hcounts.symm.trans hmin

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_transverse_middle_belt_loop {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancellation.nativeMorseIndex E f p = 0)
    (hq : MorseCancellation.nativeMorseIndex E f q = 1)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hqa : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ 2) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ δ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }),
      ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ ∧
        Function.Injective δ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) ∧
            ∃ (z₀ : Smale.Hemisphere.Sphere 1) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (β :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1 → { y : M // f y = a }),
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v ∧
                β v = δ z₀ ∧
                  Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) δ β
                      z₀ v ∧
                    (∀ᶠ w in 𝓝 v,
                        Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val)) ∧
                      (∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) ↔
                            z = z₀) ∧
                        ∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) :=
  by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.isManifold hf ha
  obtain ⟨v, γ, hγ, hγi, hγd, hreach, z₀, hsingle, htrans, hendpoints⟩ :=
    S.exists_transverse_belt_circle_reaching_level_with_endpoints hf p q hp hq 4 u hbranches hqa
      ha hlow (by omega) (by omega) (by omega)
  obtain ⟨t₀, ht₀⟩ := hreach z₀
  let za : { y : M // f y = a } := ⟨S.flow t₀ (γ z₀).val, ht₀⟩
  obtain ⟨D, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data q).upper_regular ha (γ z₀) za
  have hγsource (z : Circle) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hΓsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
        hγ.contMDiffAt
  let Γ : C(Circle, { y : M // f y = a }) := ⟨D ∘ γ, hΓsmooth.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro z w hzw
    exact hγi (D.toPartialEquiv.injOn (hγsource z) (hγsource w) hzw)
  have hΓd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hγsource z))
        (hγ.mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv D (hγsource z)).1.comp (hγd z)
  have hcross : (S.data q).surgery.beltSphere v = γ z₀ := ((hsingle z₀ v).mpr ⟨rfl, rfl⟩).symm
  have hvsource : (S.data q).surgery.beltSphere v ∈ D.source := hcross.symm ▸ hγsource z₀
  let β := D ∘ (S.data q).surgery.beltSphere
  have hβ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v :=
    (D.mdifferentiableAt (by simp) hvsource).comp v
      (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp))
  have hβcross : β v = Γ z₀ := congrArg D hcross
  have hΓtrans :
    Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ β z₀ v :=
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff D
          (hγ.mdifferentiableAt (by simp))
          (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp)) hcross (hγsource z₀)).mp
      (fun _ => htrans)
  have hβbasin :
    ∀ᶠ w in 𝓝 v, Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val) := by
    have hnear :=
      (((S.data q).belt_smooth hf 4).continuous.tendsto v) (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((S.data q).surgery.beltSphere w) hw
    change S.flow t ((S.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact
      (MorseCancellation.flow_time_atTop_limit_iff S.flow t _ q.val).mpr
        ((S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hforward (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) ↔ z = z₀ := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    have hbasin :
      Filter.Tendsto (fun s => S.flow s (Γ z).val) Filter.atTop (𝓝 q.val) ↔
        γ z ∈ Set.range (S.data q).surgery.beltSphere := by
      rw [← ht]
      exact
        (MorseCancellation.flow_time_atTop_limit_iff S.flow t (γ z).val q.val).trans
          (S.belt_basin_iff hf q (γ z))
    rw [hbasin]
    constructor
    · rintro ⟨w, hw⟩
      exact ((hsingle z w).mp hw.symm).1
    · intro hz
      exact ⟨v, ((hsingle z v).mpr ⟨hz, rfl⟩).symm⟩
  have hΓends (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    rw [← ht]
    exact
      (hendpoints z).imp ((MorseCancellation.flow_time_atTop_limit_iff S.flow t _ p.val).mpr)
        ((MorseCancellation.flow_time_atTop_limit_iff S.flow t _ q.val).mpr)
  let δ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨Γ ∘ MorseCancellation.standardCircleParametrization,
      Γ.continuous.comp MorseCancellation.standardCircleParametrization.continuous⟩
  let z := MorseCancellation.standardCircleParametrization.symm z₀
  have hz : MorseCancellation.standardCircleParametrization z = z₀ :=
    MorseCancellation.standardCircleParametrization.apply_symm_apply z₀
  have hδcross : β v = δ z := by
    change β v = Γ (MorseCancellation.standardCircleParametrization z)
    rw [hz]
    exact hβcross
  have hδtrans :
    Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) δ β z v := by
    intro _
    let B : EuclideanSpace ℝ (Fin 4) →L[ℝ] Smale.RegularLevel.Model E :=
      mfderiv (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v
    apply MorseCancellation.transverse_comp_standardCircle hΓsmooth B z
    rw [hz]
    exact hΓtrans hβcross
  refine
    ⟨δ, MorseCancellation.contMDiff_comp_standardCircle hΓsmooth,
      MorseCancellation.injective_comp_standardCircle hΓi,
      MorseCancellation.injective_derivative_comp_standardCircle hΓsmooth hΓd, z, v, β, hβ, hδcross,
      hδtrans, hβbasin, ?_, fun w => hΓends (MorseCancellation.standardCircleParametrization w)⟩
  intro w
  change
    Filter.Tendsto (fun t => S.flow t (Γ (MorseCancellation.standardCircleParametrization w)).val)
        Filter.atTop (𝓝 q.val) ↔
      _
  rw [hforward]
  exact
    ⟨fun hw => MorseCancellation.standardCircleParametrization.injective (hw.trans hz.symm), fun hw =>
      hw ▸ hz⟩

theorem MorseCancellation.exists_transverse_sheet_of_circle_placement {A B E HA HB H X Y N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace HA] {I : ModelWithCorners ℝ A HA}
    [TopologicalSpace X] [ChartedSpace HA X] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HB] {I' : ModelWithCorners ℝ B HB} [TopologicalSpace Y] [ChartedSpace HB Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] (P : Diffeomorph J J N N ∞) {γ δ : X → N} {β : Y → N}
    {x : X} {y : Y} (hγ : MDifferentiableAt I J γ x) (hβ : MDifferentiableAt I' J β y)
    (hplace : ∀ z, P (γ z) = δ z) (hcross : β y = δ x)
    (htrans : Smale.NativeTransversality.At I I' J δ β x y) :
    ∃ β' : Y → N,
      MDifferentiableAt I' J β' y ∧
        β' y = γ x ∧ Smale.NativeTransversality.At I I' J γ β' x y ∧ ∀ z, P (β' z) = β z := by
  let β' := P.symm ∘ β
  have hβ' : MDifferentiableAt I' J β' y :=
    (P.symm.contMDiff.mdifferentiableAt (by simp)).comp y hβ
  have hcross' : β' y = γ x := by
    apply P.injective
    change P (P.symm (β y)) = P (γ x)
    rw [P.apply_symm_apply, hcross, hplace]
  have hforward (z : Y) : P (β' z) = β z := P.apply_symm_apply (β z)
  refine ⟨β', hβ', hcross', ?_, hforward⟩
  apply
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff P.toPartialDiffeomorph
        hγ hβ' hcross' (Set.mem_univ _)).mpr
  have hγeq : P.toPartialDiffeomorph ∘ γ = δ := funext hplace
  have hβeq : P.toPartialDiffeomorph ∘ β' = β := funext hforward
  rw [hγeq, hβeq]
  exact htrans

theorem Degree.DiskShrinking.exists_embedded_disk_isotopy_of_path {D E M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (γ : Path (f 0) (g 0)) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨P, hP, hP0, -⟩ :=
    MorseCancellation.exists_isotopic_pointMoving_of_path (J := 𝓘(ℝ, E)) isOpen_univ γ
      (fun _ => Set.mem_univ _)
  have hPf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (P ∘ f) := P.contMDiff.comp hf
  have hPfi : Set.InjOn (P ∘ f) (Metric.closedBall (0 : D) 1) := by
    intro x hx y hy hh
    exact hfi hx hy (P.injective hh)
  have hPfd :
    ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (P ∘ f) x) := by
    intro x hx
    rw [mfderiv_comp x (P.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
    have hi : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) P (f x) : E →L[ℝ] E) :=
      Smale.PartialChart.bijective_mfderiv P.toPartialDiffeomorph (Set.mem_univ _)
    exact hi.1.comp (hfd x hx)
  obtain ⟨Q, hQ, hformula⟩ :=
    exists_embedded_disk_isotopy_of_same_center hPf hg hPfi hgi hPfd hgd n hn hdim hE hP0
  exact ⟨P.trans Q, hP.trans hQ, hformula⟩

theorem Degree.DiskShrinking.exists_embedded_disk_isotopy {D E M : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x :=
  exists_embedded_disk_isotopy_of_path hf hg hfi hgi hfd hgd n hn hdim hE
    (Joined.somePath (PathConnectedSpace.joined (f 0) (g 0)))

theorem MorseCancellation.exists_embedded_avoidance_into_level_basin {E M A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (f₀ : C(A, M)) (hf₀ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f₀)
    (hself : 2 * Module.finrank ℝ A < Module.finrank ℝ E)
    (hobstacle : Module.finrank ℝ A + d < Module.finrank ℝ E) {K L C : Set A} (hK : IsCompact K)
    (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f₀ K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f₀ x))
    (hfixed : ∀ x ∈ L ∩ C, f₀ x ∈ Degree.FlowCancellation.levelBasin S.flow f a) :
    ∃ g : C(A, M),
      ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ g ∧
        f₀.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) g x)) ∧
              (∀ x y, g x = g y → f₀ x = f₀ y) ∧
                ∀ x,
                  (f₀ x ∈ Degree.FlowCancellation.levelBasin S.flow f a ∨ x ∈ L) →
                    g x ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndex_countable S a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨b, hb, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun p : J × V => b p.1 p.2) :=
    contMDiff_discrete_family b hb
  let B : C(J × V, M) := ⟨fun p => b p.1 p.2, hs.continuous⟩
  have hrange : Set.range B = (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact range_discrete_family b
  have hclosed : IsClosed (Set.range B) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact isClosed_endpoint_obstruction S hf a
  have hdim : Module.finrank ℝ A + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hobstacle
  have hfixed' : ∀ x ∈ L ∩ C, f₀ x ∉ Set.range B := by
    intro x hx
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact hfixed x hx
  obtain ⟨g, hg, hhom, hemb, hder, hnoNew, havoid⟩ :=
    Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range f₀ B hf₀ hs
      hclosed hself hdim hK hL hC hinj hderiv hfixed'
  refine ⟨g, hg, hhom, hemb, hder, hnoNew, ?_⟩
  intro x hx
  have hx' : f₀ x ∉ Set.range B ∨ x ∈ L := by
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hx
  simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using havoid x hx'

theorem Smale.SphereBoundary.exists_extension_immersive_on_sphere {E G H N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x))
    (hdim : n + Module.finrank ℝ E < Module.finrank ℝ G) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ x : Metric.sphere (0 : E) 1, g x.1 = γ x) ∧
          ∀ x : Metric.sphere (0 : E) 1, Function.Injective (mfderiv 𝓘(ℝ, E) J g x.1) := by
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : Metric.sphere (0 : E) 1 → E) :=
    contMDiff_coe_sphere
  have hzero (x : Metric.sphere (0 : E) 1) : definingFunction x.1 = 0 :=
    (definingFunction_eq_zero_iff x.1).mpr x.property
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨g, hg, hhom, hderiv⟩ :=
    Smale.ManifoldImmersion.exists_compact_boundary_derivative_repair
      (⟨f, hf.continuous⟩ : C(E, N)) hf hb contDiff_definingFunction hzero hd
      (common_kernel_of_immersive_sphere_extension hf hext hγ)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    exact (hhom.fst_eq_snd (hzero x)).symm.trans (hext x)
  · intro x
    exact hderiv x.1 ⟨x, rfl⟩

theorem Smale.exists_embedded_disk_extension_of_smooth_extension {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : Hemisphere.Ambient 2 → N}
    (hf : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ f) {γ : Hemisphere.Sphere 1 → N}
    (hext : ∀ x : Hemisphere.Sphere 1, f x.1 = γ x) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) J γ x)) (hdim : 5 ≤ Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J g x.1) := by
  let : Fact (Module.finrank ℝ (Hemisphere.Ambient 2) = 1 + 1) :=
    ⟨by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]⟩
  have hd : 1 + Module.finrank ℝ (Hemisphere.Ambient 2) < Module.finrank ℝ G := by
    simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]
    omega
  obtain ⟨f₁, hf₁, hboundary₁, hderiv₁⟩ :=
    SphereBoundary.exists_extension_immersive_on_sphere (n := 1) hf hext hγderiv hd
  let K : Set (Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 1
  have hC : IsClosed C := Metric.isClosed_sphere
  have hfixed : Set.InjOn f₁ (K ∩ C) := by
    intro x hx y hy hxy
    let xs : Hemisphere.Sphere 1 := ⟨x, hx.2⟩
    let ys : Hemisphere.Sphere 1 := ⟨y, hy.2⟩
    have hboundaryeq : γ xs = γ ys := (hboundary₁ xs).symm.trans (hxy.trans (hboundary₁ ys))
    exact congrArg Subtype.val (hγinj hboundaryeq)
  have hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J f₁ x) :=
    fun x hx => hderiv₁ ⟨x, hx.2⟩
  obtain ⟨g, hg, hhom, hemb, hderivg⟩ :=
    ManifoldImmersion.exists_relative_compact_embedding_twoDimensional f₁ hf₁
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]) hdim hK hC hfixed hderiv
  refine ⟨g, hg, ?_, hemb, fun x => hderivg x.1 x.property⟩
  intro x
  exact (hhom.fst_eq_snd x.property).symm.trans (hboundary₁ x)

def Smale.RadialFilling.direction {n : ℕ} (b : Smale.Hemisphere.Sphere n)
    (v : Smale.Hemisphere.Ambient (n + 1)) : Smale.Hemisphere.Sphere n := by
  classical
    exact
    if hv : v = 0 then b
    else
      ⟨NormedSpace.normalize v, by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩

theorem Smale.RadialFilling.direction_coe {n : ℕ} (b : Smale.Hemisphere.Sphere n)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    (direction b v : Smale.Hemisphere.Ambient (n + 1)) = NormedSpace.normalize v := by
  classical simp only [direction, dif_neg hv]

theorem Smale.RadialFilling.direction_of_mem_sphere {n : ℕ} (b v : Smale.Hemisphere.Sphere n) :
    direction b v.1 = v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hv : v.1 ≠ 0 := by intro h; simp [h] at hn
  apply Subtype.ext
  rw [direction_coe b hv, NormedSpace.normalize_eq_self_of_norm_eq_one hn]

theorem Smale.RadialFilling.contMDiffAt_direction {n : ℕ} (b : Smale.Hemisphere.Sphere n)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (direction b) v := by
  let V : TopologicalSpace.Opens (Smale.Hemisphere.Ambient (n + 1)) :=
    ⟨{w | w ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩
  have : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hnorm :
    ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) ∞
      (fun w : V => NormedSpace.normalize (w : Smale.Hemisphere.Ambient (n + 1))) :=
    NoExotic.contMDiff_normalize contMDiff_subtype_val (fun w => w.2)
  have hmem (w : V) :
    NormedSpace.normalize (w : Smale.Hemisphere.Ambient (n + 1)) ∈
      Metric.sphere (0 : Smale.Hemisphere.Ambient (n + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize w.2
  have hsphere := hnorm.codRestrict_sphere (n := n) hmem
  have hs :
    ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (fun w : V => direction b w.1) := by
    apply hsphere.congr
    intro w
    exact Subtype.ext (direction_coe b w.2)
  exact (contMDiffAt_subtype_iff (U := V) (f := direction b) (x := ⟨v, hv⟩)).mp (hs ⟨v, hv⟩)

def Smale.RadialFilling.radialTime {n : ℕ} (v : Smale.Hemisphere.Ambient (n + 1)) :
    unitInterval :=
  Set.projIcc 0 1 zero_le_one (1 - ‖v‖)

theorem Smale.RadialFilling.coe_radialTime {n : ℕ} (v : Smale.Hemisphere.Ambient (n + 1)) :
    (radialTime v : ℝ) = Max.max 0 (Min.min 1 (1 - ‖v‖)) :=
  rfl

theorem Smale.RadialFilling.radialTime_le_quarter {n : ℕ} {v : Smale.Hemisphere.Ambient (n + 1)}
    (hv : 3 / 4 ≤ ‖v‖) : (radialTime v : ℝ) ≤ 1 / 4 := by
  rw [coe_radialTime]
  exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith))

theorem Smale.RadialFilling.three_quarters_le_radialTime {n : ℕ}
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : 3 / 4 ≤ (radialTime v : ℝ) := by
  rw [coe_radialTime]
  exact le_max_of_le_right (le_min (by norm_num) (by linarith))

theorem Smale.RadialFilling.contMDiffAt_radialTime {n : ℕ} {v : Smale.Hemisphere.Ambient (n + 1)}
    (hv : 0 < ‖v‖) (hunit : ‖v‖ < 1) :
    ContMDiffAt 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) (𝓡∂ 1) ∞ radialTime v := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have hm : 1 - ‖v‖ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hn : Set.Icc (0 : ℝ) 1 ∈ 𝓝 (1 - ‖v‖) := Icc_mem_nhds (by linarith) (by linarith)
  have hproj := (hp _ hm).contMDiffAt hn
  have hnorm : ContDiffAt ℝ ∞ (Norm.norm : Smale.Hemisphere.Ambient (n + 1) → ℝ) v :=
    contDiffAt_norm ℝ (norm_pos_iff.mp hv)
  exact hproj.comp v (contDiffAt_const.sub hnorm).contMDiffAt

def Smale.RadialFilling.filling {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n) (v : Smale.Hemisphere.Ambient (n + 1)) : M :=
  H (radialTime v, direction b v)

theorem Smale.RadialFilling.filling_eq_center {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : filling H b v = c :=
  htop _ _ (three_quarters_le_radialTime hv)

theorem Smale.RadialFilling.filling_eq_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : 3 / 4 ≤ ‖v‖) :
    filling H b v = f (direction b v) :=
  hbottom _ _ (radialTime_le_quarter hv)

theorem Smale.RadialFilling.filling_on_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (v : Smale.Hemisphere.Sphere n) : filling H b v.1 = f v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  rw [filling_eq_boundary H b hbottom (by rw [hn]; norm_num), direction_of_mem_sphere]

theorem Smale.RadialFilling.contMDiff_filling {n : ℕ} {G K M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace M]
    [ChartedSpace K M] {f : C(Smale.Hemisphere.Sphere n, M)} {c : M}
    (H : f.Homotopy (ContinuousMap.const _ c)) (b : Smale.Hemisphere.Sphere n)
    (hf : ContMDiff (𝓡 n) J ∞ f) (hH : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) J ∞ H)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) :
    ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) J ∞ (filling H b) := by
  intro v
  by_cases hinner : ‖v‖ < 1 / 4
  · apply (contMDiffAt_const (c := c)).congr_of_eventuallyEq
    have hn : {w : Smale.Hemisphere.Ambient (n + 1) | ‖w‖ < 1 / 4} ∈ 𝓝 v :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hinner
    filter_upwards [hn] with w hw
    exact filling_eq_center H b htop (le_of_lt hw)
  · by_cases houter : 3 / 4 < ‖v‖
    · have hv : v ≠ 0 := norm_pos_iff.mp (by linarith)
      have hs := (hf (direction b v)).comp v (contMDiffAt_direction b hv)
      apply hs.congr_of_eventuallyEq
      have hn : {w : Smale.Hemisphere.Ambient (n + 1) | 3 / 4 < ‖w‖} ∈ 𝓝 v :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds houter
      filter_upwards [hn] with w hw
      exact filling_eq_boundary H b hbottom (le_of_lt hw)
    · have hv : 0 < ‖v‖ := by linarith [le_of_not_gt hinner]
      have hunit : ‖v‖ < 1 := by linarith [le_of_not_gt houter]
      exact
        (hH (radialTime v, direction b v)).comp v (f := fun w => (radialTime w, direction b w))
          ((contMDiffAt_radialTime hv hunit).prodMk
            (contMDiffAt_direction b (norm_pos_iff.mp hv)))

theorem Smale.exists_smooth_nullhomotopy_of_homotopySixSphere {E G H X M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [CompactSpace X]
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold 𝓘(ℝ, G) ∞ M] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E < 6) (f : C(X, M)) (hf : ContMDiff I 𝓘(ℝ, G) ∞ f) :
    ∃ c : M,
      ∃ H : f.Homotopy (ContinuousMap.const X c),
        ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, G) ∞ H ∧
          (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x) ∧
            (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) := by
  obtain ⟨c, ⟨H⟩⟩ := manifoldMap_nullhomotopic_of_homotopySixSphere (I := I) e hdim f
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hf contMDiff_const H
  exact ⟨c, H', hH', hlo, hhi⟩

theorem Smale.exists_smooth_disk_extension_of_homotopySixSphere {G M : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold 𝓘(ℝ, G) ∞ M] (e : M ≃ₕ Smale.SixSphere) {n : ℕ} (hn : n < 6)
    (f : C(Hemisphere.Sphere n, M)) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, G) ∞ f) :
    ∃ (c : M) (F : Hemisphere.Ambient (n + 1) → M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, G) ∞ F ∧
        (∀ v : Hemisphere.Sphere n, F v.1 = f v) ∧ ∀ v, ‖v‖ ≤ 1 / 4 → F v = c := by
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) < 6 := by
    simpa only [finrank_euclideanSpace_fin] using hn
  obtain ⟨c, H, hH, hlo, hhi⟩ := exists_smooth_nullhomotopy_of_homotopySixSphere e hd f hf
  obtain ⟨v, hv⟩ : (Hemisphere.Sphere n).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere n := ⟨v, hv⟩
  exact
    ⟨c, RadialFilling.filling H b, RadialFilling.contMDiff_filling H b hf hH hlo hhi,
      RadialFilling.filling_on_sphere H b hlo, fun _ hv =>
      RadialFilling.filling_eq_center H b hhi hv⟩

theorem Smale.exists_embedded_disk_of_homotopySixSphere {G M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold 𝓘(ℝ, G) ∞ M] [T2Space M] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ G = 6) (γ : C(Hemisphere.Sphere 1, M))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ x)) :
    ∃ g : C(Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g x.1) := by
  obtain ⟨-, f, hf, hext, -⟩ :=
    exists_smooth_disk_extension_of_homotopySixSphere e (n := 1) (by decide) γ hγ
  exact exists_embedded_disk_extension_of_smooth_extension hf hext hγinj hγderiv (by omega)

theorem MorseCancellation.exists_disk_in_level_basin_of_index_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ g : C(Smale.Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, E) ∞ g ∧
        (∀ z : Smale.Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
            (∀ z : Smale.Hemisphere.Ball 2,
                Function.Injective (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, E) g z.val)) ∧
              ∀ z : Smale.Hemisphere.Ball 2,
                g z.val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨g₀, hg₀, hboundary, hemb, hderiv⟩ :=
    Smale.exists_embedded_disk_of_homotopySixSphere e hdim γ hγ hγinj hγderiv
  let K : Set (Smale.Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Smale.Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall _ _
  have hC : IsClosed C := Metric.isClosed_sphere
  have hinj : Set.InjOn g₀ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfixed (z : Smale.Hemisphere.Ambient 2) (hz : z ∈ K ∩ C) :
    g₀ z ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    refine ⟨0, ?_⟩
    rw [S.flow.map_zero_apply, hboundary ⟨z, hz.2⟩, hlevel]
  have hhigh' (p : Smale.ManifoldMorse.criticalPoints E f) (hp : a ≤ f p) :
    Module.finrank ℝ E - nativeMorseIndex E f p ≤ 3 := by
    have hh := hhigh p hp
    omega
  obtain ⟨g, hg, hhom, hembg, hderg, -, hbasin⟩ :=
    exists_embedded_avoidance_into_level_basin S hf hreg hhigh' hlow g₀ hg₀
      (by simp only [Smale.Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega)
      (by simp only [Smale.Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega) hK hK hC hinj
      (fun z hz => hderiv ⟨z, hz⟩) hfixed
  refine ⟨g, hg, ?_, hembg, fun z => hderg z.val z.property, ?_⟩
  · intro z
    exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)
  · intro z
    exact hbasin z.val (Or.inr z.property)

theorem MorseCancellation.exists_actual_regular_level_disk_of_index_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ D : C(Smale.Hemisphere.Ball 2, { y : M // f y = a }),
      ∀ z : Smale.Hemisphere.Sphere 1,
        (D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩).val = γ z := by
  obtain ⟨g, hg, hboundary, -, -, hbasin⟩ :=
    exists_disk_in_level_basin_of_index_cut S hf e hdim hreg hhigh hlow γ hγ hγinj hγderiv hlevel
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Smale.Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let z₀ : { y : M // f y = a } := ⟨γ ⟨v, hv⟩, hlevel ⟨v, hv⟩⟩
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
      (fun y hy => S.descent y (hreg y hy)) z₀
  have hcont : Continuous (fun z : Smale.Hemisphere.Ball 2 => Φ.symm (g z.val)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous (g.continuous.comp continuous_subtype_val)
      (fun z => htarget.symm ▸ hbasin z)
  let D : C(Smale.Hemisphere.Ball 2, { y : M // f y = a }) :=
    ⟨fun z => (Φ.symm (g z.val)).1, continuous_fst.comp hcont⟩
  refine ⟨D, ?_⟩
  intro z
  let p : { y : M // f y = a } := ⟨γ z, hlevel z⟩
  have hp : (p, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
  have hφ : Φ (p, 0) = γ z := by rw [hformula, S.flow.map_zero_apply]
  have hi : Φ.symm (Φ (p, 0)) = (p, 0) := Φ.left_inv' hp
  rw [hφ] at hi
  change (Φ.symm (g z.val)).1.val = γ z
  rw [hboundary z]
  exact congrArg (fun q : { y : M // f y = a } × ℝ => q.1.val) hi

theorem MorseCancellation.circle_nullhomotopy_of_disk {N : Type*} [TopologicalSpace N]
    (γ : C(Smale.Hemisphere.Sphere 1, N)) (D : C(Smale.Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Smale.Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ c : N, γ.Homotopic (ContinuousMap.const _ c) := by
  let c := D ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let H : γ.Homotopy (ContinuousMap.const _ c) :=
    { toFun := fun p => D (Smale.DiskCone.point p)
      continuous_toFun := D.continuous.comp Smale.DiskCone.continuous_point
      map_zero_left := by
        intro z
        have he :
          Smale.DiskCone.point (0, z) =
            (⟨z.val, Metric.sphere_subset_closedBall z.property⟩ : Smale.Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [Smale.DiskCone.point]
        rw [he]
        exact hboundary z
      map_one_left := by
        intro z
        have he :
          Smale.DiskCone.point (1, z) =
            (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Smale.Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [Smale.DiskCone.point]
        exact congrArg D he }
  exact ⟨c, ⟨H⟩⟩

theorem MorseCancellation.exists_smooth_embedded_disk_of_continuous_filling {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] (γ : C(Smale.Hemisphere.Sphere 1, N))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ z))
    (hdim : 5 ≤ Module.finrank ℝ G) (D : C(Smale.Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Smale.Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ g : C(Smale.Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ z : Smale.Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Smale.Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, G) g z.val) := by
  obtain ⟨c, ⟨H⟩⟩ := circle_nullhomotopy_of_disk γ D hboundary
  obtain ⟨H', hH', hlo, hhi⟩ :=
    Smale.ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ contMDiff_const H
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Smale.Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Smale.Hemisphere.Sphere 1 := ⟨v, hv⟩
  have hsmooth := Smale.RadialFilling.contMDiff_filling H' b hγ hH' hlo hhi
  have hext := Smale.RadialFilling.filling_on_sphere H' b hlo
  exact Smale.exists_embedded_disk_extension_of_smooth_extension hsmooth hext hγinj hγderiv hdim

theorem MorseCancellation.exists_embedded_regular_level_disk_of_index_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ z))
    (hlevel : ∀ z, f (γ z) = a) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ∃ g : C(Smale.Hemisphere.Ambient 2, { y : M // f y = a }),
      ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g ∧
        (∀ z : Smale.Hemisphere.Sphere 1, (g z.val).val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Smale.Hemisphere.Ball 2,
              Function.Injective
                (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g
                  z.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  obtain ⟨D, hD⟩ :=
    exists_actual_regular_level_disk_of_index_cut S hf e hdim hreg hhigh hlow γ hγ hγinj hγderiv
      hlevel
  let γL : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨fun z => ⟨γ z, hlevel z⟩, γ.continuous.subtype_mk _⟩
  have hγL : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γL :=
    (Smale.RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 1) γL).mpr hγ
  have hinj : Function.Injective γL := fun x y hxy => hγinj (congrArg Subtype.val hxy)
  have hderiv (z : Smale.Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γL z) :=
    Smale.RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 1) γL z hγ.contMDiffAt
      (hγderiv z)
  have hdimL : 5 ≤ Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    norm_num
  have hboundary (z : Smale.Hemisphere.Sphere 1) :
    D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γL z := Subtype.ext (hD z)
  obtain ⟨g, hg, hboundaryg, hemb, hderivg⟩ :=
    exists_smooth_embedded_disk_of_continuous_filling γL hγL hinj hderiv hdimL D hboundary
  exact ⟨g, hg, fun z => congrArg Subtype.val (hboundaryg z), hemb, hderivg⟩

theorem MorseCancellation.exists_native_middle_level_circle_disk {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ∃ g : C(Smale.Hemisphere.Ambient 2, { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g ∧
              (∀ z : Smale.Hemisphere.Sphere 1, g z.val = γ z) ∧
                Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
                  (∀ z : Smale.Hemisphere.Ball 2,
                    Function.Injective
                      (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g
                        z.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) → _
  intro hγ hγi hγd
  let γM : C(Smale.Hemisphere.Sphere 1, M) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γM :=
    (Smale.RegularLevel.contMDiff_inclusion hf hreg).comp hγ
  have hγMi : Function.Injective γM := Subtype.val_injective.comp hγi
  have hγMd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γM z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (Subtype.val ∘ γ) z)
    rw [mfderiv_comp z
        ((Smale.RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
        (hγ.mdifferentiableAt (by simp))]
    exact (Smale.RegularLevel.injective_mfderiv_inclusion hf hreg (γ z)).comp (hγd z)
  obtain ⟨g, hg, hb, hemb, hgd⟩ :=
    exists_embedded_regular_level_disk_of_index_cut S hf e hdim hreg hhigh hlow γM hγM hγMi hγMd
      (fun z => (γ z).property)
  exact ⟨g, hg, fun z => Subtype.ext (hb z), hemb, hgd⟩

theorem MorseCancellation.exists_native_middle_level_circle_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) →
                ∃ P :
                  Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                    { y : M // f y = a } { y : M // f y = a } ∞,
                  Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  let _ : CompactSpace { y : M // f y = a } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  obtain ⟨g, hg, hgb, hge, hgd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow γ hγ hγi hγd
  obtain ⟨h, hh, hhb, hhe, hhd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow δ hδ hδi hδd
  let _ := S.pathConnectedSpace_middle_level hf hdim hreg hhigh hlow (g 0)
  have hgi : Set.InjOn g (Metric.closedBall (0 : Smale.Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hge.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hhi : Set.InjOn h (Metric.closedBall (0 : Smale.Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hhe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcodim :
    Module.finrank ℝ (Smale.Hemisphere.Ambient 2) + 3 =
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.Hemisphere.Ambient, Smale.RegularLevel.Model, finrank_euclideanSpace_fin,
      hdim]
  have hmodel : 2 ≤ Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    omega
  obtain ⟨P, hP, hformula⟩ :=
    Degree.DiskShrinking.exists_embedded_disk_isotopy hg hh hgi hhi (fun x hx => hgd ⟨x, hx⟩)
      (fun x hx => hhd ⟨x, hx⟩) 3 (by omega) hcodim hmodel
  refine ⟨P, hP, ?_⟩
  intro z
  rw [← hgb z, hformula z.val (Metric.sphere_subset_closedBall z.property), hhb z]

def MorseCancellation.cancelled {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  cubic σ (-t) p + 2 * t * φ p * p.1

theorem MorseCancellation.contDiff_cancelled_family {m : ℕ} (σ : Fin m → ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Function.uncurry (cancelled σ φ)) := by
  exact
    ((contDiff_cubic_family σ).comp (contDiff_fst.neg.prodMk contDiff_snd)).add
      (((contDiff_const.mul contDiff_fst).mul (hφ.comp contDiff_snd)).mul contDiff_snd.fst)

theorem MorseCancellation.cancelled_zero {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) :
    cancelled σ φ 0 = cubic σ 0 := by
  funext p
  simp [cancelled]

theorem MorseCancellation.cancelled_germ_plateau {m : ℕ} (σ : Fin m → ℝ) {φ : Model m → ℝ}
    {U : Set (Model m)} (hU : IsOpen U) (hφU : Set.EqOn φ (fun _ => 1) U) (t : ℝ) {p : Model m}
    (hp : p ∈ U) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ t := by
  filter_upwards [hU.mem_nhds hp] with q hq
  simp [cancelled, cubic, hφU hq]
  ring

theorem MorseCancellation.cancelled_eq_off_support {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ)
    {p : Model m} (hp : p ∉ tsupport φ) : cancelled σ φ t p = cubic σ (-t) p := by
  simp [cancelled, image_eq_zero_of_notMem_tsupport hp]

theorem MorseCancellation.cancelled_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ)
    {p : Model m} (hp : p ∉ tsupport φ) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ (-t) := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hp] with q hq
  exact cancelled_eq_off_support σ φ t hq

theorem MorseCancellation.exists_exact_cubic_birth {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {U : Set (Model m)}
    (hU : IsOpen U) (h0 : (0 : Model m) ∈ U) (hφU : Set.EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ,
      0 < a ∧
        (a, (0 : Fin m → ℝ)) ∈ U ∧
          (-a, (0 : Fin m → ℝ)) ∈ U ∧
            ∃ g : Model m → ℝ,
              ContDiff ℝ ∞ g ∧
                (∀ p, fderiv ℝ g p = 0 ↔ p = (a, 0) ∨ p = (-a, 0)) ∧
                  (∀ p ∈ U, g =ᶠ[𝓝 p] cubic σ (-(a ^ 2))) ∧
                    ∀ p, p ∉ tsupport φ → g =ᶠ[𝓝 p] cubic σ (a ^ 2) := by
  let K := tsupport φ \ U
  have hK : IsCompact K := hc.diff hU
  have hD :=
    (Smale.MorsePerturbation.contDiff_spatialDerivative
        (contDiff_cancelled_family σ hφ)).continuous
  have hO : IsOpen {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact hK
      (isClosed_eq hD continuous_const).isOpen_compl
  have hO0 : (0 : ℝ) ∈ {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} := by
    intro p hp hcrit
    rw [cancelled_zero] at hcrit
    exact hp.2 ((cubic_zero_unique_critical σ hσ p).mp hcrit ▸ h0)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hO0)
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨a, ha, har⟩ := exists_between (lt_min hr (lt_min zero_lt_one hδ))
  have ha1 : a < 1 := (lt_min_iff.mp (lt_min_iff.mp har).2).1
  have haδ : a < δ := (lt_min_iff.mp (lt_min_iff.mp har).2).2
  have haa : a ^ 2 < δ := by nlinarith
  have htrans : ∀ p ∈ K, fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 :=
    hδball (by simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg a)] using haa)
  have hp : (a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  have hq : (-a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  refine
    ⟨a, ha, hp, hq, cancelled σ φ (-(a ^ 2)),
      (contDiff_cancelled_family σ hφ).comp (contDiff_const.prodMk contDiff_id), ?_,
      (fun p hpU => cancelled_germ_plateau σ hU hφU _ hpU), ?_⟩
  · intro p
    by_cases hpU : p ∈ U
    · rw [(cancelled_germ_plateau σ hU hφU (-(a ^ 2)) hpU).fderiv_eq]
      exact negative_parameter_critical_iff σ hσ a p
    · have hreg : fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 := by
        by_cases hpS : p ∈ tsupport φ
        · exact htrans p ⟨hpS, hpU⟩
        · rw [(cancelled_germ_off_support σ φ (-(a ^ 2)) hpS).fderiv_eq, neg_neg]
          exact positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) p
      constructor
      · exact fun h => False.elim (hreg h)
      · rintro (rfl | rfl)
        · exact False.elim (hpU hp)
        · exact False.elim (hpU hq)
  · intro p hpS
    simpa only [neg_neg] using cancelled_germ_off_support σ φ (-(a ^ 2)) hpS

theorem MorseCancellation.exists_positive_scalar_cubic_diffeomorph {a : ℝ} (ha : 0 < a) :
    ∃ e : ℝ ≃ₘ[ℝ] ℝ, ∀ s, e s = s ^ 3 / 3 + a ^ 2 * s := by
  let g : ℝ → ℝ := fun s => s ^ 3 / 3 + a ^ 2 * s
  have hg : ContDiff ℝ ∞ g := by unfold g; fun_prop
  have hd (s : ℝ) : HasDerivAt g (s ^ 2 + a ^ 2) s := by
    convert!
      (((hasDerivAt_id s).pow 3).div_const 3).add ((hasDerivAt_id s).const_mul (a ^ 2)) using 1;
    simp
  have hpos (s : ℝ) : 0 < s ^ 2 + a ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg s) (sq_pos_of_pos ha)
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd hpos
  have hbound {s t : ℝ} (hst : s ≤ t) : a ^ 2 * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
      (fun x => by rw [(hd x).deriv]; exact le_add_of_nonneg_left (sq_nonneg x)) hst
  have hzero : g 0 = 0 := by simp [g]
  have hsurj : Function.Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨Min.min 0 (y / a ^ 2), ?_⟩
      have hh := hbound (min_le_left 0 (y / a ^ 2))
      have hm : a ^ 2 * Min.min 0 (y / a ^ 2) ≤ y := by
        calc
          a ^ 2 * Min.min 0 (y / a ^ 2) ≤ a ^ 2 * (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg a)
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨Max.max 0 (y / a ^ 2), ?_⟩
      have hh := hbound (le_max_left 0 (y / a ^ 2))
      have hm : y ≤ a ^ 2 * Max.max 0 (y / a ^ 2) := by
        calc
          y = a ^ 2 * (y / a ^ 2) := by field_simp
          _ ≤ a ^ 2 * Max.max 0 (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg a)
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  have hi : ContDiff ℝ ∞ c.toHomeomorph.symm :=
    c.toHomeomorph.contDiff_symm_deriv (fun s => (hpos s).ne') hd hg
  let e : ℝ ≃ₘ[ℝ] ℝ :=
    { toEquiv := c.toEquiv
      contMDiff_toFun := hg.contMDiff
      contMDiff_invFun := hi.contMDiff }
  exact ⟨e, fun _ => rfl⟩

theorem MorseCancellation.exists_positive_cubic_height_diffeomorph {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) : ∃ D : Model m ≃ₘ[ℝ] Model m, ∀ p, D p = (cubic σ (a ^ 2) p, p.2) := by
  obtain ⟨e, he⟩ := exists_positive_scalar_cubic_diffeomorph ha
  let Q : (Fin m → ℝ) → ℝ := fun z => ∑ i, σ i * z i ^ 2
  have hQ : ContDiff ℝ ∞ Q := by unfold Q; fun_prop
  have hec : ContDiff ℝ ∞ e := contMDiff_iff_contDiff.mp e.contMDiff
  have hei : ContDiff ℝ ∞ e.symm := contMDiff_iff_contDiff.mp e.symm.contMDiff
  let D : Model m ≃ₘ[ℝ] Model m :=
    { toFun := fun p => (e p.1 + Q p.2, p.2)
      invFun := fun p => (e.symm (p.1 - Q p.2), p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      contMDiff_toFun :=
        ((hec.comp contDiff_fst |>.add (hQ.comp contDiff_snd)).prodMk contDiff_snd).contMDiff
      contMDiff_invFun :=
        ((hei.comp (contDiff_fst.sub (hQ.comp contDiff_snd))).prodMk contDiff_snd).contMDiff }
  refine ⟨D, ?_⟩
  intro p
  change (e p.1 + Q p.2, p.2) = _
  rw [he]
  rfl

theorem MorseCancellation.hessian_comp_linearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E ≃L[ℝ] F) (x : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap).comp
        ((fderiv ℝ (fderiv ℝ f) (L x)).comp L.toContinuousLinearMap) := by
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hgrad : fderiv ℝ (f ∘ L) = fun y => A (fderiv ℝ f (L y)) := by
    funext y
    rw [fderiv_comp y (hf.differentiable (by simp) (L y)) L.differentiableAt, L.fderiv]
    rfl
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [hgrad]
  exact
    (A.hasFDerivAt.comp x
        ((hdf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt)).fderiv

theorem MorseCancellation.euclidean_isMorse_comp_linearEquiv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (hm : Smale.MorsePerturbation.IsMorse f) (L : E ≃L[ℝ] F) :
    Smale.MorsePerturbation.IsMorse (f ∘ L) := by
  intro x hx
  have hcrit : fderiv ℝ f (L x) = 0 := by
    rw [fderiv_comp x (hf.differentiable (by simp) (L x)) L.differentiableAt, L.fderiv] at hx
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := L.surjective v
    exact congrArg (fun k : E →L[ℝ] ℝ => k w) hx
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hA : Function.Bijective A := by
    constructor
    · intro k l hkl
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := L.surjective v
      exact congrArg (fun k : E →L[ℝ] ℝ => k w) hkl
    · intro k
      refine ⟨k.comp L.symm.toContinuousLinearMap, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      change k (L.symm (L v)) = k v
      rw [L.symm_apply_apply]
  rw [hessian_comp_linearEquiv hf L]
  exact hA.comp ((hm (L x) hcrit).comp L.bijective)

theorem MorseCancellation.isMorseAt_of_native_model_germ {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞) (L : E ≃L[ℝ] F) {f : M → ℝ} {b : F → ℝ} {p : F}
    (hp : p ∈ Φ.source) (hb : ContDiff ℝ ∞ b) (hmb : Smale.MorsePerturbation.IsMorse b)
    (hmodel : f ∘ Φ =ᶠ[𝓝 p] b) : Smale.ManifoldMorse.IsMorseAt E f (Φ p) := by
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hpΨ : Φ p ∈ Ψ.target := by exact ⟨Φ.map_source' hp, Set.mem_univ _⟩
  have he : Ψ.symm.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    Ψ.symm.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn Ψ.contMDiffOn_invFun
      Ψ.contMDiffOn_toFun
  apply
    Smale.ManifoldMorse.isMorseAt_of_chart_eventuallyEq he hpΨ
      (euclidean_isMorse_comp_linearEquiv hb hmb L)
  have hcenter : Ψ.symm (Φ p) = L.symm p := by
    change L.symm (Φ.symm (Φ p)) = L.symm p
    exact congrArg L.symm (Φ.left_inv' hp)
  change f ∘ Ψ =ᶠ[𝓝 (Ψ.symm (Φ p))] b ∘ L
  rw [hcenter]
  have ht : Filter.Tendsto L (𝓝 (L.symm p)) (𝓝 p) := by
    simpa only [L.apply_symm_apply] using L.continuous.continuousAt.tendsto (x := L.symm p)
  exact hmodel.comp_tendsto ht

theorem MorseCancellation.euclidean_isMorse_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hm : Smale.MorsePerturbation.IsMorse f) {c : ℝ}
    (hc : c ≠ 0) (b : ℝ) : Smale.MorsePerturbation.IsMorse (fun x => b + c * f x) := by
  have hgrad : fderiv ℝ (fun x => b + c * f x) = fun x => c • fderiv ℝ f x := by
    funext x
    rw [fderiv_const_add, fderiv_const_mul (hf.differentiable (by simp) x)]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  intro x hx
  rw [hgrad] at hx ⊢
  have hcrit : fderiv ℝ f x = 0 := (smul_eq_zero.mp hx).resolve_left hc
  change Function.Bijective (fderiv ℝ (c • fderiv ℝ f) x)
  rw [fderiv_const_smul (hdf.differentiable (by simp) x)]
  exact (isUnit_iff_ne_zero.mpr hc).smul_bijective.comp (hm x hcrit)

theorem MorseCancellation.exists_pos_compact_smul_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (h0 : (0 : E) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ (fun x : E => δ • x) '' K ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let R := Max.max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hCR : C < R := by dsimp [R]; linarith [le_max_left C 0]
  let δ := r / (2 * R)
  have hδ : 0 < δ := div_pos hr (mul_pos (by norm_num) hR)
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hrU
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hnorm : ‖x‖ < R := (hC x hx).trans_lt hCR
  have hm : δ * ‖x‖ < δ * R := mul_lt_mul_of_pos_left hnorm hδ
  have heq : δ * R = r / 2 := by dsimp [δ]; field_simp
  rw [heq] at hm
  linarith

theorem MorseCancellation.exists_centered_native_height_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (0 : Model m) ∈ Φ.source ∧ Φ 0 = x ∧ Φ.target ⊆ U ∧ ∀ p ∈ Φ.source, f (Φ p) = f x + p.1 := by
  obtain ⟨Q, hxQ, hQ, hQx⟩ := Smale.RegularLevel.exists_native_height_chart hf hx
  have hdim' : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Module.finrank_pi, Fintype.card_fin, Smale.RegularLevel.Model,
      finrank_euclideanSpace_fin]
    omega
  let L : (Fin m → ℝ) ≃L[ℝ] Smale.RegularLevel.Model E := ContinuousLinearEquiv.ofFinrankEq hdim'
  let D :
    Diffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, ℝ × Smale.RegularLevel.Model E) (Model m)
      (ℝ × Smale.RegularLevel.Model E) ∞ :=
    { toFun := fun p => (f x + p.1, L p.2)
      invFun := fun p => (p.1 - f x, L.symm p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      contMDiff_toFun :=
        ((contDiff_const.add contDiff_fst).prodMk (L.contDiff.comp contDiff_snd)).contMDiff
      contMDiff_invFun :=
        ((contDiff_fst.sub contDiff_const).prodMk (L.symm.contDiff.comp contDiff_snd)).contMDiff }
  let P := D.toPartialDiffeomorph.trans Q.symm
  let Φ := Smale.PartialChart.restrictTarget P hU
  have hD0 : D 0 = Q x := by
    rw [hQx]
    change (f x + (0 : ℝ), L 0) = (f x, 0)
    simp
  have h0P : (0 : Model m) ∈ P.source := by
    change (0 : Model m) ∈ Set.univ ∧ D 0 ∈ Q.target
    exact ⟨Set.mem_univ _, hD0.symm ▸ Q.map_source' hxQ⟩
  have hP0 : P 0 = x := by
    change Q.symm (D 0) = x
    rw [hD0]
    exact Q.left_inv' hxQ
  have h0Φ : (0 : Model m) ∈ Φ.source := by
    change (0 : Model m) ∈ P.source ∧ P 0 ∈ U
    exact ⟨h0P, hP0.symm ▸ hxU⟩
  refine ⟨Φ, h0Φ, hP0, fun _ hy => hy.2, ?_⟩
  intro p hp
  have hpt : D p ∈ Q.target := hp.1.2
  have hh := hQ (Q.symm (D p)) (Q.map_target' hpt)
  have hright : Q (Q.symm (D p)) = D p := Q.right_inv' hpt
  rw [hright] at hh
  exact hh.symm

theorem MorseCancellation.insert_morse_chart_pair {E D M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (L : E ≃L[ℝ] D) {f : M → ℝ} {b₀ b₁ : D → ℝ}
    {K : Set D} {p q : D} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hb₀ : ContDiff ℝ ∞ b₀) (hb₁ : ContDiff ℝ ∞ b₁)
    (hmb₁ : Smale.MorsePerturbation.IsMorse b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) (hp : p ∈ Φ.source)
    (hq : q ∈ Φ.source) (hpq : p ≠ q) (hreg : ∀ x, fderiv ℝ b₀ x ≠ 0)
    (hcrit : ∀ x, fderiv ℝ b₁ x = 0 ↔ x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard =
              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
            (∀ y,
                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = Φ p ∨ y = Φ q) ∧
              (∀ y, y ∉ Φ '' K → g =ᶠ[𝓝 y] f) ∧
                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                  ∀ z ∈ Φ.source, g (Φ z) = b₁ z := by
  let g := Degree.LocalFunctionReplacement.replace Φ f b₁
  have hg := Degree.LocalFunctionReplacement.contMDiff_replace Φ hf hb₁ hK hKΦ hmodel hfix
  have houtside (y : M) (hy : y ∉ Φ '' K) : g =ᶠ[𝓝 y] f :=
    Degree.LocalFunctionReplacement.replace_germ_off_support Φ hK hKΦ hmodel hfix hy
  have hnot (y : M) (hy : y ∈ Φ.target) : y ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro hc
    have he := Degree.LocalFunctionReplacement.replace_critical_iff Φ f hb₀ hy
    rw [Degree.LocalFunctionReplacement.replace_self Φ hmodel] at he
    exact hreg (Φ.symm y) (he.mp hc)
  have hcritg (y : M) :
    y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
      y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = Φ p ∨ y = Φ q := by
    by_cases hy : y ∈ Φ.target
    · have he := Degree.LocalFunctionReplacement.replace_critical_iff Φ f hb₁ hy
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
      rw [he, hcrit]
      constructor
      · rintro (h | h)
        · exact Or.inr (Or.inl ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
        · exact Or.inr (Or.inr ((Φ.right_inv' hy).symm.trans (congrArg Φ h)))
      · rintro (hc | rfl | rfl)
        · exact False.elim (hnot y hy hc)
        · exact Or.inl (Φ.left_inv' hp)
        · exact Or.inr (Φ.left_inv' hq)
    · have hyK : y ∉ Φ '' K := by
        rintro ⟨z, hz, rfl⟩
        exact hy (Φ.map_source' (hKΦ hz))
      have hyp : y ≠ Φ p := fun h => hy (h.symm ▸ Φ.map_source' hp)
      have hyq : y ≠ Φ q := fun h => hy (h.symm ▸ Φ.map_source' hq)
      have he :
        y ∈ Smale.ManifoldMorse.criticalPoints E g ↔ y ∈ Smale.ManifoldMorse.criticalPoints E f :=
        by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g y = 0 ↔ _
        rw [(houtside y hyK).mfderiv_eq]
        rfl
      simpa only [hyp, hyq, or_false] using he
  have hmg : Smale.ManifoldMorse.IsMorse E g := by
    intro y
    by_cases hy : y ∈ Φ.target
    · have hx := Φ.map_target' hy
      have hmodelg : g ∘ Φ =ᶠ[𝓝 (Φ.symm y)] b₁ := by
        filter_upwards [Φ.open_source.mem_nhds hx] with z hz
        exact Degree.LocalFunctionReplacement.replace_chart Φ f b₁ hz
      have hh := isMorseAt_of_native_model_germ Φ L hx hb₁ hmb₁ hmodelg
      have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
      exact hright ▸ hh
    · apply Degree.MorseCancellationPreservation.isMorseAt_of_same_germ (hm y)
      apply houtside y
      rintro ⟨z, hz, rfl⟩
      exact hy (Φ.map_source' (hKΦ hz))
  have hneq : Φ p ≠ Φ q := fun h => hpq (Φ.toOpenPartialHomeomorph.injOn hp hq h)
  have hpnot := hnot (Φ p) (Φ.map_source' hp)
  have hqnot := hnot (Φ q) (Φ.map_source' hq)
  have heq :
    Smale.ManifoldMorse.criticalPoints E g =
      Insert.insert (Φ p) (Insert.insert (Φ q) (Smale.ManifoldMorse.criticalPoints E f)) := by
    ext y
    rw [hcritg]
    simp only [Set.mem_insert_iff]
    tauto
  refine
    ⟨g, hg, hmg, ?_, hcritg, houtside, ?_, fun z hz =>
      Degree.LocalFunctionReplacement.replace_chart Φ f b₁ hz⟩
  · rw [heq,
      Set.ncard_insert_of_notMem
        (by simp only [Set.mem_insert_iff, hneq, hpnot, or_self, not_false_eq_true])
        ((Smale.ManifoldMorse.finite_criticalPoints hf hm).insert (Φ q)),
      Set.ncard_insert_of_notMem hqnot (Smale.ManifoldMorse.finite_criticalPoints hf hm)]
  · intro y hy
    apply houtside y
    rintro ⟨z, hz, rfl⟩
    exact hnot (Φ z) (Φ.map_source' (hKΦ hz)) hy

theorem MorseCancellation.exists_native_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {x : M}
    (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E)
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ,
      0 < a ∧
        0 < δ ∧
          ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
            (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
              (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
                Φ.target ⊆ U ∧
                  (∀ z ∈ Φ.source, f (Φ z) = f x + δ * cubic σ (a ^ 2) z) ∧
                    ∃ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                        Smale.ManifoldMorse.IsMorse E g ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨
                                    y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => f x + δ * cubic σ (-(a ^ 2)) z) ∧
                                    (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z =>
                                      f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain ⟨H, h0H, -, hHU, hH⟩ := exists_centered_native_height_chart hf hx hdim hU hxU
  obtain ⟨φ, hφ, hc, -, W, hW, h0W, hφW⟩ :=
    Degree.NativeCubicCancellation.exists_cutoff (m := m) isOpen_univ (Set.mem_univ _)
  obtain ⟨a, ha, hpW, hqW, b, hb, hcritb, hgerms, hfix⟩ :=
    exists_exact_cubic_birth σ hσ hφ hc hW h0W hφW
  have hmb : Smale.MorsePerturbation.IsMorse b := by
    intro z hz
    have hzW : z ∈ W := (hcritb z).mp hz |>.elim (fun h => h ▸ hpW) (fun h => h ▸ hqW)
    have heq := hgerms z hzW
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
    apply cubic_isMorse σ hσ (neg_ne_zero.mpr (pow_ne_zero 2 ha.ne'))
    rw [← heq.fderiv_eq]
    exact hz
  obtain ⟨D, hD⟩ := exists_positive_cubic_height_diffeomorph σ ha
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_compact_smul_subset (hc.image D.continuous) H.open_source h0H
  let A : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) δ hδ.ne').toContinuousLinearEquiv
  let C := D.trans A.toDiffeomorph
  let Φ := C.toPartialDiffeomorph.trans H
  have hC (z : Model m) : C z = δ • D z := rfl
  have hKΦ : tsupport φ ⊆ Φ.source := by
    intro z hz
    change z ∈ Set.univ ∧ C z ∈ H.source
    exact ⟨Set.mem_univ _, hsmall ⟨D z, Set.mem_image_of_mem D hz, rfl⟩⟩
  have hWK : W ⊆ tsupport φ := by
    intro z hz
    apply subset_tsupport φ
    change φ z ≠ 0
    rw [hφW hz]
    norm_num
  have hpΦ := hKΦ (hWK hpW)
  have hqΦ := hKΦ (hWK hqW)
  have hΦU : Φ.target ⊆ U := fun _ hy => hHU hy.1
  let b₀ : Model m → ℝ := fun z => f x + δ * cubic σ (a ^ 2) z
  let b₁ : Model m → ℝ := fun z => f x + δ * b z
  have hb₀ : ContDiff ℝ ∞ b₀ := contDiff_const.add (contDiff_const.mul (contDiff_cubic σ _))
  have hb₁ : ContDiff ℝ ∞ b₁ := contDiff_const.add (contDiff_const.mul hb)
  have hmb₁ : Smale.MorsePerturbation.IsMorse b₁ := euclidean_isMorse_affine hb hmb hδ.ne' (f x)
  have hmodel (z : Model m) (hz : z ∈ Φ.source) : f (Φ z) = b₀ z := by
    change f (H (C z)) = _
    rw [hH (C z) hz.2, hC, hD]
    rfl
  have hfix₁ (z : Model m) (hz : z ∉ tsupport φ) : b₁ z = b₀ z := by
    dsimp [b₁, b₀]
    rw [(hfix z hz).self_of_nhds]
  have hderiv (v : Model m → ℝ) (hv : ContDiff ℝ ∞ v) (z : Model m) :
    fderiv ℝ (fun y => f x + δ * v y) z = δ • fderiv ℝ v z := by
    rw [fderiv_const_add, fderiv_const_mul (hv.differentiable (by simp) z)]
  have hreg₀ (z : Model m) : fderiv ℝ b₀ z ≠ 0 := by
    rw [hderiv _ (contDiff_cubic σ _) z]
    exact smul_ne_zero hδ.ne' (positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) z)
  have hcrit₁ (z : Model m) : fderiv ℝ b₁ z = 0 ↔ z = (a, 0) ∨ z = (-a, 0) := by
    rw [hderiv b hb z, smul_eq_zero]
    simp only [hδ.ne', false_or, hcritb]
  have hpq : (a, (0 : Fin m → ℝ)) ≠ (-a, 0) := by
    intro h
    have hh := congrArg Prod.fst h
    change a = -a at hh
    linarith
  let L : E ≃L[ℝ] Model m :=
    ContinuousLinearEquiv.ofFinrankEq
      (by
        simp only [Model, Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
          Fintype.card_fin]
        exact hdim.symm)
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior, hkeep, hnew⟩ :=
    insert_morse_chart_pair Φ L hf hm hb₀ hb₁ hmb₁ hc hKΦ hmodel hfix₁ hpΦ hqΦ hpq hreg₀ hcrit₁
  have hend (z : Model m) (hzΦ : z ∈ Φ.source) (hzW : z ∈ W) :
    g ∘ Φ =ᶠ[𝓝 z] fun w => f x + δ * cubic σ (-(a ^ 2)) w := by
    filter_upwards [Φ.open_source.mem_nhds hzΦ, hgerms z hzW] with w hw heq
    change g (Φ w) = _
    rw [hnew w hw]
    change f x + δ * b w = _
    rw [heq]
  refine
    ⟨a, δ, ha, hδ, Φ, hpΦ, hqΦ, hΦU, hmodel, g, hg, hmg, hcount, hcritg, ?_, hkeep,
      hend _ hpΦ hpW, hend _ hqΦ hqW⟩
  intro y hy
  apply hexterior y
  rintro ⟨z, hz, rfl⟩
  exact hy (hΦU (Φ.map_source' (hKΦ hz)))

theorem MorseCancellation.injOn_of_two_new_values {X : Type*} {f g : X → ℝ} {C : Set X} {p q : X}
    (hinj : Set.InjOn f C) (hkeep : ∀ y ∈ C, g y = f y) (hp : g p ∉ f '' C) (hq : g q ∉ f '' C)
    (hpq : g p ≠ g q) : Set.InjOn g {y | y ∈ C ∨ y = p ∨ y = q} := by
  intro y hy z hz heq
  rcases hy with hy | rfl | rfl
  · rcases hz with hz | rfl | rfl
    · exact hinj hy hz ((hkeep y hy).symm.trans (heq.trans (hkeep z hz)))
    · exact False.elim (hp ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
    · exact False.elim (hq ⟨y, hy, (hkeep y hy).symm.trans heq⟩)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hp ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · rfl
    · exact False.elim (hpq heq)
  · rcases hz with hz | rfl | rfl
    · exact False.elim (hq ⟨z, hz, (hkeep z hz).symm.trans heq.symm⟩)
    · exact False.elim (hpq heq.symm)
    · rfl

theorem MorseCancellation.exists_excellent_native_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {m : ℕ} (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a δ : ℝ,
      0 < a ∧
        0 < δ ∧
          ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
            (a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
              (-a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
                Φ.target ⊆ U ∧
                  ∃ g : M → ℝ,
                    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                      Smale.ManifoldMorse.IsMorse E g ∧
                        Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨
                                    y = Φ (a, 0) ∨ y = Φ (-a, 0)) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  g (Φ (a, 0)) < g (Φ (-a, 0)) ∧
                                    g (Φ (a, 0)) ∈ Set.Ioo l u ∧
                                      g (Φ (-a, 0)) ∈ Set.Ioo l u ∧
                                        (g ∘ Φ =ᶠ[𝓝 (a, 0)] fun z =>
                                            f x + δ * cubic σ (-(a ^ 2)) z) ∧
                                          (g ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z =>
                                            f x + δ * cubic σ (-(a ^ 2)) z) := by
  obtain
    ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, hmodel, g, hg, hmg, hcount, hcrit, hexterior, hkeep, hgp,
      hgq⟩ :=
    exists_native_morse_birth hf hm (hband x hx) hdim σ hσ
      (hU.inter (isOpen_Ioo.preimage hf.continuous)) ⟨hxU, hx⟩
  have hpa : f (Φ (a, 0)) = f x + δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (a, 0) hp]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hqa : f (Φ (-a, 0)) = f x - δ * (4 * a ^ 3 / 3) := by
    rw [hmodel (-a, 0) hq]
    simp only [cubic, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero]
    ring
  have hpval : g (Φ (a, 0)) = f x - δ * (2 * a ^ 3 / 3) := by
    have hh := hgp.self_of_nhds
    change g (Φ (a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (a, 0) at hh
    rw [(cubic_critical_values σ a).1] at hh
    exact hh.trans (by ring)
  have hqval : g (Φ (-a, 0)) = f x + δ * (2 * a ^ 3 / 3) := by
    have hh := hgq.self_of_nhds
    change g (Φ (-a, 0)) = f x + δ * cubic σ (-(a ^ 2)) (-a, 0) at hh
    rw [(cubic_critical_values σ a).2] at hh
    exact hh
  have hpos : 0 < δ * (2 * a ^ 3 / 3) := by positivity
  have hpq : g (Φ (a, 0)) < g (Φ (-a, 0)) := by rw [hpval, hqval]; linarith
  have hpband : g (Φ (a, 0)) ∈ Set.Ioo l u := by
    have hb := (hΦ (Φ.map_source' hq)).2
    change f (Φ (-a, 0)) ∈ Set.Ioo l u at hb
    rw [hqa] at hb
    rw [hpval]
    constructor <;> nlinarith [hb.1, hx.2]
  have hqband : g (Φ (-a, 0)) ∈ Set.Ioo l u := by
    have hb := (hΦ (Φ.map_source' hp)).2
    change f (Φ (a, 0)) ∈ Set.Ioo l u at hb
    rw [hpa] at hb
    rw [hqval]
    constructor <;> nlinarith [hx.1, hb.2]
  have hnot (v : ℝ) (hv : v ∈ Set.Ioo l u) : v ∉ f '' Smale.ManifoldMorse.criticalPoints E f := by
    rintro ⟨y, hy, rfl⟩
    exact hband y hv hy
  have hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    have hh :=
      injOn_of_two_new_values hinj (fun y hy => (hkeep y hy).self_of_nhds) (hnot _ hpband)
        (hnot _ hqband) hpq.ne
    intro y hy z hz heq
    exact hh ((hcrit y).mp hy) ((hcrit z).mp hz) heq
  refine
    ⟨a, δ, ha, hδ, Φ, hp, hq, fun _ hy => (hΦ hy).1, g, hg, hmg, hinjg, hcount, hcrit, ?_, hkeep,
      hpq, hpband, hqband, hgp, hgq⟩
  intro y hy
  exact hexterior y (fun hh => hy hh.1)

theorem MorseCancellation.exists_signed_chart_of_split_quadratic {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M} {m : ℕ}
    (P : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Model m) M (Model m) ∞) (hp : p ∈ P.source)
    (hcenter : P p = 0) (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (e : ℝ) (σ : Fin m → ℝ)
    (he : e = -1 ∨ e = 1) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hformula : ∀ y ∈ P.source, f y = f p + e * (P y).1 ^ 2 + ∑ i, σ i * (P y).2 i ^ 2) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p,
      c.weights (ρ Option.none) = e ∧ ∀ i, c.weights (ρ (Option.some i)) = σ i := by
  let w : Fin (Module.finrank ℝ E) → ℝ := fun j => (ρ.symm j).elim e σ
  have hwn : w (ρ Option.none) = e := by simp [w]
  have hws (i : Fin m) : w (ρ (Option.some i)) = σ i := by simp [w]
  have hw (j : Fin (Module.finrank ℝ E)) : w j = -1 ∨ w j = 1 := by
    change (ρ.symm j).elim e σ = -1 ∨ (ρ.symm j).elim e σ = 1
    cases h : ρ.symm j with
    | none => exact he
    | some i => exact hσ i
  have hsum (z : Model m) :
    (∑ j, w j * splitEquiv ρ z j ^ 2) = e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2 := by
    rw [split_signed_sum, hwn]
    simp only [hws]
  let C := P.trans (splitEquiv ρ).toDiffeomorph.toPartialDiffeomorph
  have hpC : p ∈ C.source := ⟨hp, Set.mem_univ _⟩
  have hC0 : C p = 0 := by
    change splitEquiv ρ (P p) = 0
    rw [hcenter, map_zero]
  have hCformula (y : M) (hy : y ∈ C.source) : f y = f p + ∑ i, w i * (C y i) ^ 2 := by
    change f y = f p + ∑ i, w i * splitEquiv ρ (P y) i ^ 2
    rw [hsum, hformula y hy.1]
    ring
  let c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p :=
    { weights := w
      signs := hw
      chart := C
      mem_source := hpC
      center := hC0
      equation := hCformula
      inverse_equation := by
        intro z hz
        have h := hCformula (C.symm z) (C.map_target' hz)
        have hr : C (C.symm z) = z := C.right_inv' hz
        rw [hr] at h
        exact h }
  exact ⟨c, hwn, hws⟩

theorem MorseCancellation.exists_signed_chart_of_scaled_cubic_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a δ b : ℝ} (ha : 0 < a) (hδ : 0 < δ) (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f (Φ (e * a, 0)),
      c.weights (ρ Option.none) = e ∧ ∀ i, c.weights (ρ (Option.some i)) = σ i := by
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hgerm
  let T := Smale.PartialChart.restrictSource Φ hW
  have hpT : (e * a, (0 : Fin m → ℝ)) ∈ T.source := ⟨hp, hpW⟩
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain ⟨P, hpP, hP0, -, hP⟩ := exists_endpoint_product_chart σ ha e he2
  let B : Model m ≃L[ℝ] Model m :=
    (LinearEquiv.smulOfNeZero ℝ (Model m) (Real.sqrt δ)
        (Real.sqrt_pos.mpr hδ).ne').toContinuousLinearEquiv
  let C := (T.symm.trans P).trans B.toDiffeomorph.toPartialDiffeomorph
  have hTinv : T.symm (Φ (e * a, 0)) = (e * a, 0) := T.left_inv' hpT
  have hpC : Φ (e * a, 0) ∈ C.source := by
    change (Φ (e * a, 0) ∈ T.target ∧ T.symm (Φ (e * a, 0)) ∈ P.source) ∧ _
    exact ⟨⟨T.map_source' hpT, hTinv.symm ▸ hpP⟩, Set.mem_univ _⟩
  have hC0 : C (Φ (e * a, 0)) = 0 := by
    change B (P (T.symm (Φ (e * a, 0)))) = 0
    rw [hTinv, hP0, map_zero]
  have hvalue : f (Φ (e * a, 0)) = b + δ * cubic σ (-(a ^ 2)) (e * a, 0) := hgerm.self_of_nhds
  have hscale (z : Model m) :
    e * (B z).1 ^ 2 + ∑ i, σ i * (B z).2 i ^ 2 = δ * (e * z.1 ^ 2 + ∑ i, σ i * z.2 i ^ 2) := by
    change e * (Real.sqrt δ * z.1) ^ 2 + (∑ i, σ i * (Real.sqrt δ * z.2 i) ^ 2) = _
    simp only [mul_pow, Real.sq_sqrt hδ.le]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  apply exists_signed_chart_of_split_quadratic C hpC hC0 ρ e σ he hσ
  intro y hy
  have hyT : y ∈ T.target := hy.1.1
  have hzT := T.map_target' hyT
  have hzP : T.symm y ∈ P.source := hy.1.2
  have hfy : f y = b + δ * cubic σ (-(a ^ 2)) (T.symm y) := by
    have hh := hWsub hzT.2
    change f (T (T.symm y)) = b + δ * cubic σ (-(a ^ 2)) (T.symm y) at hh
    have hr : T (T.symm y) = y := T.right_inv' hyT
    rw [hr] at hh
    exact hh
  change
    f y = f (Φ (e * a, 0)) + e * (B (P (T.symm y))).1 ^ 2 + ∑ i, σ i * (B (P (T.symm y))).2 i ^ 2
  rw [hfy, hvalue, hP (T.symm y) hzP]
  have hs := hscale (P (T.symm y))
  linarith

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ) :
    Fintype.card { j // w j = -1 } =
      (if w (ρ Option.none) = -1 then 1 else 0) +
        Fintype.card { i // w (ρ (Option.some i)) = -1 } := by
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← ρ.sum_comp, Fintype.sum_option]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_index_of_scaled_cubic_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a δ b : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (e : ℝ) (he : e = -1 ∨ e = 1)
    (hp : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgerm : f ∘ Φ =ᶠ[𝓝 (e * a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (e * a, 0)) =
      (if e = -1 then 1 else 0) + Fintype.card { i // σ i = -1 } := by
  let ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨c, hce, hcσ⟩ := exists_signed_chart_of_scaled_cubic_germ Φ ρ σ hσ ha hδ e he hp hgerm
  rw [nativeMorseIndex_eq_chart c]
  simp only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace]
  rw [negative_card_split ρ c.weights, hce]
  simp only [hcσ]

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.native_indices_of_cubic_birth_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hdim : 1 + m = Module.finrank ℝ E) (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a δ b : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source)
    (hgp : f ∘ Φ =ᶠ[𝓝 (a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z)
    (hgq : f ∘ Φ =ᶠ[𝓝 (-a, 0)] fun z => b + δ * cubic σ (-(a ^ 2)) z) :
    nativeMorseIndex E f (Φ (a, 0)) = Fintype.card { i // σ i = -1 } ∧
      nativeMorseIndex E f (Φ (-a, 0)) = Fintype.card { i // σ i = -1 } + 1 := by
  constructor
  · have h :=
      native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ 1 (Or.inr rfl)
        (by simpa only [one_mul] using hp) (by simpa only [one_mul] using hgp)
    simpa only [one_mul, if_neg (by norm_num : (1 : ℝ) ≠ -1), zero_add] using h
  · have h :=
      native_index_of_scaled_cubic_germ Φ hdim σ hσ ha hδ (-1) (Or.inl rfl)
        (by simpa only [neg_one_mul] using hq) (by simpa only [neg_one_mul] using hgq)
    simpa [Nat.add_comm] using h

theorem MorseCancellation.exists_transverse_signs_of_count {m k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin m → ℝ, (∀ i, σ i = -1 ∨ σ i = 1) ∧ {i | σ i = -1}.ncard = k := by
  classical
  let σ : Fin m → ℝ := fun i => if i.val < k then -1 else 1
  refine ⟨σ, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < k
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · have heq : {i : Fin m | σ i = -1} = {i : Fin m | i.val < k} := by
      ext i
      by_cases hi : i.val < k <;> norm_num [σ, hi]
    rw [heq, ← Set.fintypeCard_eq_ncard, Fintype.card_subtype]
    simp only [Set.mem_ofPred_eq]
    rw [Fin.card_filter_val_lt, min_eq_right hk]

theorem MorseCancellation.exists_excellent_indexed_morse_birth {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {l u : ℝ}
    (hband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) {k : ℕ} (hk : k < Module.finrank ℝ E) {U : Set M} (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ (g : M → ℝ) (p q : M),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            p ∈ U ∧
              q ∈ U ∧
                nativeMorseIndex E g p = k ∧
                  nativeMorseIndex E g q = k + 1 ∧
                    g p < g q ∧
                      g p ∈ Set.Ioo l u ∧
                        g q ∈ Set.Ioo l u ∧
                          (Smale.ManifoldMorse.criticalPoints E g).ncard =
                              (Smale.ManifoldMorse.criticalPoints E f).ncard + 2 ∧
                            (∀ y,
                                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q) ∧
                              (∀ y, y ∉ U → g =ᶠ[𝓝 y] f) ∧
                                (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
                                  nativeMorseCount E g k = nativeMorseCount E f k + 1 ∧
                                    nativeMorseCount E g (k + 1) =
                                        nativeMorseCount E f (k + 1) + 1 ∧
                                      ∀ j,
                                        j ≠ k →
                                          j ≠ k + 1 →
                                            nativeMorseCount E g j = nativeMorseCount E f j := by
  classical
  let m := Module.finrank ℝ E - 1
  have hdim : 1 + m = Module.finrank ℝ E := by dsimp [m]; omega
  have hkm : k ≤ m := by dsimp [m]; omega
  obtain ⟨σ, hσ, hcard⟩ := exists_transverse_signs_of_count hkm
  have hσne (i : Fin m) : σ i ≠ 0 := by rcases hσ i with h | h <;> rw [h] <;> norm_num
  obtain
    ⟨a, δ, ha, hδ, Φ, hp, hq, hΦ, g, hg, hmg, hinjg, hcount, hcrit, hexterior, hkeep, hpq, hpband,
      hqband, hgp, hgq⟩ :=
    exists_excellent_native_morse_birth hf hm hinj hband hx hdim σ hσne hU hxU
  obtain ⟨hip, hiq⟩ := native_indices_of_cubic_birth_germs Φ hdim σ hσ ha hδ hp hq hgp hgq
  have hc : Fintype.card { i // σ i = -1 } = k := (Set.fintypeCard_eq_ncard _).trans hcard
  rw [hc] at hip hiq
  have hpnot : Φ (a, 0) ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro h
    have hv : g (Φ (a, 0)) = f (Φ (a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hpband) h
  have hqnot : Φ (-a, 0) ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro h
    have hv : g (Φ (-a, 0)) = f (Φ (-a, 0)) := (hkeep _ h).self_of_nhds
    exact hband _ (hv ▸ hqband) h
  have hreverse (y : M) :
    y ∈ Smale.ManifoldMorse.criticalPoints E f ↔
      y ∈ Smale.ManifoldMorse.criticalPoints E g ∧ y ≠ Φ (a, 0) ∧ y ≠ Φ (-a, 0) := by
    rw [hcrit]
    constructor
    · intro hy
      exact ⟨Or.inl hy, fun h => hpnot (h ▸ hy), fun h => hqnot (h ▸ hy)⟩
    · rintro ⟨hy | hp' | hq', hnp, hnq⟩
      · exact hy
      · exact False.elim (hnp hp')
      · exact False.elim (hnq hq')
  have hpcrit := (hcrit (Φ (a, 0))).mpr (Or.inr (Or.inl rfl))
  have hqcrit := (hcrit (Φ (-a, 0))).mpr (Or.inr (Or.inr rfl))
  have hneq : Φ (a, 0) ≠ Φ (-a, 0) := fun h => hpq.ne (congrArg g h)
  obtain ⟨hck, hck', hcothers⟩ :=
    nativeMorseCount_adjacent_pair (Smale.ManifoldMorse.finite_criticalPoints hg hmg) hpcrit
      hqcrit hneq hreverse (fun y hy => (hkeep y hy).symm) hip hiq
  exact
    ⟨g, Φ (a, 0), Φ (-a, 0), hg, hmg, hinjg, hΦ (Φ.map_source' hp), hΦ (Φ.map_source' hq), hip,
      hiq, hpq, hpband, hqband, hcount, hcrit, hexterior, hkeep, hck.symm, hck'.symm,
      fun j hj hj' => (hcothers j hj hj').symm⟩

theorem MorseCancellation.superlevel_bound_of_critical_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} (hboundary : ∀ y, f y = l → g y = l)
    (hcritical : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    ∀ x, l ≤ f x → l ≤ g x := by
  intro x hx
  have hK : IsCompact {y : M | l ≤ f y} := (isClosed_le continuous_const hf).isCompact
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hg.continuous.continuousOn
  have hgp : l ≤ g p := by
    by_cases hlt : l < f p
    · have hlocal : IsLocalMin g p := by
        filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hlt] with y hy
        exact hmin hy.le
      exact hcritical p (Smale.ManifoldMorse.mem_criticalPoints_of_localMin hg hlocal) hp
    · have heq : f p = l := le_antisymm (le_of_not_gt hlt) hp
      exact (hboundary p heq).ge
  exact hgp.trans (hmin hx)

theorem MorseCancellation.birth_preserves_lower_levels {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l : ℝ} {U : Set M} {p q : M} (hU : U ⊆ {y : M | l < f y})
    (hexterior : ∀ y, y ∉ U → g =ᶠ[𝓝 y] f)
    (hkeep : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f)
    (hcrit :
      ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g,
        y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hp : l ≤ g p) (hq : l ≤ g q) {a : ℝ} (ha : a < l) :
    (∀ y, g y = a ↔ f y = a) ∧ (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) := by
  have hout (y : M) (hy : f y ≤ l) : y ∉ U := fun h => (hU h).not_ge hy
  have hbound : ∀ y, l ≤ f y → l ≤ g y := by
    apply superlevel_bound_of_critical_bound hf hg
    · intro y hy
      exact (hexterior y (hout y hy.le)).self_of_nhds.trans hy
    · intro y hy hfy
      rcases hcrit y hy with hold | rfl | rfl
      · rw [(hkeep y hold).self_of_nhds]
        exact hfy
      · exact hp
      · exact hq
  refine ⟨?_, fun y hy => hexterior y (hout y (hy.trans ha.le))⟩
  intro y
  constructor
  · intro hgy
    have hfy : f y ≤ l := by
      by_contra h
      have hh := hbound y (le_of_not_ge h)
      rw [hgy] at hh
      exact ha.not_ge hh
    exact ((hexterior y (hout y hfy)).self_of_nhds).symm.trans hgy
  · intro hfy
    exact (hexterior y (hout y (hfy ▸ ha.le))).self_of_nhds.trans hfy

def MorseCancellation.equalLevelDiffeomorph {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {f g : M → ℝ} {a : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a) :
    let _ := Smale.RegularLevel.chartedSpace hf hfr
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
      { y : M // f y = a } { y : M // g y = a } ∞ := by
  let _ := Smale.RegularLevel.chartedSpace hf hfr
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let F : { y : M // f y = a } → { y : M // g y = a } := fun y => ⟨y, (heq y).mpr y.property⟩
  let G : { y : M // g y = a } → { y : M // f y = a } := fun y => ⟨y, (heq y).mp y.property⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      contMDiff_toFun :=
        (Smale.RegularLevel.contMDiff_iff_inclusion hg hgr 𝓘(ℝ, Smale.RegularLevel.Model E) F).mpr
          (Smale.RegularLevel.contMDiff_inclusion hf hfr)
      contMDiff_invFun :=
        (Smale.RegularLevel.contMDiff_iff_inclusion hf hfr 𝓘(ℝ, Smale.RegularLevel.Model E) G).mpr
          (Smale.RegularLevel.contMDiff_inclusion hg hgr) }

theorem MorseCancellation.regular_level_of_retained_critical_germs {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {p q : M}
    (hcrit :
      ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g,
        y ∈ Smale.ManifoldMorse.criticalPoints E f ∨ y = p ∨ y = q)
    (hkeep : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 y] f) (hp : a < g p)
    (hq : a < g q) : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g := by
  intro y hy hcy
  rcases hcrit y hcy with hold | rfl | rfl
  · exact hfr y (((hkeep y hold).self_of_nhds).symm.trans hy) hold
  · exact hp.ne' hy
  · exact hq.ne' hy

theorem MorseCancellation.isotopicToIdentity_conj {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
    (e : Diffeomorph I J M N ∞) {d : Diffeomorph I I M M ∞}
    (hd : Smale.SupportedDiffeomorph.IsotopicToIdentity d) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity ((e.symm.trans d).trans e) := by
  obtain ⟨A, hA, hA0, hA1, hslices⟩ := hd
  refine
    ⟨(fun p => e (A (p.1, e.symm p.2))),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hA0, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (d (e.symm y))
    rw [hA1]
  · intro t
    obtain ⟨dₜ, hdₜ⟩ := hslices t
    refine ⟨(e.symm.trans dₜ).trans e, ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (dₜ (e.symm y))
    rw [hdₜ]

theorem MorseCancellation.exists_equal_level_circle_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) →
                ∃ P :
                  Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                    { y : M // g y = a } { y : M // g y = a } ∞,
                  Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := Smale.RegularLevel.chartedSpace hf hfr
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.isManifold hf hfr
  let _ := Smale.RegularLevel.isManifold hg hgr
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  let L := equalLevelDiffeomorph hf hg hfr hgr heq
  let γ' : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨L.symm ∘ γ, L.symm.continuous.comp γ.continuous⟩
  let δ' : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨L.symm ∘ δ, L.symm.continuous.comp δ.continuous⟩
  have hγ' : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ' := L.symm.contMDiff.comp hγ
  have hδ' : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ' := L.symm.contMDiff.comp hδ
  have hderiv (κ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a }))
    (hk : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ κ)
    (hkd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) κ z)) (z) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) (L.symm ∘ κ) z) := by
    rw [mfderiv_comp z (L.symm.contMDiff.mdifferentiableAt (by simp))
        (hk.mdifferentiableAt (by simp))]
    exact (L.symm.mfderivToContinuousLinearEquiv (by simp) (κ z)).injective.comp (hkd z)
  obtain ⟨Q, hQ, hformula⟩ :=
    exists_native_middle_level_circle_isotopy S hf e hdim hfr hhigh hlow γ' δ' hγ'
      (L.symm.injective.comp hγi) (hderiv γ hγ hγd) hδ' (L.symm.injective.comp hδi)
      (hderiv δ hδ hδd)
  refine ⟨(L.symm.trans Q).trans L, isotopicToIdentity_conj L hQ, ?_⟩
  intro z
  change L (Q (γ' z)) = δ z
  rw [hformula]
  exact L.apply_symm_apply (δ z)

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_new_attaching_circle_placement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ q : Smale.ManifoldMorse.criticalPoints E f, a ≤ f q → 3 ≤ nativeMorseIndex E f q)
    (hlow : ∀ q : Smale.ManifoldMorse.criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ 3)
    (p : Smale.ManifoldMorse.criticalPoints E g)
    [Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 1 + 1)] (hap : a < g p)
    (hgap : ∀ q : Smale.ManifoldMorse.criticalPoints E g, g q < g p → g q < a)
    (δ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
      Function.Injective δ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) →
          ∃ Γ : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a }),
            ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ Γ ∧
              Function.Injective Γ ∧
                (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z)) ∧
                  (∀ x,
                      x ∈ Set.range Γ ↔
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val)) ∧
                    ∃ P :
                      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E)
                        𝓘(ℝ, Smale.RegularLevel.Model E) { y : M // g y = a } { y : M // g y = a }
                        ∞,
                      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
                        (∀ z, P (Γ z) = δ z) ∧
                          ∀ x,
                            Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val) ↔
                              P x ∈ Set.range δ := by
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.chartedSpace hg (T.data p).lower_regular
  let _ := Smale.RegularLevel.isManifold hg hgr
  let _ := Smale.RegularLevel.isManifold hg (T.data p).lower_regular
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
      Function.Injective δ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) → _
  intro hδ hδi hδd
  obtain ⟨σ, D, -, -, Γ, hΓ, hΓi, hΓd, -, -, hflow⟩ :=
    T.exists_attaching_circle_lower_transport hg p hgr hap hgap
  have hrange (x : { y : M // g y = a }) :
    x ∈ Set.range Γ ↔ Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p.val) :=
    T.transported_attaching_range_iff hg p hgr σ σ.surjective Γ hflow x
  obtain ⟨P, hP, hformula⟩ :=
    exists_equal_level_circle_isotopy S hf hg e hdim hfr hgr heq hhigh hlow Γ δ hΓ hΓi hΓd hδ hδi
      hδd
  refine ⟨Γ, hΓ, hΓi, hΓd, hrange, P, hP, hformula, ?_⟩
  intro x
  rw [← hrange]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, (hformula z).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, P.injective ((hformula z).trans hz)⟩

theorem MorseCancellation.unit_level_count_of_circle_placement {M X : Type*} [TopologicalSpace M]
    (F : Flow ℝ M) {f : M → ℝ} {a : ℝ} {p q : M} (P : { y : M // f y = a } ≃ { y : M // f y = a })
    (δ : X → { y : M // f y = a }) (z₀ : X)
    (hplacement : ∀ x, Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ↔ P x ∈ Set.range δ)
    (hsingle : ∀ z, Filter.Tendsto (fun t => F t (δ z).val) Filter.atTop (𝓝 q) ↔ z = z₀) :
    {x : { y : M // f y = a } |
          Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
            Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)}.ncard =
      1 := by
  have heq :
    {x : { y : M // f y = a } |
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p) ∧
          Filter.Tendsto (fun t => F t (P x).val) Filter.atTop (𝓝 q)} =
      {P.symm (δ z₀)} := by
    ext x
    constructor
    · rintro ⟨hx, hforward⟩
      obtain ⟨z, hz⟩ := (hplacement x).mp hx
      have hz0 : z = z₀ := (hsingle z).mp (hz.symm ▸ hforward)
      apply Set.mem_singleton_iff.mpr
      apply P.injective
      rw [P.apply_symm_apply, ← hz, hz0]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      refine ⟨(hplacement _).mpr ⟨z₀, (P.apply_symm_apply _).symm⟩, ?_⟩
      rw [P.apply_symm_apply]
      exact (hsingle z₀).mpr rfl
  rw [heq]
  exact Set.ncard_singleton _

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_handle_trade_transverse_level_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    [Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    let _ := Smale.RegularLevel.chartedSpace hg hgr
    ∃ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // g y = a } { y : M // g y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        {x : { y : M // g y = a } |
                Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 r.val) ∧
                  Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 ∧
          ∃ (α : C(Smale.Hemisphere.Sphere 1, { y : M // g y = a })) (z₀ :
            Smale.Hemisphere.Sphere 1) (β :
            Metric.sphere (0 : (T.data q).chart.PositiveCoordinates) 1 → { y : M // g y = a }) (v
            : Metric.sphere (0 : (T.data q).chart.PositiveCoordinates) 1),
            ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α ∧
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v ∧
                β v = α z₀ ∧
                  Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) α β
                      z₀ v ∧
                    (∀ z, Filter.Tendsto (fun t => T.flow t (α z).val) Filter.atBot (𝓝 r.val)) ∧
                      (∀ᶠ w in 𝓝 v,
                          Filter.Tendsto (fun t => T.flow t (P (β w)).val) Filter.atTop
                            (𝓝 q.val)) ∧
                        ∀ x : { y : M // g y = a },
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 r.val) →
                            Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop (𝓝 m.val) ∨
                              Filter.Tendsto (fun t => T.flow t (P x).val) Filter.atTop
                                (𝓝 q.val) := by
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.isManifold hg hgr
  let _ : Fact (Module.finrank ℝ (T.data r).chart.NegativeCoordinates = 1 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data r).chart).symm.trans hr⟩
  obtain ⟨δ, hδ, hδi, hδd, z₀, v, β₀, hβ₀, hcross₀, htrans₀, hβbasin, hsingle, hendpoints⟩ :=
    T.exists_transverse_middle_belt_loop hg hdim m q hm hq u hbranches hqa hgr hnewlow
  obtain ⟨α, hα, -, -, hrange, P, hP, hplace, hplacement⟩ :=
    exists_new_attaching_circle_placement S T hf hg e hdim hfr hgr heq hhigh hlow r har hgap δ hδ
      hδi hδd
  obtain ⟨β, hβ, hcross, htrans, hPβ⟩ :=
    exists_transverse_sheet_of_circle_placement P (hα.mdifferentiableAt (by simp)) hβ₀ hplace
      hcross₀ htrans₀
  refine
    ⟨P, hP, unit_level_count_of_circle_placement T.flow P.toEquiv δ z₀ hplacement hsingle, α, z₀,
      β, v, hα, hβ, hcross, htrans, ?_, ?_, ?_⟩
  · intro z
    exact (hrange (α z)).mp ⟨z, rfl⟩
  · filter_upwards [hβbasin] with w hw
    rw [hPβ w]
    exact hw
  · intro x hx
    obtain ⟨z, hz⟩ := (hplacement x).mp hx
    rw [← hz]
    exact hendpoints z

theorem AdaptedWindows.realize_unit_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∃ (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (G : Flow ℝ M) (z : { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
              (∀ x, IsMIntegralCurve (fun t => G t x) V) ∧
                (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0) ∧
                  (∀ x,
                      x ∉ Smale.ManifoldMorse.criticalPoints E f →
                        mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                    (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, V y = S.field y) ∧
                      Filter.Tendsto (fun t => G t z.val) Filter.atBot (𝓝 p.val) ∧
                        Filter.Tendsto (fun t => G t z.val) Filter.atTop (𝓝 q.val) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 p.val) →
                                Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 q.val) →
                                  ∃ t, G t z.val = x) ∧
                            (∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 y)) ∧
                              ∀ (x : { y : M // f y = a }) y,
                                Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 y) ↔
                                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop
                                    (𝓝 y) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount
  obtain ⟨z₀, -⟩ := Set.ncard_eq_one.mp hcount
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level ha
  obtain
    ⟨r, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband ha z₀ P hP
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val P
      (fun x y => (hgeometry x).2.1 y) (fun x y => (hgeometry x).2.2 y) hend hleft hright
  obtain ⟨z, hzb, hzf, hunique⟩ :=
    Degree.FlowSuspension.exists_unique_connection_of_unit_level_count S.flow G hf.continuous hpa
      hqa P (fun x => hback x p.val) (fun x => hforward x q.val) hcount
  exact
    ⟨V, G, z, hV, hG, (fun x hx => (hzero x).mpr (S.zero x hx)), hdesc, hgerms, hzb, hzf, hunique,
      hback, hforward⟩

theorem AdaptedWindows.realize_unit_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ} (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          ∀ (α : X → { y : M // f y = a }) (β : Y → { y : M // f y = a }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, Smale.RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, Smale.RegularLevel.Model E) β y →
                β y = α x →
                  Smale.NativeTransversality.At I I' 𝓘(ℝ, Smale.RegularLevel.Model E) α β x y →
                    (∀ᶠ u in 𝓝 x,
                        Filter.Tendsto (fun t => S.flow t (α u).val) Filter.atBot (𝓝 p.val)) →
                      (∀ᶠ u in 𝓝 y,
                          Filter.Tendsto (fun t => S.flow t (P (β u)).val) Filter.atTop
                            (𝓝 q.val)) →
                        ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
                          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                              (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
                            (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
                              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0) ∧
                                (∀ z,
                                    z ∉ Smale.ManifoldMorse.criticalPoints E f →
                                      mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
                                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ w in 𝓝 z, V w = S.field w) ∧
                                    Filter.Tendsto (fun t => G t (α x).val) Filter.atBot
                                        (𝓝 p.val) ∧
                                      Filter.Tendsto (fun t => G t (α x).val) Filter.atTop
                                          (𝓝 q.val) ∧
                                        (∀ z,
                                            Filter.Tendsto (fun t => G t z) Filter.atBot
                                                (𝓝 p.val) →
                                              Filter.Tendsto (fun t => G t z) Filter.atTop
                                                  (𝓝 q.val) →
                                                ∃ t, G t (α x).val = z) ∧
                                          (∀ (z : { w : M // f w = a }) w,
                                              Filter.Tendsto (fun t => G t z.val) Filter.atBot
                                                  (𝓝 w) ↔
                                                Filter.Tendsto (fun t => S.flow t z.val)
                                                  Filter.atBot (𝓝 w)) ∧
                                            (∀ (z : { w : M // f w = a }) w,
                                                Filter.Tendsto (fun t => G t z.val) Filter.atTop
                                                    (𝓝 w) ↔
                                                  Filter.Tendsto (fun t => S.flow t (P z).val)
                                                    Filter.atTop (𝓝 w)) ∧
                                              let C : X × ℝ → M := fun u => G u.2 (α u.1).val
                                              let D : Y × ℝ → M := fun u => G u.2 (β u.1).val
                                              MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) C
                                                  (x, 0) ∧
                                                MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) D
                                                    (y, 0) ∧
                                                  C (x, 0) = (α x).val ∧
                                                    D (y, 0) = (α x).val ∧
                                                      (∀ᶠ u in 𝓝 (x, (0 : ℝ)),
                                                          Filter.Tendsto (fun t => G t (C u))
                                                            Filter.atBot (𝓝 p.val)) ∧
                                                        (∀ᶠ u in 𝓝 (y, (0 : ℝ)),
                                                            Filter.Tendsto (fun t => G t (D u))
                                                              Filter.atTop (𝓝 q.val)) ∧
                                                          Smale.NativeTransversality.At
                                                            (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
                                                            𝓘(ℝ, E) C D (x, 0) (y, 0) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf ha
  change
    ∀ P :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { y : M // f y = a } { y : M // f y = a } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P →
        {x : { y : M // f y = a } |
                Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => S.flow t (P x).val) Filter.atTop (𝓝 q.val)}.ncard =
            1 →
          _
  intro P hP hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨V, G, z, hV, hG, hzero, hdesc, hgerms, -, -, hunique, hback, hforward⟩ :=
    S.realize_unit_level_isotopy hf p q hpa hqa ha P hP hcount
  have hαG : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => G t (α u).val) Filter.atBot (𝓝 p.val) := by
    filter_upwards [hαbasin] with u hu
    exact (hback (α u) p.val).mpr hu
  have hβG : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => G t (β u).val) Filter.atTop (𝓝 q.val) := by
    filter_upwards [hβbasin] with u hu
    exact (hforward (β u) q.val).mpr hu
  have hxforward : Filter.Tendsto (fun t => G t (α x).val) Filter.atTop (𝓝 q.val) := by
    have hh := hβG.self_of_nhds
    rwa [hcross] at hh
  obtain ⟨s, hs⟩ := hunique (α x).val hαG.self_of_nhds hxforward
  have huniq (w : M) (hwb : Filter.Tendsto (fun t => G t w) Filter.atBot (𝓝 p.val))
    (hwf : Filter.Tendsto (fun t => G t w) Filter.atTop (𝓝 q.val)) : ∃ t, G t (α x).val = w := by
    obtain ⟨t, ht⟩ := hunique w hwb hwf
    refine ⟨t - s, ?_⟩
    rw [← hs, ← G.map_add, sub_add_cancel, ht]
  refine
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hαG.self_of_nhds, hxforward, huniq, hback, hforward, ?_⟩
  exact
    Degree.FlowSuspension.native_transverse_basin_tubes_of_level_maps hf ha hV G hG
      (fun w hw => hdesc w (ha w hw)) α β x y hα hβ hcross htrans hαG hβG

theorem MorseCancellation.no_other_connections_of_two_level_endpoints {M : Type*} [TopologicalSpace M]
    [T2Space M] (F : Flow ℝ M) {f : M → ℝ} (hf : Continuous f) {C : Set M} (hinj : Set.InjOn f C)
    (p q r : C) {a : ℝ} (hpa : a < f p) (hgap : ∀ j : C, f j < f p → f j < a)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hends :
      ∀ x : { y : M // f y = a },
        Filter.Tendsto (fun t => F t x.val) Filter.atBot (𝓝 p.val) →
          Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 q.val) ∨
            Filter.Tendsto (fun t => F t x.val) Filter.atTop (𝓝 r.val)) :
    ∀ j : C,
      j ≠ p →
        j ≠ q →
          j ≠ r →
            ∀ x,
              ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p.val) ∧
                  Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)) := by
  intro j hjp hjq hjr x hx
  have hforwardHeight := hf.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f p :=
    (hmono x).le_of_tendsto hforwardHeight 0 |>.trans ((hmono x).ge_of_tendsto hbackwardHeight 0)
  have hlt : f j < f p :=
    lt_of_le_of_ne hle (fun h => hjp (Subtype.ext (hinj j.property p.property h)))
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits F hf hx.1 hx.2 hpa
      (hgap j hlt)
  let z : { y : M // f y = a } := ⟨F t x, ht⟩
  have hzb : Filter.Tendsto (fun s => F s z.val) Filter.atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff F t x p.val).mpr hx.1
  have hzf : Filter.Tendsto (fun s => F s z.val) Filter.atTop (𝓝 j.val) :=
    (flow_time_atTop_limit_iff F t x j.val).mpr hx.2
  rcases hends z hzb with hq | hr
  · exact hjq (Subtype.ext (tendsto_nhds_unique hzf hq))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzf hr))

theorem MorseCancellation.cancel_transverse_pair_after_flow_preserving_descent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} {m : ℕ} {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB]
    {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X]
    [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hdim : Module.finrank ℝ E = m + 1) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : Smale.ManifoldMorse.criticalPoints E f) (hrp : f r < f p) (hpq : f p < f q)
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    (hnoconnection :
      ∀ j : Smale.ManifoldMorse.criticalPoints E f,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val)))
    {z : M} (hzp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p.val))
    (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q.val))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val) → ∃ t, F t z = x)
    {α : X → M} {β : Y → M} {x : X} {y : Y} (hα : MDifferentiableAt I 𝓘(ℝ, E) α x)
    (hβ : MDifferentiableAt I' 𝓘(ℝ, E) β y) (hα0 : α x = z) (hβ0 : β y = z)
    (hαbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (α u)) Filter.atBot (𝓝 q.val))
    (hβbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (β u)) Filter.atTop (𝓝 p.val))
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) α β x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E g,
                  nativeMorseIndex E g w = nativeMorseIndex E f w := by
  obtain ⟨h, hh, hmh, hcrit, hinjh, -, -, hpqh, hconsecutive, hdesch, hmodelsh, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf hm hinj hV F hF hzero hdesc hmodels p r q hrp hpq
      hnoconnection
  have hpcrit : p.val ∈ Smale.ManifoldMorse.criticalPoints E h := hcrit.symm ▸ p.property
  have hqcrit : q.val ∈ Smale.ManifoldMorse.criticalPoints E h := hcrit.symm ▸ q.property
  obtain ⟨cp, hcp⟩ := hmodelsh p.val hpcrit
  obtain ⟨cq, hcq⟩ := hmodelsh q.val hqcrit
  have hidx :
    Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
    rw [← nativeMorseIndex_eq_chart cq, ← nativeMorseIndex_eq_chart cp, hindices q.val q.property,
      hindices p.val p.property]
    exact hindex
  have hcard :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using hidx
  obtain ⟨W⟩ := Smale.ManifoldMorse.nonempty_surgeryWindows hh hmh hinjh
  let ph : Smale.ManifoldMorse.criticalPoints E h := ⟨p.val, hpcrit⟩
  let qh : Smale.ManifoldMorse.criticalPoints E h := ⟨q.val, hqcrit⟩
  have hconsecutiveh : ∀ s : Smale.ManifoldMorse.criticalPoints E h, ¬(h ph < h s ∧ h s < h qh) :=
    by
    intro s hs
    exact hconsecutive ⟨s.val, hcrit ▸ s.property⟩ hs
  have hpair := surgery_pair_band_isolation W ph qh hconsecutiveh
  obtain ⟨g, hg, hmg, hcount, hcritg, hexterior⟩ :=
    cancel_unique_connection_of_transverse_basin_sheets cp cq hh hmh hdim hcard V hV
      (fun w hw => hzero w (hcrit ▸ hw)) hdesch F hF hinjh hpcrit hqcrit hpqh
      (W.lower_lt_value ph) (W.value_lt_upper qh) hpair hzp hzq hunique hcp hcq hα hβ hα0 hβ0
      hαbasin hβbasin htrans
  have hkeep := surviving_critical_germs_of_pair_band hpair hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinjh (fun w hw => ((hcritg w).mp hw).1) hkeep
  rw [hcrit] at hcount
  refine ⟨g, hg, hmg, hinjg, hcount, ?_, ?_⟩
  · intro w
    rw [hcritg w, hcrit]
  · intro w hw
    exact
      (nativeMorseIndex_congr_germ (hkeep w hw)).trans (hindices w (hcrit ▸ ((hcritg w).mp hw).1))

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_one_two_pair_at_preserved_middle_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f) (T : AdaptedWindows E g)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (u : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 m.val))
    (hqa : T.toSurgeryWindows.upper q ≤ a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E h ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by
  let _ := Smale.RegularLevel.chartedSpace hg hgr
  let _ := Smale.RegularLevel.isManifold hg hgr
  have hnegq : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨P, hP, hcount, α, z₀, β, v, hα, hβ, hcross, htrans, hαbasin, hβbasin, hends⟩ :=
    exists_handle_trade_transverse_level_data S T hf hg e hdim hfr hgr heq hhigh hlow m q r hm hq
      hr u hbranches hqa har hgap hnewlow
  have hqcut : g q < a := (T.toSurgeryWindows.value_lt_upper q).trans_le hqa
  obtain
    ⟨V, G, hV, hG, hzero, hdesc, hgerms, hbackr, hforwardq, hunique, hback, hforward, htubes⟩ :=
    T.realize_unit_transverse_level_isotopy hg r q har hqcut hgr P hP hcount α β z₀ v
      (hα.mdifferentiableAt (by simp)) hβ hcross htrans (Filter.Eventually.of_forall hαbasin)
      hβbasin
  have hendsG (x : { y : M // g y = a })
    (hx : Filter.Tendsto (fun t => G t x.val) Filter.atBot (𝓝 r.val)) :
    Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 q.val) ∨
      Filter.Tendsto (fun t => G t x.val) Filter.atTop (𝓝 m.val) := by
    have hh := hends x ((hback x r.val).mp hx)
    exact (hh.imp ((hforward x m.val).mpr) ((hforward x q.val).mpr)).symm
  have hnoconnection :=
    no_other_connections_of_two_level_endpoints G hg.continuous T.distinct r q m har hgap
      (Smale.FlowConstruction.antitone_flow_height hg G hG hzero hdesc) hendsG
  have hmodels :
    ∀ x ∈ Smale.ManifoldMorse.criticalPoints E g,
      ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    refine ⟨(T.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, T.critical_model_germ ⟨x, hx⟩] with y hy hyt
    exact hy.trans hyt
  have hmq : g m < g q :=
    (T.forward_limit_below_regular_level hg (T.data q).lower_regular
          ((T.data q).surgery.attachingSphere u) (hbranches u)).trans
      (T.toSurgeryWindows.lower_lt_value q)
  obtain ⟨hC, hD, hC0, hD0, hCb, hDb, htransM⟩ := htubes
  exact
    cancel_transverse_pair_after_flow_preserving_descent hg hmg T.distinct (m := 5) (by omega) hV
      G hG hzero hdesc hmodels q m r hmq (hqcut.trans har) (by omega) hnoconnection hforwardq
      hbackr hunique hC hD hC0 hD0 hCb hDb htransM

theorem MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) : ∃ u v : Metric.sphere (0 : V) 1, u ≠ v := by
  obtain ⟨L⟩ :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := Degree.UnitSphereEquiv.homeomorph L
  let u : Metric.sphere (0 : ℝ) 1 := ⟨1, by simp⟩
  let v : Metric.sphere (0 : ℝ) 1 := ⟨-1, by simp⟩
  refine ⟨e.symm u, e.symm v, ?_⟩
  intro heq
  have hh : u = v := e.symm.injective heq
  have hval : (1 : ℝ) = -1 := congrArg Subtype.val hh
  norm_num at hval

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.place_one_handle_in_unique_minimum_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f r = 0 → r = p) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ d :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        (S.data q).LowerLevel (S.data q).LowerLevel ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity d ∧
        f p < S.toSurgeryWindows.lower q ∧
          ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
            Filter.Tendsto (fun t => S.flow t (d ((S.data q).surgery.attachingSphere w)).val)
              Filter.atTop (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).lower_regular
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one hi
  let α := (S.data q).surgery.attachingSphere
  have hxy : α u ≠ α v := fun h => huv ((S.data q).attaching_isClosedEmbedding.injective h)
  obtain ⟨d, hd, ⟨r, hr, hru⟩, ⟨s, hs, hsv⟩⟩ :=
    MorseCancellation.exists_isotopic_two_points_in_dense (J := 𝓘(ℝ, Smale.RegularLevel.Model E))
      (S.dense_regular_level_minimum_basins hf (S.data q).lower_regular) hxy
  have hpu : Filter.Tendsto (fun t => S.flow t (d (α u)).val) Filter.atTop (𝓝 p.val) :=
    hunique r hr ▸ hru
  have hpv : Filter.Tendsto (fun t => S.flow t (d (α v)).val) Filter.atTop (𝓝 p.val) :=
    hunique s hs ▸ hsv
  refine
    ⟨d, hd, S.forward_limit_below_regular_level hf (S.data q).lower_regular (d (α u)) hpu, ?_⟩
  intro w
  rcases MorseCancellation.unitSphere_eq_two_points_of_finrank_one hi u v huv w with rfl | rfl
  · exact hpu
  · exact hpv

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.realize_unique_minimum_one_handle_branches {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hone : MorseCancellation.nativeMorseIndex E f q = 1)
    (hunique :
      ∀ r : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancellation.nativeMorseIndex E f r = 0 → r = p) :
    ∃ T : AdaptedWindows E f,
      (∀ r : Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 r.val, T.field x = S.field x) ∧
        (∀ r, (T.data r).chart = (S.data r).chart) ∧
          (∀ w : Metric.sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
              Filter.Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere w).val)
                Filter.atTop (𝓝 p.val)) ∧
            ∀ r : Smale.ManifoldMorse.criticalPoints E f,
              r ≠ q →
                r ≠ p →
                  ∀ x,
                    ¬(Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 q.val) ∧
                        Filter.Tendsto (fun t => T.flow t x) Filter.atTop (𝓝 r.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨d, hd, hpq, hall⟩ := S.place_one_handle_in_unique_minimum_basin hf p q hone hunique
  have hi : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  obtain ⟨u, v, huv⟩ := MorseCancellation.exists_distinct_unitSphere_points_of_finrank_one hi
  obtain ⟨l, b, hl, hb, hband⟩ := S.regular_interval_around_level (S.data q).lower_regular
  obtain
    ⟨ρ, C, W, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzero, hdesc, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hb hband (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) d hd
  have hVz : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0 := fun x hx =>
    (hzero x).mpr (S.zero x hx)
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val d
      (fun x z => (hgeometry x).2.1 z) (fun x z => (hgeometry x).2.2 z) hend hleft hright
  have hbq (x : (S.data q).LowerLevel) :
    Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
      x ∈ Set.range (S.data q).surgery.attachingSphere :=
    (hback x q.val).trans (S.attaching_basin_iff hf q x)
  have hends (w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
      (𝓝 p.val) :=
    (hforward _ p.val).mpr (hall w)
  have hno (r : Smale.ManifoldMorse.criticalPoints E f) (hrq : r ≠ q) (hrp : r ≠ p) (x : M) :
    ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
        Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 r.val)) := by
    intro hx
    have hmono := Smale.FlowConstruction.antitone_flow_height hf G hG hVz hdesc x
    have hle : f r ≤ f q :=
      (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.2) 0).trans
        (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hx.1) 0)
    have hrq' : f r < f q :=
      lt_of_le_of_ne hle (fun h => hrq (Subtype.ext (S.distinct r.property q.property h)))
    have hrlow : f r < S.toSurgeryWindows.lower q :=
      (S.toSurgeryWindows.value_lt_upper r).trans (S.separated r q hrq')
    obtain ⟨t, ht⟩ :=
      Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits G hf.continuous hx.1 hx.2
        (S.toSurgeryWindows.lower_lt_value q) hrlow
    let z : (S.data q).LowerLevel := ⟨G t x, ht⟩
    have hzq : Filter.Tendsto (fun s => G s z) Filter.atBot (𝓝 q.val) :=
      (MorseCancellation.flow_time_atBot_limit_iff G t x q.val).mpr hx.1
    have hzr : Filter.Tendsto (fun s => G s z) Filter.atTop (𝓝 r.val) :=
      (MorseCancellation.flow_time_atTop_limit_iff G t x r.val).mpr hx.2
    obtain ⟨w, hw⟩ := (hbq z).mp hzq
    have hpz := hends w
    rw [hw] at hpz
    exact hrp (Subtype.ext (tendsto_nhds_unique hzr hpz))
  have hmodel (r : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ x in 𝓝 r.val, V x = (S.data r).chart.descentField x := by
    filter_upwards [hgerms r r.property, S.critical_model_germ r] with x hx hxs
    exact hx.trans hxs
  obtain ⟨T, hfield, hflow, hchart⟩ :=
    MorseCancellation.exists_adapted_windows_with_prescribed_flow hf hm S.distinct hV G hG hVz hdesc
      (fun r => (S.data r).chart) hmodel
  refine ⟨T, ?_, hchart, ?_, ?_⟩
  · intro r
    rw [hfield]
    exact hgerms r r.property
  · intro w
    let z := (T.data q).surgery.attachingSphere w
    have hzq : Filter.Tendsto (fun t => T.flow t z.val) Filter.atBot (𝓝 q.val) :=
      (T.attaching_basin_iff hf q z).mpr ⟨w, rfl⟩
    obtain ⟨r₀, hr₀, r, hr, -, hrlim, hheight⟩ :=
      Degree.FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
        T.descent T.distinct z.val
    have hrq : (⟨r, hr⟩ : Smale.ManifoldMorse.criticalPoints E f) ≠ q := by
      intro heq
      have hlt := (hheight ((T.data q).lower_regular z.val z.property)).1
      have hrval : r = q.val := congrArg Subtype.val heq
      rw [hrval, z.property] at hlt
      nlinarith [sq_nonneg (T.data q).radius]
    have hrp : (⟨r, hr⟩ : Smale.ManifoldMorse.criticalPoints E f) = p := by
      by_contra hne
      apply hno ⟨r, hr⟩ hrq hne z.val
      rw [hflow] at hzq hrlim
      exact ⟨hzq, hrlim⟩
    exact (congrArg Subtype.val hrp) ▸ hrlim
  · intro r hrq hrp x
    rw [hflow]
    exact hno r hrq hrp x

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.cancel_one_two_pair_at_unchanged_cut_of_unique_minimum {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g)) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hfr : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : Smale.ManifoldMorse.criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g r → g z < a)
    (hnewlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard + 2 =
                (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
              (∀ w,
                  w ∈ Smale.ManifoldMorse.criticalPoints E h ↔
                    w ∈ Smale.ManifoldMorse.criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
                ∀ w ∈ Smale.ManifoldMorse.criticalPoints E h,
                  nativeMorseIndex E h w = nativeMorseIndex E g w := by
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨U, -, -, hbranchesU, -⟩ :=
    T₀.realize_unique_minimum_one_handle_branches hg hmg m q hq hminimum
  obtain ⟨T, -, hflow, -, hbelow, -⟩ := U.exists_same_flow_windows_avoiding_level hg hmg hgr
  have hbranches := U.attaching_branches_of_same_flow T hg m q hflow hbranchesU
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hneg
  exact
    cancel_one_two_pair_at_preserved_middle_cut S T hf hg hmg e hdim hfr hgr heq hhigh hlow m q r
      hm hq hr u hbranches (hbelow q hqa).le har hgap hnewlow

theorem MorseCancellation.birth_preserves_lower_index_bound {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a : ℝ}
    {k : ℕ}
    (hcrit :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f) (hp : a < g p)
    (hq : a < g q)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k) :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ k := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · rw [nativeMorseIndex_congr_germ (hkeep z.val hold)]
    apply hlow ⟨z.val, hold⟩
    rwa [← (hkeep z.val hold).self_of_nhds]
  · exact False.elim (hp.not_ge (hzp ▸ hz))
  · exact False.elim (hq.not_ge (hzq ▸ hz))

theorem MorseCancellation.birth_first_new_value_gap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M} {a b : ℝ}
    (hcrit :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hreg : ∀ z, f z = a → z ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hband : ∀ z, f z ∈ Set.Ioo a b → z ∉ Smale.ManifoldMorse.criticalPoints E f) (hp : g p < b)
    (hpq : g p < g q) : ∀ z : Smale.ManifoldMorse.criticalPoints E g, g z < g p → g z < a := by
  intro z hz
  rcases hcrit z.val z.property with hold | hzp | hzq
  · have hzb : g z < b := hz.trans hp
    have heq := (hkeep z.val hold).self_of_nhds
    by_contra hnot
    have haz : a ≤ f z := by rw [← heq]; exact le_of_not_gt hnot
    have hne : a ≠ f z := fun h => hreg z.val h.symm hold
    exact hband z.val ⟨lt_of_le_of_ne haz hne, by rwa [← heq]⟩ hold
  · exact False.elim ((hzp ▸ hz : g p < g p).false)
  · exact False.elim (hpq.not_gt (hzq ▸ hz))

theorem MorseCancellation.birth_preserves_unique_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (m : Smale.ManifoldMorse.criticalPoints E f)
    (hcrit :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = p ∨ z = q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, g =ᶠ[𝓝 z] f)
    (hp : nativeMorseIndex E g p ≠ 0) (hq : nativeMorseIndex E g q ≠ 0)
    (hunique : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = m.val := by
  intro z hz hi
  rcases hcrit z hz with hold | rfl | rfl
  · have hiold : nativeMorseIndex E f z = 0 :=
      (nativeMorseIndex_congr_germ (hkeep z hold)).symm.trans hi
    exact congrArg Subtype.val (hunique ⟨z, hold⟩ hiold)
  · exact False.elim (hp hi)
  · exact False.elim (hq hi)

theorem MorseCancellation.indexed_criticalPoints_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M}
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
    exact ⟨⟨hzf, (hindex z hz).symm.trans hi⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hi⟩, hzp, hzq⟩
    have hz := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hz, (hindex z hz).trans hi⟩

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.nativeMorseCount_removed_of_index_eq {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, if_pos hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, if_neg hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_removed_of_index_eq hcrit hindex k]
  exact (Nat.add_assoc _ _ _).trans hc

theorem MorseCancellation.nativeMorseCount_adjacent_removed_of_index_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {k : ℕ} (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_removed_of_index_eq hfinite hp hq hpq hcrit hindex
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_one_to_three_handle_trade {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : Smale.ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a l u : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) (hal : a < l)
    (hband : ∀ y, f y ∈ Set.Ioo a u → y ∉ Smale.ManifoldMorse.criticalPoints E f) {x : M}
    (hx : f x ∈ Set.Ioo l u) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  let U : Set M := f ⁻¹' Set.Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage hf.continuous
  have hbirthband : ∀ y, f y ∈ Set.Ioo l u → y ∉ Smale.ManifoldMorse.criticalPoints E f :=
    fun y hy => hband y ⟨hal.trans hy.1, hy.2⟩
  obtain
    ⟨g, b₂, b₃, hg, hmg, hinjg, -, -, hi₂, hi₃, h₂₃, hv₂, hv₃, hcountbirth, hcrit, hexterior,
      hkeep, hcount₂, hcount₃, hcountOther⟩ :=
    exists_excellent_indexed_morse_birth hf hm S.distinct hbirthband hx (k := 2) (by omega) hU hx
  have hcrit' (z : M) (hz : z ∈ Smale.ManifoldMorse.criticalPoints E g) :
    z ∈ Smale.ManifoldMorse.criticalPoints E f ∨ z = b₂ ∨ z = b₃ := (hcrit z).mp hz
  have hab₂ : a < g b₂ := hal.trans hv₂.1
  have hab₃ : a < g b₃ := hal.trans hv₃.1
  obtain ⟨heq, -⟩ :=
    birth_preserves_lower_levels hf.continuous hg
      (show U ⊆ {y : M | l < f y} from fun _ hy => hy.1) hexterior hkeep hcrit' hv₂.1.le hv₃.1.le
      hal
  have hgr := regular_level_of_retained_critical_germs hreg hcrit' hkeep hab₂ hab₃
  have hgap := birth_first_new_value_gap hcrit' hkeep hreg hband hv₂.2 h₂₃
  have hnewlow := birth_preserves_lower_index_bound hcrit' hkeep hab₂ hab₃ hlow
  let mg : Smale.ManifoldMorse.criticalPoints E g :=
    ⟨m.val, (hcrit m.val).mpr (Or.inl m.property)⟩
  let qg : Smale.ManifoldMorse.criticalPoints E g :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rg : Smale.ManifoldMorse.criticalPoints E g := ⟨b₂, (hcrit b₂).mpr (Or.inr (Or.inl rfl))⟩
  have hmg0 : nativeMorseIndex E g mg = 0 :=
    (nativeMorseIndex_congr_germ (hkeep m.val m.property)).trans hm0
  have hqg1 : nativeMorseIndex E g qg = 1 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hq1
  have hminG :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z = 0 → z = mg := by
    intro z hz
    apply Subtype.ext
    exact
      birth_preserves_unique_index_zero m hcrit' hkeep (by rw [hi₂]; omega) (by rw [hi₃]; omega)
        hminimum z.val z.property hz
  have hqga : g qg < a := by
    change g q.val < a
    rw [(hkeep q.val q.property).self_of_nhds]
    exact hqa
  obtain ⟨h, hh, hmh, hinjh, hcountcancel, hcritcancel, hindices⟩ :=
    cancel_one_two_pair_at_unchanged_cut_of_unique_minimum S hf hg hmg hinjg e hdim hreg hgr heq
      hhigh (fun z hz => (hlow z hz).trans (by omega)) mg qg rg hmg0 hqg1 hi₂ hminG hqga hab₂ hgap
      hnewlow
  have hq₂ : qg.val ≠ rg.val := fun he => (hqga.trans hab₂).ne (congrArg g he)
  obtain ⟨hremove₁, hremove₂, hremoveOther⟩ :=
    nativeMorseCount_adjacent_removed_of_index_eq
      (Smale.ManifoldMorse.finite_criticalPoints hg hmg) qg.property rg.property hq₂ hcritcancel
      hindices hqg1 hi₂
  have htotal :
    (Smale.ManifoldMorse.criticalPoints E h).ncard =
      (Smale.ManifoldMorse.criticalPoints E f).ncard :=
    Nat.add_right_cancel (hcountcancel.trans hcountbirth)
  have hcount₁ : nativeMorseCount E g 1 = nativeMorseCount E f 1 :=
    hcountOther 1 (by omega) (by omega)
  have hcountₕ₂ : nativeMorseCount E h 2 = nativeMorseCount E f 2 :=
    Nat.add_right_cancel (hremove₂.trans hcount₂)
  refine
    ⟨h, hh, hmh, hinjh, htotal, hremove₁.trans hcount₁,
      (hremoveOther 3 (by omega) (by omega)).trans hcount₃, ?_⟩
  intro j hj1 hj3
  by_cases hj2 : j = 2
  · subst j
    exact hcountₕ₂
  · exact (hremoveOther j hj1 hj2).trans (hcountOther j hj2 hj3)

theorem MorseCancellation.exists_one_to_three_handle_trade_at_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) (m q : Smale.ManifoldMorse.criticalPoints E f)
    (hm0 : nativeMorseIndex E f m = 0) (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ z : Smale.ManifoldMorse.criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : Smale.ManifoldMorse.criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq1
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := S.exists_belt_point_reaching_level hf q 4 hqa hlow (by omega)
  let z := S.flow t ((S.data q).surgery.beltSphere v).val
  have hz : f z = a := ht
  obtain ⟨l₀, u, hl₀, hau, hband⟩ := S.regular_interval_around_level hreg
  have hc : Continuous (fun s : ℝ => f (S.flow s z)) :=
    hf.continuous.comp (S.flow.continuous continuous_id continuous_const)
  have h0 : (fun s : ℝ => f (S.flow s z)) 0 ∈ Set.Iio u := by
    simpa only [Flow.map_zero_apply, hz, Set.mem_Iio] using hau
  obtain ⟨ε, hε, hεball⟩ :=
    Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0))
  let x := S.flow (-ε / 2) z
  have hxu : f x < u :=
    hεball
      (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> linarith)
  have hax : a < f x := by
    have hh :=
      Smale.FlowConstruction.strictAnti_flow_height hf (S.smooth.of_le (by simp)) S.flow
        S.integral S.zero S.descent (hreg z hz) (show -ε / 2 < 0 by linarith)
    simpa only [Flow.map_zero_apply, hz] using hh
  exact
    exists_one_to_three_handle_trade S hf hm e hdim m q hm0 hq1 hminimum hreg hhigh hlow hqa
      (show a < (a + f x) / 2 by linarith) (fun y hy => hband y ⟨hl₀.le.trans hy.1.le, hy.2.le⟩)
      (show f x ∈ Set.Ioo ((a + f x) / 2) u from ⟨by linarith, hxu⟩)

attribute [local instance 100] Classical.propDecidable in
theorem AdaptedWindows.exists_ordered_index_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancellation.nativeMorseIndex E f p ≤ MorseCancellation.nativeMorseIndex E f q)
    {k : ℕ} (q : Smale.ManifoldMorse.criticalPoints E f)
    (hq : MorseCancellation.nativeMorseIndex E f q ≤ k) :
    ∃ a : ℝ,
      (∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
        f q < a ∧
          (∀ z : Smale.ManifoldMorse.criticalPoints E f,
              a ≤ f z → k + 1 ≤ MorseCancellation.nativeMorseIndex E f z) ∧
            ∀ z : Smale.ManifoldMorse.criticalPoints E f,
              f z ≤ a → MorseCancellation.nativeMorseIndex E f z ≤ k := by
  let _ := S.finite.fintype
  let K :=
    Finset.univ.filter
      (fun z : Smale.ManifoldMorse.criticalPoints E f => MorseCancellation.nativeMorseIndex E f z ≤ k)
  have hqK : q ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  obtain ⟨r, hr, hmax⟩ :=
    K.exists_max_image (fun z : Smale.ManifoldMorse.criticalPoints E f => f z) ⟨q, hqK⟩
  have hrk : MorseCancellation.nativeMorseIndex E f r ≤ k := (Finset.mem_filter.mp hr).2
  let a := S.toSurgeryWindows.upper r
  have hra : f r < a := S.toSurgeryWindows.value_lt_upper r
  refine ⟨a, (S.data r).upper_regular, (hmax q hqK).trans_lt hra, ?_, ?_⟩
  · intro z haz
    by_contra hnot
    have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact (not_lt_of_ge (haz.trans (hmax z hzK))) hra
  · intro z hza
    rcases lt_trichotomy (f z) (f r) with hzr | hzr | hrz
    · exact (horder z r hzr).trans hrk
    · have he : z = r := Subtype.ext (S.distinct z.property r.property hzr)
      simpa only [he] using hrk
    · have he : z = r :=
        Subtype.ext
          (S.toSurgeryWindows.isolated r z.val z.property
            ⟨(S.toSurgeryWindows.lower_lt_value r).le.trans hrz.le, hza⟩)
      simpa only [he] using hrk

theorem MorseCancellation.exists_one_to_three_handle_trade_of_ordered_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [PathConnectedSpace M] (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (m q : Smale.ManifoldMorse.criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∃ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧
        Smale.ManifoldMorse.IsMorse E h ∧
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) ∧
            (Smale.ManifoldMorse.criticalPoints E h).ncard =
                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
              nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
                nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
                  ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  obtain ⟨a, hreg, hqa, hhigh, hlow⟩ :=
    S.exists_ordered_index_cut horder q (show nativeMorseIndex E f q ≤ 2 by omega)
  exact
    exists_one_to_three_handle_trade_at_cut S hf hm e hdim m q hm0 hq1 hminimum hreg hhigh hlow
      hqa

theorem MorseCancellation.exists_outer_index_minimal_ordered_morse_system (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f (Module.finrank ℝ E) = 1 ∧
                  (∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        Smale.ManifoldMorse.IsMorse E g →
                          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                            (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                              (Smale.ManifoldMorse.criticalPoints E g).ncard) ∧
                    ∀ g : M → ℝ,
                      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                        Smale.ManifoldMorse.IsMorse E g →
                          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                            (Smale.ManifoldMorse.criticalPoints E g).ncard =
                                (Smale.ManifoldMorse.criticalPoints E f).ncard →
                              nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  classical
  obtain ⟨f₀, hf₀, hm₀, S₀, hminimal₀⟩ := exists_minimal_excellent_morse_system E M
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
            (Smale.ManifoldMorse.criticalPoints E f).ncard =
                (Smale.ManifoldMorse.criticalPoints E f₀).ncard ∧
              nativeMorseCount E f 1 + nativeMorseCount E f 5 = n
  have hex : ∃ n, P n := ⟨_, f₀, hf₀, hm₀, S₀.distinct, rfl, rfl⟩
  obtain ⟨g, hg, hmg, hinjg, hcardg, hcostg⟩ := Nat.find_spec hex
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨f, hf, hm, hcrit, -, S, horder, hcounts⟩ :=
    exists_index_ordered_morse_system_preserving_critical_points T hg hmg
  have hcardf :
    (Smale.ManifoldMorse.criticalPoints E f).ncard =
      (Smale.ManifoldMorse.criticalPoints E f₀).ncard := by rw [hcrit, hcardg]
  have hminimal :
    ∀ h : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
        Smale.ManifoldMorse.IsMorse E h →
          Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) →
            (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
              (Smale.ManifoldMorse.criticalPoints E h).ncard := by
    intro h hh hmh hinjh
    rw [hcardf]
    exact hminimal₀ h hh hmh hinjh
  obtain ⟨hmin, hmax⟩ := minimal_excellent_morse_extreme_counts_one S hf hm hminimal
  refine ⟨f, hf, hm, S, horder, hmin, hmax, hminimal, ?_⟩
  intro h hh hmh hinjh hcardh
  rw [hcounts 1, hcounts 5, hcostg]
  exact Nat.find_min' hex ⟨h, hh, hmh, hinjh, hcardh.trans hcardf, rfl⟩

theorem MorseCancellation.outer_index_minimal_index_one_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 := by
  by_contra hnot
  have hfinite :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  obtain ⟨q, hqcrit, hq1⟩ := (Set.ncard_pos hfinite).mp (Nat.pos_of_ne_zero hnot)
  change
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hzero
  obtain ⟨m, hmset⟩ := Set.ncard_eq_one.mp hzero
  have hmem :
    m ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} := by
    rw [hmset]
    exact Set.mem_singleton m
  let mc : Smale.ManifoldMorse.criticalPoints E f := ⟨m, hmem.1⟩
  have hminimum (z : Smale.ManifoldMorse.criticalPoints E f) (hz : nativeMorseIndex E f z = 0) :
    z = mc := by
    apply Subtype.ext
    have hzmem :
      z.val ∈ {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} :=
      ⟨z.property, hz⟩
    rwa [hmset, Set.mem_singleton_iff] at hzmem
  obtain ⟨g, hg, hmg, hinjg, hcount, hcount1, -, hother⟩ :=
    exists_one_to_three_handle_trade_of_ordered_indices S hf hm e hdim horder mc ⟨q, hqcrit⟩
      hmem.2 hq1 hminimum
  have hcost := hsecondary g hg hmg hinjg hcount
  have hcount5 := hother 5 (by omega) (by omega)
  omega

theorem MorseCancellation.outer_index_minimality_neg {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        Smale.ManifoldMorse.IsMorse E g →
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
            (Smale.ManifoldMorse.criticalPoints E g).ncard =
                (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)).ncard →
              nativeMorseCount E (fun x => -f x) 1 + nativeMorseCount E (fun x => -f x) 5 ≤
                nativeMorseCount E g 1 + nativeMorseCount E g 5 := by
  intro g hg hmg hinjg hcard
  have hh :=
    hsecondary (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
      (by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using hcard)
  have hf1 := nativeMorseCount_neg hf hm (k := 1) (by omega)
  have hf5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hg1 := nativeMorseCount_neg hg hmg (k := 1) (by omega)
  have hg5 := nativeMorseCount_neg hg hmg (k := 5) (by omega)
  simp only [hdim, Nat.reduceSub] at hf1 hf5 hg1 hg5
  omega

theorem MorseCancellation.outer_index_minimal_outer_counts_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hsecondary :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E g).ncard =
                  (Smale.ManifoldMorse.criticalPoints E f).ncard →
                nativeMorseCount E f 1 + nativeMorseCount E f 5 ≤
                  nativeMorseCount E g 1 + nativeMorseCount E g 5) :
    nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 5 = 0 := by
  refine ⟨outer_index_minimal_index_one_count_zero S hf hm e hdim horder hzero hsecondary, ?_⟩
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
  have hzeroN : nativeMorseCount E (fun x => -f x) 0 = 1 := by
    have hc := nativeMorseCount_neg hf hm (k := 6) (by omega)
    simpa only [hdim, Nat.sub_self, hsix] using hc
  have honeN :=
    outer_index_minimal_index_one_count_zero T hf.neg (isMorse_neg hm) e hdim horderN hzeroN
      (outer_index_minimality_neg hf hm hdim hsecondary)
  have hc := nativeMorseCount_neg hf hm (k := 5) (by omega)
  simpa only [hdim, Nat.reduceSub, honeN] using hc.symm

theorem MorseCancellation.exists_minimal_ordered_morse_system_without_outer_indices (E : Type)
    (M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] (e : M ≃ₕ Smale.SixSphere) (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
              nativeMorseCount E f 0 = 1 ∧
                nativeMorseCount E f 6 = 1 ∧
                  nativeMorseCount E f 1 = 0 ∧
                    nativeMorseCount E f 5 = 0 ∧
                      ∀ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                          Smale.ManifoldMorse.IsMorse E g →
                            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                                (Smale.ManifoldMorse.criticalPoints E g).ncard := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hminimal, hsecondary⟩ :=
    exists_outer_index_minimal_ordered_morse_system E M
  rw [hdim] at hsix
  obtain ⟨hone, hfive⟩ :=
    outer_index_minimal_outer_counts_zero S hf hm e hdim horder hzero hsix hsecondary
  exact ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩

def Smale.DiskOnePointCollapse.boundary {N : Type*} [NormedAddCommGroup N] :
    Set (Smale.MorseHandle.UnitDisk N) :=
  {z | ‖(z : N)‖ = 1}

theorem Smale.DiskOnePointCollapse.boundary_closed {N : Type*} [NormedAddCommGroup N] :
    IsClosed (boundary (N := N)) :=
  isClosed_eq continuous_subtype_val.norm continuous_const

theorem Smale.DiskOnePointCollapse.not_mem_boundary_iff {N : Type*} [NormedAddCommGroup N]
    (z : Smale.MorseHandle.UnitDisk N) : z ∉ boundary ↔ ‖(z : N)‖ < 1 := by
  change ‖(z : N)‖ ≠ 1 ↔ ‖(z : N)‖ < 1
  constructor
  · exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
  · exact ne_of_lt

def Smale.DiskOnePointCollapse.interiorHomeomorph {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : ↥(boundary (N := N))ᶜ ≃ₜ N :=
  (Homeomorph.setCongr (by ext z; exact not_mem_boundary_iff z)).trans
    (Smale.DiskAnnulus.openDiskHomeomorph.trans Homeomorph.unitBall.symm)

def Smale.DiskOnePointCollapse.collapse {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] :
    C(Smale.MorseHandle.UnitDisk N, OnePoint N) :=
  ⟨fun z => interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z),
    interiorHomeomorph.onePointCongr.continuous.comp
      (SixSphereCube.continuous_collapse boundary boundary_closed)⟩

theorem Smale.DiskOnePointCollapse.collapse_boundary {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ = 1) :
    collapse z = (OnePoint.infty) := by
  change interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z) = (OnePoint.infty)
  rw [SixSphereCube.collapse_of_mem boundary hz]
  rfl

theorem Smale.DiskOnePointCollapse.collapse_interior {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) (hz : ‖(z : N)‖ < 1) :
    collapse z = ((OpenPartialHomeomorph.univUnitBall.symm (z : N) : N) : OnePoint N) := by
  change interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z) = _
  rw [SixSphereCube.collapse_of_not_mem boundary ((not_mem_boundary_iff z).mpr hz)]
  rfl

theorem Smale.DiskOnePointCollapse.collapse_eq_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z w : Smale.MorseHandle.UnitDisk N) :
    collapse z = collapse w ↔ z = w ∨ ‖(z : N)‖ = 1 ∧ ‖(w : N)‖ = 1 := by
  change
    interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary z) =
        interiorHomeomorph.onePointCongr (SixSphereCube.collapse boundary w) ↔
      _
  rw [interiorHomeomorph.onePointCongr.injective.eq_iff, SixSphereCube.collapse_eq_iff]
  rfl

def Smale.DiskOnePointCollapse.compress {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (x : N) : Smale.MorseHandle.UnitDisk N :=
  ⟨Homeomorph.unitBall x, Metric.ball_subset_closedBall (Homeomorph.unitBall x).property⟩

theorem Smale.DiskOnePointCollapse.norm_compress_lt {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : ‖(compress x : N)‖ < 1 :=
  mem_ball_zero_iff.mp (Homeomorph.unitBall x).property

theorem Smale.DiskOnePointCollapse.compress_zero {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] : (compress (0 : N) : N) = 0 :=
  Homeomorph.coe_unitBall_apply_zero

theorem Smale.DiskOnePointCollapse.collapse_compress {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (x : N) : collapse (compress x) = (x : OnePoint N) := by
  rw [collapse_interior _ (norm_compress_lt x)]
  exact
    congrArg (fun y : N => (y : OnePoint N))
      (OpenPartialHomeomorph.univUnitBall.left_inv (Set.mem_univ x))

theorem Smale.DiskOnePointCollapse.collapse_eq_coe_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) (x : N) :
    collapse z = (x : OnePoint N) ↔ z = compress x := by
  rw [← collapse_compress x, collapse_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact ((ne_of_lt (norm_compress_lt x)) h.2).elim
  · exact Or.inl

theorem Smale.DiskOnePointCollapse.collapse_eq_zero_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) :
    collapse z = ((0 : N) : OnePoint N) ↔ (z : N) = 0 := by
  rw [collapse_eq_coe_iff]
  constructor
  · intro hz
    exact (congrArg Subtype.val hz).trans compress_zero
  · intro hz
    exact Subtype.ext (hz.trans compress_zero.symm)

theorem Smale.DiskOnePointCollapse.collapse_eq_infty_iff {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (z : Smale.MorseHandle.UnitDisk N) :
    collapse z = (OnePoint.infty) ↔ ‖(z : N)‖ = 1 := by
  by_cases hz : ‖(z : N)‖ = 1
  · rw [collapse_boundary z hz]
    exact iff_of_true rfl hz
  · rw [collapse_interior z ((not_mem_boundary_iff z).mp hz)]
    exact iff_of_false (OnePoint.coe_ne_infty _) hz

theorem Smale.ClosedHandleCore.collapseMaps_agree {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X))
    (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P)
    (haz : oldInclusion A h a = handleInclusion A h z) :
    ((OnePoint.infty) : OnePoint N) = Smale.DiskOnePointCollapse.collapse z.1 := by
  have heq : (a : X) = h z := congrArg Subtype.val haz
  have hz := (hface z).mp (heq ▸ a.property)
  exact (Smale.DiskOnePointCollapse.collapse_boundary z.1 hz).symm

def Smale.ClosedHandleCore.collapseMap {N P X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) :
    C(↥(A ∪ Set.range h), OnePoint N) :=
  Smale.ClosedCover.mapOfClosedPieces (oldInclusion A h) (handleInclusion A h) (old_closed A h hA)
    (handle_closed A h hh) (pieces_cover A h) (ContinuousMap.const A (OnePoint.infty))
    (Smale.DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface)

theorem Smale.ClosedHandleCore.collapseMap_old {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1) (a : A) :
    collapseMap A h hA hh hface (oldInclusion A h a) = (OnePoint.infty) :=
  Smale.ClosedCover.mapOfClosedPieces_left (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (Smale.DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) a

theorem Smale.ClosedHandleCore.collapseMap_handle {N P X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [TopologicalSpace X] (A : Set X)
    (h : C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P, X)) (hA : IsClosed A)
    (hh : Topology.IsClosedEmbedding h) (hface : ∀ z, h z ∈ A ↔ ‖(z.1 : N)‖ = 1)
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    collapseMap A h hA hh hface (handleInclusion A h z) =
      Smale.DiskOnePointCollapse.collapse z.1 :=
  Smale.ClosedCover.mapOfClosedPieces_right (oldInclusion A h) (handleInclusion A h)
    (old_closed A h hA) (handle_closed A h hh) (pieces_cover A h)
    (ContinuousMap.const A (OnePoint.infty))
    (Smale.DiskOnePointCollapse.collapse.comp ContinuousMap.fst) (collapseMaps_agree A h hface) z

theorem Smale.EmbeddedCellAttachment.collapse_piece_cover {N X : Type*} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Set.range (Subtype.val : D.old → X) ∪ Set.range D.cell = Set.univ := by
  simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using D.cover

theorem Smale.EmbeddedCellAttachment.collapseMaps_agree {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (a : D.old)
    (z : Smale.MorseHandle.UnitDisk N) (haz : (a : X) = D.cell z) :
    ((OnePoint.infty) : OnePoint N) = Smale.DiskOnePointCollapse.collapse z :=
  (Smale.DiskOnePointCollapse.collapse_boundary z ((D.boundary z).mp (haz ▸ a.property))).symm

def Smale.EmbeddedCellAttachment.collapseMap {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(X, OnePoint N) :=
  Smale.ClosedCover.mapOfClosedPieces Subtype.val D.cell D.old_closed.isClosedEmbedding_subtypeVal
    D.cell_closed D.collapse_piece_cover (ContinuousMap.const D.old (OnePoint.infty))
    Smale.DiskOnePointCollapse.collapse D.collapseMaps_agree

theorem Smale.EmbeddedCellAttachment.collapseMap_old {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (a : D.old) :
    D.collapseMap a = (OnePoint.infty) :=
  Smale.ClosedCover.mapOfClosedPieces_left Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) Smale.DiskOnePointCollapse.collapse
    D.collapseMaps_agree a

theorem Smale.EmbeddedCellAttachment.collapseMap_cell {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (z : Smale.MorseHandle.UnitDisk N) :
    D.collapseMap (D.cell z) = Smale.DiskOnePointCollapse.collapse z :=
  Smale.ClosedCover.mapOfClosedPieces_right Subtype.val D.cell
    D.old_closed.isClosedEmbedding_subtypeVal D.cell_closed D.collapse_piece_cover
    (ContinuousMap.const D.old (OnePoint.infty)) Smale.DiskOnePointCollapse.collapse
    D.collapseMaps_agree z

theorem Smale.EmbeddedCellAttachment.collapseMap_infty_iff {N X : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = (OnePoint.infty) ↔ x ∈ D.old := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · exact iff_of_true (D.collapseMap_old ⟨x, hx⟩) hx
  · rw [D.collapseMap_cell, Smale.DiskOnePointCollapse.collapse_eq_infty_iff, D.boundary]

def Smale.OnePointCover.oldPatch {N : Type*} [NormedAddCommGroup N] : Set (OnePoint N) :=
  {((0 : N) : OnePoint N)}ᶜ

def Smale.OnePointCover.finitePatch {N : Type*} : Set (OnePoint N) :=
  { OnePoint.infty }ᶜ

theorem Smale.OnePointCover.cover {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∪ finitePatch = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = ((0 : N) : OnePoint N)
  · right
    subst x
    exact OnePoint.coe_ne_infty 0
  · exact Or.inl hx

theorem Smale.OnePointCover.oldPatch_open {N : Type*} [NormedAddCommGroup N] :
    IsOpen (oldPatch (N := N)) :=
  isClosed_singleton.isOpen_compl

theorem Smale.OnePointCover.finitePatch_open {N : Type*} [NormedAddCommGroup N] :
    IsOpen (finitePatch (N := N)) :=
  isClosed_singleton.isOpen_compl

theorem Smale.OnePointCover.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] Smale.OnePointCover.instLocal1 in
private def Smale.OnePointCover.spherePunctureHomeomorph_mo1973_5327 (n : ℕ)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ↥({ a }ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) a).symm).trans
    ((stereographic' n a).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target a)).trans (Homeomorph.Set.univ _)))

attribute [local instance] Smale.OnePointCover.instLocal1 in
def Smale.OnePointCover.punctureHomeomorph {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (a : OnePoint N) :
    ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ N)) := by
  let e : OnePoint N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let es : ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ ↥({e a}ᶜ : Set _) :=
    e.subtype
      (fun x => by
        change x ≠ a ↔ e x ≠ e a
        exact e.injective.ne_iff.symm)
  exact es.trans (spherePunctureHomeomorph_mo1973_5327 _ (e a))

attribute [local instance] Smale.OnePointCover.instLocal1 in
theorem Smale.OnePointCover.oldPatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (oldPatch (N := N)) :=
  (punctureHomeomorph ((0 : N) : OnePoint N)).contractibleSpace

attribute [local instance] Smale.OnePointCover.instLocal1 in
theorem Smale.OnePointCover.finitePatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (finitePatch (N := N)) :=
  (punctureHomeomorph (OnePoint.infty : OnePoint N)).contractibleSpace

attribute [local instance] Smale.OnePointCover.instLocal1 in
theorem Smale.OnePointCover.overlap_subset_range {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∩ finitePatch ⊆ Set.range (OnePoint.some : N → _) := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx.2 rfl).elim
  | coe x => exact ⟨x, rfl⟩

attribute [local instance] Smale.OnePointCover.instLocal1 in
theorem Smale.OnePointCover.overlap_preimage {N : Type*} [NormedAddCommGroup N] :
    (OnePoint.some : N → OnePoint N) ⁻¹' (oldPatch ∩ finitePatch) = {u : N | u ≠ 0} := by
  ext x
  change ((x : OnePoint N) ≠ ((0 : N) : OnePoint N) ∧ (x : OnePoint N) ≠ OnePoint.infty) ↔ x ≠ 0
  constructor
  · rintro ⟨h, -⟩ hx
    exact h (congrArg (OnePoint.some : N → OnePoint N) hx)
  · intro hx
    exact ⟨fun h => hx (OnePoint.coe_injective h), OnePoint.coe_ne_infty x⟩

attribute [local instance] Smale.OnePointCover.instLocal1 in
def Smale.OnePointCover.overlapHomeomorph {N : Type*} [NormedAddCommGroup N] :
    Smale.PuncturedRadial.Space N ≃ₜ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Homeomorph.setCongr overlap_preimage.symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange overlap_subset_range)

attribute [local instance] Smale.OnePointCover.instLocal1 in
theorem Smale.OnePointCover.overlapHomeomorph_apply {N : Type*} [NormedAddCommGroup N]
    (u : Smale.PuncturedRadial.Space N) : (overlapHomeomorph u).val = (u.val : OnePoint N) :=
  rfl

attribute [local instance] Smale.OnePointCover.instLocal1 in
def Smale.OnePointCover.overlapSphereEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Smale.PuncturedRadial.sphereHomotopyEquiv r hr).trans overlapHomeomorph.toHomotopyEquiv

def Smale.OnePointCover.overlapRadius : ℝ :=
  (Real.sqrt (1 - (3 / 4 : ℝ) ^ 2))⁻¹ * (3 / 4)

theorem Smale.OnePointCover.overlapRadius_pos : 0 < overlapRadius := by
  have h : 0 < 1 - (3 / 4 : ℝ) ^ 2 := by norm_num
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr h)) (by norm_num)

theorem Smale.EmbeddedCellAttachment.collapseMap_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (x : X) :
    D.collapseMap x = ((0 : N) : OnePoint N) ↔ D.cell ⟨0, by simp⟩ = x := by
  have hx : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
  rcases hx with hx | ⟨z, rfl⟩
  · rw [D.collapseMap_old ⟨x, hx⟩]
    constructor
    · intro h
      exact (OnePoint.infty_ne_coe (0 : N) h).elim
    · intro h
      rw [← h, D.boundary] at hx
      simp at hx
  · rw [D.collapseMap_cell, Smale.DiskOnePointCollapse.collapse_eq_zero_iff]
    constructor
    · intro hz
      exact congrArg D.cell (Subtype.ext hz.symm)
    · intro hz
      exact (congrArg Subtype.val (D.cell_closed.injective hz)).symm

theorem Smale.EmbeddedCellAttachment.collapseMaps_oldNeighborhood {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.oldNeighborhood (Smale.OnePointCover.oldPatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ ((0 : N) : OnePoint N)
  intro h
  have heq := (D.collapseMap_eq_zero_iff x).mp h
  rw [← heq, D.cell_mem_oldNeighborhood_iff] at hx
  norm_num at hx

theorem Smale.EmbeddedCellAttachment.collapseMaps_diskPatch {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    Set.MapsTo D.collapseMap D.diskPatch (Smale.OnePointCover.finitePatch (N := N)) := by
  intro x hx
  change D.collapseMap x ≠ OnePoint.infty
  exact fun h => hx ((D.collapseMap_infty_iff x).mp h)

def Smale.EmbeddedCellAttachment.collapseOverlapMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    C(↥(D.oldNeighborhood ∩ D.diskPatch),
      ↥(Smale.OnePointCover.oldPatch (N := N) ∩ Smale.OnePointCover.finitePatch)) :=
  Smale.CoverNaturality.mapOn D.collapseMap _ _
    (Smale.CoverNaturality.map_intersection _ _ _ _ D.collapseMap D.collapseMaps_oldNeighborhood
      D.collapseMaps_diskPatch)

theorem Smale.EmbeddedCellAttachment.collapseOverlap_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (u : Metric.sphere (0 : N) 1) :
    D.collapseOverlapMap (D.overlapSphereEquiv u) =
      Smale.OnePointCover.overlapSphereEquiv Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos u := by
  apply Subtype.ext
  change
    D.collapseMap (D.cell (Smale.DiskAnnulus.middleDisk u)) =
      ((Smale.OnePointCover.overlapRadius • (u : N) : N) : OnePoint N)
  rw [D.collapseMap_cell,
    Smale.DiskOnePointCollapse.collapse_interior _ (Smale.DiskAnnulus.middleDisk_mem u).2]
  apply congrArg (OnePoint.some : N → OnePoint N)
  change
    (Real.sqrt (1 - ‖(3 / 4 : ℝ) • (u : N)‖ ^ 2))⁻¹ • ((3 / 4 : ℝ) • (u : N)) =
      Smale.OnePointCover.overlapRadius • (u : N)
  rw [Smale.DiskAnnulus.norm_middle, smul_smul]
  rfl

theorem Smale.EmbeddedCellAttachment.collapseOverlap_comp_sphere {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) :
    D.collapseOverlapMap.comp D.overlapSphereEquiv.toFun =
      (Smale.OnePointCover.overlapSphereEquiv (N := N) Smale.OnePointCover.overlapRadius
          Smale.OnePointCover.overlapRadius_pos).toFun :=
  ContinuousMap.ext D.collapseOverlap_sphere

def Smale.OnePointCover.overlapHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(oldPatch (N := N) ∩ finitePatch)) k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k

def Smale.OnePointCover.sphereConnecting {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (overlapHomologyEquiv r hr k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism oldPatch finitePatch oldPatch_open
      finitePatch_open cover k)

theorem Smale.OnePointCover.sphereConnecting_injective {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Function.Injective (sphereConnecting (N := N) r hr k) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  have hi :
    Function.Injective
      (SingularMayerVietoris.connectingHomomorphism (oldPatch (N := N)) finitePatch oldPatch_open
        finitePatch_open cover k) :=
    CuspCentralHomology.contractibleCoverConnecting_injective (oldPatch (N := N)) finitePatch
      oldPatch_open finitePatch_open cover k
  exact (overlapHomologyEquiv (N := N) r hr k).symm.injective.comp hi

def Smale.OnePointCover.sphereHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (k + 1) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  exact
    (CuspCentralHomology.contractibleCoverHomologyHigherEquiv oldPatch finitePatch oldPatch_open
          finitePatch_open cover k).trans
      (overlapHomologyEquiv r hr (k + 1)).symm

theorem Smale.EmbeddedCellAttachment.collapse_overlapHomology_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (D.overlapHomologyEquiv k a) =
      Smale.OnePointCover.overlapHomologyEquiv Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k a := by
  change
    SingularMayerVietoris.singularHomologyMap D.collapseOverlapMap k
        (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap _ k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    D.collapseOverlap_comp_sphere]

theorem Smale.EmbeddedCellAttachment.collapse_connecting_compare {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    Smale.OnePointCover.sphereConnecting Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap D.collapseMap (k + 1) a) =
      D.cellConnectingMap k a := by
  apply
    (Smale.OnePointCover.overlapHomologyEquiv (N := N) Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k).injective
  change
    Smale.OnePointCover.overlapHomologyEquiv _ _ k
        ((Smale.OnePointCover.overlapHomologyEquiv _ _ k).symm _) =
      Smale.OnePointCover.overlapHomologyEquiv _ _ k ((D.overlapHomologyEquiv k).symm _)
  rw [LinearEquiv.apply_symm_apply, ← D.collapse_overlapHomology_compare,
    LinearEquiv.apply_symm_apply]
  exact
    (Smale.CoverNaturality.connecting_naturality_apply D.oldNeighborhood D.diskPatch
        Smale.OnePointCover.oldPatch Smale.OnePointCover.finitePatch D.collapseMap
        D.collapseMaps_oldNeighborhood D.collapseMaps_diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover Smale.OnePointCover.oldPatch_open
        Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k a).symm

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.attachmentCollapseMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap),
      OnePoint d.chart.NegativeCoordinates) :=
  Smale.ClosedHandleCore.collapseMap _ d.handleMap (isClosed_le hf continuous_const)
    (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
    (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.upperCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C({ y : M // f y ≤ f p + d.radius ^ 2 }, OnePoint d.chart.NegativeCoordinates) :=
  (d.attachmentCollapseMap hf).comp d.attachmentHomeomorph.symm.toHomotopyEquiv.toFun

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_realization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap)) :
    d.upperCollapseMap hf (d.attachmentHomeomorph x) = d.attachmentCollapseMap hf x := by
  change d.attachmentCollapseMap hf (d.attachmentHomeomorph.symm (d.attachmentHomeomorph x)) = _
  exact congrArg (d.attachmentCollapseMap hf) (d.attachmentHomeomorph.symm_apply_apply x)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_old {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : { y : M // f y ≤ f p - d.radius ^ 2 }) :
    d.upperCollapseMap hf (d.realizedLowerInclusion x) = (OnePoint.infty) := by
  change
    d.upperCollapseMap hf
        (d.attachmentHomeomorph (Smale.ClosedHandleCore.oldInclusion _ d.handleMap x)) =
      (OnePoint.infty)
  rw [d.upperCollapse_realization]
  exact Smale.ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ x

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_handle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z : d.HandleDomain) :
    d.upperCollapseMap hf (d.attachmentHomeomorph ⟨d.handleMap z, Or.inr ⟨z, rfl⟩⟩) =
      Smale.DiskOnePointCollapse.collapse z.1 := by
  exact
    (d.upperCollapse_realization hf
          (Smale.ClosedHandleCore.handleInclusion _ d.handleMap z)).trans
      (Smale.ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _ z)

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.levelCollapseMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    C(d.UpperLevel, OnePoint d.chart.NegativeCoordinates) :=
  (d.upperCollapseMap hf).comp ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_realized {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (y : d.UpperLevel) (x : ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.handleMap))
    (hy : (y : M) = (d.attachmentHomeomorph x).val) :
    d.levelCollapseMap hf y = d.attachmentCollapseMap hf x := by
  change d.upperCollapseMap hf ⟨y.val, y.property.le⟩ = _
  have heq :
    (⟨y.val, y.property.le⟩ : { z : M // f z ≤ f p + d.radius ^ 2 }) = d.attachmentHomeomorph x :=
    Subtype.ext hy
  rw [heq, d.upperCollapse_realization]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_newExterior {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (r) :
    d.levelCollapseMap hf (d.surgery.newExterior r) = (OnePoint.infty) := by
  rw [d.levelCollapse_realized hf _ _ (d.newExterior_eq r)]
  exact Smale.ClosedHandleCore.collapseMap_old _ d.handleMap _ _ _ ⟨r.val, r.property.1.le⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_newPiece {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.surgery.newPiece z) =
      Smale.DiskOnePointCollapse.collapse
        (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1) := by
  rw [d.levelCollapse_realized hf _ _ (d.newPiece_eq z)]
  exact
    Smale.ClosedHandleCore.collapseMap_handle _ d.handleMap _ _ _
      (d.chart.handleBallCoordinates (z.1, Smale.PuncturedHandle.sphereToBall z.2))

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_zero_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (x : d.UpperLevel) :
    d.levelCollapseMap hf x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ Set.range d.surgery.beltSphere := by
  have hx : x ∈ Set.range d.surgery.newExterior ∪ Set.range d.surgery.newPiece := by
    rw [d.surgery.new_cover]
    trivial
  rcases hx with ⟨r, rfl⟩ | ⟨z, rfl⟩
  · rw [d.levelCollapse_newExterior]
    exact iff_of_false (OnePoint.infty_ne_coe _) (d.surgery.newExterior_avoids r)
  · rw [d.levelCollapse_newPiece, Smale.DiskOnePointCollapse.collapse_eq_zero_iff,
      d.surgery.newPiece_mem_belt_iff]
    rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_coreCell {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) :
    (d.upperCollapseMap hf).comp (d.coreUnionHomotopyEquiv hf).toFun =
      (d.coreCellPresentation hf).collapseMap := by
  apply ContinuousMap.ext
  rintro ⟨x, hx | ⟨u, rfl⟩⟩
  · exact
      (d.upperCollapse_old hf ⟨x, hx⟩).trans
        ((d.coreCellPresentation hf).collapseMap_old ⟨⟨x, Or.inl hx⟩, hx⟩).symm
  · change
      d.upperCollapseMap hf
          (d.attachmentHomeomorph ⟨d.handleMap (u, ⟨0, by simp⟩), Or.inr ⟨_, rfl⟩⟩) =
        (d.coreCellPresentation hf).collapseMap ((d.coreCellPresentation hf).cell u)
    rw [d.upperCollapse_handle, (d.coreCellPresentation hf).collapseMap_cell]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapseHomology_coreCell {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k) :
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (d.cellTotalHomologyEquiv hf k a) =
      SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).collapseMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) k
        (SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    d.upperCollapse_coreCell]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_connecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1)) :
    Smale.OnePointCover.sphereConnecting Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a) =
      d.morseConnectingMap hf k a := by
  obtain ⟨b, rfl⟩ := (d.cellTotalHomologyEquiv hf (k + 1)).surjective a
  rw [d.upperCollapseHomology_coreCell, (d.coreCellPresentation hf).collapse_connecting_compare,
    d.morseConnecting_compare]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_homology_equiv_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 2)) :
    Smale.OnePointCover.sphereHomologyEquiv Smale.OnePointCover.overlapRadius
        Smale.OnePointCover.overlapRadius_pos k
        (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2) a) =
      d.morseConnectingMap hf (k + 1) a :=
  d.upperCollapse_connecting_compare hf (k + 1) a

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_homology_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1)) =
      LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) := by
  rw [d.morse_exact_at_upper hf k]
  ext a
  change
    SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 1) a = 0 ↔
      d.morseConnectingMap hf k a = 0
  rw [← d.upperCollapse_connecting_compare]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact
      (Smale.OnePointCover.sphereConnecting_injective Smale.OnePointCover.overlapRadius
          Smale.OnePointCover.overlapRadius_pos k)
        (h.trans (map_zero _).symm)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.morseConnecting_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k)] :
    Function.Surjective (d.morseConnectingMap hf k) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.coreBoundaryHomologyMap k) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_attachingSphere hf k hk] at ha
  exact ha

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.upperCollapse_surjective_of_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } (k + 1))] :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) (k + 2)) := by
  intro a
  let C :=
    Smale.OnePointCover.sphereHomologyEquiv (N := d.chart.NegativeCoordinates)
      Smale.OnePointCover.overlapRadius Smale.OnePointCover.overlapRadius_pos k
  obtain ⟨b, hb⟩ := d.morseConnecting_surjective_of_lower hf (k + 1) (by omega) (C a)
  refine ⟨b, C.injective ?_⟩
  exact (d.upperCollapse_homology_equiv_compare hf k b).trans hb

theorem Smale.LocalDegree.exists_native_boundaryData {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) x) 0 ∧
        Nonempty
          (BoundaryData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
            ((Smale.NativeParametrization.centered (D := E) x).source ∩
              Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := Smale.NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  let A : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)
  let C : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c 0
  have hAi : A.IsInvertible := by
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (c 0)).IsInvertible
    rw [hcx]
    exact hA
  have hCi : C.IsInvertible :=
    ⟨(LinearEquiv.ofBijective C.toLinearMap
          (Smale.PartialChart.bijective_mfderiv c hc0)).toContinuousLinearEquiv,
      rfl⟩
  have hder : HasFDerivAt (f ∘ c) (A.comp C) 0 :=
    ((hcf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0
        (hc.mdifferentiableAt (by simp)).hasMFDerivAt).hasFDerivAt
  obtain ⟨L, hL⟩ := hAi.comp hCi
  have hdL : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := hL.symm ▸ hder
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hdL.fderiv.symm, ?_⟩
  apply nonempty_boundaryData_of_contDiffAt L hdL _ hs hcomp
  change f (c 0) = 0
  rw [hcx]
  exact hzero

structure Smale.LocalDegree.NeighborhoodData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (L : E ≃L[ℝ] F)
    (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  center_zero : f 0 = 0
  ball_subset : Metric.closedBall 0 radius ⊆ s
  continuous : ContinuousOn f (Metric.closedBall 0 radius)
  remainder_bound : ∀ x ∈ Metric.closedBall 0 radius, ‖f x - L x‖ ≤ (1 / 2 : ℝ) * ‖L x‖

theorem Smale.LocalDegree.nonempty_neighborhoodData {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (L : E ≃L[ℝ] F)
    {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) : Nonempty (NeighborhoodData f L s) := by
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  obtain ⟨b⟩ :=
    nonempty_boundaryData L hf hzero (Filter.inter_mem hs (Metric.ball_mem_nhds 0 hε))
      (hc.mono Set.inter_subset_left)
  have hbs : Metric.closedBall (0 : E) b.radius ⊆ s := b.ball_subset.trans Set.inter_subset_left
  exact
    ⟨⟨b.radius, b.radius_pos, hzero, hbs, hc.mono hbs, fun x hx => hεb x (b.ball_subset hx).2⟩⟩

theorem Smale.LocalDegree.nonempty_neighborhoodData_of_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (L : E ≃L[ℝ] F) {s : Set E} (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) : Nonempty (NeighborhoodData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨d⟩ :=
    nonempty_neighborhoodData L hf hzero (Filter.inter_mem hs ht)
      (htc.mono Set.inter_subset_right)
  exact ⟨{ d with ball_subset := d.ball_subset.trans Set.inter_subset_left }⟩

theorem Smale.LocalDegree.NeighborhoodData.image_ne_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) {x : E}
    (hx : x ∈ Metric.closedBall 0 d.radius) (hx0 : x ≠ 0) : f x ≠ 0 :=
  Smale.LocalDegree.image_ne_zero L hx0 (d.remainder_bound x hx)

def Smale.LocalDegree.NeighborhoodData.innerBoundary {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) :
    Smale.LocalDegree.BoundaryData f L s := by
  have hr : 0 < d.radius / 2 := half_pos d.radius_pos
  have hballs : Metric.closedBall (0 : E) (d.radius / 2) ⊆ Metric.closedBall 0 d.radius :=
    Metric.closedBall_subset_closedBall (half_le_self d.radius_pos.le)
  have hparam (u : Metric.sphere (0 : E) 1) :
    (d.radius / 2) • (u : E) ∈ Metric.closedBall (0 : E) d.radius := by
    rw [mem_closedBall_zero_iff, Smale.LocalDegree.norm_radius_smul (d.radius / 2) hr u]
    exact half_le_self d.radius_pos.le
  refine ⟨d.radius / 2, hr, hballs.trans d.ball_subset, ?_, ?_⟩
  · exact d.continuous.comp_continuous (continuous_const.smul continuous_subtype_val) hparam
  · exact fun u => d.remainder_bound _ (hparam u)

theorem Smale.LocalDegree.NeighborhoodData.innerBoundary_radius {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) :
    d.innerBoundary.radius = d.radius / 2 :=
  rfl

theorem Smale.LocalDegree.NeighborhoodData.innerBoundary_mem_ball {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s)
    (u : Metric.sphere (0 : E) 1) :
    d.innerBoundary.radius • (u : E) ∈ Metric.ball (0 : E) d.radius := by
  rw [mem_ball_zero_iff, Smale.LocalDegree.norm_radius_smul _ d.innerBoundary.radius_pos,
    innerBoundary_radius]
  exact half_lt_self d.radius_pos

theorem Smale.LocalDegree.exists_native_neighborhoodData {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → F} (x : M)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x) (hzero : f x = 0)
    (hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) (W : Set M) (hW : W ∈ 𝓝 x) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap = fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) x) 0 ∧
        Nonempty
          (NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
            ((Smale.NativeParametrization.centered (D := E) x).source ∩
              Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  obtain ⟨L, hL, _⟩ := exists_native_boundaryData x hf hzero hA W hW
  let c := Smale.NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc0)
  have hcf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (c 0) := hcx.symm ▸ hf
  have hcomp : ContDiffAt ℝ ∞ (f ∘ c) 0 := (hcf.comp 0 hc).contDiffAt
  have hd : HasFDerivAt (f ∘ c) L.toContinuousLinearMap 0 := by
    rw [hL]
    exact (hcomp.differentiableAt (by simp)).hasFDerivAt
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc.continuousAt (hcx.symm ▸ hW))
  refine ⟨L, hL, nonempty_neighborhoodData_of_contDiffAt L hd ?_ hs hcomp⟩
  change f (c 0) = 0
  rw [hcx]
  exact hzero

def Smale.ChartPuncturedBall.openSet {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M]
    (c : OpenPartialHomeomorph E M) (R : ℝ) : Set M :=
  c '' Metric.ball (0 : E) R

def Smale.ChartPuncturedBall.puncturedSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) : Set M :=
  {c 0}ᶜ ∩ openSet c R

theorem Smale.ChartPuncturedBall.zero_mem_source {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : (0 : E) ∈ c.source :=
  hs (by simpa using hR.le)

theorem Smale.ChartPuncturedBall.ball_subset_source {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : Metric.ball (0 : E) R ⊆ c.source :=
  Metric.ball_subset_closedBall.trans hs

theorem Smale.ChartPuncturedBall.isOpen_openSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : IsOpen (openSet c R) :=
  c.isOpen_image_of_subset_source Metric.isOpen_ball (ball_subset_source c R hs)

theorem Smale.ChartPuncturedBall.center_mem_openSet {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R) :
    c 0 ∈ openSet c R :=
  Set.mem_image_of_mem c (by simpa using hR)

def Smale.ChartPuncturedBall.ballHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) : Metric.ball (0 : E) R ≃ₜ openSet c R :=
  c.homeomorphOfImageSubsetSource (ball_subset_source c R hs) rfl

theorem Smale.ChartPuncturedBall.image_puncturedBall {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) :
    c '' {x : E | x ≠ 0 ∧ ‖x‖ < R} = puncturedSet c R := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx0, hxR⟩, rfl⟩
    have hx : x ∈ Metric.ball (0 : E) R := mem_ball_zero_iff.mpr hxR
    refine ⟨?_, ⟨x, hx, rfl⟩⟩
    change c x ≠ c 0
    exact fun h => hx0 (c.injOn (ball_subset_source c R hs hx) (zero_mem_source c R hR hs) h)
  · rintro ⟨hy0, x, hxR, rfl⟩
    refine ⟨x, ⟨?_, mem_ball_zero_iff.mp hxR⟩, rfl⟩
    intro hx0
    subst x
    exact hy0 rfl

def Smale.ChartPuncturedBall.puncturedHomeomorph {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] (c : OpenPartialHomeomorph E M) (R : ℝ) (hR : 0 < R)
    (hs : Metric.closedBall (0 : E) R ⊆ c.source) :
    Smale.PuncturedBall.Space E R ≃ₜ puncturedSet c R :=
  c.homeomorphOfImageSubsetSource
    (fun _ hx => ball_subset_source c R hs (mem_ball_zero_iff.mpr hx.2))
    (image_puncturedBall c R hR hs)

def Smale.LocalDegree.NativeNeighborhood.openSet {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Set M :=
  Smale.ChartPuncturedBall.openSet
    (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius

theorem Smale.LocalDegree.NativeNeighborhood.closedBall_subset_source {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.closedBall (0 : E) d.radius ⊆ (Smale.NativeParametrization.centered x).source :=
  d.ball_subset.trans Set.inter_subset_left

theorem Smale.LocalDegree.NativeNeighborhood.isOpen_openSet {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    IsOpen (openSet x d) :=
  Smale.ChartPuncturedBall.isOpen_openSet
    (Smale.NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
    (closedBall_subset_source x d)

theorem Smale.LocalDegree.NativeNeighborhood.center_mem_openSet {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    x ∈ openSet x d := by
  have h :=
    Smale.ChartPuncturedBall.center_mem_openSet
      (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph d.radius
      d.radius_pos
  change Smale.NativeParametrization.centered x (0 : E) ∈ openSet x d at h
  rwa [Smale.NativeParametrization.centered_zero] at h

theorem Smale.LocalDegree.NativeNeighborhood.openSet_subset {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    openSet x d ⊆ W := by
  rintro y ⟨u, hu, rfl⟩
  exact (d.ball_subset (Metric.ball_subset_closedBall hu)).2

def Smale.LocalDegree.NativeNeighborhood.puncturedHomeomorph {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Smale.PuncturedBall.Space E d.radius ≃ₜ ↥({ x }ᶜ ∩ openSet x d) :=
  (Smale.ChartPuncturedBall.puncturedHomeomorph
        (Smale.NativeParametrization.centered x).toOpenPartialHomeomorph d.radius d.radius_pos
        (closedBall_subset_source x d)).trans
    (Homeomorph.setCongr
      (by
        change {Smale.NativeParametrization.centered x (0 : E)}ᶜ ∩ openSet x d = _
        rw [Smale.NativeParametrization.centered_zero]))

def Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥({ x }ᶜ ∩ openSet x d) :=
  (Smale.PuncturedBall.sphereHomotopyEquiv d.radius d.innerBoundary.radius
        d.innerBoundary.radius_pos
        (by
          rw [d.innerBoundary_radius]
          exact half_lt_self d.radius_pos)).trans
    (puncturedHomeomorph x d).toHomotopyEquiv

structure Smale.LocalDegree.SeparatedNeighborhoods (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (P : Set M) (f : M → F) (W : Set M) where
  linear : P → E ≃L[ℝ] F
  derivative_eq :
    ∀ x : P,
      (linear x).toContinuousLinearMap =
        fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) 0
  data :
    ∀ x : P,
      NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) (linear x)
        ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
          Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' W)
  disjoint : Pairwise (Disjoint on (fun x : P => NativeNeighborhood.openSet (x : M) (data x)))

theorem Smale.LocalDegree.nonempty_separatedNeighborhoods (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M] {P : Set M}
    {f : M → F} {W : Set M} (hP : P.Finite) (hf : ∀ x ∈ P, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hz : ∀ x ∈ P, f x = 0) (hA : ∀ x ∈ P, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (hW : ∀ x ∈ P, W ∈ 𝓝 x) : Nonempty (SeparatedNeighborhoods E P f W) := by
  classical
  obtain ⟨U, hU, hdisj⟩ := hP.t2_separation
  have hex (x : P) :
    ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap =
          fderiv ℝ (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) 0 ∧
        Nonempty
          (NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) L
            ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
              Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x))) :=
    exists_native_neighborhoodData (x : M) (hf x x.property) (hz x x.property) (hA x x.property)
      (W ∩ U x) (Filter.inter_mem (hW x x.property) ((hU x).2.mem_nhds (hU x).1))
  choose L hL hD using hex
  let D (x : P) :
    NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) (L x)
      ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
        Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x)) :=
    Classical.choice (hD x)
  let D' (x : P) :
    NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) (x : M)) (L x)
      ((Smale.NativeParametrization.centered (D := E) (x : M)).source ∩
        Smale.NativeParametrization.centered (D := E) (x : M) ⁻¹' W) :=
    { D x with ball_subset := fun u hu => ⟨((D x).ball_subset hu).1, ((D x).ball_subset hu).2.1⟩ }
  refine ⟨⟨L, hL, D', ?_⟩⟩
  intro x y hxy
  change
    Disjoint (NativeNeighborhood.openSet (x : M) (D x)) (NativeNeighborhood.openSet (y : M) (D y))
  apply (hdisj x.property y.property (fun h => hxy (Subtype.ext h))).mono
  · exact (NativeNeighborhood.openSet_subset (x : M) (D x)).trans Set.inter_subset_right
  · exact (NativeNeighborhood.openSet_subset (y : M) (D y)).trans Set.inter_subset_right

def Smale.LocalDegree.SeparatedNeighborhoods.neighborhood {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) : Set M :=
  Smale.LocalDegree.NativeNeighborhood.openSet (x : M) (D.data x)

theorem Smale.LocalDegree.SeparatedNeighborhoods.isOpen_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    IsOpen (D.neighborhood x) :=
  Smale.LocalDegree.NativeNeighborhood.isOpen_openSet (x : M) (D.data x)

theorem Smale.LocalDegree.SeparatedNeighborhoods.center_mem_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (x : M) ∈ D.neighborhood x :=
  Smale.LocalDegree.NativeNeighborhood.center_mem_openSet (x : M) (D.data x)

theorem Smale.LocalDegree.SeparatedNeighborhoods.neighborhood_subset {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    D.neighborhood x ⊆ W :=
  Smale.LocalDegree.NativeNeighborhood.openSet_subset (x : M) (D.data x)

theorem Smale.LocalDegree.SeparatedNeighborhoods.pairwise_disjoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) :
    Pairwise (Disjoint on D.neighborhood) :=
  D.disjoint

theorem Smale.LocalDegree.SeparatedNeighborhoods.points_inter_neighborhood {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    P ∩ D.neighborhood x = {(x : M)} := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    change y = (x : M)
    by_contra hne
    let z : P := ⟨y, hyP⟩
    have hxz : x ≠ z := fun h => hne (congrArg Subtype.val h).symm
    exact Set.disjoint_left.mp (D.pairwise_disjoint hxz) hy (D.center_mem_neighborhood z)
  · rintro rfl
    exact ⟨x.property, D.center_mem_neighborhood x⟩

theorem Smale.LocalDegree.SeparatedNeighborhoods.overlap_eq {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Pᶜ ∩ D.neighborhood x = {(x : M)}ᶜ ∩ D.neighborhood x := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    refine ⟨?_, hy⟩
    rintro rfl
    exact hyP x.property
  · rintro ⟨hyx, hy⟩
    refine ⟨?_, hy⟩
    intro hyP
    have h : y ∈ P ∩ D.neighborhood x := ⟨hyP, hy⟩
    rw [D.points_inter_neighborhood x] at h
    exact hyx h

theorem Smale.LocalDegree.SeparatedNeighborhoods.open_cover {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) :
    Pᶜ ∪ (⋃ x : P, D.neighborhood x) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ P
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨y, hy⟩, D.center_mem_neighborhood ⟨y, hy⟩⟩)
  · exact Or.inl hy

def Smale.LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    Metric.sphere (0 : E) 1 ≃ₕ ↥(Pᶜ ∩ D.neighborhood x) :=
  (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).trans
    (Homeomorph.setCongr (D.overlap_eq x).symm).toHomotopyEquiv

theorem Smale.LocalDegree.SeparatedNeighborhoods.overlapSphereEquiv_apply {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (u : Metric.sphere (0 : E) 1) :
    (D.overlapSphereEquiv x u).val =
      Smale.NativeParametrization.centered (x : M) ((D.data x).innerBoundary.radius • (u : E)) :=
  rfl

def Smale.LocalDegree.NeighborhoodData.puncturedMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) :
    C(Smale.PuncturedBall.Space E d.radius, Smale.PuncturedRadial.Space F) :=
  ⟨fun x => ⟨f x.val, d.image_ne_zero (mem_closedBall_zero_iff.mpr x.property.2.le) x.property.1⟩,
    (d.continuous.comp_continuous continuous_subtype_val
          (fun x => mem_closedBall_zero_iff.mpr x.property.2.le)).subtype_mk
      _⟩

def Smale.LocalDegree.NativeNeighborhood.overlapMap {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    C(↥({ x }ᶜ ∩ openSet x d), Smale.PuncturedRadial.Space F) :=
  d.puncturedMap.comp (puncturedHomeomorph x d).symm.toHomotopyEquiv.toFun

theorem Smale.LocalDegree.NativeNeighborhood.overlapMap_coe {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (y : ↥({ x }ᶜ ∩ openSet x d)) : (overlapMap x d y).val = f y.val := by
  have h := congrArg Subtype.val ((puncturedHomeomorph x d).apply_symm_apply y)
  change
    Smale.NativeParametrization.centered x ((puncturedHomeomorph x d).symm y).val = y.val at h
  exact congrArg f h

def Smale.LocalDegree.SeparatedNeighborhoods.overlapMap {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F} {W : Set M}
    (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), Smale.PuncturedRadial.Space F) :=
  (Smale.LocalDegree.NativeNeighborhood.overlapMap (x : M) (D.data x)).comp
    (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

theorem Smale.LocalDegree.SeparatedNeighborhoods.overlapMap_coe {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P)
    (y : ↥(Pᶜ ∩ D.neighborhood x)) : (D.overlapMap x y).val = f y.val :=
  Smale.LocalDegree.NativeNeighborhood.overlapMap_coe (x : M) (D.data x) _

theorem Smale.LocalDegree.SeparatedNeighborhoods.overlapMap_sphereEquiv {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.overlapMap x).comp (D.overlapSphereEquiv x).toFun = (D.data x).innerBoundary.map := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, overlapMap_coe, overlapSphereEquiv_apply,
    Smale.LocalDegree.BoundaryData.map_coe]
  rfl

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.beltFaceCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ≃ₜ
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates :=
  (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).trans
    (Smale.MorseHandle.beltFaceDiskHomeomorph.trans
      (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).symm)

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.beltClosedDiskPoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.beltSource d.radius d.radius_pos :=
  ⟨(z.2, z.1.val),
    d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
      ⟨Set.mem_univ _, mem_closedBall_zero_iff.mpr (z.1.property.trans (by norm_num))⟩⟩

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.beltClosedDiskMap {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates,
      d.UpperLevel)
    where
  toFun
    z := (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (d.beltClosedDiskPoint z)).val
  continuous_toFun := by
    have hc : Continuous d.beltClosedDiskPoint :=
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    exact
      continuous_subtype_val.comp
        ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp hc)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.newPiece_beltFaceCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (u : Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.newPiece (d.beltFaceCoordinates u, v) = d.beltClosedDiskMap (u, v) := by
  let ud := Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates u
  let vd : Smale.MorseHandle.UnitDisk d.chart.PositiveCoordinates :=
    ⟨v.val, mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp v.property).le⟩
  have hv : ‖vd.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  let z := (Smale.MorseHandle.beltFaceDiskMap ud, vd)
  let x :
    ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
        Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) :=
    ⟨d.chart.attachingHandleMap d.radius d.radius_pos d.block z, Or.inr ⟨z, rfl⟩⟩
  have hnew :
    (d.surgery.newPiece (d.beltFaceCoordinates u, v) : M) = (d.attachmentHomeomorph x).val :=
    d.newPiece_eq _
  have hfront :
    x.val ∈
      frontier
        ({y | f y ≤ f p - d.radius ^ 2} ∪
          Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) := by
    apply (d.attachment_frontier x).mp
    rw [← hnew]
    exact (d.surgery.newPiece (d.beltFaceCoordinates u, v)).property
  have htgt := d.block (Smale.MorseHandle.modelMap_mem_product d.radius_pos z)
  have hsource : x.val ∈ d.chart.splitChart.source := d.chart.splitChart.map_target' htgt
  have hcoords : d.chart.splitChart x.val = Smale.MorseHandle.modelMap d.radius z :=
    d.chart.splitChart.right_inv' htgt
  have hend :
    Smale.MorseHandle.descentFlow (-Smale.MorseHandle.beltFaceTime ‖ud.val‖)
        (d.chart.splitChart x.val) =
      Smale.MorseHandle.beltLevelModel d.radius ud.val vd.val := by
    rw [hcoords]
    exact Smale.MorseHandle.descentFlow_neg_beltFaceTime d.radius ud vd hv
  have hpath :
    ∀ s ∈ Set.uIcc 0 (-Smale.MorseHandle.beltFaceTime ‖ud.val‖),
      Smale.MorseHandle.descentFlow s (d.chart.splitChart x.val) ∈
        Metric.closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
          Metric.closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    intro s hs
    rw [hcoords]
    exact Smale.MorseHandle.descentFlow_positiveFace_mem_block d.radius_pos ud vd hv hs
  have hlevel :
    f
        (d.chart.splitChart.symm
          (Smale.MorseHandle.descentFlow (-Smale.MorseHandle.beltFaceTime ‖ud.val‖)
            (d.chart.splitChart x.val))) =
      f p + d.radius ^ 2 := by
    rw [d.chart.splitChart_inverse_equation (d.block (hpath _ Set.right_mem_uIcc)), hend]
    have hh := Smale.MorseHandle.beltLevelModel_height d.radius_pos ud.val hv
    change
      -‖(Smale.MorseHandle.beltLevelModel d.radius ud.val vd.val).1‖ ^ 2 +
          ‖(Smale.MorseHandle.beltLevelModel d.radius ud.val vd.val).2‖ ^ 2 =
        d.radius ^ 2 at hh
    linarith
  have horbit :=
    d.attachment_model_orbits x hfront hsource (-Smale.MorseHandle.beltFaceTime ‖ud.val‖)
      (neg_nonpos.mpr (Smale.MorseHandle.beltFaceTime_nonneg _)) hpath hlevel
  apply Subtype.ext
  rw [hnew, horbit, hend]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.range_newPiece_eq_range_beltClosedDiskMap
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    Set.range d.surgery.newPiece = Set.range d.beltClosedDiskMap := by
  ext y
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    refine ⟨(d.beltFaceCoordinates.symm u, v), ?_⟩
    rw [← d.newPiece_beltFaceCoordinates, d.beltFaceCoordinates.apply_symm_apply]
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨(d.beltFaceCoordinates u, v), d.newPiece_beltFaceCoordinates u v⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.beltClosedDiskMap_mem_newInterior_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltClosedDiskMap z ∈ d.surgery.NewInterior ↔ ‖z.1.val‖ < 1 := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.surgery.newPiece_mem_newInterior_iff]
  exact Smale.MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val

theorem Smale.MorseHandle.contDiff_beltFaceMap {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] : ContDiff ℝ ∞ (beltFaceMap (N := N)) := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  exact hs.smul contDiff_id

theorem Smale.MorseHandle.hasFDerivAt_beltFaceMap_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    HasFDerivAt (beltFaceMap (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N) 0 := by
  have hs : ContDiff ℝ ∞ (fun u : N => Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) :=
    ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)).div_const _
  have hd := (hs.differentiable (by simp) (0 : N)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 + ‖u‖ ^ 2) / Real.sqrt 2) • u) _ 0
  simpa [Pi.smul_def'] using hd

theorem Smale.MorseHandle.hasFDerivAt_univUnitBall_symm_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N) (ContinuousLinearMap.id ℝ N)
      0 := by
  have hs : ContDiffAt ℝ ∞ (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹) 0 := by
    apply ContDiffAt.inv
    · exact ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffAt.sqrt (by simp))
    · simp
  have hd := (hs.differentiableAt (by simp)).hasFDerivAt.smul (hasFDerivAt_id (0 : N))
  change HasFDerivAt (fun u : N => (Real.sqrt (1 - ‖u‖ ^ 2))⁻¹ • u) (ContinuousLinearMap.id ℝ N) 0
  simpa [Pi.smul_def'] using hd

def Smale.MorseHandle.beltCollapseCoordinate {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (u : N) : N :=
  OpenPartialHomeomorph.univUnitBall.symm (beltFaceMap u)

theorem Smale.MorseHandle.beltCollapseCoordinate_zero {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] : beltCollapseCoordinate (0 : N) = 0 := by
  rw [beltCollapseCoordinate, beltFaceMap_zero,
    OpenPartialHomeomorph.univUnitBall_symm_apply_zero]

theorem Smale.MorseHandle.contDiffOn_beltCollapseCoordinate {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] :
    ContDiffOn ℝ ∞ (beltCollapseCoordinate (N := N)) (Metric.ball 0 1) := by
  apply OpenPartialHomeomorph.contDiffOn_univUnitBall_symm.comp contDiff_beltFaceMap.contDiffOn
  intro u hu
  exact mem_ball_zero_iff.mpr ((norm_beltFaceMap_lt_one_iff u).mpr (mem_ball_zero_iff.mp hu))

theorem Smale.MorseHandle.hasFDerivAt_beltCollapseCoordinate_zero {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] :
    HasFDerivAt (beltCollapseCoordinate (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N)
      0 := by
  have hout :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm : N → N) (ContinuousLinearMap.id ℝ N)
      (beltFaceMap 0) := by
    rw [beltFaceMap_zero]
    exact hasFDerivAt_univUnitBall_symm_zero
  change HasFDerivAt ((OpenPartialHomeomorph.univUnitBall.symm : N → N) ∘ beltFaceMap) _ 0
  simpa only [ContinuousLinearMap.id_comp] using hout.comp 0 hasFDerivAt_beltFaceMap_zero

theorem Smale.MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N] (ρ : ℝ) :
    HasFDerivAt (fun u : N => beltCollapseCoordinate (ρ⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * ρ⁻¹) • ContinuousLinearMap.id ℝ N) 0 := by
  have hout :
    HasFDerivAt (beltCollapseCoordinate (N := N)) ((Real.sqrt 2)⁻¹ • ContinuousLinearMap.id ℝ N)
      (ρ⁻¹ • (0 : N)) := by
    simpa only [smul_zero] using hasFDerivAt_beltCollapseCoordinate_zero (N := N)
  simpa only [Function.comp_def, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, smul_smul, mul_comm] using
    hout.comp 0 ((hasFDerivAt_id (0 : N)).const_smul ρ⁻¹)

theorem Smale.MorseHandle.scaled_beltCollapseCoordinate_factor_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < (Real.sqrt 2)⁻¹ * ρ⁻¹ := by positivity

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.beltNormal_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.beltClosedDiskMap z) = d.radius • z.1.val :=
  d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (d.beltClosedDiskPoint z)

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.collapseNormal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (x : d.UpperLevel) :
    d.chart.NegativeCoordinates :=
  Smale.MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • d.beltNormal x)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseNormal_belt {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.collapseNormal (d.surgery.beltSphere v) = 0 := by
  rw [collapseNormal, d.beltNormal_belt, smul_zero, Smale.MorseHandle.beltCollapseCoordinate_zero]

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_beltClosedDiskMap {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (z :
      Smale.PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.beltClosedDiskMap z) =
      Smale.DiskOnePointCollapse.collapse
        (Smale.MorseHandle.beltFaceDiskMap
          (Smale.MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1)) := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.levelCollapse_newPiece]
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.levelCollapse_eq_coe_collapseNormal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    {x : d.UpperLevel} (hx : x ∈ d.surgery.NewInterior) :
    d.levelCollapseMap hf x = (d.collapseNormal x : OnePoint d.chart.NegativeCoordinates) := by
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  have hz := (d.beltClosedDiskMap_mem_newInterior_iff z).mp hx
  rw [d.levelCollapse_beltClosedDiskMap,
    Smale.DiskOnePointCollapse.collapse_interior _
      ((Smale.MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val).mpr hz)]
  unfold collapseNormal
  rw [d.beltNormal_beltClosedDiskMap, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  rfl

theorem Smale.SphereNormalCoordinates.normalDerivative_smul_isInvertible {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N)
    (hA : A.IsInvertible) (c : ℝ) (hc : c ≠ 0) : (c • A).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • A.inverse)
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.self_apply_inverse, hc]
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.inverse_apply_self, hc]

theorem Smale.SphereNormalCoordinates.normalJacobian_smul_mul_pow {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : c ≠ 0) :
    normalJacobian j x (c • A) * c ^ Module.finrank ℝ N = normalJacobian j x A := by
  have hB := normalDerivative_smul_isInvertible A hA c hc
  have hcomp : A.comp A.inverse = ContinuousLinearMap.id ℝ N := by
    ext y
    exact hA.self_apply_inverse y
  have hdet : ((c • A).comp A.inverse).det = c ^ Module.finrank ℝ N := by
    rw [ContinuousLinearMap.smul_comp, hcomp]
    change (c • (LinearMap.id : N →ₗ[ℝ] N)).det = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hid : (A.comp A.inverse).det = 1 := by
    rw [hcomp]
    exact LinearMap.det_id
  have h :=
    (normalJacobian_mul_chartDet j x (c • A) hB A.inverse).trans
      (normalJacobian_mul_chartDet j x A hA A.inverse).symm
  simpa only [hdet, hid, mul_one] using h

theorem Smale.SphereNormalCoordinates.sign_normalJacobian_smul_pos {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : 0 < c) :
    SignType.sign (normalJacobian j x (c • A)) = SignType.sign (normalJacobian j x A) := by
  have h := congrArg SignType.sign (normalJacobian_smul_mul_pow j x A hA c hc.ne')
  have hp : SignType.sign (c ^ Module.finrank ℝ N) = 1 := sign_eq_one_iff.mpr (pow_pos hc _)
  simpa only [sign_mul, hp, mul_one] using h

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.mfderiv_collapseNormal_comp {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x : Smale.Hemisphere.Sphere m)
    (hg : MDifferentiableAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x =
      ((Real.sqrt 2)⁻¹ * d.radius⁻¹) •
        mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x := by
  obtain ⟨v, hv⟩ := hx
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hout :
    HasFDerivAt
      (fun u : d.chart.NegativeCoordinates =>
        Smale.MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      (((Real.sqrt 2)⁻¹ * d.radius⁻¹) • ContinuousLinearMap.id ℝ _) ((d.beltNormal ∘ g) x) := by
    rw [hzero]
    exact Smale.MorseHandle.hasFDerivAt_scaled_beltCollapseCoordinate_zero d.radius
  have h := (hout.hasMFDerivAt.comp x hg.hasMFDerivAt).mfderiv
  change mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x = _ at h
  apply h.trans
  apply ContinuousLinearMap.ext
  intro u
  rfl

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x : Smale.Hemisphere.Sphere m)
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x).IsInvertible)
    (hx : g x ∈ Set.range d.surgery.beltSphere) :
    letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    SignType.sign
        (Smale.SphereNormalCoordinates.normalJacobian j x
          (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
      d.beltIntersectionSign m j g x := by
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hA) hx]
  exact
    Smale.SphereNormalCoordinates.sign_normalJacobian_smul_pos j x _ hA _
      (Smale.MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseNormal_comp_sign_of_transverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        SignType.sign
            (Smale.SphereNormalCoordinates.normalJacobian j x
              (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x)) =
          d.beltIntersectionSign m j g x := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact d.collapseNormal_comp_sign m j g x hAi ⟨v, hv⟩

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.contMDiffAt_collapseNormal_comp {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (x : Smale.Hemisphere.Sphere m),
      g x ∈ Set.range d.surgery.beltSphere →
        ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.collapseNormal ∘ g) x := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg x hx
  obtain ⟨v, hv⟩ := hx
  have hn : ContMDiffAt (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ (d.beltNormal ∘ g) x := by
    have hnormal :=
      (d.contMDiffOn_beltNormal hf).contMDiffAt
        (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
    rw [hv] at hnormal
    exact hnormal.comp x hg.contMDiffAt
  have hzero : (d.beltNormal ∘ g) x = 0 := by
    change d.beltNormal (g x) = 0
    rw [← hv, d.beltNormal_belt]
  have hq :
    ContDiffAt ℝ ∞ (Smale.MorseHandle.beltCollapseCoordinate (N := d.chart.NegativeCoordinates))
      (d.radius⁻¹ • (d.beltNormal ∘ g) x) := by
    rw [hzero, smul_zero]
    exact
      Smale.MorseHandle.contDiffOn_beltCollapseCoordinate.contDiffAt
        (Metric.isOpen_ball.mem_nhds (by simp))
  have hs :
    ContDiffAt ℝ ∞
      (fun u : d.chart.NegativeCoordinates =>
        Smale.MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • u))
      ((d.beltNormal ∘ g) x) :=
    hq.comp _ (contDiff_id.const_smul d.radius⁻¹).contDiffAt
  exact hs.contMDiffAt.comp x hn

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.isInvertible_collapseNormal_comp_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.collapseNormal ∘ g) x).IsInvertible :=
  by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  rw [d.mfderiv_collapseNormal_comp m g x (mdifferentiableAt_of_isInvertible_mfderiv hAi) ⟨v, hv⟩]
  exact
    Smale.SphereNormalCoordinates.normalDerivative_smul_isInvertible A hAi _
      (Smale.MorseHandle.scaled_beltCollapseCoordinate_factor_pos d.radius d.radius_pos).ne'

attribute [local instance 100] Classical.propDecidable in
abbrev Smale.ManifoldMorse.MorseSurgeryData.CollapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :=
  Smale.LocalDegree.SeparatedNeighborhoods (EuclideanSpace ℝ (Fin m))
    (d.beltIntersectionPoints m g) (d.collapseNormal ∘ g) (g ⁻¹' d.surgery.NewInterior)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.nonempty_collapseNeighborhoods {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      Nonempty (d.CollapseNeighborhoods m g) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  have hfin := d.finite_beltIntersectionPoints hf n m hdim g hg hinj ht
  apply Smale.LocalDegree.nonempty_separatedNeighborhoods (EuclideanSpace ℝ (Fin m)) hfin
  · exact fun x hx => d.contMDiffAt_collapseNormal_comp hf m g hg x hx
  · intro x hx
    obtain ⟨v, hv⟩ := hx
    change d.collapseNormal (g x) = 0
    rw [← hv, d.collapseNormal_belt]
  · exact fun x hx => d.isInvertible_collapseNormal_comp_of_transverse hf n m hdim g hg ht x hx
  · intro x hx
    apply hg.continuous.continuousAt
    apply d.surgery.isOpen_newInterior.mem_nhds
    obtain ⟨v, hv⟩ := hx
    rw [← hv]
    exact d.surgery.beltSphere_mem_newInterior v

def Smale.CoverLocalContributions.localMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U')
    (hfV : ∀ i, Set.MapsTo f (V i) V') (i : ι) : C(↥(U ∩ V i), ↥(U' ∩ V')) :=
  Smale.CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

theorem Smale.CoverLocalContributions.connecting_sum {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} [Fintype ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    (U' V' : Set Y) (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) V')
    (hU' : IsOpen U') (hV' : IsOpen V') (hc' : U' ∪ V' = Set.univ) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hc' k
        (SingularMayerVietoris.singularHomologyMap f (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (localMap U V U' V' f hfU hfV i) k
          (componentConnecting U V hU hV hd hc k a i) := by
  rw [←
    Smale.CoverNaturality.connecting_naturality_apply U (⋃ i, V i) U' V' f hfU
      (map_union V V' f hfV) hU (isOpen_iUnion hV) hc hU' hV' hc' k a]
  rw [Smale.CoverOverlapHomology.homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rfl

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) :
    C(Smale.Hemisphere.Sphere m, OnePoint d.chart.NegativeCoordinates) :=
  (d.levelCollapseMap hf).comp g

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse_zero_iff {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (x : Smale.Hemisphere.Sphere m) :
    d.attachingCollapse hf m g x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ d.beltIntersectionPoints m g :=
  d.levelCollapse_zero_iff hf (g x)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_old {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) :
    Set.MapsTo (d.attachingCollapse hf m g) (d.beltIntersectionPoints m g)ᶜ
      Smale.OnePointCover.oldPatch := by
  intro x hx hzero
  exact hx ((d.attachingCollapse_zero_iff hf m g x).mp hzero)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.attachingCollapse_maps_neighborhood {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    Set.MapsTo (d.attachingCollapse hf m g) (D.neighborhood i) Smale.OnePointCover.finitePatch := by
  intro x hx
  have hnew : g x ∈ d.surgery.NewInterior := D.neighborhood_subset i hx
  change d.levelCollapseMap hf (g x) ≠ OnePoint.infty
  rw [d.levelCollapse_eq_coe_collapseNormal hf hnew]
  exact OnePoint.coe_ne_infty _

attribute [local instance 100] Classical.propDecidable in
def Smale.ManifoldMorse.MorseSurgeryData.collapseOverlapMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    C(↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i),
      ↥(Smale.OnePointCover.oldPatch (N := d.chart.NegativeCoordinates) ∩
          Smale.OnePointCover.finitePatch)) :=
  Smale.CoverNaturality.mapOn (d.attachingCollapse hf m g) _ _
    (fun _ hx =>
      ⟨d.attachingCollapse_maps_old hf m g hx.1,
        d.attachingCollapse_maps_neighborhood hf m g D i hx.2⟩)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseOverlapMap_eq {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    d.collapseOverlapMap hf m g D i =
      Smale.OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.overlapMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    d.levelCollapseMap hf (g x.val) =
      (Smale.OnePointCover.overlapHomeomorph (D.overlapMap i x)).val
  rw [Smale.OnePointCover.overlapHomeomorph_apply,
    Smale.LocalDegree.SeparatedNeighborhoods.overlapMap_coe]
  exact d.levelCollapse_eq_coe_collapseNormal hf (D.neighborhood_subset i x.property.2)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.MorseSurgeryData.collapseOverlapMap_sphereEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    (i : d.beltIntersectionPoints m g) :
    (d.collapseOverlapMap hf m g D i).comp (D.overlapSphereEquiv i).toFun =
      Smale.OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
        (D.data i).innerBoundary.map := by
  rw [d.collapseOverlapMap_eq hf m g D i, ContinuousMap.comp_assoc, D.overlapMap_sphereEquiv]

def Smale.ManifoldMorse.MorseSurgeryData.upperLevelInclusion {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) :
    C(d.UpperLevel, { y : M // f y ≤ f p + d.radius ^ 2 }) :=
  ⟨Set.inclusion (fun _ hx => hx.le), continuous_inclusion _⟩

def Smale.ManifoldMorse.MorseSurgeryData.bandSublevelHomeomorph {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) (T : M ≃ₜ M)
    (hT : T '' {y : M | f y ≤ f p + d.radius ^ 2} = {y : M | f y ≤ f q - d'.radius ^ 2}) :
    { y : M // f y ≤ f p + d.radius ^ 2 } ≃ₜ { y : M // f y ≤ f q - d'.radius ^ 2 } :=
  (T.image {y : M | f y ≤ f p + d.radius ^ 2}).trans (Homeomorph.setCongr hT)

structure Smale.ManifoldMorse.SurgeryWindows.BandData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) where
  ambient : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞
  level : (S.data (S.point i)).UpperLevel ≃ₜ (S.data (S.point j)).LowerLevel
  sublevel_image :
    ambient '' {x : M | f x ≤ S.upper (S.point i)} = {x : M | f x ≤ S.lower (S.point j)}
  level_coe : ∀ x : (S.data (S.point i)).UpperLevel, (level x : M) = ambient x

theorem Smale.ManifoldMorse.SurgeryWindows.nonempty_consecutiveBandData {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : Nonempty (S.BandData i j) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  obtain ⟨D, b, hD, hb⟩ := S.exists_consecutiveBandBridge hf i j hij
  exact ⟨⟨D, b.toHomeomorph, hD, hb⟩⟩

def Smale.ManifoldMorse.SurgeryWindows.consecutiveBandData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (i j : Fin S.count) (hij : i.val + 1 = j.val) : S.BandData i j :=
  Classical.choice (S.nonempty_consecutiveBandData hf i j hij)

def Smale.ManifoldMorse.SurgeryWindows.BandData.sublevelHomeomorph {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : Smale.ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j) :
    { x : M // f x ≤ S.upper (S.point i) } ≃ₜ { x : M // f x ≤ S.lower (S.point j) } :=
  (S.data (S.point i)).bandSublevelHomeomorph (S.data (S.point j)) D.ambient.toHomeomorph
    D.sublevel_image

def Smale.ManifoldMorse.SurgeryWindows.BandData.homologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : Smale.ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point i) } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } k :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv D.sublevelHomeomorph k

theorem Smale.SublevelDisk.contractibleSpace {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    {n : ℕ} (d : Smale.SublevelDisk n f a) : ContractibleSpace { x : M // f x ≤ a } := by
  let : ContractibleSpace (Smale.Hemisphere.Ball n) :=
    (convex_closedBall (0 : Smale.Hemisphere.Ambient n) 1).contractibleSpace ⟨0, by simp⟩
  exact d.homeomorph.symm.contractibleSpace

theorem Smale.SublevelDisk.homology_subsingleton {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} {n : ℕ} (d : Smale.SublevelDisk n f a) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology { x : M // f x ≤ a } k) := by
  let := d.contractibleSpace
  exact PeriodTorusHigherHomology.contractible_homology_subsingleton _ k hk

theorem Smale.ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val → 2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } 1) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          Subsingleton
            (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) }
              1) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 1 one_ne_zero
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n, hn'⟩) + (S.data (S.point ⟨n, hn'⟩)).radius ^ 2 } 1) :=
        ih hn' (by omega)
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨n, hn'⟩ ⟨n + 1, hn⟩ rfl
      let H :=
        (S.data (S.point ⟨n, hn'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨n + 1, hn⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
            1) :=
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton
      exact
        (S.data (S.point ⟨n + 1, hn⟩)).upperHomologyOne_subsingleton hf.continuous
          (hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj)
  have hp : j.val - 1 < S.count := by omega
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val - 1, hp⟩) + (S.data (S.point ⟨j.val - 1, hp⟩)).radius ^ 2 }
        1) :=
    hupper (j.val - 1) hp (by omega)
  obtain ⟨T, _, hT, _⟩ :=
    S.exists_consecutiveBandBridge hf ⟨j.val - 1, hp⟩ j (by change j.val - 1 + 1 = j.val; omega)
  let H :=
    (S.data (S.point ⟨j.val - 1, hp⟩)).bandSublevelHomeomorph (S.data (S.point j)) T.toHomeomorph
      hT
  exact (PeriodTorusHigherHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton

theorem Smale.ManifoldMorse.MorseSurgeryData.attachingHomology_subsingleton_of_index {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) := by
  let n := Module.finrank ℝ d.chart.NegativeCoordinates - 2
  have hn : Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1 := by
    dsimp [n]
    omega
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = (n + 1) + 1) := ⟨hn⟩
  let :
    Subsingleton (SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :=
    SphereHomology.unitSphere_homology_subsingleton n k hk (by omega)
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
            (n + 1)).symm.toHomeomorph
        k).injective.subsingleton

theorem Smale.ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_index
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  let := d.attachingHomology_subsingleton_of_index k hk hindex hne
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf k hk

def Smale.LinearSphereAction.puncturedMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hi : Function.Injective A) :
    C(Metric.sphere (0 : E) 1, Smale.PuncturedRadial.Space F) :=
  ⟨fun x => ⟨A x.val, fun h => ne_zero_of_mem_unit_sphere x (hi (h.trans (map_zero A).symm))⟩,
    (A.continuous.comp continuous_subtype_val).subtype_mk _⟩

def Smale.LinearSphereAction.sphereMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (hi : Function.Injective A) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : F) 1) :=
  Smale.PuncturedRadial.toSphere.comp (puncturedMap A hi)

theorem Smale.LinearSphereAction.sphereMap_id {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    sphereMap (ContinuousLinearMap.id ℝ E) Function.injective_id =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  ext x
  change ‖(x : E)‖⁻¹ • (x : E) = (x : E)
  rw [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

theorem Smale.LinearSphereAction.component_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {signWeight : ℝ}
    (A : Degree.LinearFramePaths.operatorComponent (D := E) signWeight) :
    Function.Injective A.val := by
  have hd : A.val.toLinearMap.det ≠ 0 := by
    intro hz
    have hp : 0 < signWeight * A.val.toLinearMap.det := A.property
    rw [hz, MulZeroClass.mul_zero] at hp
    exact lt_irrefl _ hp
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)

def Smale.LinearSphereAction.componentHomotopy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {signWeight : ℝ}
    {A B : Degree.LinearFramePaths.operatorComponent (D := E) signWeight} (γ : Path A B) :
    (sphereMap A.val (component_injective A)).Homotopy (sphereMap B.val (component_injective B))
    where
  toFun q := sphereMap (γ q.1).val (component_injective (γ q.1)) q.2
  continuous_toFun := by
    have hA : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => (γ q.1).val) :=
      continuous_subtype_val.comp (γ.continuous.comp continuous_fst)
    have hx : Continuous (fun q : (unitInterval) × Metric.sphere (0 : E) 1 => q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact Smale.PuncturedRadial.toSphere.continuous.comp ((hA.clm_apply hx).subtype_mk _)
  map_zero_left
    x := by
    change sphereMap (γ 0).val (component_injective (γ 0)) x = _
    rw [γ.source]
  map_one_left
    x := by
    change sphereMap (γ 1).val (component_injective (γ 1)) x = _
    rw [γ.target]

theorem Smale.LinearSphereAction.homotopic_of_det_mul_pos {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] [Nontrivial ι]
    (b : Module.Basis ι ℝ E) (A B : E ≃L[ℝ] E)
    (h : 0 < A.toLinearEquiv.toLinearMap.det * B.toLinearEquiv.toLinearMap.det) :
    (sphereMap A.toContinuousLinearMap A.injective).Homotopic
      (sphereMap B.toContinuousLinearMap B.injective) := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := by
    intro hz
    rw [hz, MulZeroClass.zero_mul] at h
    exact lt_irrefl _ h
  let A' : Degree.LinearFramePaths.operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨A.toContinuousLinearMap, mul_self_pos.mpr hd⟩
  let B' : Degree.LinearFramePaths.operatorComponent (D := E) A.toLinearEquiv.toLinearMap.det :=
    ⟨B.toContinuousLinearMap, h⟩
  exact ⟨componentHomotopy (Degree.LinearFramePaths.joined_operatorComponent b A' B').somePath⟩

theorem Smale.LinearSphereAction.sphereMap_comp {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E →L[ℝ] F) (B : F →L[ℝ] G) (hA : Function.Injective A)
    (hB : Function.Injective B) :
    (sphereMap B hB).comp (sphereMap A hA) = sphereMap (B.comp A) (hB.comp hA) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (B (‖A x.val‖⁻¹ • A x.val)) = NormedSpace.normalize (B (A x.val))
  rw [map_smul]
  exact
    NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (puncturedMap A hA x).property)) _

theorem Smale.LinearSphereAction.sphereMap_trans {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (A : E ≃L[ℝ] F) (B : F ≃L[ℝ] G) :
    sphereMap (A.trans B).toContinuousLinearMap (A.trans B).injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap A.toContinuousLinearMap A.injective) :=
  (sphereMap_comp A.toContinuousLinearMap B.toContinuousLinearMap A.injective B.injective).symm

theorem Smale.LinearSphereAction.normalized_linearSphereMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E ≃L[ℝ] F) (r : ℝ)
    (hr : 0 < r) :
    Smale.PuncturedRadial.toSphere.comp (Smale.LocalDegree.linearSphereMap A r hr) =
      sphereMap A.toContinuousLinearMap A.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change NormedSpace.normalize (A (r • x.val)) = NormedSpace.normalize (A x.val)
  rw [map_smul, NormedSpace.normalize_smul_of_pos hr]

theorem Smale.LinearSphereAction.sphereMap_relative {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A B : E ≃L[ℝ] F) :
    sphereMap A.toContinuousLinearMap A.injective =
      (sphereMap B.toContinuousLinearMap B.injective).comp
        (sphereMap (A.trans B.symm).toContinuousLinearMap (A.trans B.symm).injective) := by
  rw [← sphereMap_trans]
  have heq : (A.trans B.symm).trans B = A := by
    ext x
    exact B.apply_symm_apply (A x)
  rw [heq]

def Smale.LinearSphereAction.sphereHomotopyEquiv {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₕ Metric.sphere (0 : F) 1 :=
  (Smale.LocalDegree.linearSphereEquiv B 1 zero_lt_one).trans
    (Smale.PuncturedRadial.sphereHomotopyEquiv 1 zero_lt_one).symm

theorem Smale.LinearSphereAction.sphereHomotopyEquiv_toFun {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) :
    (sphereHomotopyEquiv B).toFun = sphereMap B.toContinuousLinearMap B.injective :=
  normalized_linearSphereMap B 1 zero_lt_one

def Smale.LinearSphereAction.homologyEquiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : F) 1) k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (sphereHomotopyEquiv B) k

theorem Smale.LinearSphereAction.homologyEquiv_apply {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k) :
    homologyEquiv B k a =
      SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective) k
        a := by
  change SingularMayerVietoris.singularHomologyMap (sphereHomotopyEquiv B).toFun k a = _
  rw [sphereHomotopyEquiv_toFun]

theorem Smale.SpherePoint.hyperplaneReflection_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (u : V) (hu : u ≠ 0) :
    ((ℝ ∙ u)ᗮ.reflection).toLinearMap.det = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hu,
    pow_one]

theorem Smale.SpherePoint.positive_transport_of_normal {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (v w : Metric.sphere (0 : V) 1) (u : V)
    (hu : u ≠ 0) (huw : Inner.inner ℝ u w.val = 0) (hvw : v ≠ w) :
    ∃ R : V ≃ₗᵢ[ℝ] V, R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  have hvw' : (v : V) - (w : V) ≠ 0 := by
    intro h
    exact hvw (Subtype.ext (sub_eq_zero.mp h))
  let R₁ := (ℝ ∙ ((v : V) - (w : V)))ᗮ.reflection
  let R₂ := (ℝ ∙ u)ᗮ.reflection
  have h₁ : R₁ v.val = w.val :=
    Submodule.reflection_sub
      ((mem_sphere_zero_iff_norm.mp v.property).trans
        (mem_sphere_zero_iff_norm.mp w.property).symm)
  have h₂ : R₂ w.val = w.val :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huw)
  refine ⟨R₁.trans R₂, ?_, ?_⟩
  · change R₂ (R₁ v.val) = w.val
    rw [h₁, h₂]
  · change (R₂.toLinearMap.comp R₁.toLinearMap).det = 1
    rw [LinearMap.det_comp, hyperplaneReflection_det u hu,
      hyperplaneReflection_det ((v : V) - (w : V)) hvw']
    norm_num

theorem Smale.SpherePoint.exists_positive_transport (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    ∃ R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)),
      R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  by_cases hvw : v = w
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_, ?_⟩
    · exact congrArg Subtype.val hvw
    · exact LinearMap.det_id
  · let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) := ⟨by simp⟩
    let b :=
      OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1) (ne_zero_of_mem_unit_sphere w)
    let u : EuclideanSpace ℝ (Fin (n + 2)) :=
      (b (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)))
    have hun : ‖u‖ = 1 := b.norm_eq_one 0
    have hu : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hun
      exact zero_ne_one hun
    have huw : Inner.inner ℝ u w.val = 0 := by
      have h := (b (0 : Fin (n + 1))).property
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp h
    exact positive_transport_of_normal v w u hu huw hvw

def Smale.SpherePoint.positiveTransport (n : ℕ) (v w : SphereHomology.UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Classical.choose (exists_positive_transport n v w)

theorem Smale.SpherePoint.positiveTransport_apply (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : positiveTransport n v w v.val = w.val :=
  (Classical.choose_spec (exists_positive_transport n v w)).1

theorem Smale.SpherePoint.positiveTransport_det (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) : (positiveTransport n v w).toLinearMap.det = 1 :=
  (Classical.choose_spec (exists_positive_transport n v w)).2

def Smale.SuspensionReflection.reflect {X : Type} [TopologicalSpace X] :
    C(Suspension.topSus X, Suspension.topSus X)
    where
  toFun :=
    Quotient.lift (fun q => Suspension.topSus.mk (unitInterval.symm q.1) q.2)
      (by
        rintro a b ⟨ht, h0 | h1 | hx⟩
        · apply (Suspension.topSus.mk_eq_mk_iff _ _ _ _).mpr
          refine ⟨congrArg unitInterval.symm ht, Or.inr (Or.inl ?_)⟩
          simp [h0]
        · apply (Suspension.topSus.mk_eq_mk_iff _ _ _ _).mpr
          refine ⟨congrArg unitInterval.symm ht, Or.inl ?_⟩
          simp [h1]
        · exact
            (Suspension.topSus.mk_eq_mk_iff _ _ _ _).mpr
              ⟨congrArg unitInterval.symm ht, Or.inr (Or.inr hx)⟩)
  continuous_toFun :=
    Suspension.topSus.isQuotientMap_mk.continuous_iff.mpr
      (Suspension.topSus.continuous_mk.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))

theorem Smale.SuspensionReflection.reflect_mk {X : Type} [TopologicalSpace X] (t : (unitInterval))
    (x : X) :
    reflect (Suspension.topSus.mk t x) =
      Suspension.topSus.mk (unitInterval.symm t) x :=
  rfl

theorem Smale.SuspensionReflection.reflect_height {X : Type} [TopologicalSpace X]
    (x : Suspension.topSus X) :
    Suspension.topSus.height (reflect x) =
      unitInterval.symm (Suspension.topSus.height x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.topSus.mk_surjective x
  rfl

theorem Smale.SuspensionReflection.reflect_north {X : Type} [TopologicalSpace X] :
    Set.MapsTo (reflect (X := X)) Suspension.topSus.northOpen
      Suspension.topSus.southOpen := by
  intro x hx
  change (Suspension.topSus.height x : ℝ) < 3 / 4 at hx
  change 1 / 4 < (Suspension.topSus.height (reflect x) : ℝ)
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith

theorem Smale.SuspensionReflection.reflect_south {X : Type} [TopologicalSpace X] :
    Set.MapsTo (reflect (X := X)) Suspension.topSus.southOpen
      Suspension.topSus.northOpen := by
  intro x hx
  change 1 / 4 < (Suspension.topSus.height x : ℝ) at hx
  change (Suspension.topSus.height (reflect x) : ℝ) < 3 / 4
  rw [reflect_height, unitInterval.coe_symm_eq]
  linarith

def Smale.SuspensionReflection.middleMap {X : Type} [TopologicalSpace X] :
    C(Suspension.topSus.middleBand X, Suspension.topSus.middleBand X) :=
  Smale.CoverNaturality.reversingIntersectionMap _ _ _ _ reflect reflect_north reflect_south

theorem Smale.SuspensionReflection.middle_projection {X : Type} [TopologicalSpace X]
    (x : Suspension.topSus.middleBand X) :
    Suspension.topSus.middleBandHomotopyEquiv (middleMap x) =
      Suspension.topSus.middleBandHomotopyEquiv x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.topSus.middleBandHomeomorph.symm.surjective x
  let q : Set.Ioo (1 / 4 : ℝ) (3 / 4) × X :=
    (⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩, u)
  have hpoint :
    middleMap (Suspension.topSus.middleBandHomeomorph.symm (t, u)) =
      Suspension.topSus.middleBandHomeomorph.symm q := by
    apply Subtype.ext
    change reflect (Suspension.topSus.mk _ u) = Suspension.topSus.mk _ u
    rw [reflect_mk]
    congr 1
  rw [hpoint, Suspension.topSus.middleBandHomotopyEquiv_apply,
    Suspension.topSus.middleBandHomotopyEquiv_apply, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

theorem Smale.SuspensionReflection.middle_projection_comp {X : Type} [TopologicalSpace X] :
    (Suspension.topSus.middleBandHomotopyEquiv (X := X)).toFun.comp middleMap =
      (Suspension.topSus.middleBandHomotopyEquiv (X := X)).toFun :=
  ContinuousMap.ext middle_projection

noncomputable def NoExotic.hyperplaneReflectionOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v : E) : E →L[ℝ] E :=
  ((ℝ ∙ v)ᗮ.reflection).toContinuousLinearEquiv.toContinuousLinearMap

theorem NoExotic.hyperplaneReflectionOperator_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    hyperplaneReflectionOperator v w = w - (2 * (‖v‖ ^ 2)⁻¹ * Inner.inner ℝ v w) • v := by
  change (ℝ ∙ v)ᗮ.reflection w = _
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [← add_smul]
  apply congrArg (fun r : ℝ ↦ w - r • v)
  simp only [div_eq_mul_inv]
  ring

def Smale.SphereReflection.linearReflection (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  (ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection

theorem Smale.SphereReflection.linearReflection_apply (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 2))) :
    linearReflection n y = y - (2 * y 0) • EuclideanSpace.single 0 (1 : ℝ) := by
  change NoExotic.hyperplaneReflectionOperator (EuclideanSpace.single 0 (1 : ℝ)) y = _
  rw [NoExotic.hyperplaneReflectionOperator_apply]
  simp only [PiLp.norm_single, NormOneClass.norm_one, one_pow, inv_one, mul_one,
    EuclideanSpace.inner_single_left, map_one, one_mul]

theorem Smale.SphereReflection.linearReflection_zero (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (n + 2))) : linearReflection n y 0 = -y 0 := by
  rw [linearReflection_apply]
  change y 0 - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) 0 = _
  simp
  ring

theorem Smale.SphereReflection.linearReflection_succ (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) : linearReflection n y i.succ = y i.succ := by
  rw [linearReflection_apply]
  change y i.succ - (2 * y 0) * (EuclideanSpace.single 0 (1 : ℝ)) i.succ = _
  simp

theorem Smale.SphereReflection.linearReflection_det (n : ℕ) :
    (linearReflection n).toLinearMap.det = -1 := by
  have hv : (EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ)) ≠ 0 := by simp
  change
    LinearMap.det
        ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 2)) (1 : ℝ))ᗮ.reflection).toLinearMap =
      _
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv,
    pow_one]

def Smale.SphereReflection.sphereMap (n : ℕ) :
    C(SphereHomology.UnitSphere (n + 1), SphereHomology.UnitSphere (n + 1))
    where
  toFun
    x :=
    ⟨linearReflection n x.val, by
      rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map,
        SphereHomology.unitSphere_norm]⟩
  continuous_toFun := ((linearReflection n).continuous.comp continuous_subtype_val).subtype_mk _

theorem Smale.SphereReflection.height_symm (t : (unitInterval)) :
    SphereHomology.Latitude.height (unitInterval.symm t) = -SphereHomology.Latitude.height t := by
  simp only [SphereHomology.Latitude.height, unitInterval.coe_symm_eq]
  ring

theorem Smale.SphereReflection.radius_symm (t : (unitInterval)) :
    SphereHomology.Latitude.radius (unitInterval.symm t) = SphereHomology.Latitude.radius t := by
  simp only [SphereHomology.Latitude.radius, height_symm, neg_sq]

theorem Smale.SphereReflection.sphereMap_latitude (n : ℕ) (t : (unitInterval))
    (x : SphereHomology.UnitSphere n) :
    sphereMap n (SphereHomology.Latitude.point n t x) =
      SphereHomology.Latitude.point n (unitInterval.symm t) x := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change
      linearReflection n (SphereHomology.Latitude.vector n t x) 0 =
        SphereHomology.Latitude.vector n (unitInterval.symm t) x 0
    rw [linearReflection_zero, SphereHomology.Latitude.vector_zero,
      SphereHomology.Latitude.vector_zero, height_symm]
  · change
      linearReflection n (SphereHomology.Latitude.vector n t x) j.succ =
        SphereHomology.Latitude.vector n (unitInterval.symm t) x j.succ
    rw [linearReflection_succ, SphereHomology.Latitude.vector_succ,
      SphereHomology.Latitude.vector_succ, radius_symm]

theorem Smale.SphereReflection.sphereMap_suspension (n : ℕ)
    (x : Suspension.topSus (SphereHomology.UnitSphere n)) :
    sphereMap n (SphereHomology.suspensionSphereHomeomorph n x) =
      SphereHomology.suspensionSphereHomeomorph n (Smale.SuspensionReflection.reflect x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := Suspension.topSus.mk_surjective x
  rw [SphereHomology.suspensionSphereHomeomorph_mk, sphereMap_latitude,
    Smale.SuspensionReflection.reflect_mk, SphereHomology.suspensionSphereHomeomorph_mk]

theorem Smale.SphereReflection.sphereMap_comp_suspension (n : ℕ) :
    (sphereMap n).comp (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun =
      (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun.comp
        Smale.SuspensionReflection.reflect :=
  ContinuousMap.ext (sphereMap_suspension n)

theorem Smale.SuspensionReflection.middle_homology {X : Type} [TopologicalSpace X] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Suspension.topSus.middleBand X) k) :
    SingularMayerVietoris.singularHomologyMap middleMap k a = a := by
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        Suspension.topSus.middleBandHomotopyEquiv k).injective
  change
    SingularMayerVietoris.singularHomologyMap
        Suspension.topSus.middleBandHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap middleMap k a) =
      SingularMayerVietoris.singularHomologyMap
        Suspension.topSus.middleBandHomotopyEquiv.toFun k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    middle_projection_comp]

theorem Smale.SuspensionReflection.reflect_homology {X : Type} [TopologicalSpace X] [Nonempty X]
    (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Suspension.topSus X) (n + 1)) :
    SingularMayerVietoris.singularHomologyMap reflect (n + 1) a = -a := by
  apply
    CuspCentralHomology.contractibleCoverConnecting_injective
      Suspension.topSus.northOpen Suspension.topSus.southOpen
      Suspension.topSus.northOpen_isOpen
      Suspension.topSus.southOpen_isOpen Suspension.topSus.open_cover n
  rw [Smale.CoverNaturality.connecting_reversing_naturality
      Suspension.topSus.northOpen Suspension.topSus.southOpen
      Suspension.topSus.northOpen Suspension.topSus.southOpen reflect
      reflect_north reflect_south Suspension.topSus.northOpen_isOpen
      Suspension.topSus.southOpen_isOpen Suspension.topSus.open_cover
      Suspension.topSus.northOpen_isOpen
      Suspension.topSus.southOpen_isOpen Suspension.topSus.open_cover n
      a]
  change
    -SingularMayerVietoris.singularHomologyMap middleMap n
          (SingularMayerVietoris.connectingHomomorphism _ _ _ _ _ n a) =
      _
  rw [middle_homology, map_neg]

theorem Smale.SphereReflection.sphereMap_homology (n k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap n) (k + 1) a = -a := by
  obtain ⟨b, rfl⟩ :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv (k + 1)).surjective
      a
  change
    SingularMayerVietoris.singularHomologyMap (sphereMap n) (k + 1)
        (SingularMayerVietoris.singularHomologyMap
          (SphereHomology.suspensionSphereHomeomorph n).toHomotopyEquiv.toFun (k + 1) b) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    sphereMap_comp_suspension, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, Smale.SuspensionReflection.reflect_homology, map_neg]
  rfl

theorem Smale.LinearSphereAction.sphereMap_reflection (n : ℕ) :
    sphereMap
        (Smale.SphereReflection.linearReflection n).toContinuousLinearEquiv.toContinuousLinearMap
        (Smale.SphereReflection.linearReflection n).injective =
      Smale.SphereReflection.sphereMap n := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    ‖Smale.SphereReflection.linearReflection n x.val‖⁻¹ •
        Smale.SphereReflection.linearReflection n x.val =
      Smale.SphereReflection.linearReflection n x.val
  rw [LinearIsometryEquiv.norm_map, SphereHomology.unitSphere_norm, inv_one, one_smul]

theorem Smale.LinearSphereAction.homology_of_det_pos (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : 0 < A.toLinearEquiv.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) k
        a =
      a := by
  have hh :=
    homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis A
      (ContinuousLinearEquiv.refl ℝ _)
      (by
        change 0 < A.toLinearEquiv.toLinearMap.det * (LinearMap.id : _ →ₗ[ℝ] _).det
        rwa [LinearMap.det_id, mul_one])
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hh k]
  change
    SingularMayerVietoris.singularHomologyMap
        (sphereMap (ContinuousLinearMap.id ℝ _) Function.injective_id) k a =
      a
  rw [sphereMap_id, PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

theorem Smale.LinearSphereAction.homology_of_det_neg (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : A.toLinearEquiv.toLinearMap.det < 0) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      -a := by
  have hh :=
    homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis A
      (Smale.SphereReflection.linearReflection n).toContinuousLinearEquiv
      (by
        change
          0 <
            A.toLinearEquiv.toLinearMap.det *
              (Smale.SphereReflection.linearReflection n).toLinearMap.det
        rw [Smale.SphereReflection.linearReflection_det, mul_neg_one]
        exact neg_pos.mpr h)
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hh (k + 1), sphereMap_reflection,
    Smale.SphereReflection.sphereMap_homology]

theorem Smale.LinearSphereAction.homology_eq_sign_smul (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2))) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign A.toLinearEquiv.toLinearMap.det : ℤ) • a := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  obtain hn | hp := lt_or_gt_of_ne hd
  · rw [homology_of_det_neg n A hn, sign_eq_neg_one_iff.mpr hn]
    simp
  · rw [homology_of_det_pos n A hp, sign_eq_one_iff.mpr hp]
    simp

def Smale.SpherePoint.sphereHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (R : V ≃ₗᵢ[ℝ] V) : Metric.sphere (0 : V) 1 ≃ₜ Metric.sphere (0 : V) 1 :=
  R.toContinuousLinearEquiv.toHomeomorph.subtype
    (fun x => by
      simp only [mem_sphere_zero_iff_norm]
      change ‖x‖ = 1 ↔ ‖R x‖ = 1
      rw [R.norm_map])

theorem Smale.SpherePoint.sphereHomeomorph_eq_normalized {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (R : V ≃ₗᵢ[ℝ] V) :
    (sphereHomeomorph R).toHomotopyEquiv.toFun =
      Smale.LinearSphereAction.sphereMap R.toContinuousLinearEquiv.toContinuousLinearMap
        R.injective := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change R x.val = ‖R x.val‖⁻¹ • R x.val
  rw [R.norm_map, mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul]

theorem Smale.SpherePoint.contMDiff_sphereHomeomorph {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereHomeomorph R) := by
  have h : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞ (fun x : Metric.sphere (0 : V) 1 => R x.val) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.comp
      (contMDiff_coe_sphere (m := ∞))
  exact h.codRestrict_sphere (n := n) (fun x => (sphereHomeomorph R x).property)

def Smale.SpherePoint.sphereDiffeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] (R : V ≃ₗᵢ[ℝ] V) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : V) 1) (Metric.sphere (0 : V) 1) ∞
    where
  toEquiv := (sphereHomeomorph R).toEquiv
  contMDiff_toFun := contMDiff_sphereHomeomorph R
  contMDiff_invFun := contMDiff_sphereHomeomorph R.symm

theorem Smale.SpherePoint.sphereHomeomorph_homology_of_det_pos (n : ℕ)
    (R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (hR : 0 < R.toLinearMap.det) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap (sphereHomeomorph R).toHomotopyEquiv.toFun k a =
      a := by
  rw [sphereHomeomorph_eq_normalized]
  exact Smale.LinearSphereAction.homology_of_det_pos n R.toContinuousLinearEquiv hR k a

theorem Smale.SpherePoint.positiveTransport_moves (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) :
    sphereHomeomorph (positiveTransport n v w) v = w :=
  Subtype.ext (positiveTransport_apply n v w)

theorem Smale.SpherePoint.positiveTransport_homology (n : ℕ)
    (v w : SphereHomology.UnitSphere (n + 1)) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) k) :
    SingularMayerVietoris.singularHomologyMap
        (sphereHomeomorph (positiveTransport n v w)).toHomotopyEquiv.toFun k a =
      a := by
  apply sphereHomeomorph_homology_of_det_pos n _ _ k a
  rw [positiveTransport_det]
  norm_num

theorem Smale.LocalDegree.NativeNeighborhood.singlePoint_cover {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    { x }ᶜ ∪ openSet x d = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases h : y = x
  · subst y
    exact Or.inr (center_mem_openSet x d)
  · exact Or.inl h

theorem Smale.LocalDegree.NativeNeighborhood.openSet_contractible {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) :
    ContractibleSpace (openSet x d) := by
  let : ContractibleSpace (Metric.ball (0 : E) d.radius) :=
    (convex_ball (0 : E) d.radius).contractibleSpace ⟨0, by simpa using d.radius_pos⟩
  exact
    (Smale.ChartPuncturedBall.ballHomeomorph
        (Smale.NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
        (closedBall_subset_source x d)).symm.contractibleSpace

def Smale.LocalDegree.NativeNeighborhood.sphereConnecting {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) k :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d)
        k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism { x }ᶜ (openSet x d)
      isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k)

def Smale.LocalDegree.NativeNeighborhood.sphereHomologyEquiv {E F M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] [ContractibleSpace ({ x }ᶜ : Set M)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology M (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : E) 1) (k + 1) := by
  let : ContractibleSpace (openSet x d) := openSet_contractible x d
  exact
    (CuspCentralHomology.contractibleCoverHomologyHigherEquiv { x }ᶜ (openSet x d)
          isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k).trans
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv x d) (k + 1)).symm

theorem Smale.NativeParametrization.centered_symm_self {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) :
    (centered (D := E) x).symm x = 0 := by
  have h := (centered (D := E) x).left_inv' (zero_mem_centered_source x)
  rwa [centered_zero] at h

def Smale.NativeChartTransition.chart {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  ((Smale.NativeParametrization.centered (D := E) x).trans e.toPartialDiffeomorph).trans
    (Smale.NativeParametrization.centered (D := E) y).symm

theorem Smale.NativeChartTransition.chart_apply {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (u : E) :
    chart x y e u =
      (Smale.NativeParametrization.centered (D := E) y).symm
        (e (Smale.NativeParametrization.centered (D := E) x u)) :=
  rfl

theorem Smale.NativeChartTransition.zero_mem_source {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) : (0 : E) ∈ (chart x y e).source := by
  change
    (0 ∈ (Smale.NativeParametrization.centered (D := E) x).source ∧
        Smale.NativeParametrization.centered (D := E) x 0 ∈ (Set.univ : Set M)) ∧
      e (Smale.NativeParametrization.centered (D := E) x 0) ∈
        (Smale.NativeParametrization.centered (D := E) y).target
  refine ⟨⟨Smale.NativeParametrization.zero_mem_centered_source x, Set.mem_univ _⟩, ?_⟩
  rw [Smale.NativeParametrization.centered_zero, he]
  exact Smale.NativeParametrization.mem_centered_target y

theorem Smale.NativeChartTransition.chart_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) : chart x y e (0 : E) = 0 := by
  rw [chart_apply, Smale.NativeParametrization.centered_zero, he,
    Smale.NativeParametrization.centered_symm_self]

theorem Smale.NativeChartTransition.contDiffAt_chart {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) :
    ContDiffAt ℝ ∞ (chart x y e) (0 : E) :=
  ((chart x y e).contMDiffOn_toFun.contMDiffAt
      ((chart x y e).open_source.mem_nhds (zero_mem_source x y e he))).contDiffAt

theorem Smale.NativeChartTransition.bijective_derivative {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) :
    Function.Bijective (fderiv ℝ (chart x y e) (0 : E)) := by
  have h := Smale.PartialChart.bijective_mfderiv (chart x y e) (zero_mem_source x y e he)
  rwa [mfderiv_eq_fderiv] at h

def Smale.NativeChartTransition.linear {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective (fderiv ℝ (chart x y e) (0 : E)).toLinearMap
      (bijective_derivative x y e he)).toContinuousLinearEquiv

theorem Smale.NativeChartTransition.linear_eq_derivative {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] :
    (linear x y e he).toContinuousLinearMap = fderiv ℝ (chart x y e) (0 : E) :=
  rfl

theorem Smale.NativeChartTransition.hasFDerivAt_chart {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] :
    HasFDerivAt (chart x y e) (linear x y e he).toContinuousLinearMap 0 := by
  rw [linear_eq_derivative]
  exact ((contDiffAt_chart x y e he).differentiableAt (by simp)).hasFDerivAt

theorem Smale.NativeChartTransition.nonempty_neighborhoodData {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) [FiniteDimensional ℝ E] (W : Set M)
    (hW : W ∈ 𝓝 x) :
    Nonempty
      (Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        (linear x y e he)
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W)) := by
  let c := Smale.NativeParametrization.centered (D := E) x
  have hc0 : (0 : E) ∈ c.source := Smale.NativeParametrization.zero_mem_centered_source x
  have hcx : c 0 = x := Smale.NativeParametrization.centered_zero x
  have hc : ContinuousAt c (0 : E) :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hc0)
  have hs : c.source ∩ c ⁻¹' W ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (c.open_source.mem_nhds hc0) (hc (hcx.symm ▸ hW))
  exact
    Smale.LocalDegree.nonempty_neighborhoodData_of_contDiffAt (linear x y e he)
      (hasFDerivAt_chart x y e he) (chart_zero x y e he) hs (contDiffAt_chart x y e he)

theorem Smale.SpherePoint.ambient_chart_hasFDerivAt {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source) :
    HasFDerivAt (fun u => (c u : V)) (fderiv ℝ (fun u => (c u : V)) z) z := by
  have hc : ContDiffOn ℝ ∞ (fun u => (c u : V)) c.source :=
    ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).comp_contMDiffOn c.contMDiffOn_toFun).contDiffOn
  exact ((hc.contDiffAt (c.open_source.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt

theorem Smale.SpherePoint.chart_transition_eventually_eq {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (fun u : EuclideanSpace ℝ (Fin m) =>
        (Smale.NativeParametrization.centered y
            (Smale.NativeChartTransition.chart x y (sphereDiffeomorph (n := m) R) u) :
          V)) =ᶠ[𝓝 0]
      (fun u : EuclideanSpace ℝ (Fin m) => R (Smale.NativeParametrization.centered x u : V)) := by
  let e := sphereDiffeomorph (n := m) R
  let T := Smale.NativeChartTransition.chart x y e
  have hS := T.open_source.mem_nhds (Smale.NativeChartTransition.zero_mem_source x y e he)
  filter_upwards [hS] with u hu
  have ht :
    e (Smale.NativeParametrization.centered x u) ∈
      (Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin m)) y).target :=
    hu.2
  have h := (Smale.NativeParametrization.centered y).right_inv' ht
  exact congrArg Subtype.val h

theorem Smale.SpherePoint.chart_transition_ambient_derivative {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (fderiv ℝ (fun u => (Smale.NativeParametrization.centered y u : V)) 0).comp
        (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toContinuousLinearMap =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fun u => (Smale.NativeParametrization.centered x u : V)) 0) := by
  let e := sphereDiffeomorph (n := m) R
  let T := Smale.NativeChartTransition.chart x y e
  have hx :=
    ambient_chart_hasFDerivAt (m := m) (Smale.NativeParametrization.centered x)
      (Smale.NativeParametrization.zero_mem_centered_source x)
  have hy :=
    ambient_chart_hasFDerivAt (m := m) (Smale.NativeParametrization.centered y)
      (Smale.NativeParametrization.zero_mem_centered_source y)
  have hyT :
    HasFDerivAt
      (fun u : EuclideanSpace ℝ (Fin m) => (Smale.NativeParametrization.centered y u : V))
      (fderiv ℝ (fun u => (Smale.NativeParametrization.centered y u : V)) 0) (T 0) :=
    (Smale.NativeChartTransition.chart_zero x y e he).symm ▸ hy
  have hchain := hyT.comp 0 (Smale.NativeChartTransition.hasFDerivAt_chart x y e he)
  have hR := R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0 hx
  exact hchain.unique (hR.congr_of_eventuallyEq (chart_transition_eventually_eq x y R he))

theorem Smale.SpherePoint.chart_radial_frame_comp {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) :
    (Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
            0).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap
          (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toContinuousLinearMap) =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
          0) := by
  apply ContinuousLinearMap.ext
  intro z
  have hD :=
    congrArg (fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] V => A z.2)
      (chart_transition_ambient_derivative x y R he)
  have hcenter :
    R (Smale.NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) =
      (Smale.NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) := by
    rw [Smale.NativeParametrization.centered_zero, Smale.NativeParametrization.centered_zero]
    exact congrArg Subtype.val he
  change
    z.1 • (Smale.NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) +
        (fderiv ℝ (fun u => (Smale.NativeParametrization.centered y u : V)) 0)
          (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he z.2) =
      R
        (z.1 • (Smale.NativeParametrization.centered x (0 : EuclideanSpace ℝ (Fin m)) : V) +
          (fderiv ℝ (fun u => (Smale.NativeParametrization.centered x u : V)) 0) z.2)
  rw [map_add, map_smul, hcenter]
  exact
    congrArg
      (fun v : V =>
        z.1 • (Smale.NativeParametrization.centered y (0 : EuclideanSpace ℝ (Fin m)) : V) + v)
      hD

theorem Smale.LinearSphereAction.homology_relative_sign {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) (A B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective)
        (k + 1) a =
      (SignType.sign (A.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective)
          (k + 1) a := by
  rw [sphereMap_relative A B, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, homology_eq_sign_smul]
  exact map_zsmul _ _ _

theorem Smale.LocalDegree.BoundaryData.normalized_homology_compare {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {L : E ≃L[ℝ] F} {s : Set E} (b : Smale.LocalDegree.BoundaryData f L s) (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap k =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) k := by
  change
    SingularMayerVietoris.singularHomologyMap (Smale.PuncturedRadial.toSphere.comp b.map) k = _
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, b.homology_compare, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    Smale.LinearSphereAction.normalized_linearSphereMap]

theorem Smale.LocalDegree.BoundaryData.normalized_homology_eq_sign_smul {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) {f : EuclideanSpace ℝ (Fin (n + 2)) → F}
    {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (b : Smale.LocalDegree.BoundaryData f L s) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1) a =
      (SignType.sign (L.trans B.symm).toLinearEquiv.toLinearMap.det : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  rw [b.normalized_homology_compare]
  exact Smale.LinearSphereAction.homology_relative_sign n L B k a

def Smale.SphereNormalCoordinates.chartJacobian {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) (z : EuclideanSpace ℝ (Fin m)) :
    ℝ :=
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  ((chartRadialFrame c z).comp j'.symm.toContinuousLinearMap).det

theorem Smale.SphereNormalCoordinates.chartJacobian_ne_zero {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) : chartJacobian c j B z ≠ 0 :=
  (Smale.RegularValues.bijective_iff_det_ne_zero _).mp
    ((bijective_chartRadialFrame c hz).comp
      ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans
          j).symm.bijective)

theorem Smale.SphereNormalCoordinates.chartJacobian_factor {V F : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)) *
        (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      chartJacobian c j B z := by
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] F := mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)
  let C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) c z
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  have hd : fderiv ℝ (f ∘ c) z = A.comp C := by
    have h := mfderiv_comp z hf (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hB : (B.symm.toContinuousLinearMap.comp A).IsInvertible :=
    (show B.symm.toContinuousLinearMap.IsInvertible from ⟨B.symm, rfl⟩).comp hA
  have h := normalJacobian_mul_chartDet j' (c z) (B.symm.toContinuousLinearMap.comp A) hB C
  rw [normalJacobian_change_normal_model j B (c z) A hA] at h
  change normalJacobian j (c z) A * _ = _
  rw [hd]
  rw [← ContinuousLinearMap.comp_assoc]
  apply h.trans
  unfold chartJacobian
  rw [chartRadialFrame_eq c hz]

private theorem Smale.SphereNormalCoordinates.sign_factor_mo1973_5719 {a b c : ℝ} (hb : b ≠ 0)
    (h : a * b = c) : SignType.sign c * SignType.sign b = SignType.sign a := by
  have hsq : SignType.sign b * SignType.sign b = 1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hb)
  rw [← h, sign_mul, mul_assoc, hsq, mul_one]

theorem Smale.SphereNormalCoordinates.chartJacobian_sign_factor {V F : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) (EuclideanSpace ℝ (Fin m))
        (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) {z : EuclideanSpace ℝ (Fin m)}
    (hz : z ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    SignType.sign (chartJacobian c j B z) *
        SignType.sign (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
      SignType.sign (normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z))) := by
  have h := chartJacobian_factor c j B hz f hf hA
  apply sign_factor_mo1973_5719 _ h
  intro hd
  rw [hd, MulZeroClass.mul_zero] at h
  exact chartJacobian_ne_zero c j B hz h.symm

theorem Smale.SpherePoint.chart_radial_frame_det {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y)
    (j : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] V) :
    ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).det *
        (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
                0).comp
            j.symm.toContinuousLinearMap).det := by
  let L := Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R) he
  let Q := (ContinuousLinearMap.id ℝ ℝ).prodMap L.toContinuousLinearMap
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (Q.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = L.toLinearEquiv.toLinearMap.det := by
    have hconj : T.det = Q.det := LinearMap.det_conj Q.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) L.toLinearEquiv.toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor :
    ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
                0).comp
            j.symm.toContinuousLinearMap).comp
        T =
      R.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
              0).comp
          j.symm.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro v
    change
      Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y) 0
          (j.symm (j (Q (j.symm v)))) =
        R
          (Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered x)
            0 (j.symm v))
    rw [j.symm_apply_apply]
    exact
      congrArg (fun A : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] V => A (j.symm v))
        (chart_radial_frame_comp x y R he)
  calc
    _ =
        (((Smale.SphereNormalCoordinates.chartRadialFrame (Smale.NativeParametrization.centered y)
                    0).comp
                j.symm.toContinuousLinearMap).comp
            T).det := by
      rw [hdetT.symm]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := (congrArg ContinuousLinearMap.det hfactor).trans (LinearMap.det_comp _ _)

theorem Smale.SpherePoint.chartJacobian_transport {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (j : (ℝ × F) ≃L[ℝ] V)
    (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y) j B 0 *
        (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
            he).toLinearEquiv.toLinearMap.det =
      R.toLinearEquiv.toLinearMap.det *
        Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0 :=
  chart_radial_frame_det x y R he
    ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j)

theorem Smale.SpherePoint.chartJacobian_transport_sign {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]
    (x y : Metric.sphere (0 : V) 1) (R : V ≃ₗᵢ[ℝ] V) (he : sphereHomeomorph R x = y) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hR : R.toLinearEquiv.toLinearMap.det = 1)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F) :
    SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y) j
            B 0) *
        SignType.sign
          (Smale.NativeChartTransition.linear x y (sphereDiffeomorph (n := m) R)
              he).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0) := by
  have h := chartJacobian_transport x y R he j B
  rw [hR, one_mul] at h
  rw [← sign_mul, h]

theorem Smale.LocalDegree.PointTransition.maps_point_complement {M : Type} [TopologicalSpace M]
    (e : M ≃ₜ M) (x y : M) (he : e x = y) : Set.MapsTo e { x }ᶜ { y }ᶜ := by
  intro z hz h
  exact hz (e.injective (h.trans he.symm))

def Smale.LocalDegree.PointTransition.coordinateMap {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M)
    {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy)) :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) :=
  Smale.CoverNaturality.overlapCoordinateMap { x }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy)

theorem Smale.LocalDegree.PointTransition.coordinateMap_coe {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    (u : Metric.sphere (0 : E) 1) :
    (coordinateMap x y dx dy e he hV u).val =
      ‖(Smale.NativeParametrization.centered (D := E) y).symm
              (e
                (Smale.NativeParametrization.centered (D := E) x
                  (dx.innerBoundary.radius • (u : E))))‖⁻¹ •
        (Smale.NativeParametrization.centered (D := E) y).symm
          (e
            (Smale.NativeParametrization.centered (D := E) x
              (dx.innerBoundary.radius • (u : E)))) :=
  rfl

theorem Smale.LocalDegree.PointTransition.connecting_naturality {E F G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F} {Ly : E ≃L[ℝ] G}
    {Wx Wy : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : M ≃ₜ M) (he : e x = y)
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k
        (Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx k a) =
      Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) :=
  Smale.CoverNaturality.normalized_connecting_naturality { x }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet x dx) { y }ᶜ
    (Smale.LocalDegree.NativeNeighborhood.openSet y dy) e.toHomotopyEquiv.toFun
    (maps_point_complement e x y he) hV
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv x dx)
    (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv y dy) isClosed_singleton.isOpen_compl
    (Smale.LocalDegree.NativeNeighborhood.isOpen_openSet x dx)
    (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover x dx) isClosed_singleton.isOpen_compl
    (Smale.LocalDegree.NativeNeighborhood.isOpen_openSet y dy)
    (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover y dy) k a

def Smale.LocalDegree.NeighborhoodData.restrictRadius {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E ≃L[ℝ] F}
    {s : Set E} (d : Smale.LocalDegree.NeighborhoodData f L s) (r : ℝ) (hr : 0 < r)
    (hrR : r ≤ d.radius) : Smale.LocalDegree.NeighborhoodData f L s
    where
  radius := r
  radius_pos := hr
  center_zero := d.center_zero
  ball_subset := (Metric.closedBall_subset_closedBall hrR).trans d.ball_subset
  continuous := d.continuous.mono (Metric.closedBall_subset_closedBall hrR)
  remainder_bound x hx := d.remainder_bound x (Metric.closedBall_subset_closedBall hrR hx)

private theorem Smale.LocalDegree.NativeNeighborhood.identity_center_mo1973_5731 {M : Type}
    [TopologicalSpace M] (x : M) : (Homeomorph.refl M) x = x :=
  rfl

theorem Smale.LocalDegree.NativeNeighborhood.openSet_restrictRadius_subset {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    openSet x (d.restrictRadius r hr hrR) ⊆ openSet x d := by
  change
    (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph '' Metric.ball 0 r ⊆
      (Smale.NativeParametrization.centered (D := E) x).toOpenPartialHomeomorph ''
        Metric.ball 0 d.radius
  exact Set.image_mono (Metric.ball_subset_ball hrR)

theorem Smale.LocalDegree.NativeNeighborhood.mapsTo_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    Set.MapsTo (Homeomorph.refl M) (openSet x (d.restrictRadius r hr hrR)) (openSet x d) :=
  openSet_restrictRadius_subset x d r hr hrR

theorem Smale.LocalDegree.NativeNeighborhood.coordinateMap_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) :
    Smale.LocalDegree.PointTransition.coordinateMap x x (d.restrictRadius r hr hrR) d
        (Homeomorph.refl M) (identity_center_mo1973_5731 x) (mapsTo_restrictRadius x d r hr hrR) =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [Smale.LocalDegree.PointTransition.coordinateMap_coe]
  let ds := d.restrictRadius r hr hrR
  change
    ‖(Smale.NativeParametrization.centered (D := E) x).symm
              (Smale.NativeParametrization.centered (D := E) x
                (ds.innerBoundary.radius • (u : E)))‖⁻¹ •
        (Smale.NativeParametrization.centered (D := E) x).symm
          (Smale.NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      (u : E)
  have hu : ds.innerBoundary.radius • (u : E) ∈ (Smale.NativeParametrization.centered x).source :=
    closedBall_subset_source x ds (Metric.ball_subset_closedBall (ds.innerBoundary_mem_ball u))
  have hleft :
    (Smale.NativeParametrization.centered (D := E) x).symm
        (Smale.NativeParametrization.centered (D := E) x (ds.innerBoundary.radius • (u : E))) =
      ds.innerBoundary.radius • (u : E) :=
    (Smale.NativeParametrization.centered x).left_inv' hu
  rw [hleft, Smale.LocalDegree.norm_radius_smul _ ds.innerBoundary.radius_pos,
    inv_smul_smul₀ ds.innerBoundary.radius_pos.ne']

theorem Smale.LocalDegree.NativeNeighborhood.sphereConnecting_restrictRadius {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ d.radius) [T1Space M] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x (d.restrictRadius r hr hrR) k a = sphereConnecting x d k a := by
  have h :=
    Smale.LocalDegree.PointTransition.connecting_naturality x x (d.restrictRadius r hr hrR) d
      (Homeomorph.refl M) (identity_center_mo1973_5731 x) (mapsTo_restrictRadius x d r hr hrR) k a
  rw [coordinateMap_restrictRadius, PeriodTorusHigherHomology.singularHomologyMap_id,
    LinearMap.id_apply] at h
  change
    sphereConnecting x (d.restrictRadius r hr hrR) k a =
      sphereConnecting x d k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id M) (k + 1) a) at h
  rwa [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h

theorem Smale.LocalDegree.NativeNeighborhood.sphereConnecting_eq {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x : M) {f : M → F}
    {L : E ≃L[ℝ] F} {W : Set M}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered (D := E) x) L
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W))
    [T1Space M] {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f' : M → F'}
    {L' : E ≃L[ℝ] F'} {W' : Set M}
    (d' :
      Smale.LocalDegree.NeighborhoodData (f' ∘ Smale.NativeParametrization.centered (D := E) x) L'
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W'))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    sphereConnecting x d k a = sphereConnecting x d' k a := by
  let ρ := Min.min d.radius d'.radius
  have hρ : 0 < ρ := lt_min d.radius_pos d'.radius_pos
  rw [← sphereConnecting_restrictRadius x d ρ hρ (min_le_left _ _) k a, ←
    sphereConnecting_restrictRadius x d' ρ hρ (min_le_right _ _) k a]
  rfl

theorem Smale.LocalDegree.PointTransition.coordinateMap_eq_boundary {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy)) :
    coordinateMap x y dx dy e he hV = dx.innerBoundary.normalizedMap :=
  rfl

theorem Smale.LocalDegree.PointTransition.coordinateMap_homology {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    (k : ℕ) :
    SingularMayerVietoris.singularHomologyMap (coordinateMap x y dx dy e he hV) k =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k := by
  rw [coordinateMap_eq_boundary]
  exact dx.innerBoundary.normalized_homology_compare k

theorem Smale.LocalDegree.PointTransition.connecting_derivative_naturality {E G M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (x y : M) (e : M ≃ₜ M)
    (he : e x = y) {fy : M → G} {Ly : E ≃L[ℝ] G} {Wy : Set M}
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    {Lx : E ≃L[ℝ] E} {Wx : Set M}
    (dx :
      Smale.LocalDegree.NeighborhoodData
        (((Smale.NativeParametrization.centered (D := E) y).symm ∘ e) ∘
          Smale.NativeParametrization.centered (D := E) x)
        Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (hV :
      Set.MapsTo e (Smale.LocalDegree.NativeNeighborhood.openSet x dx)
        (Smale.LocalDegree.NativeNeighborhood.openSet y dy))
    [T1Space M] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₀ : M → F} {L₀ : E ≃L[ℝ] F}
    {W₀ : Set M}
    (d₀ :
      Smale.LocalDegree.NeighborhoodData (f₀ ∘ Smale.NativeParametrization.centered (D := E) x) L₀
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' W₀))
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomotopyEquiv.toFun (k + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap Lx.toContinuousLinearMap Lx.injective) k
        (Smale.LocalDegree.NativeNeighborhood.sphereConnecting x d₀ k a) := by
  have h := connecting_naturality x y dx dy e he hV k a
  rw [coordinateMap_homology x y e he dy dx hV k,
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting_eq x dx d₀ k a] at h
  exact h.symm

theorem Smale.LocalDegree.pointConnecting_diffeomorph {E F G M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] (x y : M) {fx : M → F} {fy : M → G} {Lx : E ≃L[ℝ] F}
    {Ly : E ≃L[ℝ] G} {Wx Wy : Set M}
    (dx :
      NeighborhoodData (fx ∘ Smale.NativeParametrization.centered (D := E) x) Lx
        ((Smale.NativeParametrization.centered (D := E) x).source ∩
          Smale.NativeParametrization.centered (D := E) x ⁻¹' Wx))
    (dy :
      NeighborhoodData (fy ∘ Smale.NativeParametrization.centered (D := E) y) Ly
        ((Smale.NativeParametrization.centered (D := E) y).source ∩
          Smale.NativeParametrization.centered (D := E) y ⁻¹' Wy))
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (he : e x = y) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology M (k + 1)) :
    NativeNeighborhood.sphereConnecting y dy k
        (SingularMayerVietoris.singularHomologyMap e.toHomeomorph.toHomotopyEquiv.toFun (k + 1)
          a) =
      SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap
          (Smale.NativeChartTransition.linear x y e he).toContinuousLinearMap
          (Smale.NativeChartTransition.linear x y e he).injective)
        k (NativeNeighborhood.sphereConnecting x dx k a) := by
  let W := e.toHomeomorph ⁻¹' NativeNeighborhood.openSet y dy
  have hW : W ∈ 𝓝 x := by
    apply e.toHomeomorph.continuous.continuousAt
    have hy :=
      (NativeNeighborhood.isOpen_openSet y dy).mem_nhds
        (NativeNeighborhood.center_mem_openSet y dy)
    exact he.symm ▸ hy
  obtain ⟨b⟩ := Smale.NativeChartTransition.nonempty_neighborhoodData x y e he W hW
  have hV :
    Set.MapsTo e.toHomeomorph (NativeNeighborhood.openSet x b)
      (NativeNeighborhood.openSet y dy) :=
    NativeNeighborhood.openSet_subset x b
  exact PointTransition.connecting_derivative_naturality x y e.toHomeomorph he dy b hV dx k a

theorem Smale.SpherePoint.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.SpherePoint.instLocal1 in
def Smale.SpherePoint.pointDiffeomorph (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2))
      (SphereHomology.UnitSphere (n + 2)) ∞ :=
  sphereDiffeomorph (positiveTransport (n + 1) x y)

attribute [local instance] Smale.SpherePoint.instLocal1 in
theorem Smale.SpherePoint.pointDiffeomorph_apply (n : ℕ)
    (x y : SphereHomology.UnitSphere (n + 2)) : pointDiffeomorph n x y x = y :=
  positiveTransport_moves (n + 1) x y

attribute [local instance] Smale.SpherePoint.instLocal1 in
def Smale.SpherePoint.pointChartLinear (n : ℕ) (x y : SphereHomology.UnitSphere (n + 2)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Smale.NativeChartTransition.linear x y (pointDiffeomorph n x y) (pointDiffeomorph_apply n x y)

attribute [local instance] Smale.SpherePoint.instLocal1 in
theorem Smale.SpherePoint.pointClass_sign_compare (n : ℕ) {F G : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (x y : SphereHomology.UnitSphere (n + 2)) {fx : SphereHomology.UnitSphere (n + 2) → F}
    {fy : SphereHomology.UnitSphere (n + 2) → G} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered y) Ly
        ((Smale.NativeParametrization.centered y).source ∩
          Smale.NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      (SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det : ℤ) •
        Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a := by
  have h :=
    Smale.LocalDegree.pointConnecting_diffeomorph x y dx dy (pointDiffeomorph n x y)
      (pointDiffeomorph_apply n x y) (k + 1) a
  have hid :
    SingularMayerVietoris.singularHomologyMap
        (pointDiffeomorph n x y).toHomeomorph.toHomotopyEquiv.toFun (k + 2) a =
      a :=
    positiveTransport_homology (n + 1) x y (k + 2) a
  rw [hid] at h
  apply h.trans
  exact Smale.LinearSphereAction.homology_eq_sign_smul n (pointChartLinear n x y) k _

def Smale.SpherePoint.punctureHomeomorph {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1) :
    ↥({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    ((stereographic' n x).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target x)).trans (Homeomorph.Set.univ _)))

theorem Smale.SpherePoint.puncture_contractible {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
  (punctureHomeomorph (n := n) x).contractibleSpace

def Smale.SpherePoint.connectingHomologyEquiv {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (x : Metric.sphere (0 : V) 1)
    {f : Metric.sphere (0 : V) 1 → F} {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] F}
    {W : Set (Metric.sphere (0 : V) 1)}
    (d :
      Smale.LocalDegree.NeighborhoodData
        (f ∘ Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x) L
        ((Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x).source ∩
          Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x ⁻¹' W))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : V) 1) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
        (k + 1) := by
  let : ContractibleSpace ({ x }ᶜ : Set (Metric.sphere (0 : V) 1)) :=
    puncture_contractible (n := n) x
  exact Smale.LocalDegree.NativeNeighborhood.sphereHomologyEquiv x d k

theorem Smale.SpherePoint.instLocal2 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.SpherePoint.instLocal2 in
def Smale.SpherePoint.outwardPointClass (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  (SignType.sign
        (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0) :
      ℤ) •
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1)

attribute [local instance] Smale.SpherePoint.instLocal2 in
theorem Smale.SpherePoint.outwardPointClass_eq (n : ℕ) {F G H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x y : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {fy : SphereHomology.UnitSphere (n + 2) → G}
    {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F} {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G}
    {Wx Wy : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (dy :
      Smale.LocalDegree.NeighborhoodData (fy ∘ Smale.NativeParametrization.centered y) Ly
        ((Smale.NativeParametrization.centered y).source ∩
          Smale.NativeParametrization.centered y ⁻¹' Wy))
    (k : ℕ) : outwardPointClass n j B y dy k = outwardPointClass n j B x dx k := by
  have hs :=
    chartJacobian_transport_sign x y (positiveTransport (n + 1) x y)
      (positiveTransport_moves (n + 1) x y) (positiveTransport_det (n + 1) x y) j B
  have hs' :
    SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y) j
            B 0) *
        SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det =
      SignType.sign
        (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B
          0) :=
    hs
  apply LinearMap.ext
  intro a
  change
    (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered y)
              j B 0) :
          ℤ) •
        Smale.LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a =
      _
  rw [pointClass_sign_compare n x y dx dy k a, smul_smul, ← SignType.coe_mul, hs']
  rfl

attribute [local instance] Smale.SpherePoint.instLocal2 in
theorem Smale.SpherePoint.chartSign_mul_self (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2)) :
    (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) *
        (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) =
      1 := by
  have hn :=
    Smale.SphereNormalCoordinates.chartJacobian_ne_zero (Smale.NativeParametrization.centered x) j
      B (Smale.NativeParametrization.zero_mem_centered_source x)
  have hs :
    SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j
            B 0) *
        SignType.sign
          (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j
            B 0) =
      1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hn)
  simpa only [SignType.coe_mul, SignType.coe_one] using congrArg (fun s : SignType => (s : ℤ)) hs

attribute [local instance] Smale.SpherePoint.instLocal2 in
theorem Smale.SpherePoint.connecting_eq_sign_outward (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardPointClass n j B x dx k a := by
  change
    _ =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        ((SignType.sign
              (Smale.SphereNormalCoordinates.chartJacobian
                (Smale.NativeParametrization.centered x) j B 0) :
            ℤ) •
          Smale.LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a)
  rw [smul_smul, chartSign_mul_self n j B x, one_smul]

attribute [local instance] Smale.SpherePoint.instLocal2 in
def Smale.SpherePoint.outwardPointClassEquiv (n : ℕ) {F H : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (x : SphereHomology.UnitSphere (n + 2))
    {fx : SphereHomology.UnitSphere (n + 2) → F} {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {Wx : Set (SphereHomology.UnitSphere (n + 2))}
    (dx :
      Smale.LocalDegree.NeighborhoodData (fx ∘ Smale.NativeParametrization.centered x) Lx
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' Wx))
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) := by
  let C := connectingHomologyEquiv x dx k
  let s : ℤ :=
    SignType.sign
      (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x) j B 0)
  have hs : s * s = 1 := chartSign_mul_self n j B x
  refine LinearEquiv.ofBijective (outwardPointClass n j B x dx k) ⟨?_, ?_⟩
  · intro a b hab
    apply C.injective
    have h := congrArg (fun z => s • z) hab
    change s • (s • C a) = s • (s • C b) at h
    simpa only [smul_smul, hs, one_smul] using h
  · intro b
    refine ⟨C.symm (s • b), ?_⟩
    change s • C (C.symm (s • b)) = b
    rw [C.apply_symm_apply, smul_smul, hs, one_smul]

theorem Smale.SpherePoint.instLocal3 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.SpherePoint.instLocal3 in
def Smale.SpherePoint.referencePoint (n : ℕ) : SphereHomology.UnitSphere (n + 2) :=
  Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)

attribute [local instance] Smale.SpherePoint.instLocal3 in
def Smale.SpherePoint.referenceNeighborhood (n : ℕ) (x : SphereHomology.UnitSphere (n + 2)) :
    Smale.LocalDegree.NeighborhoodData
      (((Smale.NativeParametrization.centered (D := EuclideanSpace ℝ (Fin (n + 2))) x).symm ∘
          Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) ∘
        Smale.NativeParametrization.centered x)
      (Smale.NativeChartTransition.linear x x
        (Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) rfl)
      ((Smale.NativeParametrization.centered x).source ∩
        Smale.NativeParametrization.centered x ⁻¹'
          (Set.univ : Set (SphereHomology.UnitSphere (n + 2)))) :=
  Classical.choice
    (Smale.NativeChartTransition.nonempty_neighborhoodData x x
      (Diffeomorph.refl (𝓡 (n + 2)) (SphereHomology.UnitSphere (n + 2)) ∞) rfl Set.univ (by simp))

attribute [local instance] Smale.SpherePoint.instLocal3 in
def Smale.SpherePoint.outwardClass (n : ℕ) {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClass n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] Smale.SpherePoint.instLocal3 in
def Smale.SpherePoint.outwardClassEquiv (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1) :=
  outwardPointClassEquiv n j B (referencePoint n) (referenceNeighborhood n (referencePoint n)) k

attribute [local instance] Smale.SpherePoint.instLocal3 in
theorem Smale.SpherePoint.outwardPointClass_eq_global (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered x) L
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' W))
    (k : ℕ) : outwardPointClass n j B x d k = outwardClass n j B k :=
  outwardPointClass_eq n j B (referencePoint n) x (referenceNeighborhood n (referencePoint n)) d k

attribute [local instance] Smale.SpherePoint.instLocal3 in
theorem Smale.SpherePoint.pointConnecting_eq_outward (n : ℕ) {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : SphereHomology.UnitSphere (n + 2))
    {f : SphereHomology.UnitSphere (n + 2) → F} {L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
    {W : Set (SphereHomology.UnitSphere (n + 2))}
    (d :
      Smale.LocalDegree.NeighborhoodData (f ∘ Smale.NativeParametrization.centered x) L
        ((Smale.NativeParametrization.centered x).source ∩
          Smale.NativeParametrization.centered x ⁻¹' W))
    (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)) :
    Smale.LocalDegree.NativeNeighborhood.sphereConnecting x d (k + 1) a =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian (Smale.NativeParametrization.centered x)
              j B 0) :
          ℤ) •
        outwardClass n j B k a := by
  rw [connecting_eq_sign_outward n j B x d k a, outwardPointClass_eq_global]

def Smale.SpherePoint.sourceCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2) ≃ₗ[ℤ] ℤ :=
  (outwardClassEquiv n j B n).trans (SphereHomology.unitSphereHomologyTopEquiv n)

def Smale.SpherePoint.overlapCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (n + 1) ≃ₗ[ℤ] ℤ :=
  (Smale.LinearSphereAction.homologyEquiv B (n + 1)).symm.trans
    (SphereHomology.unitSphereHomologyTopEquiv n)

def Smale.SpherePoint.targetCountMark (n : ℕ) {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2) ≃ₗ[ℤ] ℤ :=
  (Smale.OnePointCover.sphereHomologyEquiv 1 zero_lt_one n).trans (overlapCountMark n B)

theorem Smale.SpherePoint.overlapCountMark_linear (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (n + 1)) :
    overlapCountMark n B
        (SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1) a) =
      SphereHomology.unitSphereHomologyTopEquiv n a := by
  rw [← Smale.LinearSphereAction.homologyEquiv_apply]
  change
    SphereHomology.unitSphereHomologyTopEquiv n
        ((Smale.LinearSphereAction.homologyEquiv B (n + 1)).symm
          (Smale.LinearSphereAction.homologyEquiv B (n + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

theorem Smale.SpherePoint.countMark_of_connecting (n : ℕ) {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N)
    (u : SingularMayerVietoris.SingularHomology (OnePoint N) (n + 2))
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (n + 2))
    (c : ℤ)
    (h :
      Smale.OnePointCover.sphereConnecting 1 zero_lt_one (n + 1) u =
        c •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (n + 1)
            (outwardClass n j B n a)) :
    targetCountMark n B u = c * sourceCountMark n j B a := by
  have h' := congrArg (overlapCountMark n B) h
  rw [map_zsmul, overlapCountMark_linear] at h'
  exact h'

def Smale.ManifoldMorse.MorseSurgeryData.indexTwoNormalModel {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] d.chart.NegativeCoordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [hindex])

def Smale.ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2 →ₗ[ℤ] ℤ :=
  (Smale.SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2)

theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Function.Surjective (d.indexTwoCollapseCoordinate hf hindex) :=
  (Smale.SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).surjective.comp
    (d.upperCollapse_surjective_of_lower hf 0)

theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    LinearMap.ker (d.indexTwoCollapseCoordinate hf hindex) =
      LinearMap.range (d.lowerRealizationHomologyMap 2) := by
  rw [← d.upperCollapse_homology_kernel hf 1]
  ext a
  let C := Smale.SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)
  change
    C (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a) = 0 ↔
      SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a = 0
  constructor
  · intro h
    exact C.injective (h.trans (map_zero C).symm)
  · intro h
    rw [h, map_zero]

theorem Smale.ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    Function.Injective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :=
    d.attachingHomology_subsingleton_of_index 2 (by norm_num) (by omega) (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_lower hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.coreBoundaryHomologyMap 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem Smale.ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    ∃ H :
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 × ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ a, H (a, 0) = d.lowerRealizationHomologyMap 2 a) ∧
        ∀ z, d.indexTwoCollapseCoordinate hf hindex (H z) = z.2 := by
  obtain ⟨H, hH, hcoord⟩ :=
    Smale.HomologyTransport.exists_add_split_rank_one_extension (d.lowerRealizationHomologyMap 2)
      (d.indexTwoCollapseCoordinate hf hindex) (d.lowerRealization_two_injective hf hindex)
      (d.indexTwoCoordinate_surjective hf hindex) (d.indexTwoCoordinate_kernel hf hindex)
  exact ⟨H.toIntLinearEquiv, hH, hcoord⟩

theorem Smale.ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)]
    (n : ℕ)
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) :
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ v, H (Fin.cons 0 v) = d.lowerRealizationHomologyMap 2 (e v)) ∧
        ∀ v, d.indexTwoCollapseCoordinate hf hindex (H v) = v 0 := by
  obtain ⟨H, hH, hcoord⟩ := d.exists_indexTwoHomology_split hf hindex
  let G :=
    (Smale.HomologyTransport.integerCoordinateSplit n).trans
      ((e.toAddEquiv.prodCongr (AddEquiv.refl ℤ)).trans H.toAddEquiv)
  refine ⟨G.toIntLinearEquiv, ?_, ?_⟩
  · intro v
    exact hH (e v)
  · intro v
    exact hcoord (e (fun i => v i.succ), v 0)

def Smale.ManifoldMorse.SurgeryWindows.HasIndexTwoPrefix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (n : ℕ) : Prop :=
  ∀ i : Fin S.count,
    0 < i.val → i.val ≤ n → Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2

theorem Smale.ManifoldMorse.SurgeryWindows.indexTwoPrefix_mono {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) {n m : ℕ} (hnm : n ≤ m)
    (h : S.HasIndexTwoPrefix m) : S.HasIndexTwoPrefix n := fun i hi hin => h i hi (hin.trans hnm)

theorem Smale.ManifoldMorse.SurgeryWindows.indexTwoBasis_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (hn : n + 1 < S.count) (hpre : S.HasIndexTwoPrefix (n + 1))
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology
          { x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩) } 2) :
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩) } 2,
      (∀ v,
          H (Fin.cons 0 v) =
            (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 2
              (B.homologyEquiv 2 (e v))) ∧
        ∀ v,
          (S.data (S.point ⟨n + 1, hn⟩)).indexTwoCollapseCoordinate hf.continuous
              (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) (H v) =
            v 0 := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
        1) :=
    S.lower_homologyOne_subsingleton_of_indices hf ⟨n + 1, hn⟩ (Nat.succ_pos n)
      (fun i hi hin => by
        have h := hpre i hi (Nat.le_of_lt hin)
        omega)
  let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
  exact
    (S.data (S.point ⟨n + 1, hn⟩)).exists_indexTwoBasis_extension hf.continuous
      (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) n (e.trans (B.homologyEquiv 2))

def Smale.ManifoldMorse.SurgeryWindows.indexTwoBasis {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (n : ℕ) →
      (hn : n < S.count) →
        S.HasIndexTwoPrefix n →
          (Fin n → ℤ) ≃ₗ[ℤ]
            SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) } 2
  | 0, hn, _ =>
    by
    let :
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨0, hn⟩) } 2) :=
      by
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 2 (by norm_num)
    exact LinearEquiv.ofSubsingleton _ _
  | n + 1, hn, hpre =>
    Classical.choose
      (S.indexTwoBasis_step hf n hn hpre
        (indexTwoBasis (S := S) hf n (Nat.lt_of_succ_lt hn)
          (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))

def Smale.ManifoldMorse.MorseSurgeryData.indexThreeBoundaryEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2 ≃ₗ[ℤ]
      ℤ := by
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1) := ⟨hindex⟩
  let H :=
    PeriodTorusHigherHomology.homeomorphHomologyEquiv
      (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
      2
  exact H.symm.trans (SphereHomology.unitSphereHomologyTopEquiv 1)

theorem Smale.ManifoldMorse.MorseSurgeryData.indexThreeBoundary_scalar {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    a = (d.indexThreeBoundaryEquiv hindex a) • (d.indexThreeBoundaryEquiv hindex).symm 1 := by
  apply (d.indexThreeBoundaryEquiv hindex).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]
  simp

def Smale.ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 :=
  d.coreBoundaryHomologyMap 2 ((d.indexThreeBoundaryEquiv hindex).symm 1)

theorem Smale.ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    d.coreBoundaryHomologyMap 2 a =
      (d.indexThreeBoundaryEquiv hindex a) • d.indexThreeAttachingClass hindex := by
  conv_lhs => rw [d.indexThreeBoundary_scalar hindex a]
  rw [map_zsmul]
  rfl

theorem Smale.ManifoldMorse.MorseSurgeryData.coreBoundary_two_range {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.range (d.coreBoundaryHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [d.coreBoundary_two_eq_smul hindex b]
    exact
      Submodule.mem_span_singleton.mpr
        ⟨d.indexThreeBoundaryEquiv hindex b,
          int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            _ _⟩
  · intro ha
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨z • (d.indexThreeBoundaryEquiv hindex).symm 1, ?_⟩
    rw [map_zsmul]
    exact
      (int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            z (d.indexThreeAttachingClass hindex)).symm.trans
        hz

theorem Smale.ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    Function.Surjective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 1) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_upper hf 1] at ha
  exact ha

theorem Smale.ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.ker (d.lowerRealizationHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  rw [← d.morse_exact_at_lower hf 2 (by norm_num), d.coreBoundary_two_range hindex]

def Smale.ManifoldMorse.MorseSurgeryData.indexThreePresentation {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) {r c : ℕ}
    (P :
      Smale.IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c) :
    Smale.IntegerPresentation
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2) r
      (c + 1) :=
  P.adjoin (d.lowerRealizationHomologyMap 2) (d.indexThree_lowerRealization_surjective hf hindex)
    (d.indexThreeAttachingClass hindex) (d.indexThree_lowerRealization_kernel hf hindex)

def Smale.ManifoldMorse.SurgeryWindows.HasIndexThreeBlock {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (r c : ℕ) : Prop :=
  ∀ i : Fin S.count,
    r < i.val →
      i.val ≤ r + c → Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3

theorem Smale.ManifoldMorse.SurgeryWindows.indexThreeBlock_mono {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) {r c b : ℕ} (hcb : c ≤ b)
    (h : S.HasIndexThreeBlock r b) : S.HasIndexThreeBlock r c := fun i hri hic =>
  h i hri (hic.trans (Nat.add_le_add_left hcb r))

theorem Smale.ManifoldMorse.SurgeryWindows.indexThreeBlock_last {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (r c : ℕ) (hc : r + (c + 1) < S.count)
    (h : S.HasIndexThreeBlock r (c + 1)) :
    Module.finrank ℝ (S.data (S.point ⟨r + (c + 1), hc⟩)).chart.NegativeCoordinates = 3 :=
  h ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl

def Smale.ManifoldMorse.SurgeryWindows.middlePresentation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
    (htwo : S.HasIndexTwoPrefix r) :
    (c : ℕ) →
      (hc : r + c < S.count) →
        S.HasIndexThreeBlock r c →
          Smale.IntegerPresentation
            (SingularMayerVietoris.SingularHomology
              { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) } 2)
            r c
  | 0, hc, _ => Smale.IntegerPresentation.ofEquiv (S.indexTwoBasis hf r hc htwo)
  | c + 1, hc, hthree =>
    let P :=
      middlePresentation (S := S) hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
    (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation hf.continuous
      (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2))

theorem Smale.homotopySixSphere_homology_subsingleton {M : Type} [TopologicalSpace M]
    (h : M ≃ₕ Smale.SixSphere) (k : ℕ) (hk : k ≠ 0) (hktop : k ≠ 6) :
    Subsingleton (SingularMayerVietoris.SingularHomology M k) := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology Smale.SixSphere k) :=
    SphereHomology.unitSphere_homology_subsingleton 5 k hk hktop
  exact (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv h k).injective.subsingleton

def Smale.ManifoldMorse.SurgeryWindows.lastUpperHomeomorph {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    { x : M // f x ≤ S.upper (S.last h) } ≃ₜ M :=
  (Homeomorph.setCongr (S.last_upper_univ hf h)).trans (Homeomorph.Set.univ M)

attribute [local instance 100] Classical.propDecidable in
theorem Smale.ManifoldMorse.SurgeryWindows.lastLower_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (h : 0 < S.count) (k : ℕ)
    (hk : 0 < k) (hk5 : k < 5) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.last h) } k) := by
  let d := S.data (S.last h)
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1 :=
    (S.last_index_dimension hf h).trans hdim
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 5 + 1) := ⟨hindex⟩
  let : Subsingleton (SingularMayerVietoris.SingularHomology M k) :=
    Smale.homotopySixSphere_homology_subsingleton hM k hk.ne' (by omega)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ f (S.last h) + d.radius ^ 2 } k) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (S.lastUpperHomeomorph hf h)
        k).injective.subsingleton
  let : Subsingleton (SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere 5) k) :=
    SphereHomology.unitSphere_homology_subsingleton 4 k hk.ne' (by omega)
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
            5).symm.toHomeomorph
        k).injective.subsingleton
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf.continuous k hk.ne'

theorem Smale.ManifoldMorse.SurgeryWindows.upper_homology_subsingleton_of_later_indices
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (j : Fin S.count)
    (hj : j.val + 1 < S.count) (k : ℕ) (hk : 0 < k) (hk5 : k < 5)
    (hindex :
      ∀ i : Fin S.count,
        j.val < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ k + 1) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point j) } k) := by
  have hcount : 0 < S.count := by omega
  let P : ℕ → Prop := fun i =>
    ∀ hi : i < S.count,
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point ⟨i, hi⟩) } k)
  have hlow : P (j.val + 1) := by
    apply Nat.decreasingInduction' (P := P) (m := j.val + 1) (n := S.count - 1)
    · intro i hi hji ih hi'
      have hs : i + 1 < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨i + 1, hs⟩) - (S.data (S.point ⟨i + 1, hs⟩)).radius ^ 2 }
            k) :=
        ih hs
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hs⟩ rfl
      let H :=
        (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨i + 1, hs⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨i, hi'⟩) + (S.data (S.point ⟨i, hi'⟩)).radius ^ 2 } k) :=
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv H k).injective.subsingleton
      obtain ⟨hlo, hne⟩ := hindex ⟨i, hi'⟩ (by change j.val < i; omega) hs
      exact
        (S.data (S.point ⟨i, hi'⟩)).lowerHomology_subsingleton_of_upper_and_index hf.continuous k
          hk.ne' hlo hne
    · omega
    · intro hi
      exact S.lastLower_homology_subsingleton hf hdim hM hcount k hk hk5
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val + 1, hj⟩) - (S.data (S.point ⟨j.val + 1, hj⟩)).radius ^ 2 }
        k) :=
    hlow hj
  obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf j ⟨j.val + 1, hj⟩ rfl
  let H :=
    (S.data (S.point j)).bandSublevelHomeomorph (S.data (S.point ⟨j.val + 1, hj⟩)) T.toHomeomorph
      hT
  exact (PeriodTorusHigherHomology.homeomorphHomologyEquiv H k).injective.subsingleton

def Smale.ManifoldMorse.SurgeryWindows.middleMatrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c) :
    Matrix (Fin r) (Fin c) ℤ :=
  (S.middlePresentation hf r htwo c hc hthree).matrix

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_homotopySphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hj : r + c + 1 < S.count)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val →
          i.val + 1 < S.count →
            2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ∧
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates ≠ 3) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) }
        2) :=
    S.upper_homology_subsingleton_of_later_indices hf hdim hM ⟨r + c, hc⟩ hj 2 (by norm_num)
      (by norm_num) hafter
  exact (S.middlePresentation hf r htwo c hc hthree).matrix_surjective_of_subsingleton

theorem Smale.ManifoldMorse.SurgeryWindows.middleMatrix_surjective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Surjective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_surjective_of_homotopySphere hf hdim hM r c htwo hc hthree (by omega)
  intro i hi hi'
  omega

theorem MorseCancellation.native_indices_monotone {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) :
    Monotone (fun i : Fin S.count => nativeMorseIndex E f (S.point i)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact horder _ _ (S.point_strictMono hlt)
  · exact le_rfl

attribute [local instance 100] Classical.propDecidable in
theorem MorseCancellation.exists_middle_index_blocks {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) :
    ∃ r c : ℕ,
      S.HasIndexTwoPrefix r ∧
        ∃ _ : r + c < S.count,
          S.HasIndexThreeBlock r c ∧
            r + c + 1 < S.count ∧
              ∀ i : Fin S.count,
                r + c < i.val →
                  4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates := by
  have hn := S.count_pos hf
  let index := fun i : Fin S.count => nativeMorseIndex E f (S.point i)
  have hmono : Monotone index := native_indices_monotone S horder
  have hfirst : index ⟨0, hn⟩ = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hlast : index ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ = 6 :=
    (nativeMorseIndex_eq_chart (S.data (S.last hn)).chart).trans
      ((S.last_index_dimension hf hn).trans hdim)
  have hcut (k : ℕ) : ∃ j : Fin S.count, ∀ i : Fin S.count, i ≤ j ↔ index i ≤ k := by
    let K := Finset.univ.filter (fun i : Fin S.count => index i ≤ k)
    have hK : K.Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfirst]; exact Nat.zero_le k⟩⟩
    let j := K.max' hK
    have hj : index j ≤ k := (Finset.mem_filter.mp (K.max'_mem hK)).2
    refine ⟨j, fun i => ⟨fun hij => (hmono hij).trans hj, ?_⟩⟩
    intro hi
    exact K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  obtain ⟨a, ha⟩ := hcut 2
  obtain ⟨b, hb⟩ := hcut 3
  have hab : a ≤ b := (hb a).mpr (((ha a).mp le_rfl).trans (by omega))
  have hbLast : b.val + 1 < S.count := by
    have hb3 := (hb b).mp le_rfl
    have hne : b ≠ ⟨S.count - 1, Nat.sub_lt hn zero_lt_one⟩ := by
      intro he
      rw [he, hlast] at hb3
      omega
    have hvalne : b.val ≠ S.count - 1 := fun he => hne (Fin.ext he)
    omega
  have hnonzero (i : Fin S.count) (hi : 0 < i.val) : index i ≠ 0 := by
    intro hz
    have he : S.point i = S.first hn :=
      Subtype.ext (native_index_zero_point_unique S hf hn hzero _ (S.point i).property hz)
    have hi0 : i.val = 0 := congrArg Fin.val (S.point.injective he)
    omega
  have hnonone (i : Fin S.count) : index i ≠ 1 :=
    native_index_one_excluded S hone _ (S.point i).property
  refine ⟨a.val, b.val - a.val, ?_, by omega, ?_, by omega, ?_⟩
  · intro i hi hia
    have hi2 := (ha i).mp (show i ≤ a from hia)
    have hi0 := hnonzero i hi
    have hi1 := hnonone i
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 2
    omega
  · intro i hai hib
    have hi3 := (hb i).mp (show i ≤ b by change i.val ≤ b.val; omega)
    have hi2 : ¬index i ≤ 2 := fun he => (not_le_of_gt hai) ((ha i).mpr he)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change index i = 3
    omega
  · intro i hbi
    have hi3 : ¬index i ≤ 3 := fun he =>
      (by
        have hh : i.val ≤ b.val := (hb i).mpr he
        omega)
    rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    change 4 ≤ index i
    omega

def MorseCancellation.nativeMiddleBlockPoint {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) (j : Fin n) :
    Smale.ManifoldMorse.criticalPoints E f :=
  S.toSurgeryWindows.point ⟨r + j.val + 1, by omega⟩

theorem AdaptedWindows.exists_ordered_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock r n)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ T : AdaptedWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
        (∀ p, (T.data p).radius < ε p) ∧
          (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
            ∃ α : Fin n → (Smale.Hemisphere.Sphere 2) → (S.data q).UpperLevel,
              MorseCancellation.IsNativeMiddleBasinFamily T hf (S.data q).upper_regular
                (MorseCancellation.nativeMiddleBlockPoint S r n hn) α := by
  let W := S.toSurgeryWindows
  have hnW : r + n < W.count := hn
  let q := W.point ⟨r, by omega⟩
  let p := MorseCancellation.nativeMiddleBlockPoint S r n hn
  have hp (j : Fin n) : MorseCancellation.nativeMorseIndex E f (p j) = 3 :=
    (MorseCancellation.nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have horder : StrictMono (fun j => f (p j)) := by
    intro i j hij
    apply W.point_strictMono
    change r + i.val + 1 < r + j.val + 1
    omega
  have habove (j : Fin n) : W.upper q < f (p j) := by
    have hqj : f q < f (p j) := W.point_strictMono (by change r < r + j.val + 1; omega)
    exact (W.separated q (p j) hqj).trans (W.lower_lt_value (p j))
  have hblock (j : Fin n) (z : Smale.ManifoldMorse.criticalPoints E f) (hz : W.upper q < f z)
    (hzj : f z ≤ f (p j)) : z ∈ Set.range p := by
    obtain ⟨k, rfl⟩ := W.point.surjective z
    have hrk : r < k.val := W.point_strictMono.lt_iff_lt.mp ((W.value_lt_upper q).trans hz)
    have hkj : k.val ≤ r + j.val + 1 := W.point_strictMono.le_iff_le.mp hzj
    let i : Fin n := ⟨k.val - (r + 1), by omega⟩
    refine ⟨i, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (k.val - (r + 1)) + 1 = k.val
    omega
  exact
    S.exists_middle_block_realization hf hm hdim n (S.data q).upper_regular p hp horder habove
      hblock ε hε

end Mathoverflow1973

end
