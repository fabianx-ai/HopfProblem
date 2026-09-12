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
Original source lines 133802--148196; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.LCP.CuspFilling
import Lib.AlgebraicTopology.SingularHomology.Pontryagin
import Lib.AlgebraicTopology.SingularHomology.Torus
import Lib.LinearAlgebra.ExteriorPower.MinorCoordinates

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

abbrev CuspSpecialization.ToricFibre (t : ℂ) :=
  { x : ToricSpace.Space // ToricSpace.time x = t }

abbrev CuspSpecialization.PositiveFibre (ρ : ℝ) :=
  { q : ToricSpace.PositivePart // ToricSpace.time (q : ToricSpace.Space) = (ρ : ℂ) }

@[simp]
theorem CuspSpecialization.time_positiveFibre (ρ : ℝ) (q : PositiveFibre ρ) :
    ToricSpace.time (q.1 : ToricSpace.Space) = (ρ : ℂ) :=
  q.2

theorem CuspSpecialization.norm_time_positiveFibre (ρ : ℝ) (hρ : 0 ≤ ρ) (q : PositiveFibre ρ) :
    ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ = ρ := by rw [q.2, Complex.norm_of_nonneg hρ]

def CuspSpecialization.positiveFibreInclusion (ρ : ℝ) : C(PositiveFibre ρ, ToricSpace.Space) :=
  ⟨fun q => (q.1 : ToricSpace.Space), continuous_subtype_val.comp continuous_subtype_val⟩

def CuspSpecialization.toricFibreLevelHomeomorph (η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) :
    ToricFibre t ≃ₜ CuspControlledRetraction.ToricLevel η t
    where
  toFun x := ⟨⟨(x : ToricSpace.Space), by rw [x.2]; exact htη⟩, x.2⟩
  invFun x := ⟨(x.1 : ToricSpace.Space), x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem CuspSpecialization.positiveFibre_isClosed (ρ : ℝ) :
    IsClosed {q : ToricSpace.PositivePart | ToricSpace.time (q : ToricSpace.Space) = (ρ : ℂ)} :=
  isClosed_eq (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val)
    continuous_const

theorem CuspSpecialization.positiveFibreVal_isClosedEmbedding (ρ : ℝ) :
    Topology.IsClosedEmbedding (fun q : PositiveFibre ρ => (q.1 : ToricSpace.Space)) :=
  ToricSpace.positivePart_isClosed.isClosedEmbedding_subtypeVal.comp
    (positiveFibre_isClosed ρ).isClosedEmbedding_subtypeVal

def CuspSpecialization.positiveFibrePolarMap (ρ : ℝ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) : ToricFibre (ρ : ℂ) :=
  ⟨ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space), by
    rw [ToricSpace.time_compactFibreAction, p.2.2]⟩

@[simp]
theorem CuspSpecialization.positiveFibrePolarMap_coe (ρ : ℝ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) :
    (positiveFibrePolarMap ρ p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space) :=
  rfl

theorem CuspSpecialization.positiveFibrePolarMap_continuous (ρ : ℝ) :
    Continuous (positiveFibrePolarMap ρ) :=
  (ToricSpace.compactFibreAction_continuous.comp
        (continuous_fst.prodMk
          ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))).subtype_mk
    _

@[simp]
theorem CuspSpecialization.modulus_positiveFibrePolarMap (ρ : ℝ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) :
    ToricSpace.modulus (positiveFibrePolarMap ρ p : ToricSpace.Space) =
      (p.2.1 : ToricSpace.Space) := by
  rw [positiveFibrePolarMap_coe, ToricSpace.modulus_compactFibreAction]
  exact p.2.1.2

def CuspSpecialization.positiveFibreModulus (ρ : ℝ) (hρ : 0 ≤ ρ) (x : ToricFibre (ρ : ℂ)) :
    PositiveFibre ρ :=
  ⟨ToricSpace.modulusRetraction (x : ToricSpace.Space), by
    rw [ToricSpace.modulusRetraction_coe, ToricSpace.time_modulus, x.2,
      Complex.norm_of_nonneg hρ]⟩

@[simp]
theorem CuspSpecialization.positiveFibreModulus_polarMap (ρ : ℝ) (hρ : 0 ≤ ρ)
    (p : ToricSpace.CompactFibreTorus × PositiveFibre ρ) :
    positiveFibreModulus ρ hρ (positiveFibrePolarMap ρ p) = p.2 :=
  Subtype.ext (Subtype.ext (modulus_positiveFibrePolarMap ρ p))

theorem CuspSpecialization.compactFibrePhase_injective :
    Function.Injective ToricSpace.compactFibrePhase := by
  intro u v huv
  funext i
  fin_cases i
  · exact congrFun huv 0
  · exact congrFun huv 1

theorem CuspSpecialization.compactFibreAction_injective_of_time_ne_zero {x : ToricSpace.Space}
    (hx : ToricSpace.time x ≠ 0) :
    Function.Injective
      (fun u : ToricSpace.CompactFibreTorus => ToricSpace.compactFibreAction u x) := by
  intro u v huv
  apply compactFibrePhase_injective
  apply ToricSpace.compactTorusAction_injective_of_time_ne_zero hx
  simpa only [← ToricSpace.compactFibreAction_eq_compact] using huv

theorem CuspSpecialization.positiveFibrePolarMap_injective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Injective (positiveFibrePolarMap ρ) := by
  rintro ⟨u, x⟩ ⟨v, y⟩ h
  have hxy : x = y := by
    have hm := congrArg (positiveFibreModulus ρ hρ.le) h
    simpa only [positiveFibreModulus_polarMap] using hm
  subst y
  have hx : ToricSpace.time (x.1 : ToricSpace.Space) ≠ 0 := by
    rw [x.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'
  have huv : u = v := compactFibreAction_injective_of_time_ne_zero hx (congrArg Subtype.val h)
  exact Prod.ext huv rfl

theorem CuspSpecialization.compactTorusPhase_two_eq_one_of_positive_time (ρ : ℝ) (hρ : 0 < ρ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = (ρ : ℂ)) (u : ToricSpace.CompactTorus)
    (hu : ToricSpace.compactTorusAction u (ToricSpace.modulus x) = x) : u 2 = 1 := by
  have hm : ToricSpace.time (ToricSpace.modulus x) = (ρ : ℂ) := by
    rw [ToricSpace.time_modulus, hx, Complex.norm_of_nonneg hρ.le]
  have ht := congrArg ToricSpace.time hu
  rw [ToricSpace.compactTorusAction, ToricSpace.time_torusAction,
    ToricSpace.compactTorusUnits_apply, hm, hx] at ht
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne')
  simpa only [Circle.coe_one, one_mul] using ht

theorem CuspSpecialization.exists_compactFibreAction_modulus_of_positive_time (ρ : ℝ) (hρ : 0 < ρ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = (ρ : ℂ)) :
    ∃ u : ToricSpace.CompactFibreTorus,
      ToricSpace.compactFibreAction u (ToricSpace.modulus x) = x := by
  obtain ⟨u, hu⟩ := ToricSpace.exists_compactTorusAction_modulus x
  have hu2 := compactTorusPhase_two_eq_one_of_positive_time ρ hρ hx u hu
  let uf : ToricSpace.CompactFibreTorus := ![u 0, u 1]
  have hf : ToricSpace.compactFibrePhase uf = u := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hu2.symm
  refine ⟨uf, ?_⟩
  rw [ToricSpace.compactFibreAction_eq_compact, hf]
  exact hu

theorem CuspSpecialization.positiveFibrePolarMap_surjective (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Surjective (positiveFibrePolarMap ρ) := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactFibreAction_modulus_of_positive_time ρ hρ x.2
  exact ⟨(u, positiveFibreModulus ρ hρ.le x), Subtype.ext hu⟩

theorem CuspSpecialization.positiveFibrePolarMap_isProperMap (ρ : ℝ) :
    IsProperMap (positiveFibrePolarMap ρ) := by
  have hinc :
    IsProperMap
      (fun p : ToricSpace.CompactFibreTorus × PositiveFibre ρ =>
        (p.1, (p.2.1 : ToricSpace.Space))) :=
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).isClosedEmbedding.prodMap
        (positiveFibreVal_isClosedEmbedding ρ)).isProperMap
  have hcomp :
    IsProperMap
      ((Subtype.val : ToricFibre (ρ : ℂ) → ToricSpace.Space) ∘ positiveFibrePolarMap ρ) :=
    ToricSpace.compactFibreAction_isProperMap.comp hinc
  exact
    isProperMap_of_comp_of_inj (positiveFibrePolarMap_continuous ρ) continuous_subtype_val hcomp
      Subtype.val_injective

theorem CuspSpecialization.positiveFibrePolarMap_isClosedMap (ρ : ℝ) :
    IsClosedMap (positiveFibrePolarMap ρ) :=
  (positiveFibrePolarMap_isProperMap ρ).isClosedMap

def CuspSpecialization.positiveFibrePolarHomeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    (ToricSpace.CompactFibreTorus × PositiveFibre ρ) ≃ₜ ToricFibre (ρ : ℂ) :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (positiveFibrePolarMap ρ)
      ⟨positiveFibrePolarMap_injective ρ hρ, positiveFibrePolarMap_surjective ρ hρ⟩)
    (positiveFibrePolarMap_continuous ρ) (positiveFibrePolarMap_isClosedMap ρ)

@[simp]
theorem CuspSpecialization.modulus_torusPoint (w : ToricCharts.CoordinateSpace 3) :
    ToricSpace.modulus (CuspUniformization.torusPoint w) =
      CuspUniformization.torusPoint (ToricCharts.coordinateModulus w) := by
  simp only [CuspUniformization.torusPoint, ToricSpace.modulus_inclusion,
    ToricCharts.monomial_coordinateModulus]

theorem CuspSpecialization.torusCoordinates_modulus {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) :
    ToricSpace.torusCoordinates (ToricSpace.modulus x) =
      ToricCharts.coordinateModulus (ToricSpace.torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [ToricSpace.modulus_inclusion,
    ToricSpace.torusCoordinates_inclusion _
      ((ToricCharts.coordinateModulus_mem_torus_iff z).mpr hz),
    ToricSpace.torusCoordinates_inclusion _ hz, ToricCharts.monomial_coordinateModulus]

theorem CuspSpecialization.positivePart_torusCoordinates_eq_norm (q : ToricSpace.PositivePart)
    (ht : ToricSpace.time (q : ToricSpace.Space) ≠ 0) (i : Fin 3) :
    ToricSpace.torusCoordinates (q : ToricSpace.Space) i =
      (‖ToricSpace.torusCoordinates (q : ToricSpace.Space) i‖ : ℂ) := by
  have hx : (q : ToricSpace.Space) ∈ ToricSpace.openTorus :=
    (ToricSpace.mem_openTorus_iff _).mpr ht
  have hq : ToricSpace.modulus (q : ToricSpace.Space) = (q : ToricSpace.Space) := q.2
  simpa only [hq, ToricCharts.coordinateModulus_apply] using
    congrFun (torusCoordinates_modulus hx) i

theorem CuspSpecialization.positivePart_torusCoordinates_norm_pos (q : ToricSpace.PositivePart)
    (ht : ToricSpace.time (q : ToricSpace.Space) ≠ 0) (i : Fin 3) :
    0 < ‖ToricSpace.torusCoordinates (q : ToricSpace.Space) i‖ :=
  norm_pos_iff.mpr
    (ToricSpace.torusCoordinates_nonzero ((ToricSpace.mem_openTorus_iff _).mpr ht) i)

theorem CuspSpecialization.positiveFibre_time_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (q : PositiveFibre ρ) :
    ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0 := by
  rw [q.2]
  exact Complex.ofReal_ne_zero.mpr hρ.ne'

def CuspSpecialization.positiveLogCoordinates (ρ : ℝ) (r : (CuspHoneycombTiling.Plane)) :
    ToricCharts.CoordinateSpace 3 :=
  ![(Real.exp (Real.log ρ * r 0) : ℂ), (Real.exp (Real.log ρ * r 1) : ℂ), (ρ : ℂ)]

theorem CuspSpecialization.positiveLogCoordinates_mem {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) : positiveLogCoordinates ρ r ∈ ToricCharts.torus := by
  intro i
  fin_cases i
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · exact Complex.ofReal_ne_zero.mpr hρ.ne'

theorem CuspSpecialization.torusCoordinates_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.torusCoordinates (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) =
      positiveLogCoordinates ρ r :=
  CuspUniformization.torusCoordinates_torusPoint (positiveLogCoordinates_mem hρ r)

theorem CuspSpecialization.time_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.time (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) = (ρ : ℂ) := by
  simpa [positiveLogCoordinates] using congrFun (torusCoordinates_positiveLogPoint hρ r) 2

theorem CuspSpecialization.position_positiveLogPoint {ρ : ℝ} (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0)
    (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) = r := by
  funext i
  rw [ToricSpace.position, ToricSpace.logCoordinates, torusCoordinates_positiveLogPoint hρ r,
    time_positiveLogPoint hρ r, Complex.norm_of_nonneg hρ.le]
  fin_cases i
  · change Real.log ‖(Real.exp (Real.log ρ * r 0) : ℂ)‖ / Real.log ρ = r 0
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.log_exp]
    exact mul_div_cancel_left₀ _ hlog
  · change Real.log ‖(Real.exp (Real.log ρ * r 1) : ℂ)‖ / Real.log ρ = r 1
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _), Real.log_exp]
    exact mul_div_cancel_left₀ _ hlog

theorem CuspSpecialization.positiveLogCoordinates_continuous (ρ : ℝ) :
    Continuous (positiveLogCoordinates ρ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact
      Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply 0)))
  · exact
      Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply 1)))
  · exact continuous_const

theorem CuspSpecialization.positiveLogPoint_continuous {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous
      (fun r : (CuspHoneycombTiling.Plane) =>
        CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) :=
  CuspUniformization.torusChart.symm.continuousOn.comp_continuous
    (positiveLogCoordinates_continuous ρ) (fun r => positiveLogCoordinates_mem hρ r)

theorem CuspSpecialization.positiveLogPoint_mem_positivePart {ρ : ℝ} (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) :
    CuspUniformization.torusPoint (positiveLogCoordinates ρ r) ∈ ToricSpace.positivePart := by
  change ToricSpace.modulus (CuspUniformization.torusPoint (positiveLogCoordinates ρ r)) = _
  rw [modulus_torusPoint]
  apply congrArg CuspUniformization.torusPoint
  funext i
  fin_cases i
  · change (‖(Real.exp (Real.log ρ * r 0) : ℂ)‖ : ℂ) = (Real.exp (Real.log ρ * r 0) : ℂ)
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _)]
  · change (‖(Real.exp (Real.log ρ * r 1) : ℂ)‖ : ℂ) = (Real.exp (Real.log ρ * r 1) : ℂ)
    rw [Complex.norm_of_nonneg (Real.exp_nonneg _)]
  · change (‖(ρ : ℂ)‖ : ℂ) = (ρ : ℂ)
    rw [Complex.norm_of_nonneg hρ.le]

def CuspSpecialization.positivePositionPoint (ρ : ℝ) (hρ : 0 < ρ)
    (r : (CuspHoneycombTiling.Plane)) : PositiveFibre ρ :=
  ⟨⟨CuspUniformization.torusPoint (positiveLogCoordinates ρ r),
      positiveLogPoint_mem_positivePart hρ r⟩,
    time_positiveLogPoint hρ r⟩

@[simp]
theorem CuspSpecialization.position_positivePositionPoint (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) (r : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position ((positivePositionPoint ρ hρ r).1 : ToricSpace.Space) = r :=
  position_positiveLogPoint hρ hlog r

theorem CuspSpecialization.positivePositionPoint_continuous (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (positivePositionPoint ρ hρ) := by
  apply Continuous.subtype_mk
  exact (positiveLogPoint_continuous hρ).subtype_mk _

theorem CuspSpecialization.position_positiveFibre_injective (ρ : ℝ) (hρ : 0 < ρ)
    (hlog : Real.log ρ ≠ 0) :
    Function.Injective
      (fun q : PositiveFibre ρ => ToricSpace.position (q.1 : ToricSpace.Space)) := by
  intro q r he
  have hq := positiveFibre_time_ne_zero ρ hρ q
  have hr := positiveFibre_time_ne_zero ρ hρ r
  have hcoord (i : Fin 2) :
    ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) i.castSucc =
      ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) i.castSucc := by
    have hl :
      Real.log ‖ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) i.castSucc‖ =
        Real.log ‖ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) i.castSucc‖ := by
      have hi := congrFun he i
      change
        Real.log ‖ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) i.castSucc‖ /
            Real.log ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ =
          Real.log ‖ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) i.castSucc‖ /
            Real.log ‖ToricSpace.time (r.1 : ToricSpace.Space)‖ at hi
      rw [norm_time_positiveFibre ρ hρ.le q, norm_time_positiveFibre ρ hρ.le r] at hi
      have hm := congrArg (fun z : ℝ => z * Real.log ρ) hi
      simpa only [div_mul_cancel₀ _ hlog] using hm
    have hn := congrArg Real.exp hl
    rw [Real.exp_log (positivePart_torusCoordinates_norm_pos q.1 hq i.castSucc),
      Real.exp_log (positivePart_torusCoordinates_norm_pos r.1 hr i.castSucc)] at hn
    rw [positivePart_torusCoordinates_eq_norm q.1 hq i.castSucc,
      positivePart_torusCoordinates_eq_norm r.1 hr i.castSucc, hn]
  apply Subtype.ext
  apply Subtype.ext
  apply
    CuspUniformization.torusCoordinates_injective ((ToricSpace.mem_openTorus_iff _).mpr hq)
      ((ToricSpace.mem_openTorus_iff _).mpr hr)
  funext i
  fin_cases i
  · exact hcoord 0
  · exact hcoord 1
  · change
      ToricSpace.torusCoordinates (q.1 : ToricSpace.Space) 2 =
        ToricSpace.torusCoordinates (r.1 : ToricSpace.Space) 2
    rw [ToricSpace.torusCoordinates_time, ToricSpace.torusCoordinates_time, q.2, r.2]

theorem CuspSpecialization.realCuspVector_neg_realCuspVector (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.realCuspVector (-ToricSpace.realCuspVector y) = y := by
  ext i
  fin_cases i <;> simp [ToricSpace.realCuspVector]

theorem CuspSpecialization.neg_realCuspVector_realCuspVector (y : (CuspHoneycombTiling.Plane)) :
    -ToricSpace.realCuspVector (ToricSpace.realCuspVector y) = y := by
  rw [← map_neg, realCuspVector_neg_realCuspVector]

def CuspSpecialization.normalizedPositivePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (y : (CuspHoneycombTiling.Plane)) : PositiveFibre ρ :=
  positivePositionPoint ρ hρ
    (ToricSpace.displacement (CuspPositive.positiveTwist C₀) (ρ : ℂ)
      (-ToricSpace.realCuspVector y))

theorem CuspSpecialization.normalizedPositivePoint_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) : Continuous (normalizedPositivePoint C₀ ρ hρ) :=
  (positivePositionPoint_continuous ρ hρ).comp
    ((ToricSpace.displacement (CuspPositive.positiveTwist C₀)
          (ρ : ℂ)).continuous_of_finiteDimensional.comp
      CuspControlledRetraction.realCuspVector_continuous.neg)

theorem CuspSpecialization.position_normalizedPositivePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (hlog : Real.log ρ ≠ 0) (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position ((normalizedPositivePoint C₀ ρ hρ y).1 : ToricSpace.Space) =
      ToricSpace.displacement (CuspPositive.positiveTwist C₀) (ρ : ℂ)
        (-ToricSpace.realCuspVector y) :=
  position_positivePositionPoint ρ hρ hlog _

theorem CuspSpecialization.normalizedPosition_normalizedPositivePoint
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (y : (CuspHoneycombTiling.Plane)) :
    CuspControlledRetraction.normalizedPosition C₀
        ((normalizedPositivePoint C₀ ρ hρ y).1 : ToricSpace.Space) =
      y := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ (hρε.trans hε1)
  have hlogC : Real.log ‖(ρ : ℂ)‖ < 0 := by simpa only [Complex.norm_of_nonneg hρ.le] using hlog
  rw [CuspControlledRetraction.normalizedPosition, time_positiveFibre,
    position_normalizedPositivePoint C₀ ρ hρ hlog.ne,
    ToricSpace.inverseDisplacement_displacement (CuspPositive.positiveTwist C₀) hlogC
      (hR _ (by simpa only [Complex.norm_of_nonneg hρ.le] using hρ)
        (by simpa only [Complex.norm_of_nonneg hρ.le] using hρε))]
  exact realCuspVector_neg_realCuspVector y

theorem CuspSpecialization.normalizedPositivePoint_normalizedPosition
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (q : PositiveFibre ρ) :
    normalizedPositivePoint C₀ ρ hρ
        (CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space)) =
      q := by
  have hlog : Real.log ρ < 0 := Real.log_neg hρ (hρε.trans hε1)
  have hlogC : Real.log ‖(ρ : ℂ)‖ < 0 := by simpa only [Complex.norm_of_nonneg hρ.le] using hlog
  apply position_positiveFibre_injective ρ hρ hlog.ne
  change
    ToricSpace.position
        ((normalizedPositivePoint C₀ ρ hρ
              (CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space))).1 :
          ToricSpace.Space) =
      ToricSpace.position (q.1 : ToricSpace.Space)
  rw [position_normalizedPositivePoint C₀ ρ hρ hlog.ne,
    CuspControlledRetraction.normalizedPosition, q.2, neg_realCuspVector_realCuspVector]
  exact
    ToricSpace.displacement_inverseDisplacement (CuspPositive.positiveTwist C₀) hlogC
      (hR _ (by simpa only [Complex.norm_of_nonneg hρ.le] using hρ)
        (by simpa only [Complex.norm_of_nonneg hρ.le] using hρε))
      _

theorem CuspSpecialization.normalizedPosition_positiveFibre_continuous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    Continuous
      (fun q : PositiveFibre ρ =>
        CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have ht : ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ < ε := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hρε
  exact
    ContinuousAt.comp (f := fun r : PositiveFibre ρ => (r.1 : ToricSpace.Space)) (g :=
      CuspControlledRetraction.normalizedPosition C₀)
      (CuspControlledRetraction.normalizedPosition_continuousAt C₀ hε1 hR
        (positiveFibre_time_ne_zero ρ hρ q) ht)
      (positiveFibreInclusion ρ).continuous.continuousAt

def CuspSpecialization.normalizedPositiveHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    (CuspHoneycombTiling.Plane) ≃ₜ PositiveFibre ρ
    where
  toFun := normalizedPositivePoint C₀ ρ hρ
  invFun q := CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space)
  left_inv := normalizedPosition_normalizedPositivePoint C₀ ρ hρ ε hε1 hρε hR
  right_inv := normalizedPositivePoint_normalizedPosition C₀ ρ hρ ε hε1 hρε hR
  continuous_toFun := normalizedPositivePoint_continuous C₀ ρ hρ
  continuous_invFun := normalizedPosition_positiveFibre_continuous C₀ ρ hρ ε hε1 hρε hR

@[simp]
theorem CuspSpecialization.normalizedPositiveHomeomorph_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (y : (CuspHoneycombTiling.Plane)) :
    normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y = normalizedPositivePoint C₀ ρ hρ y :=
  rfl

@[simp]
theorem CuspSpecialization.normalizedPositiveHomeomorph_symm_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (q : PositiveFibre ρ) :
    (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm q =
      CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space) :=
  rfl

def CuspSpecialization.positiveFibreTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) : PositiveFibre ρ :=
  ⟨⟨ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space),
      CuspPositive.twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by rw [ToricSpace.time_twistedTranslate, q.2]⟩

@[simp]
theorem CuspSpecialization.positiveFibreTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (v : Fin 2 → ℤ) (q : PositiveFibre ρ) :
    ((positiveFibreTranslate C₀ ρ v q).1 : ToricSpace.Space) =
      ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v (q.1 : ToricSpace.Space) :=
  rfl

theorem CuspSpecialization.normalizedPosition_positiveFibreTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    (q : PositiveFibre ρ) :
    CuspControlledRetraction.normalizedPosition C₀
        ((positiveFibreTranslate C₀ ρ v q).1 : ToricSpace.Space) =
      CuspControlledRetraction.normalizedPosition C₀ (q.1 : ToricSpace.Space) +
        CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) := by
  have hq : ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0 := by
    rw [q.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'
  have ht : ‖ToricSpace.time (q.1 : ToricSpace.Space)‖ < ε := by
    rw [norm_time_positiveFibre ρ hρ.le q]
    exact hρε
  exact CuspControlledRetraction.normalizedPosition_twistedTranslate C₀ hε1 hR v hq ht

theorem CuspSpecialization.normalizedPositiveHomeomorph_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    (y : (CuspHoneycombTiling.Plane)) :
    normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR
        (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      positiveFibreTranslate C₀ ρ v (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR y) := by
  apply (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm.injective
  rw [Homeomorph.symm_apply_apply, normalizedPositiveHomeomorph_symm_apply,
    normalizedPosition_positiveFibreTranslate C₀ ρ hρ ε hε1 hρε hR]
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply y
  rw [normalizedPositiveHomeomorph_symm_apply] at hy
  rw [hy]

theorem CuspSpecialization.normalizedPositivePoint_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    (y : (CuspHoneycombTiling.Plane)) :
    normalizedPositivePoint C₀ ρ hρ
        (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      positiveFibreTranslate C₀ ρ v (normalizedPositivePoint C₀ ρ hρ y) := by
  simpa only [normalizedPositiveHomeomorph_apply] using
    normalizedPositiveHomeomorph_equivariant C₀ ρ hρ ε hε1 hρε hR v y

def CuspSpecialization.frozenPhaseHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    CuspHoneycomb.PhasePlane ≃ₜ ToricFibre (ρ : ℂ) :=
  ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr
        (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR)).trans
    (positiveFibrePolarHomeomorph ρ hρ)

theorem CuspSpecialization.frozenPhaseHomeomorph_coe_homeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (p : CuspHoneycomb.PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1
        ((normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2).1 : ToricSpace.Space) :=
  rfl

@[simp]
theorem CuspSpecialization.frozenPhaseHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    (p : CuspHoneycomb.PhasePlane) :
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p : ToricSpace.Space) =
      ToricSpace.compactFibreAction p.1
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space) := by
  rw [frozenPhaseHomeomorph_coe_homeomorph, normalizedPositiveHomeomorph_apply]

@[simp]
theorem CuspSpecialization.sourceDeck_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) : CuspHoneycomb.honeycombDeckMap C₀ 0 p = p := by
  simp only [CuspHoneycomb.honeycombDeckMap, CuspCollapse.deckFibrePhase_zero, one_mul,
    ToricSpace.cuspVector_zero, CuspHoneycombTiling.latticePoint_zero, add_zero, Prod.eta]

theorem CuspSpecialization.sourceDeck_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.honeycombDeckMap C₀ v (CuspHoneycomb.honeycombDeckMap C₀ w p) =
      CuspHoneycomb.honeycombDeckMap C₀ (v + w) p := by
  apply Prod.ext
  · change
      CuspCollapse.deckFibrePhase C₀ v * (CuspCollapse.deckFibrePhase C₀ w * p.1) =
        CuspCollapse.deckFibrePhase C₀ (v + w) * p.1
    rw [CuspCollapse.deckFibrePhase_add, mul_assoc]
  · change
      (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector w)) +
          CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) =
        p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector (v + w))
    rw [ToricSpace.cuspVector_add, CuspHoneycombTiling.latticePoint_add]
    abel

def CuspSpecialization.sourceDeckSetoid (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Setoid CuspHoneycomb.PhasePlane
    where
  r p q := ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap C₀ v q = p
  iseqv :=
    { refl := fun p => ⟨0, sourceDeck_zero C₀ p⟩
      symm := by
        rintro p q ⟨v, hv⟩
        refine ⟨-v, ?_⟩
        rw [← hv, sourceDeck_add, neg_add_cancel, sourceDeck_zero]
      trans := by
        rintro p q r ⟨v, hv⟩ ⟨w, hw⟩
        refine ⟨v + w, ?_⟩
        rw [← sourceDeck_add, hw, hv] }

abbrev CuspSpecialization.SourceModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :=
  Quotient (sourceDeckSetoid C₀)

def CuspSpecialization.sourceProjection (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane → SourceModel C₀ :=
  Quotient.mk (sourceDeckSetoid C₀)

theorem CuspSpecialization.sourceProjection_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourceProjection C₀) :=
  continuous_quotient_mk'

theorem CuspSpecialization.sourceProjection_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProjection C₀) :=
  Quotient.mk_surjective

theorem CuspSpecialization.sourceProjection_isQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Topology.IsQuotientMap (sourceProjection C₀) :=
  isQuotientMap_quotient_mk'

theorem CuspSpecialization.sourceProjection_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : CuspHoneycomb.PhasePlane) :
    sourceProjection C₀ p = sourceProjection C₀ q ↔
      ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap C₀ v q = p :=
  ⟨Quotient.exact, fun h => @Quotient.sound CuspHoneycomb.PhasePlane (sourceDeckSetoid C₀) p q h⟩

theorem CuspSpecialization.honeycombCollapseMap_sourceDeck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.honeycombCollapseMap C ε hε (CuspHoneycomb.honeycombDeckMap (C 0) v p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε p := by
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε _ p).mpr
  refine ⟨v, rfl, ?_⟩
  change
    (CuspCollapse.deckFibrePhase (C 0) v * p.1)⁻¹ * (CuspCollapse.deckFibrePhase (C 0) v * p.1) ∈
      _
  rw [inv_mul_cancel]
  exact Subgroup.one_mem _

def CuspSpecialization.sourceCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(SourceModel (C 0), CuspRetraction.QuotientCentralFibre C ε)
    where
  toFun :=
    Quotient.lift (CuspHoneycomb.honeycombCollapseMap C ε hε)
      (by
        rintro p q ⟨v, hv⟩
        rw [← hv]
        exact honeycombCollapseMap_sourceDeck C ε hε v q)
  continuous_toFun := (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).quotient_lift _

@[simp]
theorem CuspSpecialization.sourceCollapse_projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : CuspHoneycomb.PhasePlane) :
    sourceCollapse C ε hε (sourceProjection (C 0) p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε p :=
  rfl

theorem CuspSpecialization.circle_exp_two_pi : Circle.exp (2 * Real.pi) = 1 := by
  apply Circle.ext
  simpa only [Circle.coe_exp, Circle.coe_one, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.exp_two_pi_mul_I

def CuspSpecialization.planarPhase (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.CompactFibreTorus := fun i => Circle.exp (2 * Real.pi * y i)

theorem CuspSpecialization.planarPhase_continuous : Continuous planarPhase := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_apply i))

theorem CuspSpecialization.circle_exp_add_integer (a y : ℝ) (n : ℤ) :
    Circle.exp (a * (y + n)) = Circle.exp (a * y) * Circle.exp a ^ n := by
  rw [mul_add, Circle.exp_add]
  congr 1
  rw [mul_comm, Circle.exp_intCast_mul]

theorem CuspSpecialization.planarPhase_add_latticePoint (y : (CuspHoneycombTiling.Plane))
    (v : Fin 2 → ℤ) : planarPhase (y + CuspHoneycombTiling.latticePoint v) = planarPhase y := by
  funext i
  change Circle.exp (2 * Real.pi * (y i + (v i : ℝ))) = _
  rw [circle_exp_add_integer, circle_exp_two_pi, one_zpow, mul_one]
  rfl

def CuspSpecialization.compensatingPhase (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    ToricSpace.CompactTorus :=
  ![p.1 0 * Circle.exp (2 * Real.pi * r * p.2 0), p.1 1 * Circle.exp (2 * Real.pi * r * p.2 1),
    Circle.exp (2 * Real.pi * r)]

theorem CuspSpecialization.compensatingPhase_continuous :
    Continuous (fun p : ℝ × CuspHoneycomb.PhasePlane => compensatingPhase p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [compensatingPhase] <;> fun_prop

@[simp]
theorem CuspSpecialization.compensatingPhase_zero (p : CuspHoneycomb.PhasePlane) :
    compensatingPhase 0 p = ToricSpace.compactFibrePhase p.1 := by
  funext i
  fin_cases i <;> simp [compensatingPhase, ToricSpace.compactFibrePhase]

@[simp]
theorem CuspSpecialization.compensatingPhase_one (p : CuspHoneycomb.PhasePlane) :
    compensatingPhase 1 p = ToricSpace.compactFibrePhase (p.1 * planarPhase p.2) := by
  funext i
  fin_cases i <;> simp [compensatingPhase, ToricSpace.compactFibrePhase, planarPhase]

theorem CuspSpecialization.compensatingPhase_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    compensatingPhase r (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      CuspPositive.phaseTransform C₀ v (compensatingPhase r p) := by
  funext i
  fin_cases i
  · change
      (CuspCollapse.deckFibrePhase C₀ v 0 * p.1 0) *
          Circle.exp (2 * Real.pi * r * (p.2 0 + (ToricSpace.cuspVector v 0 : ℝ))) =
        CuspPositive.frozenPhaseCoordinate C₀ v 0 *
          ((p.1 0 * Circle.exp (2 * Real.pi * r * p.2 0)) *
            Circle.exp (2 * Real.pi * r) ^ ToricSpace.cuspVector v 0)
    rw [circle_exp_add_integer]
    simp only [CuspCollapse.deckFibrePhase, mul_assoc]
  · change
      (CuspCollapse.deckFibrePhase C₀ v 1 * p.1 1) *
          Circle.exp (2 * Real.pi * r * (p.2 1 + (ToricSpace.cuspVector v 1 : ℝ))) =
        CuspPositive.frozenPhaseCoordinate C₀ v 1 *
          ((p.1 1 * Circle.exp (2 * Real.pi * r * p.2 1)) *
            Circle.exp (2 * Real.pi * r) ^ ToricSpace.cuspVector v 1)
    rw [circle_exp_add_integer]
    simp only [CuspCollapse.deckFibrePhase, mul_assoc]
  · simp [compensatingPhase, CuspPositive.phaseTransform, CuspPositive.frozenPhase,
      ToricSpace.phaseShear]

def CuspSpecialization.rotatedLevel (ρ r : ℝ) : ℂ :=
  (Circle.exp (2 * Real.pi * r) : ℂ) * (ρ : ℂ)

@[simp]
theorem CuspSpecialization.norm_rotatedLevel (ρ r : ℝ) (hρ : 0 ≤ ρ) : ‖rotatedLevel ρ r‖ = ρ := by
  rw [rotatedLevel, norm_mul, Circle.norm_coe, one_mul, Complex.norm_of_nonneg hρ]

theorem CuspSpecialization.rotatedLevel_ne_zero (ρ r : ℝ) (hρ : 0 < ρ) : rotatedLevel ρ r ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [norm_rotatedLevel ρ r hρ.le]
  exact hρ.ne'

theorem CuspSpecialization.rotatedLevel_norm_lt (ρ r : ℝ) (hρ : 0 ≤ ρ) (ε : ℝ) (hρε : ρ < ε) :
    ‖rotatedLevel ρ r‖ < ε := by rwa [norm_rotatedLevel ρ r hρ]

theorem CuspSpecialization.rotatedLevel_norm_le (ρ r : ℝ) (hρ : 0 ≤ ρ) (η : ℝ) (hρη : ρ ≤ η) :
    ‖rotatedLevel ρ r‖ ≤ η := by rwa [norm_rotatedLevel ρ r hρ]

def CuspSpecialization.baseRotationPhase (r : ℝ) : ToricSpace.CompactTorus :=
  ![1, 1, Circle.exp (2 * Real.pi * r)]

def CuspSpecialization.baseRotationMap (ρ r : ℝ) (x : ToricFibre (ρ : ℂ)) :
    ToricFibre (rotatedLevel ρ r) :=
  ⟨ToricSpace.compactTorusAction (baseRotationPhase r) x,
    by
    rw [ToricSpace.compactTorusAction, ToricSpace.time_torusAction,
      ToricSpace.compactTorusUnits_apply, x.2]
    rfl⟩

def CuspSpecialization.baseInverseRotationMap (ρ r : ℝ) (x : ToricFibre (rotatedLevel ρ r)) :
    ToricFibre (ρ : ℂ) :=
  ⟨ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹ x,
    by
    rw [ToricSpace.compactTorusAction, ToricSpace.time_torusAction,
      ToricSpace.compactTorusUnits_apply, x.2]
    change
      ((Circle.exp (2 * Real.pi * r))⁻¹ : Circle) *
          ((Circle.exp (2 * Real.pi * r) : ℂ) * (ρ : ℂ)) =
        (ρ : ℂ)
    rw [Circle.coe_inv, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]⟩

theorem CuspSpecialization.baseRotationMap_continuous (ρ r : ℝ) :
    Continuous (baseRotationMap ρ r) := by
  have h :
    Continuous
      (fun x : ToricFibre (ρ : ℂ) =>
        ToricSpace.compactTorusAction (baseRotationPhase r) (x : ToricSpace.Space)) := by
    change Continuous (fun x : ToricFibre (ρ : ℂ) => baseRotationPhase r • (x : ToricSpace.Space))
    exact
      (continuous_const : Continuous (fun _ : ToricFibre (ρ : ℂ) => baseRotationPhase r)).smul
        (continuous_subtype_val :
          Continuous (fun x : ToricFibre (ρ : ℂ) => (x : ToricSpace.Space)))
  exact h.subtype_mk _

theorem CuspSpecialization.baseInverseRotationMap_continuous (ρ r : ℝ) :
    Continuous (baseInverseRotationMap ρ r) := by
  have h :
    Continuous
      (fun x : ToricFibre (rotatedLevel ρ r) =>
        ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹ (x : ToricSpace.Space)) := by
    change
      Continuous
        (fun x : ToricFibre (rotatedLevel ρ r) =>
          (baseRotationPhase r)⁻¹ • (x : ToricSpace.Space))
    exact
      (continuous_const :
            Continuous (fun _ : ToricFibre (rotatedLevel ρ r) => (baseRotationPhase r)⁻¹)).smul
        (continuous_subtype_val :
          Continuous (fun x : ToricFibre (rotatedLevel ρ r) => (x : ToricSpace.Space)))
  exact h.subtype_mk _

def CuspSpecialization.baseRotationHomeomorph (ρ r : ℝ) :
    ToricFibre (ρ : ℂ) ≃ₜ ToricFibre (rotatedLevel ρ r)
    where
  toFun := baseRotationMap ρ r
  invFun := baseInverseRotationMap ρ r
  left_inv
    x := by
    apply Subtype.ext
    change
      ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹
          (ToricSpace.compactTorusAction (baseRotationPhase r) (x : ToricSpace.Space)) =
        (x : ToricSpace.Space)
    rw [ToricSpace.compactTorusAction_mul, inv_mul_cancel, ToricSpace.compactTorusAction_one]
  right_inv
    x := by
    apply Subtype.ext
    change
      ToricSpace.compactTorusAction (baseRotationPhase r)
          (ToricSpace.compactTorusAction (baseRotationPhase r)⁻¹ (x : ToricSpace.Space)) =
        (x : ToricSpace.Space)
    rw [ToricSpace.compactTorusAction_mul, mul_inv_cancel, ToricSpace.compactTorusAction_one]
  continuous_toFun := baseRotationMap_continuous ρ r
  continuous_invFun := baseInverseRotationMap_continuous ρ r

def CuspSpecialization.partialPlanarPhase (r : ℝ) (y : (CuspHoneycombTiling.Plane)) :
    ToricSpace.CompactFibreTorus := fun i => Circle.exp (2 * Real.pi * r * y i)

theorem CuspSpecialization.partialPlanarPhase_continuous (r : ℝ) :
    Continuous (partialPlanarPhase r) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_apply i))

def CuspSpecialization.partialPhaseHomeomorph (r : ℝ) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspHoneycomb.PhasePlane
    where
  toFun p := (p.1 * partialPlanarPhase r p.2, p.2)
  invFun p := (p.1 * (partialPlanarPhase r p.2)⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun :=
    (continuous_fst.mul ((partialPlanarPhase_continuous r).comp continuous_snd)).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul (((partialPlanarPhase_continuous r).comp continuous_snd).inv)).prodMk
      continuous_snd

theorem CuspSpecialization.baseRotationPhase_mul_partialPhase (r : ℝ)
    (p : CuspHoneycomb.PhasePlane) :
    baseRotationPhase r * ToricSpace.compactFibrePhase (p.1 * partialPlanarPhase r p.2) =
      compensatingPhase r p := by
  funext i
  fin_cases i <;>
    simp [baseRotationPhase, ToricSpace.compactFibrePhase, partialPlanarPhase, compensatingPhase]

def CuspSpecialization.complexPhaseHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) :
    CuspHoneycomb.PhasePlane ≃ₜ ToricFibre (rotatedLevel ρ r) :=
  ((partialPhaseHomeomorph r).trans (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR)).trans
    (baseRotationHomeomorph ρ r)

@[simp]
theorem CuspSpecialization.complexPhaseHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ)
    (p : CuspHoneycomb.PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p : ToricSpace.Space) =
      ToricSpace.compactTorusAction (compensatingPhase r p)
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space) := by
  change
    ToricSpace.compactTorusAction (baseRotationPhase r)
        (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR (partialPhaseHomeomorph r p) :
          ToricSpace.Space) =
      _
  rw [frozenPhaseHomeomorph_coe, ToricSpace.compactFibreAction_eq_compact,
    ToricSpace.compactTorusAction_mul]
  change
    ToricSpace.compactTorusAction
        (baseRotationPhase r * ToricSpace.compactFibrePhase (p.1 * partialPlanarPhase r p.2))
        ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space) =
      _
  rw [baseRotationPhase_mul_partialPhase]

theorem CuspSpecialization.complexPhaseHomeomorph_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r (CuspHoneycomb.honeycombDeckMap C₀ v p) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C₀) v
        (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p : ToricSpace.Space) := by
  rw [complexPhaseHomeomorph_coe, complexPhaseHomeomorph_coe, compensatingPhase_deck]
  change
    ToricSpace.compactTorusAction (CuspPositive.phaseTransform C₀ v (compensatingPhase r p))
        ((normalizedPositivePoint C₀ ρ hρ
              (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))).1 :
          ToricSpace.Space) =
      _
  rw [normalizedPositivePoint_equivariant C₀ ρ hρ ε hε1 hρε hR, positiveFibreTranslate_coe,
    CuspPositive.twistedTranslate_constant_polar]

def CuspSpecialization.toricFibrePunctured (η : ℝ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) : CuspControlledRetraction.PuncturedClosedTube η :=
  CuspControlledRetraction.levelToPunctured η t ht (toricFibreLevelHomeomorph η t htη x)

def CuspSpecialization.positiveFibrePunctured (ρ : ℝ) (hρ : 0 < ρ) (η : ℝ) (hρη : ρ ≤ η)
    (q : PositiveFibre ρ) : CuspControlledRetraction.PuncturedPositiveTube η :=
  ⟨⟨q.1, by rw [q.2, Complex.norm_of_nonneg hρ.le]; exact hρη⟩, by
    rw [q.2]
    exact Complex.ofReal_ne_zero.mpr hρ.ne'⟩

def CuspSpecialization.phasePlaneShear (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.PhasePlane :=
  (p.1 * planarPhase p.2, p.2)

theorem CuspSpecialization.phasePlaneShear_continuous : Continuous phasePlaneShear :=
  (continuous_fst.mul (planarPhase_continuous.comp continuous_snd)).prodMk continuous_snd

theorem CuspSpecialization.phasePlaneShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    phasePlaneShear (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      CuspHoneycomb.honeycombDeckMap C₀ v (phasePlaneShear p) := by
  apply Prod.ext
  · change
      (CuspCollapse.deckFibrePhase C₀ v * p.1) *
          planarPhase (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
        CuspCollapse.deckFibrePhase C₀ v * (p.1 * planarPhase p.2)
    rw [planarPhase_add_latticePoint, mul_assoc]
  · rfl

def CuspSpecialization.sourceShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(SourceModel C₀, SourceModel C₀)
    where
  toFun :=
    Quotient.map phasePlaneShear
      (by
        rintro p q ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [← phasePlaneShear_deck, hv])
  continuous_toFun :=
    ((sourceProjection_continuous C₀).comp phasePlaneShear_continuous).quotient_lift _

@[simp]
theorem CuspSpecialization.sourceShear_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    sourceShear C₀ (sourceProjection C₀ p) = sourceProjection C₀ (phasePlaneShear p) :=
  rfl

def CuspSpecialization.rotatingCentralPoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (p : CuspHoneycomb.PhasePlane) : CuspRetraction.CentralFibre :=
  ⟨ToricSpace.compactTorusAction (compensatingPhase r p)
      ((CuspHoneycomb.honeycombHomeomorph C₀ p.2).1 : ToricSpace.Space),
    by
    apply norm_eq_zero.mp
    rw [ToricSpace.norm_time_compactTorusAction, (CuspHoneycomb.honeycombHomeomorph C₀ p.2).2,
      norm_zero]⟩

theorem CuspSpecialization.rotatingCentralPoint_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun p : ℝ × CuspHoneycomb.PhasePlane => rotatingCentralPoint C₀ p.1 p.2) := by
  have hθ :
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane => CuspHoneycomb.honeycombHomeomorph C₀ p.2.2) :=
    (CuspHoneycomb.honeycombHomeomorph C₀).continuous.comp (continuous_snd.comp continuous_snd)
  have hθp :
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane => (CuspHoneycomb.honeycombHomeomorph C₀ p.2.2).1) :=
    continuous_subtype_val.comp hθ
  have hθx :
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane =>
        ((CuspHoneycomb.honeycombHomeomorph C₀ p.2.2).1 : ToricSpace.Space)) :=
    continuous_subtype_val.comp hθp
  apply Continuous.subtype_mk
  change
    Continuous
      (fun p : ℝ × CuspHoneycomb.PhasePlane =>
        compensatingPhase p.1 p.2 •
          ((CuspHoneycomb.honeycombHomeomorph C₀ p.2.2).1 : ToricSpace.Space))
  exact compensatingPhase_continuous.smul hθx

@[simp]
theorem CuspSpecialization.rotatingCentralPoint_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    rotatingCentralPoint C₀ 0 p = CuspHoneycomb.honeycombPolarMap C₀ p := by
  apply Subtype.ext
  change ToricSpace.compactTorusAction (compensatingPhase 0 p) _ = _
  rw [compensatingPhase_zero]
  rfl

@[simp]
theorem CuspSpecialization.rotatingCentralPoint_one (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    rotatingCentralPoint C₀ 1 p = CuspHoneycomb.honeycombPolarMap C₀ (phasePlaneShear p) := by
  apply Subtype.ext
  change ToricSpace.compactTorusAction (compensatingPhase 1 p) _ = _
  rw [compensatingPhase_one]
  rfl

theorem CuspSpecialization.rotatingCentralPoint_deck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    (rotatingCentralPoint (C 0) r (CuspHoneycomb.honeycombDeckMap (C 0) v p) : ToricSpace.Space) =
      ToricSpace.twistedTranslate C v (rotatingCentralPoint (C 0) r p : ToricSpace.Space) := by
  rw [CuspCollapse.twistedTranslate_central_eq_constant C v (rotatingCentralPoint (C 0) r p).2]
  change
    ToricSpace.compactTorusAction (compensatingPhase r (CuspHoneycomb.honeycombDeckMap (C 0) v p))
        ((CuspHoneycomb.honeycombHomeomorph (C 0)
              (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))).1 :
          ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C 0) v
        (ToricSpace.compactTorusAction (compensatingPhase r p)
          ((CuspHoneycomb.honeycombHomeomorph (C 0) p.2).1 : ToricSpace.Space))
  rw [compensatingPhase_deck, CuspHoneycomb.honeycombHomeomorph_equivariant,
    CuspCollapse.positiveCentralTranslate_coe, CuspPositive.twistedTranslate_constant_polar]

theorem CuspSpecialization.toricFibrePunctured_complexPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) (η : ℝ) (hρη : ρ ≤ η)
    (p : CuspHoneycomb.PhasePlane) :
    toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη) (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p) =
      CuspControlledRetraction.puncturedPolarMap η
        (compensatingPhase r p,
          positiveFibrePunctured ρ hρ η hρη (normalizedPositivePoint C₀ ρ hρ p.2)) := by
  apply Subtype.ext
  apply Subtype.ext
  exact complexPhaseHomeomorph_coe C₀ ρ hρ ε hε1 hρε hR r p

theorem CuspSpecialization.prescribedCollapse_complexPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (r : ℝ) (η : ℝ) (hρη : ρ ≤ η)
    (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.prescribedCollapse C₀ η
        (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
          (rotatedLevel_norm_le ρ r hρ.le η hρη)
          (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p)) =
      rotatingCentralPoint C₀ r p := by
  apply Subtype.ext
  rw [toricFibrePunctured_complexPhase C₀ ρ hρ ε hε1 hρε hR r η hρη p,
    CuspControlledRetraction.prescribedCollapse_polar]
  change
    ToricSpace.compactTorusAction (compensatingPhase r p)
        ((CuspHoneycomb.honeycombHomeomorph C₀
              (CuspControlledRetraction.normalizedPosition C₀
                ((normalizedPositivePoint C₀ ρ hρ p.2).1 : ToricSpace.Space))).1 :
          ToricSpace.Space) =
      ToricSpace.compactTorusAction (compensatingPhase r p)
        ((CuspHoneycomb.honeycombHomeomorph C₀ p.2).1 : ToricSpace.Space)
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply p.2
  rw [normalizedPositiveHomeomorph_symm_apply, normalizedPositiveHomeomorph_apply] at hy
  rw [hy]

def CuspSpecialization.fibreProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (t : ℂ)
    (htε : ‖t‖ < ε) : ToricFibre t → CuspControlledRetraction.ActualQuotientFibre C ε t :=
  CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl ∘
    CuspControlledRetraction.levelProjection C htε t ∘ toricFibreLevelHomeomorph ‖t‖ t le_rfl

@[simp]
theorem CuspSpecialization.fibreProjection_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (t : ℂ)
    (htε : ‖t‖ < ε) (x : ToricFibre t) :
    (fibreProjection C ε t htε x : CuspQuotient.QuotientSpace C ε) =
      CuspQuotient.quotientMap C ε
        ⟨(x : ToricSpace.Space),
          by
          change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
          rw [x.2]
          simpa only [Metric.mem_ball, dist_zero_right] using htε⟩ :=
  rfl

theorem CuspSpecialization.fibreProjection_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (t : ℂ) (htε : ‖t‖ < ε) : Function.Surjective (fibreProjection C ε t htε) :=
  (CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).surjective.comp
    ((CuspControlledRetraction.levelProjection_surjective C htε t).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).surjective)

theorem CuspSpecialization.fibreProjection_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (t : ℂ) (htε : ‖t‖ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (fibreProjection C ε t htε) :=
  (CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).isOpenQuotientMap.comp
    ((CuspControlledRetraction.levelProjection_isOpenQuotientMap C htε t hC).comp
      (toricFibreLevelHomeomorph ‖t‖ t le_rfl).isOpenQuotientMap)

theorem CuspSpecialization.fibreProjection_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (t : ℂ) (htε : ‖t‖ < ε) (x y : ToricFibre t) :
    fibreProjection C ε t htε x = fibreProjection C ε t htε y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.twistedTranslate C v (y : ToricSpace.Space) = (x : ToricSpace.Space) := by
  change
    CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl
          (CuspControlledRetraction.levelProjection C htε t
            (toricFibreLevelHomeomorph ‖t‖ t le_rfl x)) =
        CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl
          (CuspControlledRetraction.levelProjection C htε t
            (toricFibreLevelHomeomorph ‖t‖ t le_rfl y)) ↔
      _
  rw [(CuspControlledRetraction.quotientLevelFibreHomeomorph C ε ‖t‖ t le_rfl).injective.eq_iff,
    CuspControlledRetraction.levelProjection_eq_iff]
  apply exists_congr
  intro v
  exact
    ⟨fun h => congrArg (fun z : CuspRetraction.ClosedTube ‖t‖ => (z : ToricSpace.Space)) h,
      fun h => Subtype.ext h⟩

theorem CuspSpecialization.fibreProjection_eq_levelProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (t : ℂ) (htε : ‖t‖ < ε) (η : ℝ) (hηε : η < ε) (htη : ‖t‖ ≤ η) (x : ToricFibre t) :
    fibreProjection C ε t htε x =
      CuspControlledRetraction.quotientLevelFibreHomeomorph C ε η t htη
        (CuspControlledRetraction.levelProjection C hηε t
          (toricFibreLevelHomeomorph η t htη x)) :=
  rfl

def CuspSpecialization.toricFibreChangeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (x : ToricFibre t) : ToricFibre t :=
  ⟨CuspRetraction.changeTwist C D x, (CuspRetraction.time_changeTwist C D x).trans x.2⟩

def CuspSpecialization.toricFibreChangeTwistHomeomorph (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContDiffOn ℂ ω (fun z => D z i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (t : ℂ) (htε : ‖t‖ < ε) :
    ToricFibre t ≃ₜ ToricFibre t
    where
  toFun := toricFibreChangeTwist C D t
  invFun := toricFibreChangeTwist D C t
  left_inv
    x :=
    Subtype.ext
      (CuspRetraction.changeTwist_inverse_on_disc C D hε1 hRC hRD
        (by
          rw [x.2]
          exact htε))
  right_inv
    x :=
    Subtype.ext
      (CuspRetraction.changeTwist_inverse_on_disc D C hε1 hRD hRC
        (by
          rw [x.2]
          exact htε))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      (CuspRetraction.changeTwist_continuousOn C D hε hε1 (fun i j => (hC i j).continuousOn)
            (fun i j => (hD i j).continuousOn) hzero hRC).comp_continuous
        continuous_subtype_val
        (fun x => by
          change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
          rw [x.2]
          simpa only [Metric.mem_ball, dist_zero_right] using htε)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact
      (CuspRetraction.changeTwist_continuousOn D C hε hε1 (fun i j => (hD i j).continuousOn)
            (fun i j => (hC i j).continuousOn) hzero.symm hRD).comp_continuous
        continuous_subtype_val
        (fun x => by
          change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
          rw [x.2]
          simpa only [Metric.mem_ball, dist_zero_right] using htε)

theorem CuspSpecialization.centralRotation_sourceDeck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    CuspCollapse.centralProject C ε hε
        (rotatingCentralPoint (C 0) r (CuspHoneycomb.honeycombDeckMap (C 0) v p)) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  apply (CuspCollapse.centralProject_eq_iff C ε hε _ _).mpr
  exact ⟨v, (rotatingCentralPoint_deck C v r p).symm⟩

def CuspSpecialization.sourceRotation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (r : ℝ) : C(SourceModel (C 0), CuspRetraction.QuotientCentralFibre C ε)
    where
  toFun :=
    Quotient.lift
      (fun p : CuspHoneycomb.PhasePlane =>
        CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p))
      (by
        rintro p q ⟨v, hv⟩
        rw [← hv]
        exact centralRotation_sourceDeck C ε hε r v q)
  continuous_toFun :=
    ((CuspCollapse.centralProject_continuous C ε hε).comp
          ((rotatingCentralPoint_continuous (C 0)).comp
            (continuous_const.prodMk continuous_id))).quotient_lift
      _

@[simp]
theorem CuspSpecialization.sourceRotation_projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    sourceRotation C ε hε r (sourceProjection (C 0) p) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) :=
  rfl

theorem CuspSpecialization.sourceRotation_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (fun p : ℝ × SourceModel (C 0) => sourceRotation C ε hε p.1 p.2) := by
  apply (sourceProjection_isQuotientMap (C 0)).continuous_lift_prod_right
  simpa only [Function.comp_def, sourceRotation_projection] using
    (CuspCollapse.centralProject_continuous C ε hε).comp (rotatingCentralPoint_continuous (C 0))

@[simp]
theorem CuspSpecialization.sourceRotation_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : sourceRotation C ε hε 0 = sourceCollapse C ε hε := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, rotatingCentralPoint_zero]
  rfl

@[simp]
theorem CuspSpecialization.sourceRotation_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : sourceRotation C ε hε 1 = (sourceCollapse C ε hε).comp (sourceShear (C 0)) := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [sourceRotation_projection, rotatingCentralPoint_one]
  rfl

def CuspSpecialization.sourceRotationHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) : (sourceCollapse C ε hε).Homotopy (sourceRotation C ε hε r)
    where
  toFun p := sourceRotation C ε hε ((p.1 : ℝ) * r) p.2
  continuous_toFun := by
    have hs : Continuous (fun p : unitInterval × SourceModel (C 0) => ((p.1 : ℝ) * r, p.2)) :=
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd
    simpa only [Function.comp_def] using (sourceRotation_continuous C ε hε).comp hs
  map_zero_left
    q := by
    change sourceRotation C ε hε (0 * r) q = sourceCollapse C ε hε q
    rw [MulZeroClass.zero_mul, sourceRotation_zero]
  map_one_left
    q := by
    change sourceRotation C ε hε (1 * r) q = sourceRotation C ε hε r q
    rw [one_mul]

def CuspSpecialization.varyingComplexPhaseHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) : CuspHoneycomb.PhasePlane ≃ₜ ToricFibre (rotatedLevel ρ r) :=
  (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε (CuspPositive.smallDrift_positiveTwist (C 0) hRD)
        r).trans
    (toricFibreChangeTwistHomeomorph C (CuspRetraction.frozen C) ε hε hε1 hC
        (fun _ _ => contDiffOn_const) rfl hRC hRD (rotatedLevel ρ r)
        (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).symm

@[simp]
theorem CuspSpecialization.varyingComplexPhaseHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : ToricSpace.Space) =
      CuspRetraction.changeTwist (CuspRetraction.frozen C) C
        (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
            (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p :
          ToricSpace.Space) :=
  rfl

theorem CuspSpecialization.varyingComplexPhaseHomeomorph_straightened
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    CuspRetraction.changeTwist C (CuspRetraction.frozen C)
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : ToricSpace.Space) =
      (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p :
        ToricSpace.Space) := by
  rw [varyingComplexPhaseHomeomorph_coe]
  apply CuspRetraction.changeTwist_inverse_on_disc (CuspRetraction.frozen C) C hε1 hRD hRC
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
        (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p).2]
  exact rotatedLevel_norm_lt ρ r hρ.le ε hρε

theorem CuspSpecialization.varyingComplexPhaseHomeomorph_deck (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
          (CuspHoneycomb.honeycombDeckMap (C 0) v p) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate C v
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : ToricSpace.Space) := by
  rw [varyingComplexPhaseHomeomorph_coe, varyingComplexPhaseHomeomorph_coe,
    complexPhaseHomeomorph_deck]
  apply CuspRetraction.changeTwist_equivariant_on_disc (CuspRetraction.frozen C) C rfl hε1 hRD
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
        (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p).2]
  exact rotatedLevel_norm_lt ρ r hρ.le ε hρε

def CuspSpecialization.varyingComplexFibreMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) :
    CuspHoneycomb.PhasePlane →
      CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  fibreProjection C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε) ∘
    varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r

theorem CuspSpecialization.varyingComplexFibreMap_isOpenQuotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) : IsOpenQuotientMap (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (fibreProjection_isOpenQuotientMap C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε)
        hC).comp
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).isOpenQuotientMap

theorem CuspSpecialization.varyingComplexFibreMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) : Topology.IsQuotientMap (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (varyingComplexFibreMap_isOpenQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD r).isQuotientMap

theorem CuspSpecialization.varyingComplexFibreMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p q : CuspHoneycomb.PhasePlane) :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
        varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r q ↔
      ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap (C 0) v q = p := by
  change
    fibreProjection C ε (rotatedLevel ρ r) _
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p) =
        fibreProjection C ε (rotatedLevel ρ r) _
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q) ↔
      _
  rw [fibreProjection_eq_iff]
  apply exists_congr
  intro v
  rw [← varyingComplexPhaseHomeomorph_deck C ρ hρ ε hε hε1 hρε hC hRC hRD r v q]
  exact
    ⟨fun h =>
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).injective (Subtype.ext h),
      fun h =>
      congrArg
        (fun z : CuspHoneycomb.PhasePlane =>
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r z : ToricSpace.Space))
        h⟩

def CuspSpecialization.varyingComplexSourceHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) :
    SourceModel (C 0) ≃ₜ CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  CuspHoneycombClosedCover.quotientHomeomorph (sourceProjection (C 0))
    (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r)
    (sourceProjection_isQuotientMap (C 0))
    (varyingComplexFibreMap_isQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD r)
    (fun p q =>
      (sourceProjection_eq_iff (C 0) p q).trans
        (varyingComplexFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD r p q).symm)

@[simp]
theorem CuspSpecialization.varyingComplexSourceHomeomorph_projection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (p : CuspHoneycomb.PhasePlane) :
    varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r (sourceProjection (C 0) p) =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

def CuspSpecialization.varyingComplexPhaseLevelHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspControlledRetraction.ToricLevel η (rotatedLevel ρ r) :=
  (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).trans
    (toricFibreLevelHomeomorph η (rotatedLevel ρ r) (rotatedLevel_norm_le ρ r hρ.le η hρη))

theorem CuspSpecialization.varyingComplexFibreMap_eq_levelProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CuspHoneycomb.PhasePlane) :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      CuspControlledRetraction.quotientLevelFibreHomeomorph C ε η (rotatedLevel ρ r)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r)
          (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p)) :=
  fibreProjection_eq_levelProjection C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε)
    η hηε (rotatedLevel_norm_le ρ r hρ.le η hρη)
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)

theorem CuspSpecialization.puncturedStraightening_varyingComplexPhase
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.puncturedStraightening C η
        (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
          (rotatedLevel_norm_le ρ r hρ.le η hρη)
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)) =
      toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r p) := by
  apply Subtype.ext
  apply Subtype.ext
  exact varyingComplexPhaseHomeomorph_straightened C ρ hρ ε hε hε1 hρε hC hRC hRD r p

theorem CuspSpecialization.prescribedFibreUpstairs_varyingComplexPhaseLevel
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ)
        (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  change
    CuspCollapse.centralProject C ε hε
        (CuspControlledRetraction.prescribedCollapse (C 0) η
          (CuspControlledRetraction.puncturedStraightening C η
            (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
              (rotatedLevel_norm_le ρ r hρ.le η hρη)
              (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)))) =
      _
  rw [puncturedStraightening_varyingComplexPhase C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p,
    prescribedCollapse_complexPhase (C 0) ρ hρ ε hε1 hρε
      (CuspPositive.smallDrift_positiveTwist (C 0) hRD) r η hρη p]

theorem CuspSpecialization.prescribedFibreUpstairs_varyingComplex_compatible
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (x y : CuspControlledRetraction.ToricLevel η (rotatedLevel ρ r))
    (hxy :
      CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r) x =
        CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r) y) :
    CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) x =
      CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) y := by
  obtain ⟨p, rfl⟩ :=
    (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη).surjective x
  obtain ⟨q, rfl⟩ :=
    (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη).surjective y
  have hf :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r q := by
    rw [varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε p,
      varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε q, hxy]
  obtain ⟨v, hv⟩ := (varyingComplexFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD r p q).mp hf
  rw [prescribedFibreUpstairs_varyingComplexPhaseLevel,
    prescribedFibreUpstairs_varyingComplexPhaseLevel, ← hv, centralRotation_sourceDeck]

theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplexFibreMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : CuspHoneycomb.PhasePlane) :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p) =
      CuspCollapse.centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  rw [CuspControlledRetraction.prescribedActualFibreCollapse, Function.comp_apply,
    varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε p,
    Homeomorph.symm_apply_apply]
  change
    CuspControlledRetraction.levelDescend C hηε (rotatedLevel ρ r)
        (CuspControlledRetraction.prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r)
          (rotatedLevel_ne_zero ρ r hρ))
        (CuspControlledRetraction.levelProjection C hηε (rotatedLevel ρ r)
          (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p)) =
      _
  rw [CuspControlledRetraction.levelDescend_levelProjection C hηε (rotatedLevel ρ r) _
      (prescribedFibreUpstairs_varyingComplex_compatible C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη
        hηε)]
  exact prescribedFibreUpstairs_varyingComplexPhaseLevel C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p

theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplexSourceHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (q : SourceModel (C 0)) :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q) =
      sourceRotation C ε hε r q := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [varyingComplexSourceHomeomorph_projection, sourceRotation_projection]
  exact
    prescribedActualFibreCollapse_varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη
      hηε p

theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplex_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Continuous
      (CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)) := by
  apply
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
          r).isQuotientMap |>.continuous_iff.mpr
  have he :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
          (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη) ∘
        varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r =
      sourceRotation C ε hε r :=
    funext
      (prescribedActualFibreCollapse_varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
        r η hρη hηε)
  rw [he]
  exact (sourceRotation C ε hε r).continuous

def CuspSpecialization.varyingComplexCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    C(CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r),
      CuspRetraction.QuotientCentralFibre C ε)
    where
  toFun :=
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
  continuous_toFun :=
    prescribedActualFibreCollapse_varyingComplex_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη
      hηε

def CuspSpecialization.sourcePhaseArgument (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) : (CuspHoneycombTiling.Plane) :=
  (fun i j => (C₀ i j).re) *ᵥ (-ToricSpace.realCuspVector y)

theorem CuspSpecialization.sourcePhaseArgument_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y z : (CuspHoneycombTiling.Plane)) :
    sourcePhaseArgument C₀ (y + z) = sourcePhaseArgument C₀ y + sourcePhaseArgument C₀ z := by
  funext i
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    ToricSpace.realCuspVector, mul_add, add_comm, add_left_comm, add_assoc]

@[simp]
theorem CuspSpecialization.sourcePhaseArgument_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    sourcePhaseArgument C₀ 0 = 0 := by
  funext i
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    ToricSpace.realCuspVector]

theorem CuspSpecialization.sourcePhaseArgument_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourcePhaseArgument C₀) := by
  unfold sourcePhaseArgument
  simp only [ToricSpace.realCuspVector]
  fun_prop

theorem CuspSpecialization.sourcePhaseArgument_lattice_cuspVector (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    sourcePhaseArgument C₀ (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) i =
      ((C₀ *ᵥ (fun j => (v j : ℂ))) i).re := by
  simp [sourcePhaseArgument, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    ToricSpace.realCuspVector, CuspHoneycombTiling.latticePoint, ToricSpace.cuspVector,
    Complex.mul_re, add_comm]

def CuspSpecialization.sourcePhaseCharacter (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y : (CuspHoneycombTiling.Plane)) : ToricSpace.CompactFibreTorus := fun i =>
  Circle.exp (2 * Real.pi * sourcePhaseArgument C₀ y i)

theorem CuspSpecialization.sourcePhaseCharacter_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (sourcePhaseCharacter C₀) := by
  apply continuous_pi
  intro i
  exact
    Circle.exp.continuous.comp
      (continuous_const.mul ((continuous_apply i).comp (sourcePhaseArgument_continuous C₀)))

@[simp]
theorem CuspSpecialization.sourcePhaseCharacter_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    sourcePhaseCharacter C₀ 0 = 1 := by
  funext i
  simp [sourcePhaseCharacter]

theorem CuspSpecialization.sourcePhaseCharacter_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (y z : (CuspHoneycombTiling.Plane)) :
    sourcePhaseCharacter C₀ (y + z) = sourcePhaseCharacter C₀ y * sourcePhaseCharacter C₀ z := by
  funext i
  simp only [sourcePhaseCharacter, sourcePhaseArgument_add, Pi.add_apply, mul_add, Circle.exp_add,
    Pi.mul_apply]

@[simp]
theorem CuspSpecialization.sourcePhaseCharacter_lattice_cuspVector (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    sourcePhaseCharacter C₀ (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      CuspCollapse.deckFibrePhase C₀ v := by
  funext i
  rw [sourcePhaseCharacter, sourcePhaseArgument_lattice_cuspVector, CuspCollapse.deckFibrePhase,
    CuspPositive.frozenPhaseCoordinate_eq_exp]

theorem CuspSpecialization.sourcePhaseCharacter_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (y : (CuspHoneycombTiling.Plane)) :
    sourcePhaseCharacter C₀ (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      CuspCollapse.deckFibrePhase C₀ v * sourcePhaseCharacter C₀ y := by
  rw [sourcePhaseCharacter_add, sourcePhaseCharacter_lattice_cuspVector, mul_comm]

def CuspSpecialization.sourcePhaseShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspHoneycomb.PhasePlane
    where
  toFun p := (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, p.2)
  invFun p := (p.1 * sourcePhaseCharacter C₀ p.2, p.2)
  left_inv p := by simp only [mul_assoc, inv_mul_cancel, mul_one, Prod.eta]
  right_inv p := by simp only [mul_inv_cancel_right, Prod.eta]
  continuous_toFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp continuous_snd).inv).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp continuous_snd)).prodMk
      continuous_snd

@[simp]
theorem CuspSpecialization.sourcePhaseShear_apply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    sourcePhaseShear C₀ p = (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹, p.2) :=
  rfl

theorem CuspSpecialization.sourcePhaseShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    sourcePhaseShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      ((sourcePhaseShear C₀ p).1,
        p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) := by
  simp only [sourcePhaseShear_apply, CuspHoneycomb.honeycombDeckMap, sourcePhaseCharacter_deck]
  apply Prod.ext
  · simp only [mul_inv_rev]
    calc
      (CuspCollapse.deckFibrePhase C₀ v * p.1) *
            ((sourcePhaseCharacter C₀ p.2)⁻¹ * (CuspCollapse.deckFibrePhase C₀ v)⁻¹) =
          (CuspCollapse.deckFibrePhase C₀ v * (CuspCollapse.deckFibrePhase C₀ v)⁻¹) *
            (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) := by ac_rfl
      _ = p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹ := by rw [mul_inv_cancel, one_mul]
  · rfl

def CuspSpecialization.sourceBaseMarking :
    (CuspHoneycombTiling.Plane) ≃ₜ (CuspHoneycombTiling.Plane)
    where
  toFun y := -ToricSpace.realCuspVector y
  invFun y := ToricSpace.realCuspVector y
  left_inv
    y := by
    funext i
    fin_cases i <;> simp [ToricSpace.realCuspVector]
  right_inv
    y := by
    funext i
    fin_cases i <;> simp [ToricSpace.realCuspVector]
  continuous_toFun := by simp only [ToricSpace.realCuspVector]; fun_prop
  continuous_invFun := by simp only [ToricSpace.realCuspVector]; fun_prop

@[simp]
theorem CuspSpecialization.sourceBaseMarking_apply (y : (CuspHoneycombTiling.Plane)) :
    sourceBaseMarking y = -ToricSpace.realCuspVector y :=
  rfl

theorem CuspSpecialization.sourceBaseMarking_add (y z : (CuspHoneycombTiling.Plane)) :
    sourceBaseMarking (y + z) = sourceBaseMarking y + sourceBaseMarking z := by
  simp only [sourceBaseMarking_apply, map_add, neg_add]

@[simp]
theorem CuspSpecialization.sourceBaseMarking_lattice_cuspVector (v : Fin 2 → ℤ) :
    sourceBaseMarking (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      CuspHoneycombTiling.latticePoint v := by
  funext i
  fin_cases i <;>
    simp [sourceBaseMarking_apply, ToricSpace.realCuspVector, CuspHoneycombTiling.latticePoint,
      ToricSpace.cuspVector]

theorem CuspSpecialization.sourceBaseMarking_deck (v : Fin 2 → ℤ)
    (y : (CuspHoneycombTiling.Plane)) :
    sourceBaseMarking (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      sourceBaseMarking y + CuspHoneycombTiling.latticePoint v := by
  rw [sourceBaseMarking_add, sourceBaseMarking_lattice_cuspVector]

def CuspSpecialization.sourceMarkedShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane ≃ₜ CuspHoneycomb.PhasePlane :=
  (sourcePhaseShear C₀).trans
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr sourceBaseMarking)

theorem CuspSpecialization.sourceMarkedShear_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (p : CuspHoneycomb.PhasePlane) :
    sourceMarkedShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      ((sourceMarkedShear C₀ p).1,
        (sourceMarkedShear C₀ p).2 + CuspHoneycombTiling.latticePoint v) := by
  change
    ((sourcePhaseShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p)).1,
        sourceBaseMarking (CuspHoneycomb.honeycombDeckMap C₀ v p).2) =
      _
  rw [sourcePhaseShear_deck]
  change
    ((sourceMarkedShear C₀ p).1,
        sourceBaseMarking (p.2 + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))) =
      _
  rw [sourceBaseMarking_deck]
  rfl

theorem CuspSpecialization.sourceCoordinateProjection_isOpenQuotientMap :
    IsOpenQuotientMap (PeriodTorusHigherHomology.coordinateProjection 2) := by
  exact
    IsOpenQuotientMap.piMap
      (fun _ : Fin 2 =>
        (QuotientAddGroup.isOpenQuotientMap_mk : IsOpenQuotientMap ((↑) : ℝ → AddCircle (1 : ℝ))))

theorem CuspSpecialization.sourceCoordinateProjection_eq_iff (y z : (CuspHoneycombTiling.Plane)) :
    PeriodTorusHigherHomology.coordinateProjection 2 y =
        PeriodTorusHigherHomology.coordinateProjection 2 z ↔
      ∃ v : Fin 2 → ℤ, y = z + CuspHoneycombTiling.latticePoint v := by
  constructor
  · intro h
    have hz : PeriodTorusHigherHomology.coordinateProjection 2 (y - z) = 0 := by
      rw [map_sub, h, sub_self]
    obtain ⟨v, hv⟩ := (PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff 2 _).mp hz
    refine ⟨v, ?_⟩
    change y - z = CuspHoneycombTiling.latticePoint v at hv
    calc
      y = (y - z) + z := (sub_add_cancel y z).symm
      _ = z + CuspHoneycombTiling.latticePoint v := by rw [hv, add_comm]
  · rintro ⟨v, rfl⟩
    have hz :
      PeriodTorusHigherHomology.coordinateProjection 2 (CuspHoneycombTiling.latticePoint v) = 0 :=
      (PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff 2
            (CuspHoneycombTiling.latticePoint v)).mpr
        ⟨v, rfl⟩
    rw [map_add, hz, add_zero]

def CuspSpecialization.sourceProductCoordinates (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    CuspHoneycomb.PhasePlane →
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 :=
  Prod.map id (PeriodTorusHigherHomology.coordinateProjection 2) ∘ sourceMarkedShear C₀

theorem CuspSpecialization.sourceProductCoordinates_isOpenQuotientMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : IsOpenQuotientMap (sourceProductCoordinates C₀) :=
  (IsOpenQuotientMap.id.prodMap sourceCoordinateProjection_isOpenQuotientMap).comp
    (sourceMarkedShear C₀).isOpenQuotientMap

theorem CuspSpecialization.sourceProductCoordinates_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProductCoordinates C₀) :=
  (sourceProductCoordinates_isOpenQuotientMap C₀).surjective

theorem CuspSpecialization.sourceProductCoordinates_deck (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (p : CuspHoneycomb.PhasePlane) :
    sourceProductCoordinates C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p) =
      sourceProductCoordinates C₀ p := by
  change
    Prod.map id (PeriodTorusHigherHomology.coordinateProjection 2)
        (sourceMarkedShear C₀ (CuspHoneycomb.honeycombDeckMap C₀ v p)) =
      _
  rw [sourceMarkedShear_deck]
  apply Prod.ext
  · rfl
  · change
      PeriodTorusHigherHomology.coordinateProjection 2
          ((sourceMarkedShear C₀ p).2 + CuspHoneycombTiling.latticePoint v) =
        PeriodTorusHigherHomology.coordinateProjection 2 (sourceMarkedShear C₀ p).2
    exact (sourceCoordinateProjection_eq_iff _ _).mpr ⟨v, rfl⟩

theorem CuspSpecialization.sourceProductCoordinates_eq_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : CuspHoneycomb.PhasePlane) :
    sourceProductCoordinates C₀ p = sourceProductCoordinates C₀ q ↔
      ∃ v : Fin 2 → ℤ, CuspHoneycomb.honeycombDeckMap C₀ v q = p := by
  constructor
  · intro h
    have hphase : (sourceMarkedShear C₀ p).1 = (sourceMarkedShear C₀ q).1 :=
      congrArg
        (fun x : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 => x.1) h
    have hbase :
      PeriodTorusHigherHomology.coordinateProjection 2 (sourceMarkedShear C₀ p).2 =
        PeriodTorusHigherHomology.coordinateProjection 2 (sourceMarkedShear C₀ q).2 :=
      congrArg
        (fun x : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 => x.2) h
    obtain ⟨v, hv⟩ := (sourceCoordinateProjection_eq_iff _ _).mp hbase
    refine ⟨v, (sourceMarkedShear C₀).injective ?_⟩
    rw [sourceMarkedShear_deck]
    apply Prod.ext
    · exact hphase.symm
    · exact hv.symm
  · rintro ⟨v, hv⟩
    rw [← hv, sourceProductCoordinates_deck]

def CuspSpecialization.sourceProductMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ → ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 :=
  Quotient.lift (sourceProductCoordinates C₀)
    (by
      rintro p q ⟨v, hv⟩
      rw [← hv]
      exact sourceProductCoordinates_deck C₀ v q)

theorem CuspSpecialization.sourceProductMap_injective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Injective (sourceProductMap C₀) := by
  intro x y h
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ x
  obtain ⟨q, rfl⟩ := sourceProjection_surjective C₀ y
  exact (sourceProjection_eq_iff C₀ p q).mpr ((sourceProductCoordinates_eq_iff C₀ p q).mp h)

theorem CuspSpecialization.sourceProductMap_surjective (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Function.Surjective (sourceProductMap C₀) := by
  intro x
  obtain ⟨p, hp⟩ := sourceProductCoordinates_surjective C₀ x
  exact ⟨sourceProjection C₀ p, hp⟩

theorem CuspSpecialization.sourceProductMap_isQuotientMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Topology.IsQuotientMap (sourceProductMap C₀) :=
  (sourceProjection_isQuotientMap C₀).of_comp_isQuotientMap
    (sourceProductCoordinates_isOpenQuotientMap C₀).isQuotientMap

def CuspSpecialization.sourceProductHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ ≃ₜ ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2 :=
  (Equiv.ofBijective (sourceProductMap C₀)
        ⟨sourceProductMap_injective C₀, sourceProductMap_surjective C₀⟩).toHomeomorph
    (fun _ => (sourceProductMap_isQuotientMap C₀).isOpen_preimage)

@[simp]
theorem CuspSpecialization.sourceProductHomeomorph_projection (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : CuspHoneycomb.PhasePlane) :
    sourceProductHomeomorph C₀ (sourceProjection C₀ p) =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹,
        PeriodTorusHigherHomology.coordinateProjection 2 (-ToricSpace.realCuspVector p.2)) :=
  rfl

theorem CuspSpecialization.sourceProductHomeomorph_symm_coordinateProjection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (u : ToricSpace.CompactFibreTorus)
    (y : (CuspHoneycombTiling.Plane)) :
    (sourceProductHomeomorph C₀).symm (u, PeriodTorusHigherHomology.coordinateProjection 2 y) =
      sourceProjection C₀
        (u * sourcePhaseCharacter C₀ (ToricSpace.realCuspVector y),
          ToricSpace.realCuspVector y) := by
  apply (sourceProductHomeomorph C₀).injective
  rw [Homeomorph.apply_symm_apply]
  change
    (u, PeriodTorusHigherHomology.coordinateProjection 2 y) =
      sourceProductCoordinates C₀ ((sourceMarkedShear C₀).symm (u, y))
  unfold sourceProductCoordinates
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  rfl

def CuspSpecialization.productCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
      CuspRetraction.QuotientCentralFibre C ε) :=
  (sourceCollapse C ε hε).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
        SourceModel (C 0)))

theorem CuspSpecialization.productCollapse_coordinateProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (y : (CuspHoneycombTiling.Plane)) :
    productCollapse C ε hε (u, PeriodTorusHigherHomology.coordinateProjection 2 y) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * sourcePhaseCharacter (C 0) (ToricSpace.realCuspVector y),
          ToricSpace.realCuspVector y) := by
  change
    sourceCollapse C ε hε
        ((sourceProductHomeomorph (C 0)).symm
          (u, PeriodTorusHigherHomology.coordinateProjection 2 y)) =
      _
  rw [sourceProductHomeomorph_symm_coordinateProjection, sourceCollapse_projection]

def CuspSpecialization.productRotation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (r : ℝ) :
    C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
      CuspRetraction.QuotientCentralFibre C ε) :=
  (sourceRotation C ε hε r).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
        SourceModel (C 0)))

def CuspSpecialization.productRotationHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) : (productCollapse C ε hε).Homotopy (productRotation C ε hε r) :=
  (sourceRotationHomotopy C ε hε r).compContinuousMap
    ((sourceProductHomeomorph (C 0)).symm :
      C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
        SourceModel (C 0)))

theorem CuspSpecialization.productRotation_homologyMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (r : ℝ) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (productRotation C ε hε r) n =
      SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n :=
  (PeriodTorusHigherHomology.homotopy_homologyMap (productRotationHomotopy C ε hε r) n).symm

def CuspSpecialization.varyingComplexProductFibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) :
    (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  (sourceProductHomeomorph (C 0)).symm.trans
    (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r)

theorem CuspSpecialization.prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r p) =
      productRotation C ε hε r p :=
  prescribedActualFibreCollapse_varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η
    hρη hηε ((sourceProductHomeomorph (C 0)).symm p)

theorem CuspSpecialization.varyingComplexCollapseMap_comp_product
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r))) =
      productRotation C ε hε r :=
  ContinuousMap.ext
    (prescribedActualFibreCollapse_varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC
      hRD r η hρη hηε)

def CuspSpecialization.varyingComplexProductCollapseHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (productCollapse C ε hε).Homotopy
      ((varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
        (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r)))) := by
  rw [varyingComplexCollapseMap_comp_product]
  exact productRotationHomotopy C ε hε r

theorem CuspSpecialization.varyingComplexProductCollapseMap_homology
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : 0 < ρ) (hε1 : ε < 1)
    (hρε : ρ < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (r : ℝ) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) n) :
    SingularMayerVietoris.singularHomologyMap
        (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r) n a) =
      SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n a := by
  change
    (SingularMayerVietoris.singularHomologyMap
            (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n).comp
        (SingularMayerVietoris.singularHomologyMap
          (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r :
            C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
              CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ρ r)))
          n)
        a =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp,
    varyingComplexCollapseMap_comp_product, productRotation_homologyMap]

def CuspSpecialization.argumentTurns (t : ℂ) : ℝ :=
  t.arg / (2 * Real.pi)

theorem CuspSpecialization.rotatedLevel_norm_argumentTurns (t : ℂ) :
    rotatedLevel ‖t‖ (argumentTurns t) = t := by
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he : 2 * Real.pi * (t.arg / (2 * Real.pi)) = t.arg := mul_div_cancel₀ t.arg hπ
  rw [rotatedLevel, argumentTurns, he, Circle.coe_exp, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I t

def CuspSpecialization.IsPrescribedProductModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : ℂ) (ht : t ≠ 0)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε t) :
    Prop :=
  ∀ (η : ℝ) (htη : ‖t‖ ≤ η) (hηε : η < ε),
    ∃ hc :
      Continuous (CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε t ht htη),
      (productCollapse C ε hε).Homotopic
          ((⟨CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε t ht htη, hc⟩ :
                C(CuspControlledRetraction.ActualQuotientFibre C ε t,
                  CuspRetraction.QuotientCentralFibre C ε)).comp
            (e :
              C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
                CuspControlledRetraction.ActualQuotientFibre C ε t))) ∧
        ∀ (n : ℕ)
          (a :
            SingularMayerVietoris.SingularHomology
              (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) n),
          SingularMayerVietoris.singularHomologyMap
              (⟨CuspControlledRetraction.prescribedActualFibreCollapse C ε hε hηε t ht htη, hc⟩ :
                C(CuspControlledRetraction.ActualQuotientFibre C ε t,
                  CuspRetraction.QuotientCentralFibre C ε))
              n (PeriodTorusHigherHomology.homeomorphHomologyEquiv e n a) =
            SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n a

theorem CuspSpecialization.varyingComplexProductFibreHomeomorph_isPrescribedProductModel
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ < ε) (r : ℝ) :
    IsPrescribedProductModel C ε hε (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
      (varyingComplexProductFibreHomeomorph C ε hε ρ hρ hε1 hρε hC hRC hRD r) := by
  intro η htη hηε
  have hρη : ρ ≤ η := by rwa [norm_rotatedLevel ρ r hρ.le] at htη
  refine
    ⟨prescribedActualFibreCollapse_varyingComplex_continuous C ρ hρ ε hε hε1 hρε hC hRC hRD r η
        hρη hηε,
      ?_, ?_⟩
  · exact ⟨varyingComplexProductCollapseHomotopy C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε⟩
  · intro n a
    exact varyingComplexProductCollapseMap_homology C ε hε ρ hρ hε1 hρε hC hRC hRD r η hρη hηε n a

theorem CuspSpecialization.exists_product_model_at_nonzero_level
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε)
    (t : ℂ) (ht : t ≠ 0) (htε : ‖t‖ < ε) :
    ∃ e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε t,
      IsPrescribedProductModel C ε hε t ht e := by
  have hρ : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hm :
    ∃ e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε (rotatedLevel ‖t‖ (argumentTurns t)),
      IsPrescribedProductModel C ε hε (rotatedLevel ‖t‖ (argumentTurns t))
        (rotatedLevel_ne_zero ‖t‖ (argumentTurns t) hρ) e :=
    ⟨varyingComplexProductFibreHomeomorph C ε hε ‖t‖ hρ hε1 htε hC hRC hRD (argumentTurns t),
      varyingComplexProductFibreHomeomorph_isPrescribedProductModel C ε hε hε1 hC hRC hRD ‖t‖ hρ
        htε (argumentTurns t)⟩
  have transfer (u : ℂ) (hu : u ≠ 0) (hut : u = t)
    (huModel :
      ∃ e :
        (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
          CuspControlledRetraction.ActualQuotientFibre C ε u,
        IsPrescribedProductModel C ε hε u hu e) :
    ∃ e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C ε t,
      IsPrescribedProductModel C ε hε t ht e := by
    subst u
    exact huModel
  exact transfer _ _ (rotatedLevel_norm_argumentTurns t) hm

@[simp]
theorem CuspCentralHomology.fibreRadiusHomeomorph_fibreProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (htδ : ‖t‖ < δ)
    (x : CuspSpecialization.ToricFibre t) :
    fibreRadiusHomeomorph C r δ t hδr hC htδ (CuspSpecialization.fibreProjection C δ t htδ x) =
      CuspSpecialization.fibreProjection C r t (htδ.trans_le hδr) x := by
  apply Subtype.ext
  change
    (openQuotientRadiusHomeomorph C hδr hC (CuspSpecialization.fibreProjection C δ t htδ x).1).1 =
      (CuspSpecialization.fibreProjection C r t (htδ.trans_le hδr) x).1
  simp only [CuspSpecialization.fibreProjection_coe, openQuotientRadiusHomeomorph_quotientMap,
    openQuotientMap]

@[simp]
theorem CuspCentralHomology.centralRadiusHomeomorph_centralProject
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (x : CuspRetraction.CentralFibre) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspCollapse.centralProject C δ hδ x) =
      CuspCollapse.centralProject C r (hδ.trans_le hδr) x := by
  apply Subtype.ext
  change
    (openQuotientRadiusHomeomorph C hδr hC (CuspCollapse.centralProject C δ hδ x).1).1 =
      (CuspCollapse.centralProject C r (hδ.trans_le hδr) x).1
  simp only [CuspCollapse.centralProject, openQuotientRadiusHomeomorph_quotientMap,
    openQuotientMap]

@[simp]
theorem CuspCentralHomology.centralRadiusHomeomorph_centralCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (p : CuspCollapse.PhasePositiveSpace) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspCollapse.centralCollapseMap C δ hδ p) =
      CuspCollapse.centralCollapseMap C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_centralProject C r δ hδr hC hδ (CuspCollapse.centralPolarMap p)

@[simp]
theorem CuspCentralHomology.centralRadiusHomeomorph_honeycombCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (p : CuspHoneycomb.PhasePlane) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspHoneycomb.honeycombCollapseMap C δ hδ p) =
      CuspHoneycomb.honeycombCollapseMap C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_centralCollapseMap C r δ hδr hC hδ
    (CuspHoneycomb.phaseCoordinatesHomeomorph (C 0) p)

@[simp]
theorem CuspCentralHomology.centralRadiusHomeomorph_sourceCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (q : CuspSpecialization.SourceModel (C 0)) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspSpecialization.sourceCollapse C δ hδ q) =
      CuspSpecialization.sourceCollapse C r (hδ.trans_le hδr) q := by
  induction q using Quotient.inductionOn with
  | h p => exact centralRadiusHomeomorph_honeycombCollapseMap C r δ hδr hC hδ p

@[simp]
theorem CuspCentralHomology.centralRadiusHomeomorph_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ)
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    centralRadiusHomeomorph C r δ hδr hC hδ (CuspSpecialization.productCollapse C δ hδ p) =
      CuspSpecialization.productCollapse C r (hδ.trans_le hδr) p :=
  centralRadiusHomeomorph_sourceCollapse C r δ hδr hC hδ
    ((CuspSpecialization.sourceProductHomeomorph (C 0)).symm p)

theorem CuspCentralHomology.centralRadiusHomeomorph_comp_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ : 0 < δ) :
    (centralRadiusHomeomorph C r δ hδr hC hδ :
            C(CuspRetraction.QuotientCentralFibre C δ,
              CuspRetraction.QuotientCentralFibre C r)).comp
        (CuspSpecialization.productCollapse C δ hδ) =
      CuspSpecialization.productCollapse C r (hδ.trans_le hδr) := by
  apply ContinuousMap.ext
  intro p
  exact centralRadiusHomeomorph_productCollapse C r δ hδr hC hδ p

def CuspControlledRetraction.puncturedPositiveTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : PuncturedPositiveTube η) : PuncturedPositiveTube η :=
  ⟨CuspPositive.closedPositiveTranslate C₀ η v q.1,
    by
    change
      ToricSpace.time
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v
            (q.1.1 : ToricSpace.Space)) ≠
        0
    rw [ToricSpace.time_twistedTranslate]
    exact q.2⟩

def CuspControlledRetraction.puncturedFrozenTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨CuspRetraction.closedTranslate (fun _ => C₀) η v x.1,
    by
    change
      ToricSpace.time (ToricSpace.twistedTranslate (fun _ => C₀) v (x.1 : ToricSpace.Space)) ≠ 0
    rw [ToricSpace.time_twistedTranslate]
    exact x.2⟩

theorem CuspControlledRetraction.puncturedFrozenTranslate_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (v : Fin 2 → ℤ) (u : ToricSpace.CompactTorus) (q : PuncturedPositiveTube η) :
    puncturedFrozenTranslate C₀ η v (puncturedPolarMap η (u, q)) =
      puncturedPolarMap η
        (CuspPositive.phaseTransform C₀ v u, puncturedPositiveTranslate C₀ η v q) :=
  Subtype.ext
    (Subtype.ext (CuspPositive.twistedTranslate_constant_polar C₀ v u (q.1.1 : ToricSpace.Space)))

theorem CuspControlledRetraction.prescribedPositiveCollapse_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    (q : PuncturedPositiveTube η) :
    prescribedPositiveCollapse C₀ η (puncturedPositiveTranslate C₀ η v q) =
      CuspCollapse.positiveCentralTranslate C₀ v (prescribedPositiveCollapse C₀ η q) := by
  change
    CuspHoneycomb.honeycombHomeomorph C₀
        (normalizedPosition C₀
          ((CuspPositive.closedPositiveTranslate C₀ η v q.1).1 : ToricSpace.Space)) =
      CuspCollapse.positiveCentralTranslate C₀ v
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : ToricSpace.Space)))
  rw [normalizedPosition_closedPositive_twistedTranslate C₀ hε1 hR hηε v q.2,
    CuspHoneycomb.honeycombHomeomorph_equivariant]

theorem CuspControlledRetraction.prescribedCollapse_frozen_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    (x : PuncturedClosedTube η) :
    (prescribedCollapse C₀ η (puncturedFrozenTranslate C₀ η v x) : ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C₀) v
        (prescribedCollapse C₀ η x : ToricSpace.Space) := by
  obtain ⟨⟨u, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  rw [puncturedFrozenTranslate_polar, prescribedCollapse_puncturedPolarMap,
    prescribedCollapse_puncturedPolarMap]
  change
    ToricSpace.compactTorusAction (CuspPositive.phaseTransform C₀ v u)
        ((prescribedPositiveCollapse C₀ η (puncturedPositiveTranslate C₀ η v q)).1 :
          ToricSpace.Space) =
      ToricSpace.twistedTranslate (fun _ => C₀) v
        (ToricSpace.compactTorusAction u
          ((prescribedPositiveCollapse C₀ η q).1 : ToricSpace.Space))
  rw [prescribedPositiveCollapse_equivariant C₀ hε1 hR hηε]
  exact
    (CuspPositive.twistedTranslate_constant_polar C₀ v u
        ((prescribedPositiveCollapse C₀ η q).1 : ToricSpace.Space)).symm

def CuspSpecialization.puncturedTwistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (x : CuspControlledRetraction.PuncturedClosedTube η) :
    CuspControlledRetraction.PuncturedClosedTube η :=
  ⟨CuspRetraction.closedTranslate C η v x.1,
    by
    change ToricSpace.time (ToricSpace.twistedTranslate C v (x.1 : ToricSpace.Space)) ≠ 0
    rw [ToricSpace.time_twistedTranslate]
    exact x.2⟩

theorem CuspSpecialization.puncturedStraightening_twistedTranslate
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hηε : η < ε) (v : Fin 2 → ℤ) (x : CuspControlledRetraction.PuncturedClosedTube η) :
    CuspControlledRetraction.puncturedStraightening C η (puncturedTwistedTranslate C η v x) =
      CuspControlledRetraction.puncturedFrozenTranslate (C 0) η v
        (CuspControlledRetraction.puncturedStraightening C η x) := by
  apply Subtype.ext
  apply Subtype.ext
  exact CuspRetraction.changeTwist_frozen_equivariant C hε1 hRC v (x.1.2.trans_lt hηε)

theorem CuspSpecialization.twistedTranslate_frozen_central (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : CuspRetraction.CentralFibre) :
    ToricSpace.twistedTranslate (CuspRetraction.frozen C) v (x : ToricSpace.Space) =
      ToricSpace.twistedTranslate C v (x : ToricSpace.Space) := by
  rw [CuspRetraction.twistedTranslate_eq_expFibreAction,
    CuspRetraction.twistedTranslate_eq_expFibreAction, x.2]
  rfl

@[simp]
theorem CuspSpecialization.levelToPunctured_levelTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (t : ℂ) (ht : t ≠ 0) (v : Fin 2 → ℤ) (x : CuspControlledRetraction.ToricLevel η t) :
    CuspControlledRetraction.levelToPunctured η t ht
        (CuspControlledRetraction.levelTranslate C η t v x) =
      puncturedTwistedTranslate C η v (CuspControlledRetraction.levelToPunctured η t ht x) :=
  rfl

theorem CuspSpecialization.straightenedPrescribedCollapse_equivariant
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    (x : CuspControlledRetraction.PuncturedClosedTube η) :
    (CuspControlledRetraction.straightenedPrescribedCollapse C η
          (puncturedTwistedTranslate C η v x) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate C v
        (CuspControlledRetraction.straightenedPrescribedCollapse C η x : ToricSpace.Space) := by
  change
    (CuspControlledRetraction.prescribedCollapse (C 0) η
          (CuspControlledRetraction.puncturedStraightening C η
            (puncturedTwistedTranslate C η v x)) :
        ToricSpace.Space) =
      ToricSpace.twistedTranslate C v
        (CuspControlledRetraction.prescribedCollapse (C 0) η
            (CuspControlledRetraction.puncturedStraightening C η x) :
          ToricSpace.Space)
  rw [puncturedStraightening_twistedTranslate C hε1 hRC hηε,
    CuspControlledRetraction.prescribedCollapse_frozen_equivariant (C 0) hε1
      (CuspPositive.smallDrift_positiveTwist (C 0) hRD) hηε]
  exact
    twistedTranslate_frozen_central C v
      (CuspControlledRetraction.prescribedCollapse (C 0) η
        (CuspControlledRetraction.puncturedStraightening C η x))

theorem CuspSpecialization.prescribedFibreUpstairs_invariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (t : ℂ) (ht : t ≠ 0) (v : Fin 2 → ℤ) (x : CuspControlledRetraction.ToricLevel η t) :
    CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht
        (CuspControlledRetraction.levelTranslate C η t v x) =
      CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht x := by
  unfold CuspControlledRetraction.prescribedFibreUpstairs
  rw [levelToPunctured_levelTranslate]
  apply (CuspCollapse.centralProject_eq_iff C r hr _ _).mpr
  exact
    ⟨v,
      (straightenedPrescribedCollapse_equivariant C hε1 hRC hRD hηε v
          (CuspControlledRetraction.levelToPunctured η t ht x)).symm⟩

theorem CuspSpecialization.prescribedFibreUpstairs_compatible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0) :
    ∀ x y : CuspControlledRetraction.ToricLevel η t,
      CuspControlledRetraction.levelProjection C hηr t x =
          CuspControlledRetraction.levelProjection C hηr t y →
        CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht x =
          CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht y :=
  CuspControlledRetraction.levelProjection_fibre_compatible_of_invariant C hηr t
    (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht)
    (prescribedFibreUpstairs_invariant C hε1 hRC hRD hηε r hr t ht)

theorem CuspSpecialization.prescribedFibreCollapse_levelProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (x : CuspControlledRetraction.ToricLevel η t) :
    CuspControlledRetraction.prescribedFibreCollapse C r hr hηr t ht
        (CuspControlledRetraction.levelProjection C hηr t x) =
      CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht x :=
  CuspControlledRetraction.levelDescend_levelProjection C hηr t
    (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht)
    (prescribedFibreUpstairs_compatible C hε1 hRC hRD hηε r hr hηr t ht) x

theorem CuspSpecialization.prescribedActualFibreCollapse_fibreProjection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1) (hRC : ToricSpace.SmallDrift C ε)
    (hRD : ToricSpace.SmallDrift (CuspRetraction.frozen C) ε) (hηε : η < ε) (r : ℝ) (hr : 0 < r)
    (hηr : η < r) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) (x : ToricFibre t) :
    CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη
        (fibreProjection C r t (htη.trans_lt hηr) x) =
      CuspCollapse.centralProject C r hr
        (CuspControlledRetraction.straightenedPrescribedCollapse C η
          (toricFibrePunctured η t ht htη x)) := by
  rw [fibreProjection_eq_levelProjection C r t (htη.trans_lt hηr) η hηr htη x]
  change
    CuspControlledRetraction.prescribedFibreCollapse C r hr hηr t ht
        ((CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη).symm
          (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη
            (CuspControlledRetraction.levelProjection C hηr t
              (toricFibreLevelHomeomorph η t htη x)))) =
      _
  rw [Homeomorph.symm_apply_apply]
  exact
    prescribedFibreCollapse_levelProjection C hε1 hRC hRD hηε r hr hηr t ht
      (toricFibreLevelHomeomorph η t htη x)

theorem CuspCentralHomology.prescribedActualFibreCollapse_radius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η)
    (q : CuspControlledRetraction.ActualQuotientFibre C δ t) :
    CuspControlledRetraction.prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη
        (fibreRadiusHomeomorph C r δ t hδr hC (htη.trans_lt hηδ) q) =
      centralRadiusHomeomorph C r δ hδr hC hδ
        (CuspControlledRetraction.prescribedActualFibreCollapse C δ hδ hηδ t ht htη q) := by
  obtain ⟨x, rfl⟩ := CuspSpecialization.fibreProjection_surjective C δ t (htη.trans_lt hηδ) q
  rw [fibreRadiusHomeomorph_fibreProjection,
    CuspSpecialization.prescribedActualFibreCollapse_fibreProjection C hδ1 hRC hRF hηδ r hr
      (hηδ.trans_le hδr) t ht htη,
    CuspSpecialization.prescribedActualFibreCollapse_fibreProjection C hδ1 hRC hRF hηδ δ hδ hηδ t
      ht htη,
    centralRadiusHomeomorph_centralProject]

theorem CuspCentralHomology.levelToPunctured_continuous (η : ℝ) (t : ℂ) (ht : t ≠ 0) :
    Continuous (CuspControlledRetraction.levelToPunctured η t ht) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem CuspCentralHomology.prescribedFibreUpstairs_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hCδ : ∀ i j, ContinuousOn (fun z => C z i j) (Metric.ball 0 δ))
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) :
    Continuous (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht) := by
  change
    Continuous
      (CuspCollapse.centralProject C r hr ∘
        (CuspControlledRetraction.straightenedPrescribedCollapse C η ∘
          CuspControlledRetraction.levelToPunctured η t ht))
  have hc : Continuous (CuspControlledRetraction.straightenedPrescribedCollapse C η) :=
    CuspControlledRetraction.straightenedPrescribedCollapse_continuous C hδ hδ1 hCδ hRC hRF hηδ
  have hp : Continuous (CuspControlledRetraction.levelToPunctured η t ht) :=
    levelToPunctured_continuous η t ht
  have hi :
    Continuous
      (CuspControlledRetraction.straightenedPrescribedCollapse C η ∘
        CuspControlledRetraction.levelToPunctured η t ht) :=
    Continuous.comp (f := CuspControlledRetraction.levelToPunctured η t ht) (g :=
      CuspControlledRetraction.straightenedPrescribedCollapse C η) hc hp
  exact
    Continuous.comp (f :=
      CuspControlledRetraction.straightenedPrescribedCollapse C η ∘
        CuspControlledRetraction.levelToPunctured η t ht)
      (g := CuspCollapse.centralProject C r hr) (CuspCollapse.centralProject_continuous C r hr) hi

theorem CuspCentralHomology.prescribedFibreCollapse_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) :
    Continuous
      (CuspControlledRetraction.prescribedFibreCollapse C r hr (hηδ.trans_le hδr) t ht) := by
  have hCδ (i j) : ContinuousOn (fun z => C z i j) (Metric.ball 0 δ) :=
    ((hC i j).mono (Metric.ball_subset_ball hδr)).continuousOn
  have hf : Continuous (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht) :=
    prescribedFibreUpstairs_continuous_of_smallRadius C r hr hδ hδ1 hCδ hRC hRF hηδ t ht
  exact
    CuspControlledRetraction.levelDescend_continuous C (hηδ.trans_le hδr) t
      (CuspControlledRetraction.prescribedFibreUpstairs C r hr η t ht) hC hf
      (CuspSpecialization.prescribedFibreUpstairs_compatible C hδ1 hRC hRF hηδ r hr
        (hηδ.trans_le hδr) t ht)

theorem CuspCentralHomology.prescribedActualFibreCollapse_continuous_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) :
    Continuous
      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht
        htη) := by
  change
    Continuous
      (CuspControlledRetraction.prescribedFibreCollapse C r hr (hηδ.trans_le hδr) t ht ∘
        (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη).symm)
  exact
    (prescribedFibreCollapse_continuous_of_smallRadius C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t
          ht).comp
      (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t htη).symm.continuous

def CuspCentralHomology.smallRadiusActualFibreCollapseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (η : ℝ) (hηδ : η < δ) (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η) :
    C(CuspControlledRetraction.ActualQuotientFibre C r t, CuspRetraction.QuotientCentralFibre C r)
    where
  toFun :=
    CuspControlledRetraction.prescribedActualFibreCollapse C r hr (hηδ.trans_le hδr) t ht htη
  continuous_toFun :=
    prescribedActualFibreCollapse_continuous_of_smallRadius C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t
      ht htη

def PeriodTorusHigherHomology.torusMatrixLinearMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ProductTorus n →ₗ[ℤ] ProductTorus m
    where
  toFun x i := ∑ j, A i j • x j
  map_add' x
    y := by
    ext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r
    x := by
    ext i
    change (∑ j, A i j • (r • x j)) = r • ∑ j, A i j • x j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact SMulCommClass.smul_comm (A i j) r (x j)

theorem PeriodTorusHigherHomology.torusMatrixLinearMap_continuous {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) : Continuous (torusMatrixLinearMap A) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ProductTorus n => ∑ j, A i j • x j)
  exact continuous_finsetSum Finset.univ (fun j _ => (continuous_apply j).zsmul (A i j))

def PeriodTorusHigherHomology.torusMatrixMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    C(ProductTorus n, ProductTorus m) :=
  ⟨torusMatrixLinearMap A, torusMatrixLinearMap_continuous A⟩

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x : ProductTorus n) (i : Fin m) : torusMatrixMap A x i = ∑ j, A i j • x j :=
  rfl

theorem PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℝ) :
    torusMatrixMap A (coordinateProjection n x) =
      coordinateProjection m (A.map (Int.castRingHom ℝ) *ᵥ x) := by
  ext i
  change
    (∑ j, A i j • (x j : AddCircle (1 : ℝ))) = ((∑ j, (A i j : ℝ) * x j : ℝ) : AddCircle (1 : ℝ))
  have h :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (fun j : Fin n => A i j • x j)
      Finset.univ
  calc
    _ = ((∑ j, A i j • x j : ℝ) : AddCircle (1 : ℝ)) := h.symm
    _ = _ := congrArg (fun y : ℝ => (y : AddCircle (1 : ℝ))) (by simp only [zsmul_eq_mul])

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_one (n : ℕ) :
    torusMatrixMap (1 : Matrix (Fin n) (Fin n) ℤ) = ContinuousMap.id (ProductTorus n) := by
  apply ContinuousMap.ext
  intro x
  ext i
  simp [torusMatrixMap_apply, Matrix.one_apply]

theorem PeriodTorusHigherHomology.torusMatrixMap_mul {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin r) ℤ) :
    torusMatrixMap (A * B) = (torusMatrixMap A).comp (torusMatrixMap B) := by
  apply ContinuousMap.ext
  intro x
  ext i
  change (∑ j, (A * B) i j • x j) = ∑ k, A i k • ∑ j, B k j • x j
  simp only [Matrix.mul_apply, Finset.sum_smul, SemigroupAction.mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

def CuspSpecialization.sourceProductCoordinateHomeomorph :
    (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
      PeriodTorusHigherHomology.ProductTorus 4 :=
  ((Homeomorph.prodComm ToricSpace.CompactFibreTorus
            (PeriodTorusHigherHomology.ProductTorus 2)).trans
        ((Homeomorph.refl (PeriodTorusHigherHomology.ProductTorus 2)).prodCongr
          CuspCentralHomology.compactFibreTorusHomeomorph)).trans
    (Fin.appendHomeomorph 2 2)

@[simp]
theorem CuspSpecialization.sourceProductCoordinateHomeomorph_apply
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    sourceProductCoordinateHomeomorph p =
      ![p.2 0, p.2 1, CuspCentralHomology.compactFibreTorusHomeomorph p.1 0,
        CuspCentralHomology.compactFibreTorusHomeomorph p.1 1] := by
  funext i
  fin_cases i <;> rfl

def CuspSpecialization.sourceCoordinateTorusHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    SourceModel C₀ ≃ₜ PeriodTorusHigherHomology.ProductTorus 4 :=
  (sourceProductHomeomorph C₀).trans sourceProductCoordinateHomeomorph

@[simp]
theorem CuspSpecialization.sourceCoordinateTorusHomeomorph_projection
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (p : CuspHoneycomb.PhasePlane) :
    sourceCoordinateTorusHomeomorph C₀ (sourceProjection C₀ p) =
      ![((-p.2 1 : ℝ) : AddCircle (1 : ℝ)), (p.2 0 : AddCircle (1 : ℝ)),
        CuspCentralHomology.compactFibreTorusHomeomorph (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) 0,
        CuspCentralHomology.compactFibreTorusHomeomorph (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹)
          1] := by
  rw [sourceCoordinateTorusHomeomorph, Homeomorph.trans_apply, sourceProductHomeomorph_projection,
    sourceProductCoordinateHomeomorph_apply]
  simp [ToricSpace.realCuspVector]

theorem CuspSpecialization.compactFibreTorusHomeomorph_planarPhase
    (y : (CuspHoneycombTiling.Plane)) :
    CuspCentralHomology.compactFibreTorusHomeomorph (planarPhase y) =
      PeriodTorusHigherHomology.coordinateProjection 2 y :=
  CuspCentralHomology.compactFibreTorusHomeomorph_exp y

theorem CuspSpecialization.sourceTorusMatrix_M₀_apply
    (x : PeriodTorusHigherHomology.ProductTorus 4) :
    PeriodTorusHigherHomology.torusMatrixMap M₀ x = ![x 0, x 1, x 1 + x 2, -x 0 + x 3] := by
  funext i
  fin_cases i <;> simp [PeriodTorusHigherHomology.torusMatrixMap_apply, M₀, Fin.sum_univ_four]

theorem CuspSpecialization.sourceCoordinateTorusHomeomorph_shear (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : SourceModel C₀) :
    sourceCoordinateTorusHomeomorph C₀ (sourceShear C₀ x) =
      PeriodTorusHigherHomology.torusMatrixMap M₀ (sourceCoordinateTorusHomeomorph C₀ x) := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ x
  rw [sourceShear_projection, sourceCoordinateTorusHomeomorph_projection,
    sourceCoordinateTorusHomeomorph_projection, sourceTorusMatrix_M₀_apply]
  have hp :
    (p.1 * planarPhase p.2) * (sourcePhaseCharacter C₀ p.2)⁻¹ =
      (p.1 * (sourcePhaseCharacter C₀ p.2)⁻¹) * planarPhase p.2 := by ac_rfl
  simp only [phasePlaneShear, hp, CuspCentralHomology.compactFibreTorusHomeomorph_mul,
    compactFibreTorusHomeomorph_planarPhase]
  funext i
  fin_cases i <;>
    simp [PeriodTorusHigherHomology.coordinateProjection_apply, QuotientAddGroup.mk_neg, add_comm]

def CuspSpecialization.markedCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(PeriodTorusHigherHomology.ProductTorus 4, CuspRetraction.QuotientCentralFibre C ε) :=
  (sourceCollapse C ε hε).comp
    ((sourceCoordinateTorusHomeomorph (C 0)).symm :
      C(PeriodTorusHigherHomology.ProductTorus 4, SourceModel (C 0)))

theorem CuspSpecialization.markedCollapse_eq_product (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    markedCollapse C ε hε =
      (productCollapse C ε hε).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)) :=
  rfl

theorem CuspSpecialization.markedCollapse_comp_productCoordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    (markedCollapse C ε hε).comp
        (sourceProductCoordinateHomeomorph :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            PeriodTorusHigherHomology.ProductTorus 4)) =
      productCollapse C ε hε := by
  rw [markedCollapse_eq_product]
  apply ContinuousMap.ext
  intro x
  change
    productCollapse C ε hε
        (sourceProductCoordinateHomeomorph.symm (sourceProductCoordinateHomeomorph x)) =
      _
  rw [Homeomorph.symm_apply_apply]

theorem CuspSpecialization.sourceCoordinateTorusHomeomorph_symm_matrix
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : PeriodTorusHigherHomology.ProductTorus 4) :
    (sourceCoordinateTorusHomeomorph (C 0)).symm (PeriodTorusHigherHomology.torusMatrixMap M₀ x) =
      sourceShear (C 0) ((sourceCoordinateTorusHomeomorph (C 0)).symm x) := by
  apply (sourceCoordinateTorusHomeomorph (C 0)).injective
  rw [Homeomorph.apply_symm_apply, sourceCoordinateTorusHomeomorph_shear,
    Homeomorph.apply_symm_apply]

theorem CuspSpecialization.markedCollapse_comp_matrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (markedCollapse C ε hε).comp (PeriodTorusHigherHomology.torusMatrixMap M₀) =
      ((sourceCollapse C ε hε).comp (sourceShear (C 0))).comp
        ((sourceCoordinateTorusHomeomorph (C 0)).symm :
          C(PeriodTorusHigherHomology.ProductTorus 4, SourceModel (C 0))) := by
  apply ContinuousMap.ext
  intro x
  change
    sourceCollapse C ε hε
        ((sourceCoordinateTorusHomeomorph (C 0)).symm
          (PeriodTorusHigherHomology.torusMatrixMap M₀ x)) =
      _
  rw [sourceCoordinateTorusHomeomorph_symm_matrix]
  rfl

def CuspSpecialization.markedCollapseMonodromyHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (markedCollapse C ε hε).Homotopy
      ((markedCollapse C ε hε).comp (PeriodTorusHigherHomology.torusMatrixMap M₀)) := by
  rw [markedCollapse_comp_matrix]
  have h :=
    (sourceRotationHomotopy C ε hε 1).compContinuousMap
      ((sourceCoordinateTorusHomeomorph (C 0)).symm :
        C(PeriodTorusHigherHomology.ProductTorus 4, SourceModel (C 0)))
  simpa only [sourceRotation_one, markedCollapse] using h

theorem CuspSpecialization.markedCollapse_homology_comp_matrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n).comp
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
          n) =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    (PeriodTorusHigherHomology.homotopy_homologyMap (markedCollapseMonodromyHomotopy C ε hε)
        n).symm

theorem CuspSpecialization.markedCollapse_homology_invariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
          a) =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n a :=
  LinearMap.congr_fun (markedCollapse_homology_comp_matrix C ε hε n) a

theorem CuspSpecialization.markedCollapse_homology_range_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            n -
          LinearMap.id) ≤
      LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n) := by
  rintro a ⟨b, rfl⟩
  change
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
            b -
          b) =
      0
  rw [map_sub, markedCollapse_homology_invariant, sub_self]

theorem CuspSpecialization.markedCollapse_homology_product (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) n) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv sourceProductCoordinateHomeomorph n
          a) =
      SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n a := by
  have h :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f n)
      (markedCollapse_comp_productCoordinates C ε hε)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem CuspSpecialization.markedCollapse_homology_surjective_of_product
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hf :
      Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (productCollapse C ε hε) n)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) n) := by
  intro x
  obtain ⟨a, rfl⟩ := hf x
  exact
    ⟨PeriodTorusHigherHomology.homeomorphHomologyEquiv sourceProductCoordinateHomeomorph n a,
      markedCollapse_homology_product C ε hε n a⟩

def CuspSpecialization.radiusMarkedHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (t : ℂ)
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (htδ : ‖t‖ < δ)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C δ t) :
    PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t :=
  sourceProductCoordinateHomeomorph.symm.trans
    (e.trans (CuspCentralHomology.fibreRadiusHomeomorph C r δ t hδr hC htδ))

theorem CuspSpecialization.radiusMarkedHomeomorph_homotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C δ t)
    (he : IsPrescribedProductModel C δ hδ t ht e) (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η) :
    (markedCollapse C r hr).Homotopic
      ((CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ
            t ht htη).comp
        (radiusMarkedHomeomorph C r δ t hδr hC htδ e :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            CuspControlledRetraction.ActualQuotientFibre C r t))) := by
  obtain ⟨hc, hh, _⟩ := he η htη hηδ
  let f :
    C(CuspControlledRetraction.ActualQuotientFibre C δ t,
      CuspRetraction.QuotientCentralFibre C δ) :=
    ⟨CuspControlledRetraction.prescribedActualFibreCollapse C δ hδ hηδ t ht htη, hc⟩
  let g :=
    CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η hηδ t
      ht htη
  let eW : C(CuspRetraction.QuotientCentralFibre C δ, CuspRetraction.QuotientCentralFibre C r) :=
    (CuspCentralHomology.centralRadiusHomeomorph C r δ hδr hC hδ :
      C(CuspRetraction.QuotientCentralFibre C δ, CuspRetraction.QuotientCentralFibre C r))
  let eF := CuspCentralHomology.fibreRadiusHomeomorph C r δ t hδr hC htδ
  let eP :
    (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre C r t :=
    e.trans eF
  have hleft : eW.comp (productCollapse C δ hδ) = productCollapse C r hr :=
    CuspCentralHomology.centralRadiusHomeomorph_comp_productCollapse C r δ hδr hC hδ
  have hright :
    eW.comp
        (f.comp
          (e :
            C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
              CuspControlledRetraction.ActualQuotientFibre C δ t))) =
      g.comp
        (eP :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C r t)) := by
    apply ContinuousMap.ext
    intro x
    exact
      (CuspCentralHomology.prescribedActualFibreCollapse_radius C r δ hr hδ hδr hC hδ1 hRC hRF η
          hηδ t ht htη (e x)).symm
  have hp :
    (productCollapse C r hr).Homotopic
      (g.comp
        (eP :
          C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
            CuspControlledRetraction.ActualQuotientFibre C r t))) := by
    have h := (ContinuousMap.Homotopic.refl eW).comp hh
    change
      (eW.comp (productCollapse C δ hδ)).Homotopic
        (eW.comp
          (f.comp
            (e :
              C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
                CuspControlledRetraction.ActualQuotientFibre C δ t)))) at h
    rwa [hleft, hright] at h
  have h :=
    hp.comp
      (ContinuousMap.Homotopic.refl
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)))
  have hmarked :
    (productCollapse C r hr).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)) =
      markedCollapse C r hr :=
    (markedCollapse_eq_product C r hr).symm
  have hend :
    (g.comp
            (eP :
              C(ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2,
                CuspControlledRetraction.ActualQuotientFibre C r t))).comp
        (sourceProductCoordinateHomeomorph.symm :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)) =
      g.comp
        (radiusMarkedHomeomorph C r δ t hδr hC htδ e :
          C(PeriodTorusHigherHomology.ProductTorus 4,
            CuspControlledRetraction.ActualQuotientFibre C r t)) := by
    apply ContinuousMap.ext
    intro x
    rfl
  rwa [hmarked, hend] at h

theorem CuspSpecialization.radiusMarkedHomeomorph_homology (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ)
    (e :
      (ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C δ t)
    (he : IsPrescribedProductModel C δ hδ t ht e) (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap
        (CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF η
          hηδ t ht htη)
        n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (radiusMarkedHomeomorph C r δ t hδr hC htδ e) n a) =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a := by
  have h :=
    PeriodTorusHigherHomology.homotopic_homologyMap
      (radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF t ht htδ e he η hηδ htη) n
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact (LinearMap.congr_fun h a).symm

theorem CuspSpecialization.exists_original_marked_model_of_smallRadius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (hδ1 : δ < 1)
    (hRC : ToricSpace.SmallDrift C δ) (hRF : ToricSpace.SmallDrift (CuspRetraction.frozen C) δ)
    (t : ℂ) (ht : t ≠ 0) (htδ : ‖t‖ < δ) :
    ∃ E :
      PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
        CuspControlledRetraction.ActualQuotientFibre C r t,
      ∀ (η : ℝ) (hηδ : η < δ) (htη : ‖t‖ ≤ η),
        (markedCollapse C r hr).Homotopic
            ((CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC hRF
                  η hηδ t ht htη).comp
              (E :
                C(PeriodTorusHigherHomology.ProductTorus 4,
                  CuspControlledRetraction.ActualQuotientFibre C r t))) ∧
          ∀ (n : ℕ)
            (a :
              SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4)
                n),
            SingularMayerVietoris.singularHomologyMap
                (CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr hC hδ1 hRC
                  hRF η hηδ t ht htη)
                n (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n a) =
              SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a := by
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr)
  obtain ⟨e, he⟩ := exists_product_model_at_nonzero_level C δ hδ hδ1 hCδ hRC hRF t ht htδ
  refine ⟨radiusMarkedHomeomorph C r δ t hδr hC htδ e, ?_⟩
  intro η hηδ htη
  exact
    ⟨radiusMarkedHomeomorph_homotopic C r δ hr hδ hδr hC hδ1 hRC hRF t ht htδ e he η hηδ htη,
      radiusMarkedHomeomorph_homology C r δ hr hδ hδr hC hδ1 hRC hRF t ht htδ e he η hηδ htη⟩

theorem CuspSpecialization.exists_original_marked_specialization_models
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀),
      η₀ < r ∧
        η₀ < 1 ∧
          ∀ (t : ℂ) (ht : t ≠ 0),
            ‖t‖ ≤ η₀ →
              ∃ E :
                PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
                  CuspControlledRetraction.ActualQuotientFibre C r t,
                ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
                  ∃ hc :
                    Continuous
                      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
                        htη),
                    (markedCollapse C r hr).Homotopic
                        ((⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
                                  htη,
                                hc⟩ :
                              C(CuspControlledRetraction.ActualQuotientFibre C r t,
                                CuspRetraction.QuotientCentralFibre C r)).comp
                          (E :
                            C(PeriodTorusHigherHomology.ProductTorus 4,
                              CuspControlledRetraction.ActualQuotientFibre C r t))) ∧
                      ∀ (n : ℕ)
                        (a :
                          SingularMayerVietoris.SingularHomology
                            (PeriodTorusHigherHomology.ProductTorus 4) n),
                        SingularMayerVietoris.singularHomologyMap
                            (⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t
                                  ht htη,
                                hc⟩ :
                              C(CuspControlledRetraction.ActualQuotientFibre C r t,
                                CuspRetraction.QuotientCentralFibre C r))
                            n (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n a) =
                          SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a :=
  by
  obtain ⟨δ, hδ, hδr, hδ1, hRC, hRF⟩ :=
    CuspRetraction.exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  let η₀ : ℝ := δ / 2
  have hη₀ : 0 < η₀ := half_pos hδ
  have hη₀δ : η₀ < δ := half_lt_self hδ
  refine ⟨η₀, hη₀, hη₀δ.trans hδr, hη₀δ.trans hδ1, ?_⟩
  intro t ht ht₀
  have htδ : ‖t‖ < δ := ht₀.trans_lt hη₀δ
  obtain ⟨E, hE⟩ :=
    exists_original_marked_model_of_smallRadius C r δ hr hδ hδr.le hC hδ1 hRC hRF t ht htδ
  refine ⟨E, ?_⟩
  intro η hη htη hηr
  have hηδ : η < δ := hη.trans_lt hη₀δ
  let f :=
    CuspCentralHomology.smallRadiusActualFibreCollapseMap C r δ hr hδ hδr.le hC hδ1 hRC hRF η hηδ
      t ht htη
  refine ⟨f.continuous, ?_, ?_⟩
  · exact (hE η hηδ htη).1
  · exact (hE η hηδ htη).2

def CuspCoinvariants.oneDifference : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  (M₀ - 1).mulVecLin

def CuspCoinvariants.squareDifference : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ) :=
  (PeriodTorusHigherHomologyExterior.squareM₀ - 1).mulVecLin

def CuspCoinvariants.cubeDifference : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  (PeriodTorusHigherHomologyExterior.cubeM₀ - 1).mulVecLin

@[simp]
theorem CuspCoinvariants.squareDifference_apply (v : Fin 6 → ℤ) :
    squareDifference v = ![0, v 0, 0, 0, v 0, v 0 + v 1 + v 4] := by
  ext i
  fin_cases i <;>
    simp [squareDifference, PeriodTorusHigherHomologyExterior.squareM₀_eq, dotProduct,
      Fin.sum_univ_succ]
  ring

theorem CuspCoinvariants.cubeM₀_eq_M₀ : PeriodTorusHigherHomologyExterior.cubeM₀ = M₀ := by
  rw [PeriodTorusHigherHomologyExterior.cubeM₀_eq]
  rfl

theorem CuspCoinvariants.cubeDifference_eq_oneDifference : cubeDifference = oneDifference := by
  rw [cubeDifference, oneDifference, cubeM₀_eq_M₀]

def CuspCoinvariants.squareProjection : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)
    where
  toFun v := ![v 0, v 2, v 3, v 4 - v 1]
  map_add' v
    w := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c
    v := by
    ext i
    fin_cases i <;> simp
    ring

def CuspCoinvariants.squareSection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ)
    where
  toFun z := ![z 0, 0, z 1, z 2, z 3, 0]
  map_add' v
    w := by
    ext i
    fin_cases i <;> simp
  map_smul' c
    v := by
    ext i
    fin_cases i <;> simp

@[simp]
theorem CuspCoinvariants.squareProjection_section (z : Fin 4 → ℤ) :
    squareProjection (squareSection z) = z := by
  ext i
  fin_cases i <;> simp [squareProjection, squareSection]

theorem CuspCoinvariants.squareProjection_surjective : Function.Surjective squareProjection :=
  fun z => ⟨squareSection z, squareProjection_section z⟩

theorem CuspCoinvariants.squareDifference_range_iff (v : Fin 6 → ℤ) :
    v ∈ LinearMap.range squareDifference ↔ v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = v 1 := by
  change (∃ w, squareDifference w = v) ↔ _
  constructor
  · rintro ⟨w, rfl⟩
    simp
  · rintro ⟨h0, h2, h3, h41⟩
    refine ⟨![v 1, v 5 - v 1, 0, 0, 0, 0], ?_⟩
    rw [squareDifference_apply]
    ext i
    fin_cases i <;> simp [h0, h2, h3, h41]

theorem CuspCoinvariants.squareProjection_eq_zero_iff (v : Fin 6 → ℤ) :
    squareProjection v = 0 ↔ v 0 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = v 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    change v 0 = 0 at h0
    change v 2 = 0 at h1
    change v 3 = 0 at h2
    change v 4 - v 1 = 0 at h3
    exact ⟨h0, h1, h2, sub_eq_zero.mp h3⟩
  · rintro ⟨h0, h2, h3, h41⟩
    ext i
    fin_cases i <;> simp [squareProjection, h0, h2, h3, h41]

theorem CuspCoinvariants.squareProjection_ker_eq_range :
    LinearMap.ker squareProjection = LinearMap.range squareDifference := by
  ext v
  rw [LinearMap.mem_ker, squareProjection_eq_zero_iff, squareDifference_range_iff]

def CuspCoinvariants.squareCoinvariantEquiv :
    ((Fin 6 → ℤ) ⧸ LinearMap.range squareDifference) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ squareProjection_ker_eq_range.symm).trans
    (squareProjection.quotKerEquivOfSurjective squareProjection_surjective)

def CuspCoinvariants.oneProjection : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun v := ![v 0, v 1]
  map_add' v
    w := by
    ext i
    fin_cases i <;> rfl
  map_smul' c
    v := by
    ext i
    fin_cases i <;> rfl

def CuspCoinvariants.oneSection : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ)
    where
  toFun z := ![z 0, z 1, 0, 0]
  map_add' v
    w := by
    ext i
    fin_cases i <;> simp
  map_smul' c
    v := by
    ext i
    fin_cases i <;> simp

@[simp]
theorem CuspCoinvariants.oneProjection_section (z : Fin 2 → ℤ) :
    oneProjection (oneSection z) = z := by
  ext i
  fin_cases i <;> rfl

theorem CuspCoinvariants.oneProjection_surjective : Function.Surjective oneProjection := fun z =>
  ⟨oneSection z, oneProjection_section z⟩

theorem CuspCoinvariants.oneDifference_range_iff (v : Fin 4 → ℤ) :
    v ∈ LinearMap.range oneDifference ↔ v 0 = 0 ∧ v 1 = 0 :=
  M₀_sub_one_range v

theorem CuspCoinvariants.oneProjection_eq_zero_iff (v : Fin 4 → ℤ) :
    oneProjection v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i <;> simp [oneProjection, h0, h1]

theorem CuspCoinvariants.oneProjection_ker_eq_range :
    LinearMap.ker oneProjection = LinearMap.range oneDifference := by
  ext v
  rw [LinearMap.mem_ker, oneProjection_eq_zero_iff, oneDifference_range_iff]

def CuspCoinvariants.oneCoinvariantEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range oneDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ oneProjection_ker_eq_range.symm).trans
    (oneProjection.quotKerEquivOfSurjective oneProjection_surjective)

abbrev CuspCoinvariants.cubeProjection :=
  oneProjection

theorem CuspCoinvariants.cubeProjection_surjective : Function.Surjective cubeProjection :=
  oneProjection_surjective

theorem CuspCoinvariants.cubeProjection_ker_eq_range :
    LinearMap.ker cubeProjection = LinearMap.range cubeDifference := by
  rw [cubeDifference_eq_oneDifference]
  exact oneProjection_ker_eq_range

def CuspCoinvariants.cubeCoinvariantEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range cubeDifference) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (Submodule.quotEquivOfEq _ _ cubeProjection_ker_eq_range.symm).trans
    (cubeProjection.quotKerEquivOfSurjective cubeProjection_surjective)

theorem CuspCoinvariants.map_range_of_intertwines {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) : (LinearMap.range A).map e.toLinearMap = LinearMap.range B := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, (h z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨A (e.symm z), ⟨e.symm z, rfl⟩, ?_⟩
    change e (A (e.symm z)) = B z
    rw [h, LinearEquiv.apply_symm_apply]

def CuspCoinvariants.quotientRangeEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) : (M ⧸ LinearMap.range A) ≃ₗ[ℤ] (N ⧸ LinearMap.range B) := by
  let q :=
    Submodule.Quotient.equiv (LinearMap.range A) (LinearMap.range B) e
      (map_range_of_intertwines e A B h)
  let qa : (M ⧸ LinearMap.range A) ≃+ (N ⧸ LinearMap.range B) := by
    letI := Submodule.Quotient.module (LinearMap.range A)
    letI := Submodule.Quotient.module (LinearMap.range B)
    exact q.toAddEquiv
  exact qa.toIntLinearEquiv

theorem CuspCoinvariants.mem_range_iff_of_intertwines {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (A : M →ₗ[ℤ] M) (B : N →ₗ[ℤ] N)
    (h : ∀ x, e (A x) = B (e x)) (x : M) : x ∈ LinearMap.range A ↔ e x ∈ LinearMap.range B := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e z, (h z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, e.injective ?_⟩
    rw [h, LinearEquiv.apply_symm_apply, hz]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.product_natural {G H : Type} [TopologicalSpace G]
    [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H] [IsTopologicalAddGroup G]
    [IsTopologicalAddGroup H] (f : C(G, H)) (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology G 1)
    (b : SingularMayerVietoris.SingularHomology G n) :
    SingularMayerVietoris.singularHomologyMap f (n + 1) (product G n a b) =
      product H n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f n b) :=
  (LinearMap.congr_fun (addition_homology_natural f hf (n + 1))
        (PeriodTorusHigherHomology.crossProductHomology G G n a b)).trans
    (congrArg (SingularMayerVietoris.singularHomologyMap (additionMap H) (n + 1))
      (PeriodTorusHigherHomology.crossProductHomology_natural f f n a b))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_natural {G H : Type}
    [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
    [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y) (a b c : SingularMayerVietoris.SingularHomology G 1) :
    SingularMayerVietoris.singularHomologyMap f 3 (tripleProduct G a b c) =
      tripleProduct H (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap f 1 b)
        (SingularMayerVietoris.singularHomologyMap f 1 c) := by
  change
    SingularMayerVietoris.singularHomologyMap f 3 (product G 2 a (product G 1 b c)) =
      product H 2 (SingularMayerVietoris.singularHomologyMap f 1 a)
        (product H 1 (SingularMayerVietoris.singularHomologyMap f 1 b)
          (SingularMayerVietoris.singularHomologyMap f 1 c))
  rw [product_natural f hf 2, product_natural f hf 1]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_eq_cross (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c =
      SingularMayerVietoris.singularHomologyMap (rightAdditionMap G) 3
        (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)) := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural (ContinuousMap.id G) (additionMap G) 2
      a (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)
  change
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id G).prodMap (additionMap G)) 3
        (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)) =
      PeriodTorusHigherHomology.crossProductHomology G G 2
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id G) 1 a)
        (SingularMayerVietoris.singularHomologyMap (additionMap G) 2
          (PeriodTorusHigherHomology.crossProductHomology G G 1 b c)) at h
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at h
  calc
    tripleProduct G a b c =
        SingularMayerVietoris.singularHomologyMap (additionMap G) 3
          (PeriodTorusHigherHomology.crossProductHomology G G 2 a
            (SingularMayerVietoris.singularHomologyMap (additionMap G) 2
              (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))) :=
      rfl
    _ =
        SingularMayerVietoris.singularHomologyMap (additionMap G) 3
          (SingularMayerVietoris.singularHomologyMap
            ((ContinuousMap.id G).prodMap (additionMap G)) 3
            (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
              (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))) :=
      (congrArg (SingularMayerVietoris.singularHomologyMap (additionMap G) 3) h.symm)
    _ = _ :=
      (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp
            ((ContinuousMap.id G).prodMap (additionMap G)) (additionMap G) 3)
          (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 a
            (PeriodTorusHigherHomology.crossProductHomology G G 1 b c))).symm

@[simp]
theorem PeriodTorusHigherHomology.flatTorusCircleHomeomorph_add (x y : RealTorus₄) :
    flatTorusCircleHomeomorph (x + y) =
      flatTorusCircleHomeomorph x + flatTorusCircleHomeomorph y :=
  flatTorusCircleMap.map_add x y

theorem PeriodTorusHigherHomology.periodTorusCircle_inducedHomology_periodLoop (p : PeriodDomain)
    (v : Lattice) :
    FirstHurewicz.inducedHomology (periodTorusCircleHomeomorph p : C(_, _))
        (FirstHurewicz.loopHomologyClass (p.periodLoop v)) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, periodTorusCircleHomeomorph_periodLoop]
  rfl

def PeriodTorusHigherHomology.coordinateCircleMap {n : ℕ} (v : Fin n → ℤ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle), ProductTorus n)
    where
  toFun z i := v i • z
  continuous_toFun := continuous_pi fun i => continuous_id.zsmul (v i)

@[simp]
theorem PeriodTorusHigherHomology.coordinateCircleMap_apply {n : ℕ} (v : Fin n → ℤ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) (i : Fin n) :
    coordinateCircleMap v z i = v i • z :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.coordinateCircleMap_zero {n : ℕ} (v : Fin n → ℤ) :
    coordinateCircleMap v 0 = 0 := by
  ext i
  exact smul_zero (v i)

theorem PeriodTorusHigherHomology.coordinateCircleMap_add {n : ℕ} (v : Fin n → ℤ)
    (x y : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    coordinateCircleMap v (x + y) = coordinateCircleMap v x + coordinateCircleMap v y := by
  ext i
  exact smul_add (v i) x y

theorem PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop_apply {n : ℕ} (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinateCircleMap v (CirclePaths.positiveLoop t) = coordinatePeriodLoop n v t := by
  ext i
  rw [coordinateCircleMap_apply, CirclePaths.positiveLoop_apply, coordinatePeriodLoop_apply]
  change
    ((v i • (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      (((t : ℝ) * (v i : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

theorem PeriodTorusHigherHomology.coordinateCircleMap_positiveLoop {n : ℕ} (v : Fin n → ℤ) :
    CirclePaths.positiveLoop.map (coordinateCircleMap v).continuous =
      (coordinatePeriodLoop n v).cast (coordinateCircleMap_zero v) (coordinateCircleMap_zero v) :=
  by
  apply Path.ext
  funext t
  exact coordinateCircleMap_positiveLoop_apply v t

theorem PeriodTorusHigherHomology.coordinateCircleMap_positiveHomology {n : ℕ} (v : Fin n → ℤ) :
    FirstHurewicz.inducedHomology (coordinateCircleMap v)
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n v) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, coordinateCircleMap_positiveLoop]
  rfl

theorem PeriodTorusHigherHomology.coordinatePeriodLoop_eq_projection (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinatePeriodLoop n v t = coordinateProjection n ((t : ℝ) • (fun i => (v i : ℝ))) := by
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) (t : unitInterval) :
    torusMatrixMap A (coordinatePeriodLoop n v t) = coordinatePeriodLoop m (A *ᵥ v) t := by
  rw [coordinatePeriodLoop_eq_projection, torusMatrixMap_coordinateProjection,
    coordinatePeriodLoop_eq_projection, Matrix.mulVec_smul]
  congr 2
  ext i
  exact ((Int.castRingHom ℝ).map_mulVec A v i).symm

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    torusMatrixMap A 0 = 0 :=
  (torusMatrixLinearMap A).map_zero

theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodLoop {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusMatrixMap A).continuous =
      (coordinatePeriodLoop m (A *ᵥ v)).cast (torusMatrixMap_zero A) (torusMatrixMap_zero A) := by
  apply Path.ext
  funext t
  exact torusMatrixMap_coordinatePeriodLoop_apply A v t

theorem PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    FirstHurewicz.inducedHomology (torusMatrixMap A)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n v)) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop m (A *ᵥ v)) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, torusMatrixMap_coordinatePeriodLoop]
  rfl

def PeriodTorusHigherHomology.torusHeadCircleMap (n : ℕ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle), ProductTorus (n + 1)) :=
  coordinateCircleMap (Pi.single (0 : Fin (n + 1)) 1)

@[simp]
theorem PeriodTorusHigherHomology.torusHeadCircleMap_apply (n : ℕ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    torusHeadCircleMap n z = Fin.cons z 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]
  · simp [torusHeadCircleMap, coordinateCircleMap_apply]

def PeriodTorusHigherHomology.torusTailMap (n : ℕ) : C(ProductTorus n, ProductTorus (n + 1)) :=
  ((productTorusSuccHomeomorph n).symm : C(_, _)).comp
    (CircleTopology.productSection (ProductTorus n))

@[simp]
theorem PeriodTorusHigherHomology.torusTailMap_apply (n : ℕ) (x : ProductTorus n) :
    torusTailMap n x = Fin.cons 0 x :=
  rfl

theorem PeriodTorusHigherHomology.torusTailMap_add (n : ℕ) (x y : ProductTorus n) :
    torusTailMap n (x + y) = torusTailMap n x + torusTailMap n y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

@[simp]
theorem PeriodTorusHigherHomology.torusTailMap_zero (n : ℕ) : torusTailMap n 0 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusTailMap_apply]

theorem PeriodTorusHigherHomology.torusTailMap_coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusTailMap n).continuous =
      (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)).cast (torusTailMap_zero n)
        (torusTailMap_zero n) := by
  apply Path.ext
  funext t
  apply funext
  intro i
  change
    torusTailMap n (coordinatePeriodLoop n v t) i =
      coordinatePeriodLoop (n + 1) (Fin.cons 0 v) t i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]
  · simp [torusTailMap_apply, coordinatePeriodLoop_apply]

theorem PeriodTorusHigherHomology.torusTailMap_coordinatePeriodHomology (n : ℕ) (v : Fin n → ℤ) :
    SingularMayerVietoris.singularHomologyMap (torusTailMap n) 1
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n v)) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop (n + 1) (Fin.cons 0 v)) := by
  rw [SingularMayerVietoris.singularHomologyMap_one,
    FirstHurewicz.inducedHomology_loopHomologyClass, torusTailMap_coordinatePeriodLoop]
  rfl

theorem PeriodTorusHigherHomology.productTorusSucc_inverse_eq_add (n : ℕ) :
    ((productTorusSuccHomeomorph n).symm :
        C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus n,
          ProductTorus (n + 1))) =
      (PeriodTorusHigherHomologyPontryagin.additionMap (ProductTorus (n + 1))).comp
        ((torusHeadCircleMap n).prodMap (torusTailMap n)) := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  change Fin.cons z x = torusHeadCircleMap n z + torusTailMap n x
  rw [torusHeadCircleMap_apply, torusTailMap_apply]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem PeriodTorusHigherHomology.torusSplit_positiveCircleCross (r n : ℕ)
    (b : SingularMayerVietoris.SingularHomology (ProductTorus r) n) :
    SingularMayerVietoris.singularHomologyMap ((productTorusSuccHomeomorph r).symm : C(_, _))
        (n + 1) (positiveCircleCross (ProductTorus r) n b) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (r + 1)) n
        (SingularMayerVietoris.singularHomologyMap (torusHeadCircleMap r) 1
          (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop))
        (SingularMayerVietoris.singularHomologyMap (torusTailMap r) n b) := by
  rw [PeriodTorusHigherHomologyPontryagin.product_apply]
  have h :=
    crossProductHomology_natural (torusHeadCircleMap r) (torusTailMap r) n
      (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) b
  rw [← h]
  rw [productTorusSucc_inverse_eq_add, singularHomologyMap_comp]
  rfl

theorem PeriodTorusHigherHomology.torusHeadCircleMap_positiveHomology (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (torusHeadCircleMap n) 1
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop (n + 1) (Pi.single 0 1)) :=
  coordinateCircleMap_positiveHomology (Pi.single (0 : Fin (n + 1)) 1)

theorem PeriodTorusHigherHomology.productTorusTopClass_succ_cross (n : ℕ) :
    productTorusTopClass (n + 1) =
      SingularMayerVietoris.singularHomologyMap ((productTorusSuccHomeomorph n).symm : C(_, _))
        (n + 1) (positiveCircleCross (ProductTorus n) n (productTorusTopClass n)) := by
  apply (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).injective
  apply (circleProductHomologyEquiv (ProductTorus n) n).injective
  rw [productTorusTopClass_succ_coordinates]
  change
    (0, productTorusTopClass n) =
      circleProductHomologyEquiv (ProductTorus n) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)
          ((homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1)).symm
            (positiveCircleCross (ProductTorus n) n (productTorusTopClass n))))
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_positiveCircleCross]

theorem PeriodTorusHigherHomology.productTorusTopClass_succ_product (n : ℕ) :
    productTorusTopClass (n + 1) =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus (n + 1)) n
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop (n + 1) (Pi.single 0 1)))
        (SingularMayerVietoris.singularHomologyMap (torusTailMap n) n (productTorusTopClass n)) :=
  by
  rw [productTorusTopClass_succ_cross, torusSplit_positiveCircleCross,
    torusHeadCircleMap_positiveHomology]

theorem PeriodTorusHigherHomology.productTorusTopClass_one :
    productTorusTopClass 1 =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 1 (Pi.single 0 1)) := by
  rw [productTorusTopClass_succ_cross, productTorusTopClass_zero, positiveCircleCross,
    crossProductHomology_pointClass_right]
  have hmap :
    ((productTorusSuccHomeomorph 0).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus 0,
              ProductTorus 1)).comp
        (crossInsertRight (0 : ProductTorus 0)) =
      torusHeadCircleMap 0 := by
    apply ContinuousMap.ext
    intro z
    rw [torusHeadCircleMap_apply]
    rfl
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hmap]
  exact torusHeadCircleMap_positiveHomology 0

theorem PeriodTorusHigherHomology.productTorusTopClass_two :
    productTorusTopClass 2 =
      PeriodTorusHigherHomologyPontryagin.product (ProductTorus 2) 1
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_one,
    torusTailMap_coordinatePeriodHomology]
  congr 3
  decide

theorem PeriodTorusHigherHomology.productTorusTopClass_three :
    productTorusTopClass 3 =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 3)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 1 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 2 1))) := by
  rw [productTorusTopClass_succ_product, productTorusTopClass_two,
    PeriodTorusHigherHomologyPontryagin.product_natural (torusTailMap 2) (torusTailMap_add 2),
    torusTailMap_coordinatePeriodHomology, torusTailMap_coordinatePeriodHomology]
  have h₁ : Fin.cons 0 (Pi.single 0 1 : Fin 2 → ℤ) = (Pi.single 1 1 : Fin 3 → ℤ) := by decide
  have h₂ : Fin.cons 0 (Pi.single 1 1 : Fin 2 → ℤ) = (Pi.single 2 1 : Fin 3 → ℤ) := by decide
  rw [h₁, h₂]
  rfl

theorem PeriodTorusHigherHomology.formalMap_comp {V W Z : Type*} (f : W → Z) (g : V → W) (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap f n (SingularMayerVietoris.formalMap g n c) =
      SingularMayerVietoris.formalMap (f ∘ g) n c := by
  have h :
    (SingularMayerVietoris.formalMap f n).comp (SingularMayerVietoris.formalMap g n) =
      SingularMayerVietoris.formalMap (f ∘ g) n := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.formalMap_prod_swap {V W V' W' : Type*} (f : V → V')
    (g : W → W') (n : ℕ) (c : SingularMayerVietoris.FormalChains (W × V) n) :
    SingularMayerVietoris.formalMap (Prod.map f g) n
        (SingularMayerVietoris.formalMap Prod.swap n c) =
      SingularMayerVietoris.formalMap Prod.swap n
        (SingularMayerVietoris.formalMap (Prod.map g f) n c) := by
  rw [formalMap_comp, formalMap_comp]
  rfl

theorem PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_one {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap Prod.swap 2 (formalPointCrossProduct 1 c d) =
      formalEdgeCrossProduct 0 d c := by
  have h :
    (formalPointCrossProduct (V := V) (W := W) 1).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 2) =
      (formalEdgeCrossProduct 0).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 2
          (formalPointCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 2
            (SingularMayerVietoris.formalMap (fun z => (v 0, z)) 2
              (SingularMayerVietoris.formalSimplex w)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 2)
          (formalPointCrossProduct_simplex_left 1 v (SingularMayerVietoris.formalSimplex w))
      _ =
          SingularMayerVietoris.formalMap (fun z => (z, v 0)) 2
            (SingularMayerVietoris.formalSimplex w) := by
        rw [formalMap_comp]
        rfl
      _ = _ :=
        (formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w) v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

theorem PeriodTorusHigherHomology.formalMap_swap_edgeCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalMap Prod.swap 2 (formalEdgeCrossProduct 0 c d) =
      formalPointCrossProduct 1 d c := by
  have h :
    (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 2) =
      (formalPointCrossProduct 1).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 2
          (formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        formalPointCrossProduct 1 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 2
            (SingularMayerVietoris.formalMap (fun z => (z, w 0)) 2
              (SingularMayerVietoris.formalSimplex v)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 2)
          (formalEdgeCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex v) w)
      _ =
          SingularMayerVietoris.formalMap (fun z => (w 0, z)) 2
            (SingularMayerVietoris.formalSimplex v) := by
        rw [formalMap_comp]
        rfl
      _ = _ :=
        (formalPointCrossProduct_simplex_left 1 w (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

def PeriodTorusHigherHomology.formalEdgeSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 3 :=
  formalEdgeCrossProduct 1 +
    (formalEdgeCrossProduct 1).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 3)

@[simp]
theorem PeriodTorusHigherHomology.formalEdgeSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    formalEdgeSwapDefect c d =
      formalEdgeCrossProduct 1 c d +
        SingularMayerVietoris.formalMap Prod.swap 3 (formalEdgeCrossProduct 1 d c) :=
  rfl

theorem PeriodTorusHigherHomology.formalBoundary_edgeSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 2 (formalEdgeSwapDefect c d) = 0 := by
  rw [formalEdgeSwapDefect_apply, map_add, formalBoundary_edgeCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, formalBoundary_edgeCrossProduct, map_sub,
    formalMap_swap_pointCrossProduct_one, formalMap_swap_edgeCrossProduct_zero]
  abel

theorem PeriodTorusHigherHomology.formalMap_edgeSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 3 (formalEdgeSwapDefect c d) =
      formalEdgeSwapDefect (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [formalEdgeSwapDefect_apply, map_add, formalMap_edgeCrossProduct, formalMap_prod_swap,
    formalMap_edgeCrossProduct, formalEdgeSwapDefect_apply]

def PeriodTorusHigherHomology.formalEdgeSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 3
      (formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w))

@[simp]
theorem PeriodTorusHigherHomology.formalEdgeSwapHomotopy_simplex {V W : Type*} (v : Fin 2 → V)
    (w : Fin 2 → W) :
    formalEdgeSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 3
        (formalEdgeSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)) :=
  formalBilinearLift_simplex _ _ _

theorem PeriodTorusHigherHomology.formalEdgeSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (formalEdgeSwapHomotopy c d) =
      formalEdgeSwapDefect c d := by
  have h :
    (formalEdgeSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 3) =
      formalEdgeSwapDefect := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, formalEdgeSwapHomotopy_simplex,
      SingularMayerVietoris.formalBoundary_cone, formalBoundary_edgeSwapDefect, map_zero,
      sub_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

theorem PeriodTorusHigherHomology.formalMap_edgeSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 2)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (formalEdgeSwapHomotopy c d) =
      formalEdgeSwapHomotopy (SingularMayerVietoris.formalMap f 2 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have h :
    (formalEdgeSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 4) =
      ((formalEdgeSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 2) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, formalEdgeSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone, formalMap_edgeSwapDefect,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.prodSwap_productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    (ContinuousMap.prodSwap :
            C(FirstHurewicz.Simplex p × FirstHurewicz.Simplex q,
              FirstHurewicz.Simplex q × FirstHurewicz.Simplex p)).comp
        (productAffineSimplex v) =
      productAffineSimplex (Prod.swap ∘ v) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.inducedChain_swap_productAffineChainMap (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
        (n + 1)) :
    FirstHurewicz.inducedChain
        (ContinuousMap.prodSwap :
          C(FirstHurewicz.Simplex p × FirstHurewicz.Simplex q,
            FirstHurewicz.Simplex q × FirstHurewicz.Simplex p))
        n (productAffineChainMap p q n c) =
      productAffineChainMap q p n (SingularMayerVietoris.formalMap Prod.swap (n + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain
            (ContinuousMap.prodSwap :
              C(FirstHurewicz.Simplex p × FirstHurewicz.Simplex q,
                FirstHurewicz.Simplex q × FirstHurewicz.Simplex p))
            n).comp
        (productAffineChainMap p q n) =
      (productAffineChainMap q p n).comp (SingularMayerVietoris.formalMap Prod.swap (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      prodSwap_productAffineSimplex]
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.inducedChain_prodMap_swap {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (c : FirstHurewicz.Chains (Y × X) n) :
    FirstHurewicz.inducedChain (f.prodMap g) n
        (FirstHurewicz.inducedChain ContinuousMap.prodSwap n c) =
      FirstHurewicz.inducedChain ContinuousMap.prodSwap n
        (FirstHurewicz.inducedChain (g.prodMap f) n c) := by
  calc
    _ = FirstHurewicz.inducedChain ((f.prodMap g).comp ContinuousMap.prodSwap) n c :=
      (LinearMap.congr_fun (FirstHurewicz.inducedChain_comp _ _ n) c).symm
    _ = FirstHurewicz.inducedChain (ContinuousMap.prodSwap.comp (g.prodMap f)) n c := rfl
    _ = _ := LinearMap.congr_fun (FirstHurewicz.inducedChain_comp _ _ n) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 3 :=
  chainBilinearLift X Y 1 1 fun σ τ =>
    FirstHurewicz.inducedChain (σ.prodMap τ) 3
      (productAffineChainMap 1 1 3
        (formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : FirstHurewicz.SingularSimplex X 1)
    (τ : FirstHurewicz.SingularSimplex Y 1) :
    crossProductSwapHomotopy X Y (FirstHurewicz.simplexChain X 1 σ)
        (FirstHurewicz.simplexChain Y 1 τ) =
      FirstHurewicz.inducedChain (σ.prodMap τ) 3
        (productAffineChainMap 1 1 3
          (formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  chainBilinearLift_simplex X Y 1 1 _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1) :
    FirstHurewicz.inducedChain (f.prodMap g) 3 (crossProductSwapHomotopy X Y a b) =
      crossProductSwapHomotopy X' Y' (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g 1 b) := by
  have h :
    integerBilinearPostcompose (crossProductSwapHomotopy X Y)
        (FirstHurewicz.inducedChain (f.prodMap g) 3) =
      integerBilinearPrecompose (crossProductSwapHomotopy X' Y') (FirstHurewicz.inducedChain f 1)
        (FirstHurewicz.inducedChain g 1) := by
    apply chainBilinearMap_ext X Y 1 1
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      productAffineChainMap p q 3 (formalEdgeSwapHomotopy a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q))
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1) =
      integerBilinearPostcompose formalEdgeSwapHomotopy (productAffineChainMap p q 3) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductSwapHomotopy_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q 3
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            4
            (formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [formalMap_edgeSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d 3
            2).hom
        (crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)) =
      crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b) +
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 2
          (crossProductEdge (FirstHurewicz.Simplex q) (FirstHurewicz.Simplex p) 1
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 1 a)) := by
  rw [crossProductSwapHomotopy_affineChainMap, productAffineChainMap_boundary,
    formalEdgeSwapHomotopy_boundary, formalEdgeSwapDefect_apply, map_add,
    crossProductEdge_affineChainMap, crossProductEdge_affineChainMap,
    inducedChain_swap_productAffineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) :
    ((FirstHurewicz.singularComplex (X × Y)).d 3 2).hom (crossProductSwapHomotopy X Y a b) =
      crossProductEdge X Y 1 a b +
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 2 (crossProductEdge Y X 1 b a) := by
  have h :
    integerBilinearPostcompose (crossProductSwapHomotopy X Y)
        ((FirstHurewicz.singularComplex (X × Y)).d 3 2).hom =
      crossProductEdge X Y 1 +
        integerBilinearPostcompose (integerBilinearFlip (crossProductEdge Y X 1))
          (FirstHurewicz.inducedChain ContinuousMap.prodSwap 2) := by
    apply chainBilinearMap_ext X Y 1 1
    intro σ τ
    have hstd :=
      crossProductSwapHomotopy_boundary_affine 1 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) 2) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearFlip_apply, LinearMap.add_apply,
      map_add, FirstHurewicz.inducedChain_boundary, crossProductSwapHomotopy_natural,
      inducedChain_prodMap_swap, crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCycleClasses_add_swap_eq_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1) :
    crossProductCycleClasses X Y 1 a b +
        SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
          (crossProductCycleClasses Y X 1 b a) =
      0 := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y)) 2
          (crossProductCycles X Y 1 a b) +
        (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap ContinuousMap.prodSwap)
              2).hom
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (Y × X))
            2 (crossProductCycles Y X 1 b a)) =
      0
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, ← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (FirstHurewicz.singularComplex (X × Y)) 2 _).mpr
  refine ⟨crossProductSwapHomotopy X Y a.1 b.1, ?_⟩
  rw [Submodule.coe_add, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact crossProductSwapHomotopy_boundary a.1 b.1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_add_swap_eq_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    crossProductHomology X Y 1 a b +
        SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
          (crossProductHomology Y X 1 b a) =
      0 := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Y) 1
      b
  rw [crossProductHomology_cycleClass, crossProductHomology_cycleClass]
  exact crossProductCycleClasses_add_swap_eq_zero a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_swap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 2
        (crossProductHomology X Y 1 a b) =
      -crossProductHomology Y X 1 b a := by
  have h := crossProductHomology_add_swap_eq_zero b a
  exact eq_neg_of_add_eq_zero_right h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute {X Z : Type}
    [TopologicalSpace X] [TopologicalSpace Z] (f : C(X × X, Z))
    (hf : f.comp ContinuousMap.prodSwap = f) (a b : SingularMayerVietoris.SingularHomology X 1) :
    SingularMayerVietoris.singularHomologyMap f 2 (crossProductHomology X X 1 a b) =
      -SingularMayerVietoris.singularHomologyMap f 2 (crossProductHomology X X 1 b a) := by
  have h :=
    congrArg (SingularMayerVietoris.singularHomologyMap f 2) (crossProductHomology_swap a b)
  rw [map_neg] at h
  have hc :=
    LinearMap.congr_fun (singularHomologyMap_comp (ContinuousMap.prodSwap : C(X × X, X × X)) f 2)
      (crossProductHomology X X 1 a b)
  rw [hf] at hc
  exact hc.trans h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.product11_skew (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b : SingularMayerVietoris.SingularHomology G 1) : product11 G a b = -product11 G b a :=
  PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute (additionMap G)
    (by ext p; exact add_comm p.2 p.1) a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.product11_self (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a : SingularMayerVietoris.SingularHomology G 1) : product11 G a a = 0 :=
  skewBilinear_diagonal_zero (product11 G) (product11_skew G) a

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomologyPontryagin.homologyAlternatingTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 2) (Fin 2) :=
  alternatingOfBilinear (product11 G) (product11_self G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^2 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 2 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingTwo G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeTwo_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 2 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeTwo G (exteriorPower.ιMulti ℤ 2 v) = product11 G (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 2 :=
  (homologyWedgeTwo G).comp (exteriorPower.map 2 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (v : Fin 2 → Lattice) :
    latticeWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v) = product11 G (c (v 0)) (c (v 1)) := by
  change homologyWedgeTwo G (exteriorPower.map 2 c (exteriorPower.ιMulti ℤ 2 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeTwo_apply_ιMulti]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 2).comp (latticeWedgeTwo G c) =
      (latticeWedgeTwo H d).comp (exteriorPower.map 2 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    SingularMayerVietoris.singularHomologyMap f 2
        (latticeWedgeTwo G c (exteriorPower.ιMulti ℤ 2 v)) =
      latticeWedgeTwo H d (exteriorPower.map 2 A (exteriorPower.ιMulti ℤ 2 v))
  rw [exteriorPower.map_apply_ιMulti, latticeWedgeTwo_apply_ιMulti, latticeWedgeTwo_apply_ιMulti]
  rw [product_natural f hf 1, hmark, hmark]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerTrilinearPostcompose {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := integerBilinearPostcompose (F a) g
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => g (l b c)) (F.map_smul r a)).trans
        (g.map_smul r (F a b c))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.integerTrilinearPostcompose_apply {A B C D E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) (a : A) (b : B) (c : C) :
    integerTrilinearPostcompose F g a b c = g (F a b c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerTrilinearPrecompose {A B C D A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    [Module ℤ A'] [Module ℤ B'] [Module ℤ C'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) : A' →ₗ[ℤ] B' →ₗ[ℤ] C' →ₗ[ℤ] D
    where
  toFun a := integerBilinearPrecompose (F (f a)) g h
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPrecompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun x => F x (g b) (h c)) (f.map_smul r a)).trans
        (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => l (g b) (h c)) (F.map_smul r (f a)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.integerTrilinearPrecompose_apply {A B C D A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    [Module ℤ A'] [Module ℤ B'] [Module ℤ C'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) (a : A') (b : B') (c : C') :
    integerTrilinearPrecompose F f g h a b c = F (f a) (g b) (h c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerTrilinearLeftAssociated {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] B →ₗ[ℤ] D) (G : D →ₗ[ℤ] C →ₗ[ℤ] E) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := integerBilinearPrecompose G (F a) LinearMap.id
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPrecompose_apply, LinearMap.id_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact
      (congrArg (fun l : B →ₗ[ℤ] D => G (l b) c) (F.map_smul r a)).trans
        (congrArg (fun l : C →ₗ[ℤ] E => l c) (G.map_smul r (F a b)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.integerTrilinearRightAssociated {A B C D E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] [Module ℤ E] (F : A →ₗ[ℤ] D →ₗ[ℤ] E) (G : B →ₗ[ℤ] C →ₗ[ℤ] D) :
    A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E
    where
  toFun a := integerBilinearPostcompose G (F a)
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact congrArg (fun l : D →ₗ[ℤ] E => l (G b c)) (F.map_smul r a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.chainTrilinearLift (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f :
      FirstHurewicz.SingularSimplex X p →
        FirstHurewicz.SingularSimplex Y q → FirstHurewicz.SingularSimplex Z r → M) :
    FirstHurewicz.Chains X p →ₗ[ℤ]
      FirstHurewicz.Chains Y q →ₗ[ℤ] FirstHurewicz.Chains Z r →ₗ[ℤ] M :=
  FirstHurewicz.chainLift X p fun σ => chainBilinearLift Y Z q r (f σ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.chainTrilinearLift_simplex (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f :
      FirstHurewicz.SingularSimplex X p →
        FirstHurewicz.SingularSimplex Y q → FirstHurewicz.SingularSimplex Z r → M)
    (σ : FirstHurewicz.SingularSimplex X p) (τ : FirstHurewicz.SingularSimplex Y q)
    (υ : FirstHurewicz.SingularSimplex Z r) :
    chainTrilinearLift X Y Z p q r f (FirstHurewicz.simplexChain X p σ)
        (FirstHurewicz.simplexChain Y q τ) (FirstHurewicz.simplexChain Z r υ) =
      f σ τ υ := by
  rw [chainTrilinearLift, FirstHurewicz.chainLift_simplex, chainBilinearLift_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.chainTrilinearMap_ext (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    {F G :
      FirstHurewicz.Chains X p →ₗ[ℤ]
        FirstHurewicz.Chains Y q →ₗ[ℤ] FirstHurewicz.Chains Z r →ₗ[ℤ] M}
    (h :
      ∀ σ τ υ,
        F (FirstHurewicz.simplexChain X p σ) (FirstHurewicz.simplexChain Y q τ)
            (FirstHurewicz.simplexChain Z r υ) =
          G (FirstHurewicz.simplexChain X p σ) (FirstHurewicz.simplexChain Y q τ)
            (FirstHurewicz.simplexChain Z r υ)) :
    F = G := by
  apply FirstHurewicz.chainMap_ext X p
  intro σ
  apply chainBilinearMap_ext Y Z q r
  exact h σ

theorem PeriodTorusHigherHomology.formalMap_comp_apply {V W Z : Type*} (f : W → Z) (g : V → W)
    (n : ℕ) (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap f n (SingularMayerVietoris.formalMap g n c) =
      SingularMayerVietoris.formalMap (f ∘ g) n c := by
  have h :
    (SingularMayerVietoris.formalMap f n).comp (SingularMayerVietoris.formalMap g n) =
      SingularMayerVietoris.formalMap (f ∘ g) n := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.formalMap_id_apply {V : Type*} (n : ℕ)
    (c : SingularMayerVietoris.FormalChains V n) :
    SingularMayerVietoris.formalMap (id : V → V) n c = c := by
  have h : SingularMayerVietoris.formalMap (id : V → V) n = LinearMap.id := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [SingularMayerVietoris.formalMap_simplex, LinearMap.id_apply]
    rfl
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_point_left {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 1) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (formalEdgeCrossProduct q (formalPointCrossProduct 1 a b) c) =
      formalPointCrossProduct (q + 1) a (formalEdgeCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((formalEdgeCrossProduct q).flip c).comp ((formalPointCrossProduct 1).flip b)) =
      (formalPointCrossProduct (q + 1)).flip (formalEdgeCrossProduct q b c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, formalPointCrossProduct_simplex_left]
    have hn := formalMap_edgeCrossProduct (fun w : W => (v 0, w)) (id : Z → Z) q b c
    rw [formalMap_id_apply] at hn
    rw [← hn, formalMap_comp_apply]
    rfl
  exact LinearMap.congr_fun h a

theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_point_middle {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 1)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (formalEdgeCrossProduct q (formalEdgeCrossProduct 0 a b) c) =
      formalEdgeCrossProduct q a (formalPointCrossProduct q b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)).comp
        (((formalEdgeCrossProduct q).flip c).comp (formalEdgeCrossProduct 0 a)) =
      (formalEdgeCrossProduct q a).comp ((formalPointCrossProduct q).flip c) := by
    apply SingularMayerVietoris.formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [formalEdgeCrossProduct_zero_simplex_right, formalPointCrossProduct_simplex_left]
    have hl := formalMap_edgeCrossProduct (fun v : V => (v, w 0)) (id : Z → Z) q a c
    have hr := formalMap_edgeCrossProduct (id : V → V) (fun z : Z => (w 0, z)) q a c
    rw [formalMap_id_apply] at hl hr
    rw [← hl, formalMap_comp_apply, ← hr]
    rfl
  exact LinearMap.congr_fun h b

theorem PeriodTorusHigherHomology.formalTriangleCrossProduct_point_right {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3
        (formalTriangleCrossProduct 0 (formalEdgeCrossProduct 1 a b) c) =
      formalEdgeCrossProduct 1 a (formalEdgeCrossProduct 0 b c) := by
  have h :
    (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3).comp
        (formalTriangleCrossProduct 0 (formalEdgeCrossProduct 1 a b)) =
      (formalEdgeCrossProduct 1 a).comp (formalEdgeCrossProduct 0 b) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, formalTriangleCrossProduct_zero_simplex_right,
      formalEdgeCrossProduct_zero_simplex_right, formalMap_comp_apply]
    have hn := formalMap_edgeCrossProduct (id : V → V) (fun w : W => (w, z 0)) 1 a b
    rw [formalMap_id_apply] at hn
    exact hn
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.formalChains_trilinear_ext {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M]
    {f g :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M}
    (h :
      ∀ v w z,
        f (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalSimplex z) =
          g (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalSimplex z)) :
    f = g := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply formalChains_bilinear_ext
  exact h v

def PeriodTorusHigherHomology.formalTrilinearLift {V W Z M : Type*} {n m l : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => formalBilinearLift (f v)

@[simp]
theorem PeriodTorusHigherHomology.formalTrilinearLift_simplex {V W Z M : Type*} {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M)
    (v : Fin n → V) (w : Fin m → W) (z : Fin l → Z) :
    formalTrilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      f v w z := by simp [formalTrilinearLift]

def PeriodTorusHigherHomology.formalAssociatorDefect {V W Z : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3) :=
  (formalEdgeCrossProduct 1).compr₂
      ((formalTriangleCrossProduct q).compr₂
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
          (q + 3))) -
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z (q + 1))
              (SingularMayerVietoris.FormalChains (W × Z) (q + 2))
              (SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 3))).compl₂
          (formalEdgeCrossProduct q)).comp
      (formalEdgeCrossProduct (q + 1))

@[simp]
theorem PeriodTorusHigherHomology.formalAssociatorDefect_apply {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    formalAssociatorDefect q a b c =
      SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 3)
          (formalTriangleCrossProduct q (formalEdgeCrossProduct 1 a b) c) -
        formalEdgeCrossProduct (q + 1) a (formalEdgeCrossProduct q b c) :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.formalAssociatorDefect_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : formalAssociatorDefect 0 a b c = 0 := by
  rw [formalAssociatorDefect_apply, formalTriangleCrossProduct_point_right, sub_self]

theorem PeriodTorusHigherHomology.formalBoundary_associatorDefect {V W Z : Type*} (q : ℕ)
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 2)) :
    SingularMayerVietoris.formalBoundary (q + 3) (formalAssociatorDefect (q + 1) a b c) =
      formalAssociatorDefect q a b (SingularMayerVietoris.formalBoundary (q + 1) c) := by
  simp only [formalAssociatorDefect_apply, map_sub, ← SingularMayerVietoris.formalMap_boundary,
    formalBoundary_triangleCrossProduct, formalBoundary_edgeCrossProduct, map_add,
    LinearMap.sub_apply, formalEdgeCrossProduct_point_middle]
  rw [formalEdgeCrossProduct_point_left (q + 1) (SingularMayerVietoris.formalBoundary 1 a) b c]
  abel

theorem PeriodTorusHigherHomology.formalMap_prodAssoc_naturality {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') (n : ℕ)
    (c : SingularMayerVietoris.FormalChains ((V × W) × Z) n) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n c) =
      SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n c) := by
  have heq :
    (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) n).comp
        (SingularMayerVietoris.formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n) =
      (SingularMayerVietoris.formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n).comp
        (SingularMayerVietoris.formalMap (Prod.map (Prod.map f g) h) n) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun heq c

theorem PeriodTorusHigherHomology.formalMap_associatorDefect {V W Z V' W' Z' : Type*} (f : V → V')
    (g : W → W') (h : Z → Z') (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
    (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 3)
        (formalAssociatorDefect q a b c) =
      formalAssociatorDefect q (SingularMayerVietoris.formalMap f 2 a)
        (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) := by
  rw [formalAssociatorDefect_apply, map_sub, formalMap_prodAssoc_naturality,
    formalMap_triangleCrossProduct, formalMap_edgeCrossProduct, formalMap_edgeCrossProduct,
    formalMap_edgeCrossProduct]
  rfl

private def PeriodTorusHigherHomology.triplePostcomp_mo1973_13949 {V W Z U U' : Type*}
    {n m l r s : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains U r →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U' s :=
  F.compr₂
    (LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z l)
      (SingularMayerVietoris.FormalChains U r) (SingularMayerVietoris.FormalChains U' s) f)

private def PeriodTorusHigherHomology.triplePrecompLast_mo1973_13950 {V W Z Z' U : Type*}
    {n m l l' r : ℕ}
    (F :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z l →ₗ[ℤ] SingularMayerVietoris.FormalChains U r)
    (f : SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains Z l) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W m →ₗ[ℤ]
        SingularMayerVietoris.FormalChains Z' l' →ₗ[ℤ] SingularMayerVietoris.FormalChains U r :=
  F.compr₂
    ((LinearMap.llcomp ℤ (SingularMayerVietoris.FormalChains Z' l')
          (SingularMayerVietoris.FormalChains Z l) (SingularMayerVietoris.FormalChains U r)).flip
      f)

def PeriodTorusHigherHomology.formalAssociatorHomotopy {V W Z : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ]
          SingularMayerVietoris.FormalChains Z (q + 1) →ₗ[ℤ]
            SingularMayerVietoris.FormalChains (V × (W × Z)) (q + 4)
  | 0 => 0
  | q + 1 =>
    formalTrilinearLift fun v w z =>
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z)))

@[simp]
theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) : formalAssociatorHomotopy 0 a b c = 0 :=
  rfl

@[simp]
theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_simplex_succ {V W Z : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin 2 → W) (z : Fin (q + 2) → Z) :
    formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) =
      SingularMayerVietoris.formalCone (v 0, (w 0, z 0)) (q + 4)
        (formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
          formalAssociatorHomotopy q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex z))) :=
  formalTrilinearLift_simplex _ _ _ _

theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary_zero {V W Z : Type*}
    (a : SingularMayerVietoris.FormalChains V 2) (b : SingularMayerVietoris.FormalChains W 2)
    (c : SingularMayerVietoris.FormalChains Z 1) :
    SingularMayerVietoris.formalBoundary 3 (formalAssociatorHomotopy 0 a b c) =
      formalAssociatorDefect 0 a b c := by
  rw [formalAssociatorHomotopy_zero, map_zero, formalAssociatorDefect_zero]

theorem PeriodTorusHigherHomology.formalAssociatorHomotopy_boundary {V W Z : Type*} :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 4) (formalAssociatorHomotopy (q + 1) a b c) +
          formalAssociatorHomotopy q a b (SingularMayerVietoris.formalBoundary (q + 1) c) =
        formalAssociatorDefect (q + 1) a b c := by
  intro q
  induction q with
  | zero =>
    intro a b c
    have heq :
      triplePostcomp_mo1973_13949 (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) 1)
            (SingularMayerVietoris.formalBoundary 4) +
          triplePrecompLast_mo1973_13950 (formalAssociatorHomotopy 0)
            (SingularMayerVietoris.formalBoundary 1) =
        formalAssociatorDefect 1 := by
      apply formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary 4
              (formalAssociatorHomotopy 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex z)) =
          formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hz :
        SingularMayerVietoris.formalBoundary 3
            (formalAssociatorDefect 1 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              formalAssociatorHomotopy 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by
        rw [map_sub, formalBoundary_associatorDefect, formalAssociatorDefect_zero,
          formalAssociatorHomotopy_zero, map_zero, sub_self]
      rw [formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c
  | succ q ih =>
    intro a b c
    have heq :
      triplePostcomp_mo1973_13949 (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 2))
            (SingularMayerVietoris.formalBoundary (q + 5)) +
          triplePrecompLast_mo1973_13950 (formalAssociatorHomotopy (q + 1))
            (SingularMayerVietoris.formalBoundary (q + 2)) =
        formalAssociatorDefect (q + 2) := by
      apply formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalBoundary (q + 5)
              (formalAssociatorHomotopy (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) +
            formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z)) =
          formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)
      have hp :
        SingularMayerVietoris.formalBoundary (q + 4)
            (formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)
              (SingularMayerVietoris.formalBoundary (q + 2)
                (SingularMayerVietoris.formalSimplex z))) =
          formalAssociatorDefect (q + 1) (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2)
              (SingularMayerVietoris.formalSimplex z)) := by
        simpa only [SingularMayerVietoris.formalBoundary_boundary, map_zero, add_zero] using
          ih (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)
            (SingularMayerVietoris.formalBoundary (q + 2) (SingularMayerVietoris.formalSimplex z))
      have hz :
        SingularMayerVietoris.formalBoundary (q + 4)
            (formalAssociatorDefect (q + 2) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z) -
              formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalSimplex w)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex z))) =
          0 := by rw [map_sub, formalBoundary_associatorDefect, hp, sub_self]
      rw [formalAssociatorHomotopy_simplex_succ, SingularMayerVietoris.formalBoundary_cone, hz,
        map_zero, sub_zero, sub_add_cancel]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

theorem PeriodTorusHigherHomology.formalMap_associatorHomotopy {V W Z V' W' Z' : Type*}
    (f : V → V') (g : W → W') (h : Z → Z') :
    ∀ (q : ℕ) (a : SingularMayerVietoris.FormalChains V 2)
      (b : SingularMayerVietoris.FormalChains W 2)
      (c : SingularMayerVietoris.FormalChains Z (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 4)
          (formalAssociatorHomotopy q a b c) =
        formalAssociatorHomotopy q (SingularMayerVietoris.formalMap f 2 a)
          (SingularMayerVietoris.formalMap g 2 b) (SingularMayerVietoris.formalMap h (q + 1) c) :=
  by
  intro q
  induction q with
  | zero =>
    intro a b c
    simp only [formalAssociatorHomotopy_zero, map_zero]
  | succ q ih =>
    intro a b c
    have heq :
      triplePostcomp_mo1973_13949 (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 1))
          (SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)) =
        ((triplePrecompLast_mo1973_13950 (formalAssociatorHomotopy (q + 1))
                  (SingularMayerVietoris.formalMap h (q + 2))).compl₂
              (SingularMayerVietoris.formalMap g 2)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply formalChains_trilinear_ext
      intro v w z
      change
        SingularMayerVietoris.formalMap (Prod.map f (Prod.map g h)) (q + 5)
            (formalAssociatorHomotopy (q + 1) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) (SingularMayerVietoris.formalSimplex z)) =
          formalAssociatorHomotopy (q + 1)
            (SingularMayerVietoris.formalMap f 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalMap g 2 (SingularMayerVietoris.formalSimplex w))
            (SingularMayerVietoris.formalMap h (q + 2) (SingularMayerVietoris.formalSimplex z))
      simp only [SingularMayerVietoris.formalMap_simplex, formalAssociatorHomotopy_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, formalMap_associatorDefect, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

def PeriodTorusHigherHomology.tripleAffineSimplex {n p q r : ℕ}
    (v :
      Fin (n + 1) →
        FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :
    C(FirstHurewicz.Simplex n,
      FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (productAffineSimplex (fun i => (v i).2))

theorem PeriodTorusHigherHomology.tripleAffineSimplex_face {n p q r : ℕ}
    (v :
      Fin (n + 2) → FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))
    (i : Fin (n + 2)) :
    (tripleAffineSimplex v).comp (FirstHurewicz.simplexFace n i) =
      tripleAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg
        (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex q × FirstHurewicz.Simplex r) =>
          f t)
        (productAffineSimplex_face (fun j => (v j).2) i)

def PeriodTorusHigherHomology.tripleAffineChainMap (p q r n : ℕ) :
    SingularMayerVietoris.FormalChains
        (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))
        (n + 1) →ₗ[ℤ]
      FirstHurewicz.Chains
        (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) n :=
  SingularMayerVietoris.formalLift fun v => FirstHurewicz.simplexChain _ n (tripleAffineSimplex v)

@[simp]
theorem PeriodTorusHigherHomology.tripleAffineChainMap_simplex (p q r n : ℕ)
    (v :
      Fin (n + 1) →
        FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :
    tripleAffineChainMap p q r n (SingularMayerVietoris.formalSimplex v) =
      FirstHurewicz.simplexChain _ n (tripleAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

theorem PeriodTorusHigherHomology.tripleAffineChainMap_boundary (p q r n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains
        (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) (n + 2)) :
    ((FirstHurewicz.singularComplex
                (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
            (n + 1) n).hom
        (tripleAffineChainMap p q r (n + 1) c) =
      tripleAffineChainMap p q r n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((FirstHurewicz.singularComplex
                  (FirstHurewicz.Simplex p ×
                    (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
              (n + 1) n).hom).comp
        (tripleAffineChainMap p q r (n + 1)) =
      (tripleAffineChainMap p q r n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((FirstHurewicz.singularComplex
                  (FirstHurewicz.Simplex p ×
                    (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
              (n + 1) n).hom
          (tripleAffineChainMap p q r (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [tripleAffineChainMap_simplex, FirstHurewicz.boundary_simplex]
    change
      _ =
        tripleAffineChainMap p q r n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, tripleAffineChainMap_simplex, tripleAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

def PeriodTorusHigherHomology.affineProductLeft {a b p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
    (w : Fin (b + 1) → FirstHurewicz.Simplex r) :
    C(FirstHurewicz.Simplex a × FirstHurewicz.Simplex b,
      FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :=
  (Homeomorph.prodAssoc (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) :
        C(_, _)).comp
    ((productAffineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))

def PeriodTorusHigherHomology.affineProductRight {a b p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p)
    (w : Fin (b + 1) → FirstHurewicz.Simplex q × FirstHurewicz.Simplex r) :
    C(FirstHurewicz.Simplex a × FirstHurewicz.Simplex b,
      FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)) :=
  (SingularMayerVietoris.affineSimplex v).prodMap (productAffineSimplex w)

theorem PeriodTorusHigherHomology.affineProductLeft_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
    (w : Fin (b + 1) → FirstHurewicz.Simplex r)
    (z : Fin (m + 1) → FirstHurewicz.Simplex a × FirstHurewicz.Simplex b) :
    (affineProductLeft v w).comp (productAffineSimplex z) =
      tripleAffineSimplex (fun j => affineProductLeft v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).1) (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (v j).2) (fun j => (z j).1))
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))

theorem PeriodTorusHigherHomology.affineProductRight_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p)
    (w : Fin (b + 1) → FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
    (z : Fin (m + 1) → FirstHurewicz.Simplex a × FirstHurewicz.Simplex b) :
    (affineProductRight v w).comp (productAffineSimplex z) =
      tripleAffineSimplex (fun j => affineProductRight v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex q) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).1) (fun j => (z j).2))
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f t)
          (SingularMayerVietoris.affineSimplex_comp (fun j => (w j).2) (fun j => (z j).2))

theorem PeriodTorusHigherHomology.inducedChain_affineProductLeft {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
    (w : Fin (b + 1) → FirstHurewicz.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex a × FirstHurewicz.Simplex b)
        (m + 1)) :
    FirstHurewicz.inducedChain (affineProductLeft v w) m (productAffineChainMap a b m c) =
      tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (affineProductLeft v w) (m + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain (affineProductLeft v w) m).comp (productAffineChainMap a b m) =
      (tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (affineProductLeft v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      tripleAffineChainMap_simplex, affineProductLeft_comp]
    rfl
  exact LinearMap.congr_fun h c

theorem PeriodTorusHigherHomology.inducedChain_affineProductRight {a b m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p)
    (w : Fin (b + 1) → FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex a × FirstHurewicz.Simplex b)
        (m + 1)) :
    FirstHurewicz.inducedChain (affineProductRight v w) m (productAffineChainMap a b m c) =
      tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap (affineProductRight v w) (m + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain (affineProductRight v w) m).comp (productAffineChainMap a b m) =
      (tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap (affineProductRight v w) (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      tripleAffineChainMap_simplex, affineProductRight_comp]
    rfl
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductAssociatorDefect (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ]
        FirstHurewicz.Chains Z n →ₗ[ℤ] FirstHurewicz.Chains (X × (Y × Z)) (n + 2) :=
  integerTrilinearPostcompose
      (integerTrilinearLeftAssociated (crossProductEdge X Y 1) (crossProductTriangle (X × Y) Z n))
      (FirstHurewicz.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)) -
    integerTrilinearRightAssociated (crossProductEdge X (Y × Z) (n + 1)) (crossProductEdge Y Z n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_apply (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n) :
    crossProductAssociatorDefect X Y Z n a b c =
      FirstHurewicz.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) (n + 2)
          (crossProductTriangle (X × Y) Z n (crossProductEdge X Y 1 a b) c) -
        crossProductEdge X (Y × Z) (n + 1) a (crossProductEdge Y Z n b c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductAssociatorHomotopy (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ) :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ]
        FirstHurewicz.Chains Z n →ₗ[ℤ] FirstHurewicz.Chains (X × (Y × Z)) (n + 3) :=
  chainTrilinearLift X Y Z 1 1 n fun σ τ υ =>
    FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
      (tripleAffineChainMap 1 1 n (n + 3)
        (formalAssociatorHomotopy n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_simplex (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (σ : FirstHurewicz.SingularSimplex X 1) (τ : FirstHurewicz.SingularSimplex Y 1)
    (υ : FirstHurewicz.SingularSimplex Z n) :
    crossProductAssociatorHomotopy X Y Z n (FirstHurewicz.simplexChain X 1 σ)
        (FirstHurewicz.simplexChain Y 1 τ) (FirstHurewicz.simplexChain Z n υ) =
      FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)
        (tripleAffineChainMap 1 1 n (n + 3)
          (formalAssociatorHomotopy n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainTrilinearLift_simplex X Y Z 1 1 n _ σ τ υ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n) :
    FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) (n + 3)
        (crossProductAssociatorHomotopy X Y Z n a b c) =
      crossProductAssociatorHomotopy X' Y' Z' n (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g 1 b) (FirstHurewicz.inducedChain h n c) := by
  have heq :
    integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z n)
        (FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) (n + 3)) =
      integerTrilinearPrecompose (crossProductAssociatorHomotopy X' Y' Z' n)
        (FirstHurewicz.inducedChain f 1) (FirstHurewicz.inducedChain g 1)
        (FirstHurewicz.inducedChain h n) := by
    apply chainTrilinearMap_ext X Y Z 1 1 n
    intro σ τ υ
    simp only [integerTrilinearPostcompose_apply, integerTrilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductAssociatorHomotopy_simplex]
    have hc :
      (f.comp σ).prodMap ((g.comp τ).prodMap (h.comp υ)) =
        (f.prodMap (g.prodMap h)).comp (σ.prodMap (τ.prodMap υ)) :=
      rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.inducedChain_prodAssoc_natural {X : Type} {Y : Type} {Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (c : FirstHurewicz.Chains ((X × Y) × Z) n) :
    FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) n
        (FirstHurewicz.inducedChain (Homeomorph.prodAssoc X Y Z : C(_, _)) n c) =
      FirstHurewicz.inducedChain (Homeomorph.prodAssoc X' Y' Z' : C(_, _)) n
        (FirstHurewicz.inducedChain ((f.prodMap g).prodMap h) n c) := by
  have hc :
    (f.prodMap (g.prodMap h)).comp (Homeomorph.prodAssoc X Y Z : C(_, _)) =
      (Homeomorph.prodAssoc X' Y' Z' : C(_, _)).comp ((f.prodMap g).prodMap h) :=
    rfl
  have heq := congrArg (fun k => FirstHurewicz.inducedChain k n c) hc
  simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using heq

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_natural {X : Type} {Y : Type}
    {Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {X' Y' Z' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z'] (f : C(X, X'))
    (g : C(Y, Y')) (h : C(Z, Z')) (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n) :
    FirstHurewicz.inducedChain (f.prodMap (g.prodMap h)) (n + 2)
        (crossProductAssociatorDefect X Y Z n a b c) =
      crossProductAssociatorDefect X' Y' Z' n (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g 1 b) (FirstHurewicz.inducedChain h n c) := by
  simp only [crossProductAssociatorDefect_apply, map_sub, inducedChain_prodAssoc_natural,
    crossProductTriangle_natural, crossProductEdge_natural]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.productAffineSimplex_stdVertices_image {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    productAffineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact productAffineSimplex_vertex v i

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.prodMap_tripleAffineSimplex {a b c m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p) (w : Fin (b + 1) → FirstHurewicz.Simplex q)
    (z : Fin (c + 1) → FirstHurewicz.Simplex r)
    (t :
      Fin (m + 1) →
        FirstHurewicz.Simplex a × (FirstHurewicz.Simplex b × FirstHurewicz.Simplex c)) :
    ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z))).comp
        (tripleAffineSimplex t) =
      tripleAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (t j).1,
            (SingularMayerVietoris.affineSimplex w (t j).2.1,
              SingularMayerVietoris.affineSimplex z (t j).2.2))) := by
  apply ContinuousMap.ext
  intro s
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex p) => f s)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (t j).1))
  · apply Prod.ext
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex q) => f s)
          (SingularMayerVietoris.affineSimplex_comp w (fun j => (t j).2.1))
    · exact
        congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f s)
          (SingularMayerVietoris.affineSimplex_comp z (fun j => (t j).2.2))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.inducedChain_tripleAffineChainMap {a b c m p q r : ℕ}
    (v : Fin (a + 1) → FirstHurewicz.Simplex p) (w : Fin (b + 1) → FirstHurewicz.Simplex q)
    (z : Fin (c + 1) → FirstHurewicz.Simplex r)
    (t :
      SingularMayerVietoris.FormalChains
        (FirstHurewicz.Simplex a × (FirstHurewicz.Simplex b × FirstHurewicz.Simplex c)) (m + 1)) :
    FirstHurewicz.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap
          ((SingularMayerVietoris.affineSimplex w).prodMap
            (SingularMayerVietoris.affineSimplex z)))
        m (tripleAffineChainMap a b c m t) =
      tripleAffineChainMap p q r m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1) t) := by
  have h :
    (FirstHurewicz.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              ((SingularMayerVietoris.affineSimplex w).prodMap
                (SingularMayerVietoris.affineSimplex z)))
            m).comp
        (tripleAffineChainMap a b c m) =
      (tripleAffineChainMap p q r m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            ((SingularMayerVietoris.affineSimplex w).prodMap
              (SingularMayerVietoris.affineSimplex z)))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro s
    simp only [LinearMap.comp_apply, tripleAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      prodMap_tripleAffineSimplex]
    rfl
  exact LinearMap.congr_fun h t

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductTriangle_productAffineChainMap_left (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 1)) :
    FirstHurewicz.inducedChain
        (Homeomorph.prodAssoc (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
            (FirstHurewicz.Simplex r) :
          C(_, _))
        (n + 2)
        (crossProductTriangle (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) n (productAffineChainMap p q 2 a)
          (SingularMayerVietoris.affineChainMap r n b)) =
      tripleAffineChainMap p q r (n + 2)
        (SingularMayerVietoris.formalMap
          (fun x :
              (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) × FirstHurewicz.Simplex r =>
            (x.1.1, (x.1.2, x.2)))
          (n + 3) (formalTriangleCrossProduct n a b)) := by
  have h :
    integerBilinearPostcompose
        (integerBilinearPrecompose
          (crossProductTriangle (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
            (FirstHurewicz.Simplex r) n)
          (productAffineChainMap p q 2) (SingularMayerVietoris.affineChainMap r n))
        (FirstHurewicz.inducedChain
          (Homeomorph.prodAssoc (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
              (FirstHurewicz.Simplex r) :
            C(_, _))
          (n + 2)) =
      integerBilinearPostcompose (formalTriangleCrossProduct n)
        ((tripleAffineChainMap p q r (n + 2)).comp
          (SingularMayerVietoris.formalMap
            (fun x :
                (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) × FirstHurewicz.Simplex r =>
              (x.1.1, (x.1.2, x.2)))
            (n + 3))) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      productAffineChainMap_simplex, SingularMayerVietoris.affineChainMap_simplex,
      crossProductTriangle_simplex, LinearMap.comp_apply]
    rw [← LinearMap.comp_apply, ← FirstHurewicz.inducedChain_comp]
    change
      FirstHurewicz.inducedChain (affineProductLeft v w) (n + 2)
          (productAffineChainMap 2 n (n + 2)
            (formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [inducedChain_affineProductLeft]
    apply congrArg (tripleAffineChainMap p q r (n + 2))
    change
      SingularMayerVietoris.formalMap
          ((fun x :
                (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) × FirstHurewicz.Simplex r =>
              (x.1.1, (x.1.2, x.2))) ∘
            Prod.map (productAffineSimplex v) (SingularMayerVietoris.affineSimplex w))
          (n + 3)
          (formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))) =
        _
    rw [← formalMap_comp_apply, formalMap_triangleCrossProduct,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      productAffineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductEdge_productAffineChainMap_right (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
        (n + 1)) :
    crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r)
        n (SingularMayerVietoris.affineChainMap p 1 a) (productAffineChainMap q r n b) =
      tripleAffineChainMap p q r (n + 1) (formalEdgeCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductEdge (FirstHurewicz.Simplex p)
          (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (productAffineChainMap q r n) =
      integerBilinearPostcompose (formalEdgeCrossProduct n)
        (tripleAffineChainMap p q r (n + 1)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, productAffineChainMap_simplex,
      crossProductEdge_simplex]
    change
      FirstHurewicz.inducedChain (affineProductRight v w) (n + 1)
          (productAffineChainMap 1 n (n + 1)
            (formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [inducedChain_affineProductRight]
    change
      tripleAffineChainMap p q r (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v) (productAffineSimplex w)) (n + 2)
            (formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      productAffineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 1)) :
    crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      tripleAffineChainMap p q r (n + 3) (formalAssociatorHomotopy n a b c) := by
  have heq :
    integerTrilinearPrecompose
        (crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q 1)
        (SingularMayerVietoris.affineChainMap r n) =
      integerTrilinearPostcompose (formalAssociatorHomotopy n)
        (tripleAffineChainMap p q r (n + 3)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    apply SingularMayerVietoris.formalChains_ext
    intro w
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [integerTrilinearPrecompose_apply, integerTrilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductAssociatorHomotopy_simplex]
    rw [inducedChain_tripleAffineChainMap]
    change
      tripleAffineChainMap p q r (n + 3)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (Prod.map (SingularMayerVietoris.affineSimplex w)
                (SingularMayerVietoris.affineSimplex z)))
            (n + 4)
            (formalAssociatorHomotopy n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_associatorHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalMap_simplex,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorDefect_affineChainMap (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 1)) :
    crossProductAssociatorDefect (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r n c) =
      tripleAffineChainMap p q r (n + 2) (formalAssociatorDefect n a b c) := by
  simp only [crossProductAssociatorDefect_apply, crossProductEdge_affineChainMap, Nat.reduceAdd,
    crossProductTriangle_productAffineChainMap_left, crossProductEdge_productAffineChainMap_right,
    formalAssociatorDefect_apply, map_sub]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero_affine (p q r : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) 1) :
    ((FirstHurewicz.singularComplex
                (FirstHurewicz.Simplex p × (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
            3 2).hom
        (crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (SingularMayerVietoris.affineChainMap r 0 c)) =
      crossProductAssociatorDefect (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) 0 (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r 0 c) := by
  rw [crossProductAssociatorHomotopy_affineChainMap, tripleAffineChainMap_boundary,
    formalAssociatorHomotopy_boundary_zero, crossProductAssociatorDefect_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_affine (p q r n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2)
    (c : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex r) (n + 2)) :
    ((FirstHurewicz.singularComplex
                  (FirstHurewicz.Simplex p ×
                    (FirstHurewicz.Simplex q × FirstHurewicz.Simplex r))).d
              (n + 4) (n + 3)).hom
          (crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
            (FirstHurewicz.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) +
        crossProductAssociatorHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (FirstHurewicz.Simplex r) n (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 1 b)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex r)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap r (n + 1) c)) =
      crossProductAssociatorDefect (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (FirstHurewicz.Simplex r) (n + 1) (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q 1 b)
        (SingularMayerVietoris.affineChainMap r (n + 1) c) := by
  rw [crossProductAssociatorHomotopy_affineChainMap, tripleAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductAssociatorHomotopy_affineChainMap,
    ← map_add, formalAssociatorHomotopy_boundary, crossProductAssociatorDefect_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_zero {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z 0) :
    ((FirstHurewicz.singularComplex (X × (Y × Z))).d 3 2).hom
        (crossProductAssociatorHomotopy X Y Z 0 a b c) =
      crossProductAssociatorDefect X Y Z 0 a b c := by
  have heq :
    integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z 0)
        ((FirstHurewicz.singularComplex (X × (Y × Z))).d 3 2).hom =
      crossProductAssociatorDefect X Y Z 0 := by
    apply chainTrilinearMap_ext X Y Z 1 1 0
    intro σ τ υ
    have hstd :=
      crossProductAssociatorHomotopy_boundary_zero_affine 1 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστυ := congrArg (FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) 2) hstd
    simpa only [integerTrilinearPostcompose_apply, FirstHurewicz.inducedChain_boundary,
      crossProductAssociatorHomotopy_natural, crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1)
    (c : FirstHurewicz.Chains Z (n + 1)) :
    ((FirstHurewicz.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom
          (crossProductAssociatorHomotopy X Y Z (n + 1) a b c) +
        crossProductAssociatorHomotopy X Y Z n a b
          (((FirstHurewicz.singularComplex Z).d (n + 1) n).hom c) =
      crossProductAssociatorDefect X Y Z (n + 1) a b c := by
  have heq :
    integerTrilinearPostcompose (crossProductAssociatorHomotopy X Y Z (n + 1))
          ((FirstHurewicz.singularComplex (X × (Y × Z))).d (n + 4) (n + 3)).hom +
        integerTrilinearPrecompose (crossProductAssociatorHomotopy X Y Z n) LinearMap.id
          LinearMap.id ((FirstHurewicz.singularComplex Z).d (n + 1) n).hom =
      crossProductAssociatorDefect X Y Z (n + 1) := by
    apply chainTrilinearMap_ext X Y Z 1 1 (n + 1)
    intro σ τ υ
    have hstd :=
      crossProductAssociatorHomotopy_boundary_affine 1 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστυ := congrArg (FirstHurewicz.inducedChain (σ.prodMap (τ.prodMap υ)) (n + 3)) hstd
    simpa only [integerTrilinearPostcompose_apply, integerTrilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, FirstHurewicz.inducedChain_boundary,
      crossProductAssociatorHomotopy_natural, crossProductAssociatorDefect_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστυ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductAssociatorHomotopy_boundary_of_cycle {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (n : ℕ)
    (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 1) (c : FirstHurewicz.Chains Z n)
    (hc : ((FirstHurewicz.singularComplex Z).d n (n - 1)).hom c = 0) :
    ((FirstHurewicz.singularComplex (X × (Y × Z))).d (n + 3) (n + 2)).hom
        (crossProductAssociatorHomotopy X Y Z n a b c) =
      crossProductAssociatorDefect X Y Z n a b c := by
  cases n with
  | zero => exact crossProductAssociatorHomotopy_boundary_zero a b c
  | succ
    n =>
    have hc' : ((FirstHurewicz.singularComplex Z).d (n + 1) n).hom c = 0 := by
      simpa only [Nat.succ_sub_one] using hc
    simpa only [hc', map_zero, add_zero] using crossProductAssociatorHomotopy_boundary n a b c

theorem PeriodTorusHigherHomology.formalMap_swap_pointCrossProduct_two {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (d : SingularMayerVietoris.FormalChains W 3) :
    SingularMayerVietoris.formalMap Prod.swap 3 (formalPointCrossProduct 2 c d) =
      formalTriangleCrossProduct 0 d c := by
  have heq :
    (formalPointCrossProduct (V := V) (W := W) 2).compr₂
        (SingularMayerVietoris.formalMap Prod.swap 3) =
      (formalTriangleCrossProduct 0).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalMap Prod.swap 3
          (formalPointCrossProduct 2 (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w)) =
        formalTriangleCrossProduct 0 (SingularMayerVietoris.formalSimplex w)
          (SingularMayerVietoris.formalSimplex v)
    calc
      _ =
          SingularMayerVietoris.formalMap Prod.swap 3
            (SingularMayerVietoris.formalMap (fun z => (v 0, z)) 3
              (SingularMayerVietoris.formalSimplex w)) :=
        congrArg (SingularMayerVietoris.formalMap Prod.swap 3)
          (formalPointCrossProduct_simplex_left 2 v (SingularMayerVietoris.formalSimplex w))
      _ =
          SingularMayerVietoris.formalMap (fun z => (z, v 0)) 3
            (SingularMayerVietoris.formalSimplex w) := by
        rw [formalMap_comp]
        rfl
      _ = _ :=
        (formalTriangleCrossProduct_zero_simplex_right (SingularMayerVietoris.formalSimplex w)
            v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

def PeriodTorusHigherHomology.formalMixedSwapDefect {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 4 :=
  formalTriangleCrossProduct 1 -
    (formalEdgeCrossProduct 2).flip.compr₂ (SingularMayerVietoris.formalMap Prod.swap 4)

@[simp]
theorem PeriodTorusHigherHomology.formalMixedSwapDefect_apply {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    formalMixedSwapDefect c d =
      formalTriangleCrossProduct 1 c d -
        SingularMayerVietoris.formalMap Prod.swap 4 (formalEdgeCrossProduct 2 d c) :=
  rfl

theorem PeriodTorusHigherHomology.formalBoundary_mixedSwapDefect {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 3 (formalMixedSwapDefect c d) =
      formalEdgeSwapDefect (SingularMayerVietoris.formalBoundary 2 c) d := by
  rw [formalMixedSwapDefect_apply, map_sub, formalBoundary_triangleCrossProduct, ←
    SingularMayerVietoris.formalMap_boundary, formalBoundary_edgeCrossProduct, map_sub,
    formalMap_swap_pointCrossProduct_two, formalEdgeSwapDefect_apply]
  abel

theorem PeriodTorusHigherHomology.formalMap_mixedSwapDefect {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 4 (formalMixedSwapDefect c d) =
      formalMixedSwapDefect (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  rw [formalMixedSwapDefect_apply, map_sub, formalMap_triangleCrossProduct, formalMap_prod_swap,
    formalMap_edgeCrossProduct, formalMixedSwapDefect_apply]

def PeriodTorusHigherHomology.formalMixedSwapHomotopy {V W : Type*} :
    SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W 2 →ₗ[ℤ] SingularMayerVietoris.FormalChains (V × W) 5 :=
  formalBilinearLift fun v w =>
    SingularMayerVietoris.formalCone (v 0, w 0) 4
      (formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w) -
        formalEdgeSwapHomotopy
          (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
          (SingularMayerVietoris.formalSimplex w))

@[simp]
theorem PeriodTorusHigherHomology.formalMixedSwapHomotopy_simplex {V W : Type*} (v : Fin 3 → V)
    (w : Fin 2 → W) :
    formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) 4
        (formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalSimplex w) -
          formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w)) :=
  formalBilinearLift_simplex _ _ _

theorem PeriodTorusHigherHomology.formalMixedSwapHomotopy_boundary {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalBoundary 4 (formalMixedSwapHomotopy c d) +
        formalEdgeSwapHomotopy (SingularMayerVietoris.formalBoundary 2 c) d =
      formalMixedSwapDefect c d := by
  have heq :
    (formalMixedSwapHomotopy (V := V) (W := W)).compr₂ (SingularMayerVietoris.formalBoundary 4) +
        (formalEdgeSwapHomotopy).comp (SingularMayerVietoris.formalBoundary 2) =
      formalMixedSwapDefect := by
    apply formalChains_bilinear_ext
    intro v w
    change
      SingularMayerVietoris.formalBoundary 4
            (formalMixedSwapHomotopy (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) +
          formalEdgeSwapHomotopy
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) =
        formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
          (SingularMayerVietoris.formalSimplex w)
    have hz :
      SingularMayerVietoris.formalBoundary 3
          (formalMixedSwapDefect (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w) -
            formalEdgeSwapHomotopy
              (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
              (SingularMayerVietoris.formalSimplex w)) =
        0 := by
      rw [map_sub, formalBoundary_mixedSwapDefect, formalEdgeSwapHomotopy_boundary, sub_self]
    rw [formalMixedSwapHomotopy_simplex, SingularMayerVietoris.formalBoundary_cone, hz, map_zero,
      sub_zero, sub_add_cancel]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

theorem PeriodTorusHigherHomology.formalMap_mixedSwapHomotopy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (c : SingularMayerVietoris.FormalChains V 3)
    (d : SingularMayerVietoris.FormalChains W 2) :
    SingularMayerVietoris.formalMap (Prod.map f g) 5 (formalMixedSwapHomotopy c d) =
      formalMixedSwapHomotopy (SingularMayerVietoris.formalMap f 3 c)
        (SingularMayerVietoris.formalMap g 2 d) := by
  have heq :
    (formalMixedSwapHomotopy (V := V) (W := W)).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) 5) =
      ((formalMixedSwapHomotopy).compl₂ (SingularMayerVietoris.formalMap g 2)).comp
        (SingularMayerVietoris.formalMap f 3) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      SingularMayerVietoris.formalMap_simplex, formalMixedSwapHomotopy_simplex]
    rw [SingularMayerVietoris.formalMap_cone]
    congr 1
    rw [map_sub, formalMap_mixedSwapDefect, formalMap_edgeSwapHomotopy,
      SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductMixedSwapHomotopy (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    FirstHurewicz.Chains X 2 →ₗ[ℤ]
      FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 4 :=
  chainBilinearLift X Y 2 1 fun σ τ =>
    FirstHurewicz.inducedChain (σ.prodMap τ) 4
      (productAffineChainMap 2 1 4
        (formalMixedSwapHomotopy
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (σ : FirstHurewicz.SingularSimplex X 2)
    (τ : FirstHurewicz.SingularSimplex Y 1) :
    crossProductMixedSwapHomotopy X Y (FirstHurewicz.simplexChain X 2 σ)
        (FirstHurewicz.simplexChain Y 1 τ) =
      FirstHurewicz.inducedChain (σ.prodMap τ) 4
        (productAffineChainMap 2 1 4
          (formalMixedSwapHomotopy
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) :=
  chainBilinearLift_simplex X Y 2 1 _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (a : FirstHurewicz.Chains X 2) (b : FirstHurewicz.Chains Y 1) :
    FirstHurewicz.inducedChain (f.prodMap g) 4 (crossProductMixedSwapHomotopy X Y a b) =
      crossProductMixedSwapHomotopy X' Y' (FirstHurewicz.inducedChain f 2 a)
        (FirstHurewicz.inducedChain g 1 b) := by
  have h :
    integerBilinearPostcompose (crossProductMixedSwapHomotopy X Y)
        (FirstHurewicz.inducedChain (f.prodMap g) 4) =
      integerBilinearPrecompose (crossProductMixedSwapHomotopy X' Y')
        (FirstHurewicz.inducedChain f 2) (FirstHurewicz.inducedChain g 1) := by
    apply chainBilinearMap_ext X Y 2 1
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductMixedSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_affineChainMap (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    crossProductMixedSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q 1 b) =
      productAffineChainMap p q 4 (formalMixedSwapHomotopy a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductMixedSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q))
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q 1) =
      integerBilinearPostcompose formalMixedSwapHomotopy (productAffineChainMap p q 4) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductMixedSwapHomotopy_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q 4
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            5
            (formalMixedSwapHomotopy
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1)))) =
        _
    rw [formalMap_mixedSwapHomotopy, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 2) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d 4
              3).hom
          (crossProductMixedSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
            (SingularMayerVietoris.affineChainMap p 2 a)
            (SingularMayerVietoris.affineChainMap q 1 b)) +
        crossProductSwapHomotopy (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p)).d 2 1).hom
            (SingularMayerVietoris.affineChainMap p 2 a))
          (SingularMayerVietoris.affineChainMap q 1 b) =
      crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 1
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q 1 b) -
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 3
          (crossProductEdge (FirstHurewicz.Simplex q) (FirstHurewicz.Simplex p) 2
            (SingularMayerVietoris.affineChainMap q 1 b)
            (SingularMayerVietoris.affineChainMap p 2 a)) := by
  rw [crossProductMixedSwapHomotopy_affineChainMap, productAffineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductSwapHomotopy_affineChainMap,
    crossProductTriangle_affineChainMap, crossProductEdge_affineChainMap,
    inducedChain_swap_productAffineChainMap, ← map_add, formalMixedSwapHomotopy_boundary,
    formalMixedSwapDefect_apply, map_sub]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2)
    (b : FirstHurewicz.Chains Y 1) :
    ((FirstHurewicz.singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) +
        crossProductSwapHomotopy X Y (((FirstHurewicz.singularComplex X).d 2 1).hom a) b =
      crossProductTriangle X Y 1 a b -
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) := by
  have h :
    integerBilinearPostcompose (crossProductMixedSwapHomotopy X Y)
          ((FirstHurewicz.singularComplex (X × Y)).d 4 3).hom +
        integerBilinearPrecompose (crossProductSwapHomotopy X Y)
          ((FirstHurewicz.singularComplex X).d 2 1).hom LinearMap.id =
      crossProductTriangle X Y 1 -
        integerBilinearPostcompose (integerBilinearFlip (crossProductEdge Y X 2))
          (FirstHurewicz.inducedChain ContinuousMap.prodSwap 3) := by
    apply chainBilinearMap_ext X Y 2 1
    intro σ τ
    have hstd :=
      crossProductMixedSwapHomotopy_boundary_affine 2 1
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) 3) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      integerBilinearFlip_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, FirstHurewicz.inducedChain_boundary,
      crossProductMixedSwapHomotopy_natural, crossProductSwapHomotopy_natural,
      inducedChain_prodMap_swap, crossProductTriangle_natural, crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductMixedSwapHomotopy_boundary_of_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2)
    (ha : ((FirstHurewicz.singularComplex X).d 2 1).hom a = 0) (b : FirstHurewicz.Chains Y 1) :
    ((FirstHurewicz.singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) =
      crossProductTriangle X Y 1 a b -
        FirstHurewicz.inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) := by
  simpa only [ha, map_zero, LinearMap.zero_apply, add_zero] using
    crossProductMixedSwapHomotopy_boundary a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductTwoOneCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1 →ₗ[ℤ]
        SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (X × Y)) 3
    where
  toFun
    a :=
    { toFun
        b :=
        SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex (X × Y)) 3
          (crossProductTriangle X Y 1 a.1 b.1)
          (by
            change
              ((FirstHurewicz.singularComplex (X × Y)).d 3 2).hom
                  (crossProductTriangle X Y 1 a.1 b.1) =
                0
            simp only [crossProductTriangle_boundary,
              SingularMayerVietoris.ModuleHomology.cycle_condition
                  (FirstHurewicz.singularComplex X) 2 a,
              SingularMayerVietoris.ModuleHomology.cycle_condition
                  (FirstHurewicz.singularComplex Y) 1 b,
              map_zero, LinearMap.zero_apply, zero_add])
      map_add' b
        c := by
        apply Subtype.ext
        exact (crossProductTriangle X Y 1 a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (crossProductTriangle X Y 1 a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 3 => f c.1)
        ((crossProductTriangle X Y 1).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg (fun f : FirstHurewicz.Chains Y 1 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) 3 => f c.1)
        ((crossProductTriangle X Y 1).map_smul r a.1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductTwoOneCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1) :
    (crossProductTwoOneCycles X Y a b).1 = crossProductTriangle X Y 1 a.1 b.1 :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductHomologyTwoOne (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology Y 1 →ₗ[ℤ]
        SingularMayerVietoris.SingularHomology (X × Y) 3 :=
  integerBilinearPostcompose (integerBilinearFlip (crossProductHomology Y X 2))
    (SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductHomologyTwoOne_apply (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 2)
    (b : SingularMayerVietoris.SingularHomology Y 1) :
    crossProductHomologyTwoOne X Y a b =
      SingularMayerVietoris.singularHomologyMap ContinuousMap.prodSwap 3
        (crossProductHomology Y X 2 b a) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.crossProductHomologyTwoOne_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1) :
    crossProductHomologyTwoOne X Y
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) 1 b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y)) 3
        (crossProductTwoOneCycles X Y a b) := by
  rw [crossProductHomologyTwoOne_apply, crossProductHomology_cycleClass]
  change
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap ContinuousMap.prodSwap) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (Y × X)) 3
          (crossProductCycles Y X 2 b a)) =
      _
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply Eq.symm
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (FirstHurewicz.singularComplex (X × Y)) 3 _ _).mpr
  refine ⟨crossProductMixedSwapHomotopy X Y a.1 b.1, ?_⟩
  simp only [crossProductTwoOneCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val,
    crossProductCycles_val]
  exact
    crossProductMixedSwapHomotopy_boundary_of_cycle a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2 a)
      b.1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCycleClasses_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Z) 1) :
    (HomologicalComplex.homologyMap
            (FirstHurewicz.singularChainMap (Homeomorph.prodAssoc X Y Z : C(_, _))) 3).hom
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex ((X × Y) × Z)) 3
          (crossProductTwoOneCycles (X × Y) Z (crossProductCycles X Y 1 a b) c)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (X × (Y × Z))) 3
        (crossProductCycles X (Y × Z) 2 a (crossProductCycles Y Z 1 b c)) := by
  rw [SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff
        (FirstHurewicz.singularComplex (X × (Y × Z))) 3 _ _).mpr
  refine ⟨crossProductAssociatorHomotopy X Y Z 1 a.1 b.1 c.1, ?_⟩
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, crossProductTwoOneCycles_val,
    crossProductCycles_val]
  exact
    crossProductAssociatorHomotopy_boundary_of_cycle 1 a.1 b.1 c.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex Z) 1 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_associative {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc X Y Z : C(_, _)) 3
        (crossProductHomologyTwoOne (X × Y) Z (crossProductHomology X Y 1 a b) c) =
      crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Y) 1
      b
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Z) 1
      c
  rw [crossProductHomology_cycleClass, crossProductHomologyTwoOne_cycleClass,
    crossProductHomology_cycleClass, crossProductHomology_cycleClass]
  exact crossProductCycleClasses_associative a b c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.crossProductCyclicMap (X Y Z : Type) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] : C(Y × (Z × X), X × (Y × Z)) :=
  ContinuousMap.prodSwap.comp ((Homeomorph.prodAssoc Y Z X).symm : C(_, _))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductCyclicMap_assoc_swap {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    (crossProductCyclicMap X Y Z).comp
        ((Homeomorph.prodAssoc Y Z X : C(_, _)).comp ContinuousMap.prodSwap) =
      ContinuousMap.id (X × (Y × Z)) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.crossProductHomology_cyclic {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y 1)
    (c : SingularMayerVietoris.SingularHomology Z 1) :
    crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c) =
      SingularMayerVietoris.singularHomologyMap (crossProductCyclicMap X Y Z) 3
        (crossProductHomology Y (Z × X) 2 b (crossProductHomology Z X 1 c a)) := by
  have h := crossProductHomology_associative b c a
  rw [crossProductHomologyTwoOne_apply] at h
  have h' :=
    congrArg (SingularMayerVietoris.singularHomologyMap (crossProductCyclicMap X Y Z) 3) h
  have hmap :
    (SingularMayerVietoris.singularHomologyMap (crossProductCyclicMap X Y Z) 3).comp
        ((SingularMayerVietoris.singularHomologyMap (Homeomorph.prodAssoc Y Z X : C(_, _)) 3).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.prodSwap : C(X × (Y × Z), (Y × Z) × X)) 3)) =
      LinearMap.id := by
    rw [← singularHomologyMap_comp, ← singularHomologyMap_comp, crossProductCyclicMap_assoc_swap,
      singularHomologyMap_id]
  exact
    (LinearMap.congr_fun hmap
          (crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c))).symm.trans
      h'

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_cyclic (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b c : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b c = tripleProduct G b c a := by
  rw [tripleProduct_eq_cross G a b c, tripleProduct_eq_cross G b c a,
    PeriodTorusHigherHomology.crossProductHomology_cyclic]
  have he : PeriodTorusHigherHomology.crossProductCyclicMap G G G = cyclicMap G G G := by
    apply ContinuousMap.ext
    intro p
    rfl
  rw [he]
  exact
    LinearMap.congr_fun (rightAddition_homology_cyclic G 3)
      (PeriodTorusHigherHomology.crossProductHomology G (G × G) 2 b
        (PeriodTorusHigherHomology.crossProductHomology G G 1 c a))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self12 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a b b = 0 := by
  rw [tripleProduct_apply, product11_self, map_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self02 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a b a = 0 :=
  (tripleProduct_cyclic G a b a).trans (tripleProduct_self12 G b a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_self01 (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (a b : SingularMayerVietoris.SingularHomology G 1) : tripleProduct G a a b = 0 :=
  (tripleProduct_cyclic G a a b).trans (tripleProduct_self02 G a b)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomologyPontryagin.homologyAlternatingThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    AlternatingMap ℤ (SingularMayerVietoris.SingularHomology G 1)
      (SingularMayerVietoris.SingularHomology G 3) (Fin 3) :=
  alternatingOfTrilinear (tripleProduct G) (tripleProduct_self01 G) (tripleProduct_self02 G)
    (tripleProduct_self12 G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomologyPontryagin.homologyWedgeThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] :
    (⋀[ℤ]^3 (SingularMayerVietoris.SingularHomology G 1)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology G 3 :=
  exteriorPower.alternatingMapLinearEquiv (homologyAlternatingThree G)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.homologyWedgeThree_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (v : Fin 3 → SingularMayerVietoris.SingularHomology G 1) :
    homologyWedgeThree G (exteriorPower.ιMulti ℤ 3 v) = tripleProduct G (v 0) (v 1) (v 2) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomologyPontryagin.latticeWedgeThree (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 3 :=
  (homologyWedgeThree G).comp (exteriorPower.map 3 c)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_apply_ιMulti (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (v : Fin 3 → Lattice) :
    latticeWedgeThree G c (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct G (c (v 0)) (c (v 1)) (c (v 2)) := by
  change homologyWedgeThree G (exteriorPower.map 3 c (exteriorPower.ιMulti ℤ 3 v)) = _
  rw [exteriorPower.map_apply_ιMulti, homologyWedgeThree_apply_ιMulti]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_natural {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {H : Type}
    [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology H 2)] (f : C(G, H))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1)
    (d : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology H 1) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, SingularMayerVietoris.singularHomologyMap f 1 (c v) = d (A v)) :
    (SingularMayerVietoris.singularHomologyMap f 3).comp (latticeWedgeThree G c) =
      (latticeWedgeThree H d).comp (exteriorPower.map 3 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    SingularMayerVietoris.singularHomologyMap f 3
        (latticeWedgeThree G c (exteriorPower.ιMulti ℤ 3 v)) =
      latticeWedgeThree H d (exteriorPower.map 3 A (exteriorPower.ιMulti ℤ 3 v))
  rw [exteriorPower.map_apply_ιMulti, latticeWedgeThree_apply_ιMulti,
    latticeWedgeThree_apply_ιMulti]
  rw [tripleProduct_natural f hf, hmark, hmark, hmark]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.product11_mem_range_latticeWedgeTwo (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (a b : SingularMayerVietoris.SingularHomology G 1) :
    product11 G a b ∈ LinearMap.range (latticeWedgeTwo G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  refine ⟨exteriorPower.ιMulti ℤ 2 ![v, w], ?_⟩
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.tripleProduct_mem_range_latticeWedgeThree (G : Type)
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (a b d : SingularMayerVietoris.SingularHomology G 1) :
    tripleProduct G a b d ∈ LinearMap.range (latticeWedgeThree G c) := by
  obtain ⟨v, rfl⟩ := hc a
  obtain ⟨w, rfl⟩ := hc b
  obtain ⟨u, rfl⟩ := hc d
  refine ⟨exteriorPower.ιMulti ℤ 3 ![v, w, u], ?_⟩
  simp

theorem PeriodTorusHigherHomology.productTorusTopClass_two_is_product :
    ∃ a b : SingularMayerVietoris.SingularHomology (ProductTorus 2) 1,
      productTorusTopClass 2 =
        PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 2) a b := by
  refine
    ⟨FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)),
      SingularMayerVietoris.singularHomologyMap (torusTailMap 1) 1 (productTorusTopClass 1), ?_⟩
  exact productTorusTopClass_succ_product 1

theorem PeriodTorusHigherHomology.productTorusTopClass_three_is_tripleProduct :
    ∃ a b c : SingularMayerVietoris.SingularHomology (ProductTorus 3) 1,
      productTorusTopClass 3 =
        PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 3) a b c := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  refine
    ⟨FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 3 (Pi.single 0 1)),
      SingularMayerVietoris.singularHomologyMap (torusTailMap 2) 1 a,
      SingularMayerVietoris.singularHomologyMap (torusTailMap 2) 1 b, ?_⟩
  rw [PeriodTorusHigherHomologyPontryagin.tripleProduct_apply,
    productTorusTopClass_succ_product 2, hab,
    PeriodTorusHigherHomologyPontryagin.product_natural (torusTailMap 2) (torusTailMap_add 2) 1]

theorem PeriodTorusHigherHomology.map_topClass_two_mem_range_latticeWedgeTwo {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 2, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 2 (productTorusTopClass 2) ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c) := by
  obtain ⟨a, b, hab⟩ := productTorusTopClass_two_is_product
  rw [hab, PeriodTorusHigherHomologyPontryagin.product_natural f hf 1]
  exact PeriodTorusHigherHomologyPontryagin.product11_mem_range_latticeWedgeTwo G c hc _ _

theorem PeriodTorusHigherHomology.map_topClass_three_mem_range_latticeWedgeThree {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)]
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (f : C(ProductTorus 3, G)) (hf : ∀ x y, f (x + y) = f x + f y) :
    SingularMayerVietoris.singularHomologyMap f 3 (productTorusTopClass 3) ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c) := by
  obtain ⟨a, b, d, habd⟩ := productTorusTopClass_three_is_tripleProduct
  rw [habd, PeriodTorusHigherHomologyPontryagin.tripleProduct_natural f hf]
  exact PeriodTorusHigherHomologyPontryagin.tripleProduct_mem_range_latticeWedgeThree G c hc _ _ _

def PeriodTorusHigherHomology.omitHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin n) ℤ :=
  Fin.cons 0 A

def PeriodTorusHigherHomology.takeHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i))

theorem PeriodTorusHigherHomology.torusMatrixMap_omitHeadMatrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (x : ProductTorus n) :
    torusMatrixMap (omitHeadMatrix A) x = Fin.cons 0 (torusMatrixMap A x) := by
  have hzero (j : Fin n) : omitHeadMatrix A 0 j = 0 := rfl
  have hsucc (i : Fin r) (j : Fin n) : omitHeadMatrix A i.succ j = A i j := rfl
  funext i
  change (∑ j, omitHeadMatrix A i j • x j) = _
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [hzero]
  · simp [hsucc]

theorem PeriodTorusHigherHomology.torusMatrixMap_takeHeadMatrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (x : ProductTorus (n + 1)) :
    torusMatrixMap (takeHeadMatrix A) x = Fin.cons (x 0) (torusMatrixMap A (fun k => x k.succ)) :=
  by
  funext i
  change (∑ j, takeHeadMatrix A i j • x j) = _
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [takeHeadMatrix, Fin.sum_univ_succ]
  · simp [takeHeadMatrix, Fin.sum_univ_succ]

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_zero_source {r : ℕ}
    (A : Matrix (Fin r) (Fin 0) ℤ) : torusMatrixMap A = ContinuousMap.const (ProductTorus 0) 0 := by
  apply ContinuousMap.ext
  intro x
  funext i
  simp

def PeriodTorusHigherHomology.coordinateTorusMap :
    (r n : ℕ) → Fin (r.choose n) → C(ProductTorus n, ProductTorus r)
  | 0, 0, _ => ContinuousMap.const _ 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => ContinuousMap.const _ 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j =>
      ((productTorusSuccHomeomorph r).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r,
              ProductTorus (r + 1))).comp
        ((CircleTopology.productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j))
    | Sum.inr j =>
      ((productTorusSuccHomeomorph r).symm :
            C((PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r,
              ProductTorus (r + 1))).comp
        ((circleProductMap (coordinateTorusMap r n j)).comp
          (productTorusSuccHomeomorph n :
            C(ProductTorus (n + 1),
              (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus n)))

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_degree_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusMap r 0 i = ContinuousMap.const _ 0 := by cases r <;> rfl

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_omit_apply (r n : ℕ)
    (j : Fin (r.choose (n + 1))) (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x =
      Fin.cons 0 (coordinateTorusMap r (n + 1) j x) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_take_apply (r n : ℕ) (j : Fin (r.choose n))
    (x : ProductTorus (n + 1)) :
    coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x =
      Fin.cons (x 0) (coordinateTorusMap r n j (fun k => x k.succ)) := by
  rw [coordinateTorusMap, Equiv.apply_symm_apply]
  rfl

theorem PeriodTorusHigherHomology.coordinateTorusMap_omit (r n : ℕ) (j : Fin (r.choose (n + 1))) :
    (productTorusSuccHomeomorph r :
            C(ProductTorus (r + 1),
              (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j))) =
      (CircleTopology.productSection (ProductTorus r)).comp (coordinateTorusMap r (n + 1) j) := by
  apply ContinuousMap.ext
  intro x
  change
    productTorusSuccHomeomorph r
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) x) =
      _
  rw [coordinateTorusMap_omit_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

theorem PeriodTorusHigherHomology.coordinateTorusMap_take (r n : ℕ) (j : Fin (r.choose n)) :
    (productTorusSuccHomeomorph r :
            C(ProductTorus (r + 1),
              (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r)).comp
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j))) =
      (circleProductMap (coordinateTorusMap r n j)).comp
        (productTorusSuccHomeomorph n :
          C(ProductTorus (n + 1),
            (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus n)) := by
  apply ContinuousMap.ext
  intro x
  change
    productTorusSuccHomeomorph r
        (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) x) =
      _
  rw [coordinateTorusMap_take_apply]
  simp only [productTorusSuccHomeomorph_apply, Fin.cons_zero, Fin.cons_succ]
  rfl

def PeriodTorusHigherHomology.coordinateTorusMatrix :
    (r n : ℕ) → Fin (r.choose n) → Matrix (Fin r) (Fin n) ℤ
  | 0, 0, _ => 0
  | 0, _n + 1, i => Fin.elim0 i
  | _r + 1, 0, _ => 0
  | r + 1, n + 1, i =>
    match binomialPascalIndexEquiv r n i with
    | Sum.inl j => omitHeadMatrix (coordinateTorusMatrix r (n + 1) j)
    | Sum.inr j => takeHeadMatrix (coordinateTorusMatrix r n j)

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMatrix_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)) =
      omitHeadMatrix (coordinateTorusMatrix r (n + 1) j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMatrix_take (r n : ℕ) (j : Fin (r.choose n)) :
    coordinateTorusMatrix (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)) =
      takeHeadMatrix (coordinateTorusMatrix r n j) := by
  rw [coordinateTorusMatrix, Equiv.apply_symm_apply]

theorem PeriodTorusHigherHomology.coordinateTorusMap_eq_torusMatrixMap (r n : ℕ)
    (i : Fin (r.choose n)) :
    coordinateTorusMap r n i = torusMatrixMap (coordinateTorusMatrix r n i) := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => rw [coordinateTorusMap_degree_zero, torusMatrixMap_zero_source]
    | succ n => exact Fin.elim0 i
  | succ r ih =>
    cases n with
    | zero => rw [coordinateTorusMap_degree_zero, torusMatrixMap_zero_source]
    | succ n =>
      obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
      cases j with
      | inl j =>
        apply ContinuousMap.ext
        intro x
        rw [coordinateTorusMap_omit_apply, coordinateTorusMatrix_omit,
          torusMatrixMap_omitHeadMatrix, ih (n + 1) j]
      | inr j =>
        apply ContinuousMap.ext
        intro x
        rw [coordinateTorusMap_take_apply, coordinateTorusMatrix_take,
          torusMatrixMap_takeHeadMatrix, ih n j]

def PeriodTorusHigherHomology.coordinateTorusClass (r n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology (ProductTorus r) n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n (productTorusTopClass n)

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusClass_zero (r : ℕ) (i : Fin (r.choose 0)) :
    coordinateTorusClass r 0 i = pointClass (0 : ProductTorus r) := by
  rw [coordinateTorusClass, productTorusTopClass_zero, singularHomologyMap_pointClass,
    coordinateTorusMap_degree_zero]
  rfl

theorem PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1)))
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))
          (n + 1) a) =
      circleSectionHomology (ProductTorus r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r (n + 1) j) (n + 1) a) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (productTorusSuccHomeomorph r :
                C(ProductTorus (r + 1),
                  (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r))
              (n + 1)).comp
          (SingularMayerVietoris.singularHomologyMap
            (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))
            (n + 1)))
        a =
      _
  rw [← singularHomologyMap_comp, coordinateTorusMap_omit, singularHomologyMap_comp]
  rfl

theorem PeriodTorusHigherHomology.homeomorphHomology_coordinateTorusMap_take (r n : ℕ)
    (j : Fin (r.choose n))
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (n + 1)) (n + 1)) :
    homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))
          (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap (circleProductMap (coordinateTorusMap r n j))
        (n + 1) (homeomorphHomologyEquiv (productTorusSuccHomeomorph n) (n + 1) a) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (productTorusSuccHomeomorph r :
                C(ProductTorus (r + 1),
                  (PeriodTorusHigherHomology.CircleTopology.Circle) × ProductTorus r))
              (n + 1)).comp
          (SingularMayerVietoris.singularHomologyMap
            (coordinateTorusMap (r + 1) (n + 1) ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))
            (n + 1)))
        a =
      _
  rw [← singularHomologyMap_comp, coordinateTorusMap_take, singularHomologyMap_comp]
  rfl

theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_omit (r n : ℕ)
    (j : Fin (r.choose (n + 1))) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inl j)))) =
      (coordinateTorusClass r (n + 1) j, 0) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_omit, circleProductHomologyEquiv_section]

theorem PeriodTorusHigherHomology.circleCoordinates_coordinateTorusClass_take (r n : ℕ)
    (j : Fin (r.choose n)) :
    circleProductHomologyEquiv (ProductTorus r) n
        (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)
          (coordinateTorusClass (r + 1) (n + 1)
            ((binomialPascalIndexEquiv r n).symm (Sum.inr j)))) =
      (0, coordinateTorusClass r n j) := by
  unfold coordinateTorusClass
  rw [homeomorphHomology_coordinateTorusMap_take, circleProductHomologyEquiv_naturality,
    productTorusTopClass_succ_coordinates, map_zero]

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_pair (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      ((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
          (productTorusHomologyEquiv r n).toAddEquiv)
        (circleProductHomologyEquiv (ProductTorus r) n
          (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)) :=
  productTorusHomologyEquiv_succ_apply r n a

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass_zero (r : ℕ)
    (i : Fin (r.choose 0)) :
    productTorusHomologyEquiv r 0 (coordinateTorusClass r 0 i) = Pi.single i 1 := by
  rw [coordinateTorusClass_zero, productTorusHomologyEquiv_zero]
  change
    integerBinomialZeroEquiv r
        (connectedHomologyZeroEquiv (ProductTorus r) (pointClass (0 : ProductTorus r))) =
      _
  rw [connectedHomologyZeroEquiv_pointClass]
  exact integerBinomialZeroEquiv_one_single r i

theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass (r n : ℕ)
    (i : Fin (r.choose n)) :
    productTorusHomologyEquiv r n (coordinateTorusClass r n i) = Pi.single i 1 := by
  induction r generalizing n with
  | zero =>
    cases n with
    | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero 0 i
    | succ n => exact Fin.elim0 i
  | succ r ih =>
    cases n with
    | zero => exact productTorusHomologyEquiv_coordinateTorusClass_zero (r + 1) i
    | succ n =>
      obtain ⟨j, rfl⟩ := (binomialPascalIndexEquiv r n).symm.surjective i
      cases j with
      | inl j =>
        apply (binomialModuleSuccEquiv r n).injective
        rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_omit,
          binomialModuleSuccEquiv_single_inl]
        change
          (productTorusHomologyEquiv r (n + 1) (coordinateTorusClass r (n + 1) j),
              productTorusHomologyEquiv r n 0) =
            (Pi.single j 1, 0)
        rw [ih (n + 1) j, map_zero]
      | inr j =>
        apply (binomialModuleSuccEquiv r n).injective
        rw [productTorusHomologyEquiv_succ_pair, circleCoordinates_coordinateTorusClass_take,
          binomialModuleSuccEquiv_single_inr]
        change
          (productTorusHomologyEquiv r (n + 1) 0,
              productTorusHomologyEquiv r n (coordinateTorusClass r n j)) =
            (0, Pi.single j 1)
        rw [map_zero, ih n j]

def PeriodTorusHigherHomology.coordinateTorusBasis (r n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ
      (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  (binomialCoordinateBasis r n).map (productTorusHomologyEquiv r n).symm

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusBasis_apply (r n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasis r n i = coordinateTorusClass r n i := by
  apply (productTorusHomologyEquiv r n).injective
  rw [coordinateTorusBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    binomialCoordinateBasis_apply, productTorusHomologyEquiv_coordinateTorusClass]

def PeriodTorusHigherHomology.realTorusHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology RealTorus₄ n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv flatTorusCircleHomeomorph n).trans (productTorusHomologyEquiv 4 n)

def PeriodTorusHigherHomology.periodTorusHomologyEquiv (p : PeriodDomain) (n : ℕ) :
    SingularMayerVietoris.SingularHomology p.Torus n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) n).trans
    (productTorusHomologyEquiv 4 n)

@[simp]
theorem PeriodTorusHigherHomology.realTorusHomologyEquiv_apply (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology RealTorus₄ n) :
    realTorusHomologyEquiv n a =
      productTorusHomologyEquiv 4 n
        (SingularMayerVietoris.singularHomologyMap
          (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n a) :=
  rfl

theorem PeriodTorusHigherHomology.realTorus_homology_free (n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  Module.Free.of_equiv (realTorusHomologyEquiv n).symm

theorem PeriodTorusHigherHomology.realTorus_homology_finite (n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) :=
  Module.Finite.of_surjective (realTorusHomologyEquiv n).symm.toLinearMap
    (realTorusHomologyEquiv n).symm.surjective

theorem PeriodTorusHigherHomology.realTorus_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) = Nat.choose 4 n := by
  rw [(realTorusHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 4 n

theorem PeriodTorusHigherHomology.realTorus_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology RealTorus₄ n) := by
  let := realTorus_homology_free n
  infer_instance

theorem PeriodTorusHigherHomology.realTorus_homology_subsingleton_of_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology RealTorus₄ n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (realTorusHomologyEquiv n).injective.subsingleton

theorem PeriodTorusHigherHomology.periodTorus_homology_subsingleton_of_lt (p : PeriodDomain)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularMayerVietoris.SingularHomology p.Torus n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (periodTorusHomologyEquiv p n).injective.subsingleton

def PeriodTorusHigherHomology.realTorusH4Equiv :
    SingularMayerVietoris.SingularHomology RealTorus₄ 4 ≃ₗ[ℤ] ℤ :=
  (realTorusHomologyEquiv 4).trans (integerBinomialZeroEquiv 4).symm

def PeriodTorusHigherHomology.coordinateTorusMapAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) : C(ProductTorus n, X) :=
  (e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)

def PeriodTorusHigherHomology.coordinateTorusClassAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (coordinateTorusMapAlong e n i) n
    (productTorusTopClass n)

def PeriodTorusHigherHomology.coordinateTorusBasisAlong {X : Type} [TopologicalSpace X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Module.Basis (Fin (r.choose n)) ℤ (SingularMayerVietoris.SingularHomology X n) :=
  (coordinateTorusBasis r n).map (homeomorphHomologyEquiv e n).symm

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_apply {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) (i : Fin (r.choose n)) :
    coordinateTorusBasisAlong e n i = coordinateTorusClassAlong e n i := by
  rw [coordinateTorusBasisAlong, Module.Basis.map_apply, coordinateTorusBasis_apply,
    homeomorphHomologyEquiv_symm_apply]
  change
    SingularMayerVietoris.singularHomologyMap (e.symm : C(ProductTorus r, X)) n
        (SingularMayerVietoris.singularHomologyMap (coordinateTorusMap r n i) n
          (productTorusTopClass n)) =
      SingularMayerVietoris.singularHomologyMap
        ((e.symm : C(ProductTorus r, X)).comp (coordinateTorusMap r n i)) n
        (productTorusTopClass n)
  rw [singularHomologyMap_comp]
  rfl

theorem PeriodTorusHigherHomology.coordinateTorusBasisAlong_coe {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    ⇑(coordinateTorusBasisAlong e n) = coordinateTorusClassAlong e n :=
  funext (coordinateTorusBasisAlong_apply e n)

theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_span {X : Type} [TopologicalSpace X]
    {r : ℕ} (e : X ≃ₜ ProductTorus r) (n : ℕ) :
    Submodule.span ℤ (Set.range (coordinateTorusClassAlong e n)) = ⊤ := by
  simpa only [coordinateTorusBasisAlong_coe] using (coordinateTorusBasisAlong e n).span_eq

theorem PeriodTorusHigherHomology.surjective_of_coordinateTorusClassAlong_mem_range {X : Type}
    [TopologicalSpace X] {r : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : X ≃ₜ ProductTorus r) (n : ℕ) (f : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hf : ∀ i : Fin (r.choose n), coordinateTorusClassAlong e n i ∈ LinearMap.range f) :
    Function.Surjective f := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← coordinateTorusClassAlong_span e n]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hf i

@[simp]
theorem PeriodTorusHigherHomology.torusMatrixMap_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x y : ProductTorus n) : torusMatrixMap A (x + y) = torusMatrixMap A x + torusMatrixMap A y :=
  (torusMatrixLinearMap A).map_add x y

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusMap_add (r n : ℕ) (i : Fin (r.choose n))
    (x y : ProductTorus n) :
    coordinateTorusMap r n i (x + y) = coordinateTorusMap r n i x + coordinateTorusMap r n i y := by
  simpa only [coordinateTorusMap_eq_torusMatrixMap] using
    torusMatrixMap_add (coordinateTorusMatrix r n i) x y

theorem PeriodTorusHigherHomology.homeomorph_symm_add_of_add {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Add X] [Add Y] (e : X ≃ₜ Y) (he : ∀ x y, e (x + y) = e x + e y)
    (x y : Y) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem PeriodTorusHigherHomology.coordinateTorusMapAlong_add {X : Type} [TopologicalSpace X]
    [Add X] {r : ℕ} (e : X ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y) (n : ℕ)
    (i : Fin (r.choose n)) (x y : ProductTorus n) :
    coordinateTorusMapAlong e n i (x + y) =
      coordinateTorusMapAlong e n i x + coordinateTorusMapAlong e n i y := by
  change
    e.symm (coordinateTorusMap r n i (x + y)) =
      e.symm (coordinateTorusMap r n i x) + e.symm (coordinateTorusMap r n i y)
  rw [coordinateTorusMap_add]
  exact homeomorph_symm_add_of_add e he _ _

abbrev PeriodTorusHigherHomologyExterior.latticeExterior (n : ℕ) :=
  ⋀[ℤ]^n Lattice

def PeriodTorusHigherHomologyExterior.latticeBasis : Module.Basis (Fin 4) ℤ Lattice :=
  Pi.basisFun ℤ (Fin 4)

def PeriodTorusHigherHomologyExterior.latticeExteriorBasis (n : ℕ) :
    Module.Basis (Set.powersetCard (Fin 4) n) ℤ (latticeExterior n) :=
  standardExteriorBasis 4 n

theorem PeriodTorusHigherHomologyExterior.pairIndices_strictMono (i : Fin 6) :
    StrictMono (LocalSystemMatrices.pairIndices i) := by fin_cases i <;> decide

theorem PeriodTorusHigherHomologyExterior.tripleIndices_strictMono (i : Fin 4) :
    StrictMono (LocalSystemMatrices.tripleIndices i) := by fin_cases i <;> decide

theorem PeriodTorusHigherHomologyExterior.pairIndices_injective :
    Function.Injective LocalSystemMatrices.pairIndices := by decide

theorem PeriodTorusHigherHomologyExterior.tripleIndices_injective :
    Function.Injective LocalSystemMatrices.tripleIndices := by decide

def PeriodTorusHigherHomologyExterior.pairEmbedding (i : Fin 6) : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (LocalSystemMatrices.pairIndices i) (pairIndices_strictMono i)

def PeriodTorusHigherHomologyExterior.tripleEmbedding (i : Fin 4) : Fin 3 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (LocalSystemMatrices.tripleIndices i) (tripleIndices_strictMono i)

def PeriodTorusHigherHomologyExterior.pairSubset (i : Fin 6) : Set.powersetCard (Fin 4) 2 :=
  Set.powersetCard.ofFinEmbEquiv (pairEmbedding i)

def PeriodTorusHigherHomologyExterior.tripleSubset (i : Fin 4) : Set.powersetCard (Fin 4) 3 :=
  Set.powersetCard.ofFinEmbEquiv (tripleEmbedding i)

@[simp]
theorem PeriodTorusHigherHomologyExterior.pairSubset_ordered (i : Fin 6) :
    (Set.powersetCard.ofFinEmbEquiv.symm (pairSubset i) : Fin 2 → Fin 4) =
      LocalSystemMatrices.pairIndices i := by
  rw [pairSubset, Equiv.symm_apply_apply]
  rfl

@[simp]
theorem PeriodTorusHigherHomologyExterior.tripleSubset_ordered (i : Fin 4) :
    (Set.powersetCard.ofFinEmbEquiv.symm (tripleSubset i) : Fin 3 → Fin 4) =
      LocalSystemMatrices.tripleIndices i := by
  rw [tripleSubset, Equiv.symm_apply_apply]
  rfl

theorem PeriodTorusHigherHomologyExterior.pairSubset_injective : Function.Injective pairSubset := by
  intro i j hij
  apply pairIndices_injective
  simpa only [pairSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 2 → Fin 4)) hij

theorem PeriodTorusHigherHomologyExterior.tripleSubset_injective :
    Function.Injective tripleSubset := by
  intro i j hij
  apply tripleIndices_injective
  simpa only [tripleSubset_ordered] using
    congrArg (fun s => (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 3 → Fin 4)) hij

theorem PeriodTorusHigherHomologyExterior.pairSubset_bijective : Function.Bijective pairSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨pairSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 4 2 = 6 by decide] using
    (Set.powersetCard.card (Fin 4) 2).symm

theorem PeriodTorusHigherHomologyExterior.tripleSubset_bijective :
    Function.Bijective tripleSubset := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨tripleSubset_injective, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.choose 4 3 = 4 by decide] using
    (Set.powersetCard.card (Fin 4) 3).symm

def PeriodTorusHigherHomologyExterior.pairSubsetEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective pairSubset pairSubset_bijective

def PeriodTorusHigherHomologyExterior.tripleSubsetEquiv : Fin 4 ≃ Set.powersetCard (Fin 4) 3 :=
  Equiv.ofBijective tripleSubset tripleSubset_bijective

def PeriodTorusHigherHomologyExterior.squareBasis : Module.Basis (Fin 6) ℤ (latticeExterior 2) :=
  (latticeExteriorBasis 2).reindex pairSubsetEquiv.symm

def PeriodTorusHigherHomologyExterior.cubeBasis : Module.Basis (Fin 4) ℤ (latticeExterior 3) :=
  (latticeExteriorBasis 3).reindex tripleSubsetEquiv.symm

theorem PeriodTorusHigherHomologyExterior.squareBasis_apply (i : Fin 6) :
    squareBasis i = exteriorPower.ιMulti ℤ 2 (latticeBasis ∘ LocalSystemMatrices.pairIndices i) :=
  by
  rw [squareBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 4)).exteriorPower 2 (pairSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, pairSubset_ordered]
  rfl

theorem PeriodTorusHigherHomologyExterior.cubeBasis_apply (i : Fin 4) :
    cubeBasis i = exteriorPower.ιMulti ℤ 3 (latticeBasis ∘ LocalSystemMatrices.tripleIndices i) :=
  by
  rw [cubeBasis, Module.Basis.reindex_apply]
  change (Pi.basisFun ℤ (Fin 4)).exteriorPower 3 (tripleSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, tripleSubset_ordered]
  rfl

def PeriodTorusHigherHomologyExterior.squareCoordinates : latticeExterior 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  squareBasis.equivFun

def PeriodTorusHigherHomologyExterior.cubeCoordinates : latticeExterior 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  cubeBasis.equivFun

@[simp]
theorem PeriodTorusHigherHomologyExterior.squareCoordinates_apply (x : latticeExterior 2)
    (i : Fin 6) : squareCoordinates x i = squareBasis.repr x i :=
  congrFun (squareBasis.equivFun_apply x) i

@[simp]
theorem PeriodTorusHigherHomologyExterior.cubeCoordinates_apply (x : latticeExterior 3)
    (i : Fin 4) : cubeCoordinates x i = cubeBasis.repr x i :=
  congrFun (cubeBasis.equivFun_apply x) i

theorem PeriodTorusHigherHomologyExterior.latticeExterior_finrank (n : ℕ) :
    Module.finrank ℤ (latticeExterior n) = Nat.choose 4 n := by
  rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis latticeBasis, Fintype.card_fin]

theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_mem_range_latticeWedgeTwo {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 2)) :
    coordinateTorusClassAlong e 2 i ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c) :=
  map_topClass_two_mem_range_latticeWedgeTwo c hc (coordinateTorusMapAlong e 2 i)
    (coordinateTorusMapAlong_add e he 2 i)

theorem PeriodTorusHigherHomology.coordinateTorusClassAlong_mem_range_latticeWedgeThree {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c)
    (i : Fin (r.choose 3)) :
    coordinateTorusClassAlong e 3 i ∈
      LinearMap.range (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c) :=
  map_topClass_three_mem_range_latticeWedgeThree c hc (coordinateTorusMapAlong e 3 i)
    (coordinateTorusMapAlong_add e he 3 i)

theorem PeriodTorusHigherHomology.latticeWedgeTwo_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 2
    (PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo G c)
    (coordinateTorusClassAlong_mem_range_latticeWedgeTwo e he c hc)

theorem PeriodTorusHigherHomology.latticeWedgeThree_surjective_of_torusHomeomorph {G : Type}
    [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology G 2)] {r : ℕ}
    (e : G ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (c : Lattice →ₗ[ℤ] SingularMayerVietoris.SingularHomology G 1) (hc : Function.Surjective c) :
    Function.Surjective (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c) :=
  surjective_of_coordinateTorusClassAlong_mem_range e 3
    (PeriodTorusHigherHomologyPontryagin.latticeWedgeThree G c)
    (coordinateTorusClassAlong_mem_range_latticeWedgeThree e he c hc)

def PeriodTorusHigherHomologyExterior.exteriorMap (n : ℕ) (T : LatticeMatrix) :
    latticeExterior n →ₗ[ℤ] latticeExterior n :=
  exteriorPower.map n T.mulVecLin

theorem PeriodTorusHigherHomologyExterior.squareMap_coefficient (T : LatticeMatrix)
    (i j : Fin 6) :
    squareBasis.repr (exteriorMap 2 T (squareBasis j)) i =
      LocalSystemMatrices.exteriorSquare T i j := by
  rw [squareBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change
    (standardExteriorBasis 4 2).repr
        (exteriorPower.map 2 T.mulVecLin (standardExteriorBasis 4 2 (pairSubset j)))
        (pairSubset i) =
      _
  rw [standardExterior_map_coefficient, pairSubset_ordered, pairSubset_ordered]
  rfl

theorem PeriodTorusHigherHomologyExterior.cubeMap_coefficient (T : LatticeMatrix) (i j : Fin 4) :
    cubeBasis.repr (exteriorMap 3 T (cubeBasis j)) i = LocalSystemMatrices.exteriorCube T i j := by
  rw [cubeBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply]
  change
    (standardExteriorBasis 4 3).repr
        (exteriorPower.map 3 T.mulVecLin (standardExteriorBasis 4 3 (tripleSubset j)))
        (tripleSubset i) =
      _
  rw [standardExterior_map_coefficient, tripleSubset_ordered, tripleSubset_ordered]
  rfl

theorem PeriodTorusHigherHomologyExterior.squareMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix squareBasis squareBasis (exteriorMap 2 T) =
      LocalSystemMatrices.exteriorSquare T := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact squareMap_coefficient T i j

theorem PeriodTorusHigherHomologyExterior.cubeMap_toMatrix (T : LatticeMatrix) :
    LinearMap.toMatrix cubeBasis cubeBasis (exteriorMap 3 T) =
      LocalSystemMatrices.exteriorCube T := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact cubeMap_coefficient T i j

theorem PeriodTorusHigherHomologyExterior.squareCoordinates_map (T : LatticeMatrix)
    (x : latticeExterior 2) :
    squareCoordinates (exteriorMap 2 T x) =
      LocalSystemMatrices.exteriorSquare T *ᵥ squareCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr squareBasis squareBasis (exteriorMap 2 T) x
  rw [squareMap_toMatrix] at h
  simpa only [squareCoordinates, Module.Basis.equivFun_apply] using h.symm

theorem PeriodTorusHigherHomologyExterior.cubeCoordinates_map (T : LatticeMatrix)
    (x : latticeExterior 3) :
    cubeCoordinates (exteriorMap 3 T x) =
      LocalSystemMatrices.exteriorCube T *ᵥ cubeCoordinates x := by
  have h := LinearMap.toMatrix_mulVec_repr cubeBasis cubeBasis (exteriorMap 3 T) x
  rw [cubeMap_toMatrix] at h
  simpa only [cubeCoordinates, Module.Basis.equivFun_apply] using h.symm

def PeriodTorusHigherHomology.coordinateH1Add (n : ℕ) :
    (Fin n → ℤ) →+ FirstHurewicz.SingularH1 (ProductTorus n)
    where
  toFun v := ∑ i, v i • FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))
  map_zero' := by simp only [Pi.zero_apply, zero_zsmul, Finset.sum_const_zero]
  map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

def PeriodTorusHigherHomology.coordinateH1 (n : ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] FirstHurewicz.SingularH1 (ProductTorus n) :=
  { toFun := coordinateH1Add n
    map_add' := (coordinateH1Add n).map_add
    map_smul' r
      a := by
      convert! (coordinateH1Add n).map_zsmul r a using 1
      exact int_smul_eq_zsmul .. }

@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_basis (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.basisFun ℤ (Fin n) i) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simp [coordinateH1, coordinateH1Add, Pi.basisFun_apply, Pi.single_apply]

@[simp]
theorem PeriodTorusHigherHomology.coordinateH1_single (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.single i 1) =
      FirstHurewicz.loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simpa only [Pi.basisFun_apply] using coordinateH1_basis n i

theorem PeriodTorusHigherHomology.coordinateH1_four_eq_periodMarking (p : PeriodDomain) :
    coordinateH1 4 =
      (FirstHurewicz.inducedHomology (periodTorusCircleHomeomorph p : C(_, _))).comp
        p.singularH1Equiv.symm.toLinearMap := by
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro i
  rw [coordinateH1_basis, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [p.singularH1Equiv_symm_apply, periodTorusCircle_inducedHomology_periodLoop]
  simp only [Pi.basisFun_apply]

theorem PeriodTorusHigherHomology.coordinateH1_four_apply (p : PeriodDomain) (v : Lattice) :
    coordinateH1 4 v = FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [coordinateH1_four_eq_periodMarking p, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [p.singularH1Equiv_symm_apply, periodTorusCircle_inducedHomology_periodLoop]

theorem PeriodTorusHigherHomology.coordinateH1_four_bijective (p : PeriodDomain) :
    Function.Bijective (coordinateH1 4) := by
  rw [coordinateH1_four_eq_periodMarking p]
  exact
    (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) 1).bijective.comp
      p.singularH1Equiv.symm.bijective

def PeriodTorusHigherHomology.coordinateH1FourEquiv (p : PeriodDomain) :
    Lattice ≃ₗ[ℤ] FirstHurewicz.SingularH1 (ProductTorus 4) :=
  LinearEquiv.ofBijective (coordinateH1 4) (coordinateH1_four_bijective p)

theorem PeriodTorusHigherHomology.coordinateH1_matrix_natural (p : PeriodDomain)
    (A : LatticeMatrix) (v : Lattice) :
    FirstHurewicz.inducedHomology (torusMatrixMap A) (coordinateH1 4 v) =
      coordinateH1 4 (A *ᵥ v) := by
  rw [coordinateH1_four_apply p, coordinateH1_four_apply p,
    torusMatrixMap_coordinatePeriodHomology]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.coordinateTorusWedgeTwo :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 := by
  letI := productTorus_homology_torsionFree 4 2
  exact PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo (ProductTorus 4) (coordinateH1 4)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def PeriodTorusHigherHomology.coordinateTorusWedgeThree :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 := by
  letI := productTorus_homology_torsionFree 4 2
  exact PeriodTorusHigherHomologyPontryagin.latticeWedgeThree (ProductTorus 4) (coordinateH1 4)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti (v : Fin 2 → Lattice) :
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 4) (coordinateH1 4 (v 0))
        (coordinateH1 4 (v 1)) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_apply_ιMulti (ProductTorus 4)
      (coordinateH1 4) v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_apply_ιMulti (v : Fin 3 → Lattice) :
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 4) (coordinateH1 4 (v 0))
        (coordinateH1 4 (v 1)) (coordinateH1 4 (v 2)) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_apply_ιMulti (ProductTorus 4)
      (coordinateH1 4) v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_apply_ιMulti_periodLoops
    (p : PeriodDomain) (v : Fin 2 → Lattice) :
    coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v) =
      PeriodTorusHigherHomologyPontryagin.product11 (ProductTorus 4)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 1))) := by
  rw [coordinateTorusWedgeTwo_apply_ιMulti, coordinateH1_four_apply p, coordinateH1_four_apply p]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_apply_ιMulti_periodLoops
    (p : PeriodDomain) (v : Fin 3 → Lattice) :
    coordinateTorusWedgeThree (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 4)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 2))) := by
  rw [coordinateTorusWedgeThree_apply_ιMulti, coordinateH1_four_apply p,
    coordinateH1_four_apply p, coordinateH1_four_apply p]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_matrix (p : PeriodDomain)
    (A : LatticeMatrix) :
    (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2).comp
        coordinateTorusWedgeTwo =
      coordinateTorusWedgeTwo.comp (exteriorPower.map 2 A.mulVecLin) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeTwo_natural (torusMatrixMap A)
      (fun x y => (torusMatrixLinearMap A).map_add x y) (coordinateH1 4) (coordinateH1 4)
      A.mulVecLin (coordinateH1_matrix_natural p A)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_matrix (p : PeriodDomain)
    (A : LatticeMatrix) :
    (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3).comp
        coordinateTorusWedgeThree =
      coordinateTorusWedgeThree.comp (exteriorPower.map 3 A.mulVecLin) := by
  let := productTorus_homology_torsionFree 4 2
  exact
    PeriodTorusHigherHomologyPontryagin.latticeWedgeThree_natural (torusMatrixMap A)
      (fun x y => (torusMatrixLinearMap A).map_add x y) (coordinateH1 4) (coordinateH1 4)
      A.mulVecLin (coordinateH1_matrix_natural p A)

theorem PeriodTorusHigherHomology.coordinateH1_four_surjective :
    Function.Surjective (coordinateH1 4) :=
  (coordinateH1_four_bijective (Elliptic.examplePeriod .four)).surjective

theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_surjective :
    Function.Surjective coordinateTorusWedgeTwo := by
  let := productTorus_homology_torsionFree 4 2
  exact
    latticeWedgeTwo_surjective_of_torusHomeomorph (Homeomorph.refl (ProductTorus 4))
      (fun _ _ => rfl) (coordinateH1 4) coordinateH1_four_surjective

theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_surjective :
    Function.Surjective coordinateTorusWedgeThree := by
  let := productTorus_homology_torsionFree 4 2
  exact
    latticeWedgeThree_surjective_of_torusHomeomorph (Homeomorph.refl (ProductTorus 4))
      (fun _ _ => rfl) (coordinateH1 4) coordinateH1_four_surjective

theorem PeriodTorusHigherHomology.coordinateTorusWedgeTwo_bijective :
    Function.Bijective coordinateTorusWedgeTwo := by
  let := productTorus_homology_free 4 2
  let := productTorus_homology_finite 4 2
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le coordinateTorusWedgeTwo
      coordinateTorusWedgeTwo_surjective
  rw [PeriodTorusHigherHomologyExterior.latticeExterior_finrank, productTorus_homology_finrank]

theorem PeriodTorusHigherHomology.coordinateTorusWedgeThree_bijective :
    Function.Bijective coordinateTorusWedgeThree := by
  let := productTorus_homology_free 4 3
  let := productTorus_homology_finite 4 3
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le coordinateTorusWedgeThree
      coordinateTorusWedgeThree_surjective
  rw [PeriodTorusHigherHomologyExterior.latticeExterior_finrank, productTorus_homology_finrank]

def PeriodTorusHigherHomology.coordinateTorusWedgeTwoEquiv :
    PeriodTorusHigherHomologyExterior.latticeExterior 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 :=
  LinearEquiv.ofBijective coordinateTorusWedgeTwo coordinateTorusWedgeTwo_bijective

def PeriodTorusHigherHomology.coordinateTorusWedgeThreeEquiv :
    PeriodTorusHigherHomologyExterior.latticeExterior 3 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 :=
  LinearEquiv.ofBijective coordinateTorusWedgeThree coordinateTorusWedgeThree_bijective

def PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 ≃ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 2 :=
  coordinateTorusWedgeTwoEquiv.symm

def PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 ≃ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 3 :=
  coordinateTorusWedgeThreeEquiv.symm

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_wedge
    (v : PeriodTorusHigherHomologyExterior.latticeExterior 2) :
    coordinateTorusH2ExteriorEquiv (coordinateTorusWedgeTwo v) = v :=
  coordinateTorusWedgeTwoEquiv.symm_apply_apply v

@[simp]
theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_wedge
    (v : PeriodTorusHigherHomologyExterior.latticeExterior 3) :
    coordinateTorusH3ExteriorEquiv (coordinateTorusWedgeThree v) = v :=
  coordinateTorusWedgeThreeEquiv.symm_apply_apply v

theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_symm_ιMulti
    (v : Fin 3 → Lattice) :
    coordinateTorusH3ExteriorEquiv.symm (exteriorPower.ιMulti ℤ 3 v) =
      PeriodTorusHigherHomologyPontryagin.tripleProduct (ProductTorus 4)
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 0)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 1)))
        (FirstHurewicz.loopHomologyClass (coordinatePeriodLoop 4 (v 2))) :=
  coordinateTorusWedgeThree_apply_ιMulti_periodLoops (Elliptic.examplePeriod .four) v

theorem PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a) =
      exteriorPower.map 2 A.mulVecLin (coordinateTorusH2ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeTwo_surjective a
  have h :=
    LinearMap.congr_fun (coordinateTorusWedgeTwo_matrix (Elliptic.examplePeriod .four) A) v
  change
    SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 (coordinateTorusWedgeTwo v) =
      coordinateTorusWedgeTwo (exteriorPower.map 2 A.mulVecLin v) at h
  rw [h, coordinateTorusH2ExteriorEquiv_wedge, coordinateTorusH2ExteriorEquiv_wedge]

theorem PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a) =
      exteriorPower.map 3 A.mulVecLin (coordinateTorusH3ExteriorEquiv a) := by
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeThree_surjective a
  have h :=
    LinearMap.congr_fun (coordinateTorusWedgeThree_matrix (Elliptic.examplePeriod .four) A) v
  change
    SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 (coordinateTorusWedgeThree v) =
      coordinateTorusWedgeThree (exteriorPower.map 3 A.mulVecLin v) at h
  rw [h, coordinateTorusH3ExteriorEquiv_wedge, coordinateTorusH3ExteriorEquiv_wedge]

def PeriodTorusHigherHomology.coordinateTorusH2Coordinates :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  coordinateTorusH2ExteriorEquiv.trans PeriodTorusHigherHomologyExterior.squareCoordinates

def PeriodTorusHigherHomology.coordinateTorusH3Coordinates :
    SingularMayerVietoris.SingularHomology (ProductTorus 4) 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  coordinateTorusH3ExteriorEquiv.trans PeriodTorusHigherHomologyExterior.cubeCoordinates

theorem PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 2) :
    coordinateTorusH2Coordinates
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a) =
      LocalSystemMatrices.exteriorSquare A *ᵥ coordinateTorusH2Coordinates a := by
  change
    PeriodTorusHigherHomologyExterior.squareCoordinates
        (coordinateTorusH2ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 2 a)) =
      _
  rw [coordinateTorusH2ExteriorEquiv_matrix]
  exact
    PeriodTorusHigherHomologyExterior.squareCoordinates_map A (coordinateTorusH2ExteriorEquiv a)

theorem PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus 4) 3) :
    coordinateTorusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a) =
      LocalSystemMatrices.exteriorCube A *ᵥ coordinateTorusH3Coordinates a := by
  change
    PeriodTorusHigherHomologyExterior.cubeCoordinates
        (coordinateTorusH3ExteriorEquiv
          (SingularMayerVietoris.singularHomologyMap (torusMatrixMap A) 3 a)) =
      _
  rw [coordinateTorusH3ExteriorEquiv_matrix]
  exact PeriodTorusHigherHomologyExterior.cubeCoordinates_map A (coordinateTorusH3ExteriorEquiv a)

def CuspCoinvariants.torusDifference (q : ℕ) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q :=
  SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) q -
    LinearMap.id

@[simp]
theorem CuspCoinvariants.torusDifference_apply (q : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q) :
    torusDifference q a =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) q
          a -
        a :=
  rfl

theorem CuspCoinvariants.torusDifference_two_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates (torusDifference 2 a) =
      squareDifference (PeriodTorusHigherHomology.coordinateTorusH2Coordinates a) := by
  rw [torusDifference_apply, map_sub,
    PeriodTorusHigherHomology.coordinateTorusH2Coordinates_matrix]
  simp only [squareDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    PeriodTorusHigherHomologyExterior.squareM₀]

theorem CuspCoinvariants.torusDifference_three_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates (torusDifference 3 a) =
      cubeDifference (PeriodTorusHigherHomology.coordinateTorusH3Coordinates a) := by
  rw [torusDifference_apply, map_sub,
    PeriodTorusHigherHomology.coordinateTorusH3Coordinates_matrix]
  simp only [cubeDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    PeriodTorusHigherHomologyExterior.cubeM₀]

abbrev CuspCoinvariants.TorusCoinvariants (q : ℕ) :=
  SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) q ⧸
    LinearMap.range (torusDifference q)

def CuspCoinvariants.torusTwoCoinvariantEquiv : TorusCoinvariants 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((quotientRangeEquiv PeriodTorusHigherHomology.coordinateTorusH2Coordinates (torusDifference 2)
          squareDifference torusDifference_two_coordinates).toAddEquiv.trans
      squareCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

def CuspCoinvariants.torusThreeCoinvariantEquiv : TorusCoinvariants 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((quotientRangeEquiv PeriodTorusHigherHomology.coordinateTorusH3Coordinates (torusDifference 3)
          cubeDifference torusDifference_three_coordinates).toAddEquiv.trans
      cubeCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

def CuspSpecialization.coordinateTorusH1Coordinates :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1 ≃ₗ[ℤ]
      (Fin 4 → ℤ) :=
  (PeriodTorusHigherHomology.coordinateH1FourEquiv (Elliptic.examplePeriod .four)).symm

@[simp]
theorem CuspSpecialization.coordinateTorusH1Coordinates_coordinateH1 (v : Fin 4 → ℤ) :
    coordinateTorusH1Coordinates (PeriodTorusHigherHomology.coordinateH1 4 v) = v :=
  (PeriodTorusHigherHomology.coordinateH1FourEquiv
        (Elliptic.examplePeriod .four)).symm_apply_apply
    v

theorem CuspSpecialization.coordinateTorusH1Coordinates_matrix (A : LatticeMatrix)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    coordinateTorusH1Coordinates
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap A) 1
          a) =
      A *ᵥ coordinateTorusH1Coordinates a := by
  obtain ⟨v, hv⟩ :=
    (PeriodTorusHigherHomology.coordinateH1FourEquiv (Elliptic.examplePeriod .four)).surjective a
  change PeriodTorusHigherHomology.coordinateH1 4 v = a at hv
  rw [← hv, SingularMayerVietoris.singularHomologyMap_one,
    PeriodTorusHigherHomology.coordinateH1_matrix_natural (Elliptic.examplePeriod .four),
    coordinateTorusH1Coordinates_coordinateH1, coordinateTorusH1Coordinates_coordinateH1]

theorem CuspSpecialization.torusDifference_one_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 1) :
    coordinateTorusH1Coordinates (CuspCoinvariants.torusDifference 1 a) =
      CuspCoinvariants.oneDifference (coordinateTorusH1Coordinates a) := by
  rw [CuspCoinvariants.torusDifference_apply, map_sub, coordinateTorusH1Coordinates_matrix]
  simp only [CuspCoinvariants.oneDifference, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

def CuspSpecialization.torusOneCoinvariantEquiv :
    CuspCoinvariants.TorusCoinvariants 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((CuspCoinvariants.quotientRangeEquiv coordinateTorusH1Coordinates
          (CuspCoinvariants.torusDifference 1) CuspCoinvariants.oneDifference
          torusDifference_one_coordinates).toAddEquiv.trans
      CuspCoinvariants.oneCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

def CuspCentralHomology.baseTorusPoint (y : CuspHoneycombTiling.Plane) :
    PeriodTorusHigherHomology.ProductTorus 2 :=
  PeriodTorusHigherHomology.coordinateProjection 2 (CuspSpecialization.sourceBaseMarking y)

@[simp]
theorem CuspCentralHomology.baseTorusPoint_apply (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint y =
      PeriodTorusHigherHomology.coordinateProjection 2 (-ToricSpace.realCuspVector y) :=
  rfl

theorem CuspCentralHomology.baseTorusPoint_continuous : Continuous baseTorusPoint :=
  (PeriodTorusHigherHomology.coordinateProjection_continuous 2).comp
    CuspSpecialization.sourceBaseMarking.continuous

theorem CuspCentralHomology.baseTorusPoint_surjective : Function.Surjective baseTorusPoint :=
  (PeriodTorusHigherHomology.coordinateProjection_surjective 2).comp
    CuspSpecialization.sourceBaseMarking.surjective

theorem CuspCentralHomology.baseTorusPoint_deck (v : Fin 2 → ℤ) (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint (y + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v)) =
      baseTorusPoint y := by
  apply (CuspSpecialization.sourceCoordinateProjection_eq_iff _ _).mpr
  exact ⟨v, CuspSpecialization.sourceBaseMarking_deck v y⟩

@[simp]
theorem CuspCentralHomology.baseTorusPoint_realCuspVector (y : CuspHoneycombTiling.Plane) :
    baseTorusPoint (ToricSpace.realCuspVector y) =
      PeriodTorusHigherHomology.coordinateProjection 2 y := by
  change
    PeriodTorusHigherHomology.coordinateProjection 2
        (CuspSpecialization.sourceBaseMarking (CuspSpecialization.sourceBaseMarking.symm y)) =
      _
  rw [Homeomorph.apply_symm_apply]

theorem CuspCentralHomology.baseTorusPoint_eq_iff (y z : CuspHoneycombTiling.Plane) :
    baseTorusPoint y = baseTorusPoint z ↔
      ∃ v : Fin 2 → ℤ, y = z + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (CuspSpecialization.sourceCoordinateProjection_eq_iff _ _).mp h
    refine ⟨v, CuspSpecialization.sourceBaseMarking.injective ?_⟩
    rw [CuspSpecialization.sourceBaseMarking_deck]
    exact hv
  · rintro ⟨v, rfl⟩
    exact baseTorusPoint_deck v z

private theorem CuspCentralHomology.baseTorusPoint_eq_of_collapse_eq_mo1973_14352
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (p q : CuspHoneycomb.PhasePlane)
    (h :
      CuspHoneycomb.honeycombCollapseMap C r hr p = CuspHoneycomb.honeycombCollapseMap C r hr q) :
    baseTorusPoint p.2 = baseTorusPoint q.2 := by
  obtain ⟨v, hv, _⟩ := (CuspHoneycomb.honeycombCollapseMap_eq_iff C r hr p q).mp h
  rw [hv, baseTorusPoint_deck]

def CuspCentralHomology.baseTorusProjection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    CuspRetraction.QuotientCentralFibre C r → PeriodTorusHigherHomology.ProductTorus 2 :=
  CuspHoneycombHexagon.CommonFibres.descend (CuspHoneycomb.honeycombCollapseMap C r hr)
    (fun p => baseTorusPoint p.2) (CuspHoneycomb.honeycombCollapseMap_surjective C r hr)

@[simp]
theorem CuspCentralHomology.baseTorusProjection_honeycombCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (p : CuspHoneycomb.PhasePlane) :
    baseTorusProjection C r hr (CuspHoneycomb.honeycombCollapseMap C r hr p) =
      baseTorusPoint p.2 :=
  CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
    (baseTorusPoint_eq_of_collapse_eq_mo1973_14352 C r hr) p

theorem CuspCentralHomology.baseTorusProjection_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Continuous (baseTorusProjection C r hr) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous _ _ _
    (CuspHoneycomb.honeycombCollapseMap_isQuotientMap C r hr hC)
    (baseTorusPoint_continuous.comp continuous_snd)
    (baseTorusPoint_eq_of_collapse_eq_mo1973_14352 C r hr)

def CuspCentralHomology.baseTorusProjectionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    C(CuspRetraction.QuotientCentralFibre C r, PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨baseTorusProjection C r hr, baseTorusProjection_continuous C r hr hC⟩

@[simp]
theorem CuspCentralHomology.baseTorusProjection_productCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r)
    (p : ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :
    baseTorusProjection C r hr (CuspSpecialization.productCollapse C r hr p) = p.2 := by
  rcases p with ⟨u, t⟩
  obtain ⟨y, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 2 t
  rw [CuspSpecialization.productCollapse_coordinateProjection,
    baseTorusProjection_honeycombCollapseMap]
  exact baseTorusPoint_realCuspVector y

def CuspCentralHomology.baseTorusSection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    C(PeriodTorusHigherHomology.ProductTorus 2, CuspRetraction.QuotientCentralFibre C r)
    where
  toFun t := CuspSpecialization.productCollapse C r hr (1, t)
  continuous_toFun :=
    (CuspSpecialization.productCollapse C r hr).continuous.comp
      (continuous_const.prodMk continuous_id)

@[simp]
theorem CuspCentralHomology.baseTorusProjection_section (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (t : PeriodTorusHigherHomology.ProductTorus 2) :
    baseTorusProjection C r hr (baseTorusSection C r hr t) = t :=
  baseTorusProjection_productCollapse C r hr (1, t)

abbrev CuspCentralHomology.Theta :=
  Suspension (Fin 3)

def CuspCentralHomology.thetaEdgeIndex (j : Fin 3) : Fin 6 :=
  j.castLE (by decide)

def CuspCentralHomology.thetaCircleInclusion (j : Fin 3) (z : Circle) : ThreeCircles :=
  ![Sum.inl z, Sum.inr (Sum.inl z), Sum.inr (Sum.inr z)] j

theorem CuspCentralHomology.thetaCircleInclusion_continuous (j : Fin 3) :
    Continuous (thetaCircleInclusion j) := by
  fin_cases j
  · exact continuous_inl
  · exact continuous_inr.comp continuous_inl
  · exact continuous_inr.comp continuous_inr

def CuspCentralHomology.thetaCharacterMap : C(ToricSpace.CompactFibreTorus × Fin 3, ThreeCircles)
    where
  toFun p := thetaCircleInclusion p.2 (hexagonCharacter (thetaEdgeIndex p.2) p.1)
  continuous_toFun :=
    continuous_prod_of_discrete_right.mpr fun j =>
      (thetaCircleInclusion_continuous j).comp
        (edgeCharacter_continuous (ToricComponent.hexagonRay (thetaEdgeIndex j)))

private def CuspCentralHomology.thetaCharacterCollapseFun_mo1973_14386
    (p : ToricSpace.CompactFibreTorus × Theta) : ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid (Fin 3))
    (fun q => Suspension.mk q.1 (thetaCharacterMap (p.1, q.2)))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hj⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (by rw [hj]))⟩)
    p.2

private theorem CuspCentralHomology.thetaCharacterCollapseFun_continuous_mo1973_14387 :
    Continuous thetaCharacterCollapseFun_mo1973_14386 := by
  apply (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_lift_prod_right
  change
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × (unitInterval × Fin 3) =>
        Suspension.mk p.2.1 (thetaCharacterMap (p.1, p.2.2)))
  exact
    Suspension.continuous_mk.comp
      ((continuous_fst.comp continuous_snd).prodMk
        (thetaCharacterMap.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))

def CuspCentralHomology.thetaCharacterCollapse :
    C(ToricSpace.CompactFibreTorus × Theta, ThreeCircleSuspension) :=
  ⟨thetaCharacterCollapseFun_mo1973_14386, thetaCharacterCollapseFun_continuous_mo1973_14387⟩

@[simp]
theorem CuspCentralHomology.thetaCharacterCollapse_mk (u : ToricSpace.CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaCharacterCollapse (u, Suspension.mk t j) =
      Suspension.mk t (thetaCircleInclusion j (hexagonCharacter (thetaEdgeIndex j) u)) :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaCharacterCollapse_height
    (p : ToricSpace.CompactFibreTorus × Theta) :
    Suspension.height (thetaCharacterCollapse p) = Suspension.height p.2 := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rfl

def CuspCentralHomology.thetaNorth : Set (ToricSpace.CompactFibreTorus × Theta) :=
  Prod.snd ⁻¹' Suspension.northOpen

def CuspCentralHomology.thetaSouth : Set (ToricSpace.CompactFibreTorus × Theta) :=
  Prod.snd ⁻¹' Suspension.southOpen

@[simp]
theorem CuspCentralHomology.mem_thetaNorth (p : ToricSpace.CompactFibreTorus × Theta) :
    p ∈ thetaNorth ↔ (Suspension.height p.2 : ℝ) < 3 / 4 :=
  Iff.rfl

@[simp]
theorem CuspCentralHomology.mem_thetaSouth (p : ToricSpace.CompactFibreTorus × Theta) :
    p ∈ thetaSouth ↔ 1 / 4 < (Suspension.height p.2 : ℝ) :=
  Iff.rfl

theorem CuspCentralHomology.thetaNorth_isOpen : IsOpen thetaNorth :=
  Suspension.northOpen_isOpen.preimage continuous_snd

theorem CuspCentralHomology.thetaSouth_isOpen : IsOpen thetaSouth :=
  Suspension.southOpen_isOpen.preimage continuous_snd

theorem CuspCentralHomology.theta_open_cover : thetaNorth ∪ thetaSouth = Set.univ := by
  rw [thetaNorth, thetaSouth, ← Set.preimage_union, Suspension.open_cover, Set.preimage_univ]

theorem CuspCentralHomology.thetaCharacterCollapse_preimage_north :
    thetaCharacterCollapse ⁻¹' Suspension.northOpen = thetaNorth := by
  ext p
  simp only [Set.mem_preimage, Suspension.mem_northOpen, mem_thetaNorth,
    thetaCharacterCollapse_height]

theorem CuspCentralHomology.thetaCharacterCollapse_preimage_south :
    thetaCharacterCollapse ⁻¹' Suspension.southOpen = thetaSouth := by
  ext p
  simp only [Set.mem_preimage, Suspension.mem_southOpen, mem_thetaSouth,
    thetaCharacterCollapse_height]

theorem CuspCentralHomology.thetaCharacterCollapse_mapsTo_north :
    Set.MapsTo thetaCharacterCollapse thetaNorth Suspension.northOpen := by
  intro p hp
  rw [← thetaCharacterCollapse_preimage_north] at hp
  exact hp

theorem CuspCentralHomology.thetaCharacterCollapse_mapsTo_south :
    Set.MapsTo thetaCharacterCollapse thetaSouth Suspension.southOpen := by
  intro p hp
  rw [← thetaCharacterCollapse_preimage_south] at hp
  exact hp

def CuspCentralHomology.thetaCircleLabel : C(ThreeCircles, Fin 3)
    where
  toFun := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))
  continuous_toFun := continuous_const.sumElim (continuous_const.sumElim continuous_const)

@[simp]
theorem CuspCentralHomology.thetaCircleLabel_inl (z : _root_.Circle) :
    thetaCircleLabel (Sum.inl z) = 0 :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaCircleLabel_inr_inl (z : _root_.Circle) :
    thetaCircleLabel (Sum.inr (Sum.inl z)) = 1 :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaCircleLabel_inr_inr (z : _root_.Circle) :
    thetaCircleLabel (Sum.inr (Sum.inr z)) = 2 :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaCircleLabel_inclusion (j : Fin 3) (z : _root_.Circle) :
    thetaCircleLabel (thetaCircleInclusion j z) = j := by fin_cases j <;> rfl

private def CuspCentralHomology.thetaForgetCircleFun_mo1973_14410 :
    ThreeCircleSuspension → Theta :=
  Quotient.lift (s := suspensionSetoid ThreeCircles)
    (fun p => Suspension.mk p.1 (thetaCircleLabel p.2))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hz⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (congrArg thetaCircleLabel hz))⟩)

private theorem CuspCentralHomology.thetaForgetCircleFun_continuous_mo1973_14411 :
    Continuous thetaForgetCircleFun_mo1973_14410 := by
  apply (Suspension.isQuotientMap_mk (X := ThreeCircles)).continuous_iff.mpr
  change
    Continuous (fun p : unitInterval × ThreeCircles => Suspension.mk p.1 (thetaCircleLabel p.2))
  exact
    Suspension.continuous_mk.comp
      (continuous_fst.prodMk (thetaCircleLabel.continuous.comp continuous_snd))

def CuspCentralHomology.thetaForgetCircle : C(ThreeCircleSuspension, Theta) :=
  ⟨thetaForgetCircleFun_mo1973_14410, thetaForgetCircleFun_continuous_mo1973_14411⟩

@[simp]
theorem CuspCentralHomology.thetaForgetCircle_mk (t : unitInterval) (z : ThreeCircles) :
    thetaForgetCircle (Suspension.mk t z) = Suspension.mk t (thetaCircleLabel z) :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaForgetCircle_circle (t : unitInterval) (j : Fin 3)
    (z : _root_.Circle) :
    thetaForgetCircle (Suspension.mk t (thetaCircleInclusion j z)) = Suspension.mk t j := by
  rw [thetaForgetCircle_mk, thetaCircleLabel_inclusion]

@[simp]
theorem CuspCentralHomology.thetaForgetCircle_collapse (u : ToricSpace.CompactFibreTorus)
    (q : Theta) : thetaForgetCircle (thetaCharacterCollapse (u, q)) = q := by
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaCharacterCollapse_mk, thetaForgetCircle_circle]

theorem CuspCentralHomology.threePoint_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology (Fin 3) n) :=
  PeriodTorusHigherHomology.totallyDisconnected_homology_subsingleton (Fin 3) n hn

theorem CuspCentralHomology.theta_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology Theta (n + 2)) := by
  let := threePoint_homology_subsingleton (n + 1) (Nat.succ_ne_zero n)
  exact
    ((contractibleCoverHomologyHigherEquiv (Suspension.northOpen : Set Theta) Suspension.southOpen
            Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover n).trans
        (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Suspension.middleBandHomotopyEquiv (X := Fin 3)) (n + 1))).injective.subsingleton

def CuspCentralHomology.dualSidePoint (k : Fin 6) (t : unitInterval) :
    (CuspHoneycombTiling.Plane) :=
  CuspHoneycombTiling.dualStandardPlaneHomeomorph.symm
    (CuspHoneycombHexagon.sideIntervalHomeomorph k t : (CuspHoneycombTiling.Plane))

theorem CuspCentralHomology.dualSidePoint_continuous (k : Fin 6) : Continuous (dualSidePoint k) :=
  CuspHoneycombTiling.dualStandardPlaneHomeomorph.symm.continuous.comp
    (continuous_subtype_val.comp (CuspHoneycombHexagon.sideIntervalHomeomorph k).continuous)

theorem CuspCentralHomology.edgeArcBase_eq_dualSidePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) = dualSidePoint k t := by
  have h :
    edgeArcBase C₀ k t =
      CuspHoneycombTiling.standardHexagonDualHomeomorph
        ⟨(CuspHoneycombHexagon.sideIntervalHomeomorph k t : (CuspHoneycombTiling.Plane)),
          (CuspHoneycombHexagon.sideIntervalHomeomorph k t).2.1⟩ := by
    apply (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).injective
    rw [compatibleCellHomeomorph_edgeArcBase,
      CuspHoneycombHexagon.compatibleCellHomeomorph_sideInterval]
  exact congrArg Subtype.val h

def CuspCentralHomology.orientedEdgeBasePoint (t : unitInterval) (j : Fin 3) :
    (CuspHoneycombTiling.Plane) :=
  dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)

@[simp]
theorem CuspCentralHomology.orientedEdgeBasePoint_zero (t : unitInterval) :
    orientedEdgeBasePoint t 0 = dualSidePoint 0 t := by
  simp [thetaEdgeIndex, orientedEdgeBasePoint]

@[simp]
theorem CuspCentralHomology.orientedEdgeBasePoint_one (t : unitInterval) :
    orientedEdgeBasePoint t 1 = dualSidePoint 1 (unitInterval.symm t) := by
  simp [thetaEdgeIndex, orientedEdgeBasePoint]

@[simp]
theorem CuspCentralHomology.orientedEdgeBasePoint_two (t : unitInterval) :
    orientedEdgeBasePoint t 2 = dualSidePoint 2 t := by
  simp [thetaEdgeIndex, orientedEdgeBasePoint]

theorem CuspCentralHomology.orientedEdgeBasePoint_continuous (j : Fin 3) :
    Continuous (fun t => orientedEdgeBasePoint t j) := by
  by_cases hj : j = 1
  · simpa only [orientedEdgeBasePoint, if_pos hj, Function.comp_def] using
      (dualSidePoint_continuous (thetaEdgeIndex j)).comp unitInterval.continuous_symm
  · simpa only [orientedEdgeBasePoint, if_neg hj] using
      dualSidePoint_continuous (thetaEdgeIndex j)

def CuspCentralHomology.thetaBaseCylinder (p : unitInterval × Fin 3) :
    PeriodTorusHigherHomology.ProductTorus 2 :=
  baseTorusPoint (orientedEdgeBasePoint p.1 p.2)

@[simp]
theorem CuspCentralHomology.thetaBaseCylinder_apply (t : unitInterval) (j : Fin 3) :
    thetaBaseCylinder (t, j) = baseTorusPoint (orientedEdgeBasePoint t j) :=
  rfl

theorem CuspCentralHomology.thetaBaseCylinder_continuous : Continuous thetaBaseCylinder :=
  continuous_prod_of_discrete_right.mpr fun j =>
    baseTorusPoint_continuous.comp (orientedEdgeBasePoint_continuous j)

@[simp]
theorem CuspCentralHomology.baseTorusProjection_edgeCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (k : Fin 6) (t : unitInterval) (a : Circle) :
    baseTorusProjection C r hr
        (CuspCollapse.centralProject C r hr (edgeCylinder (C 0) k (t, a))) =
      baseTorusPoint (dualSidePoint k t) := by
  have h :
    CuspCollapse.centralProject C r hr (edgeCylinder (C 0) k (t, a)) =
      CuspHoneycomb.honeycombCollapseMap C r hr
        (hexagonCharacterSection k a, (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane))) := by
    change
      CuspCollapse.centralCollapseMap C r hr
          (hexagonCharacterSection k a, edgeArcPositive (C 0) k t) =
        CuspCollapse.centralCollapseMap C r hr
          (hexagonCharacterSection k a,
            CuspHoneycomb.honeycombHomeomorph (C 0)
              (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane)))
    rw [honeycombHomeomorph_edgeArcBase]
  rw [h, baseTorusProjection_honeycombCollapseMap, edgeArcBase_eq_dualSidePoint]

theorem CuspCentralHomology.baseTorusProjection_doubleCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (p : unitInterval × ThreeCircles) :
    baseTorusProjection C r hr (doubleCylinder C r hr p) =
      thetaBaseCylinder (p.1, thetaCircleLabel p.2) := by
  rcases p with ⟨t, a | (a | a)⟩ <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      baseTorusProjection_edgeCylinder, thetaCircleLabel_inl, thetaCircleLabel_inr_inl,
      thetaCircleLabel_inr_inr, thetaBaseCylinder_apply, orientedEdgeBasePoint_zero,
      orientedEdgeBasePoint_one, orientedEdgeBasePoint_two]

theorem CuspCentralHomology.thetaBaseCylinder_respects (p q : unitInterval × Fin 3)
    (h : (suspensionSetoid (Fin 3)).r p q) : thetaBaseCylinder p = thetaBaseCylinder q := by
  have h' :
    (suspensionSetoid ThreeCircles).r (p.1, thetaCircleInclusion p.2 1)
      (q.1, thetaCircleInclusion q.2 1) := by
    rcases h with ⟨ht, hzero | hone | hj⟩
    · exact ⟨ht, Or.inl hzero⟩
    · exact ⟨ht, Or.inr (Or.inl hone)⟩
    · exact ⟨ht, Or.inr (Or.inr (congrArg (fun j => thetaCircleInclusion j 1) hj))⟩
  have he :=
    congrArg (baseTorusProjection (fun _ => 0) 1 zero_lt_one)
      (doubleCylinder_respects (fun _ => 0) 1 zero_lt_one _ _ h')
  simpa only [baseTorusProjection_doubleCylinder, thetaCircleLabel_inclusion] using he

private def CuspCentralHomology.thetaBaseMapFun_mo1973_14442 :
    Theta → PeriodTorusHigherHomology.ProductTorus 2 :=
  Quotient.lift thetaBaseCylinder thetaBaseCylinder_respects

private theorem CuspCentralHomology.thetaBaseMapFun_continuous_mo1973_14443 :
    Continuous thetaBaseMapFun_mo1973_14442 :=
  (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_iff.mpr thetaBaseCylinder_continuous

def CuspCentralHomology.thetaBaseMap : C(Theta, PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨thetaBaseMapFun_mo1973_14442, thetaBaseMapFun_continuous_mo1973_14443⟩

@[simp]
theorem CuspCentralHomology.thetaBaseMap_mk (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) = thetaBaseCylinder (t, j) :=
  rfl

theorem CuspCentralHomology.thetaBaseMap_mk_point (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) =
      baseTorusPoint
        (dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)) :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaBaseMap_mk_zero (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 0) = baseTorusPoint (dualSidePoint 0 t) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_zero]

@[simp]
theorem CuspCentralHomology.thetaBaseMap_mk_one (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 1) = baseTorusPoint (dualSidePoint 1 (unitInterval.symm t)) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_one]

@[simp]
theorem CuspCentralHomology.thetaBaseMap_mk_two (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 2) = baseTorusPoint (dualSidePoint 2 t) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_two]

theorem CuspCentralHomology.thetaBaseMap_homology_eq_zero (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap thetaBaseMap (n + 2) = 0 := by
  let := theta_homology_subsingleton n
  exact Subsingleton.elim _ _

theorem CuspCentralHomology.baseTorusProjection_doubleSuspensionMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (q : ThreeCircleSuspension) :
    baseTorusProjection C r hr (doubleSuspensionMap C r hr q) =
      thetaBaseMap (thetaForgetCircle q) := by
  obtain ⟨⟨t, a⟩, rfl⟩ := Suspension.mk_surjective q
  rw [doubleSuspensionMap_mk, baseTorusProjection_doubleCylinder, thetaForgetCircle_mk,
    thetaBaseMap_mk]

theorem CuspCentralHomology.baseTorusProjection_boundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (q : centralBoundary C r hr) :
    baseTorusProjection C r hr (q : CuspRetraction.QuotientCentralFibre C r) =
      thetaBaseMap (thetaForgetCircle (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR q)) :=
  by
  obtain ⟨p, rfl⟩ := (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR).symm.surjective q
  rw [Homeomorph.apply_symm_apply, centralBoundarySuspensionHomeomorph_symm_coe]
  exact baseTorusProjection_doubleSuspensionMap C r hr p

theorem CuspCentralHomology.baseTorusProjectionMap_comp_boundaryInclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    (baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr) =
      thetaBaseMap.comp
        (thetaForgetCircle.comp
          (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR :
            C(centralBoundary C r hr, ThreeCircleSuspension))) := by
  apply ContinuousMap.ext
  intro q
  exact baseTorusProjection_boundary C r hr hr1 hC hR q

theorem CuspCentralHomology.baseTorusProjection_boundary_homology_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        ((baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr)) (n + 2) =
      0 := by
  rw [baseTorusProjectionMap_comp_boundaryInclusion C r hr hr1 hC hR,
    PeriodTorusHigherHomology.singularHomologyMap_comp, thetaBaseMap_homology_eq_zero,
    LinearMap.zero_comp]

theorem CuspCentralHomology.baseTorusProjection_boundary_homology_two_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    SingularMayerVietoris.singularHomologyMap
        ((baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr)) 2 =
      0 :=
  baseTorusProjection_boundary_homology_eq_zero C r hr hr1 hC hR 0

abbrev CuspCentralHomology.baseTorusSectionHomologyMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n :=
  SingularMayerVietoris.singularHomologyMap (baseTorusSection C r hr) n

abbrev CuspCentralHomology.baseTorusProjectionHomologyMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) n :=
  SingularMayerVietoris.singularHomologyMap (baseTorusProjectionMap C r hr hC) n

@[simp]
theorem CuspCentralHomology.baseTorusProjectionMap_comp_section (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    (baseTorusProjectionMap C r hr hC).comp (baseTorusSection C r hr) =
      ContinuousMap.id (PeriodTorusHigherHomology.ProductTorus 2) :=
  ContinuousMap.ext (baseTorusProjection_section C r hr)

@[simp]
theorem CuspCentralHomology.baseTorusProjectionHomologyMap_comp_section
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    (baseTorusProjectionHomologyMap C r hr hC n).comp (baseTorusSectionHomologyMap C r hr n) =
      LinearMap.id := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, baseTorusProjectionMap_comp_section,
    PeriodTorusHigherHomology.singularHomologyMap_id]

@[simp]
theorem CuspCentralHomology.baseTorusProjectionHomologyMap_section
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) n) :
    baseTorusProjectionHomologyMap C r hr hC n (baseTorusSectionHomologyMap C r hr n a) = a :=
  LinearMap.congr_fun (baseTorusProjectionHomologyMap_comp_section C r hr hC n) a

theorem CuspCentralHomology.baseTorusProjectionHomologyMap_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    Function.Surjective (baseTorusProjectionHomologyMap C r hr hC n) :=
  (show
      Function.LeftInverse (baseTorusProjectionHomologyMap C r hr hC n)
        (baseTorusSectionHomologyMap C r hr n)
      from baseTorusProjectionHomologyMap_section C r hr hC n).surjective

def CuspCentralHomology.baseTorusH2Marking :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 2).trans
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

def CuspCentralHomology.baseTorusH2Functional (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 →ₗ[ℤ] ℤ :=
  baseTorusH2Marking.toLinearMap.comp (baseTorusProjectionHomologyMap C r hr hC 2)

theorem CuspCentralHomology.baseTorusH2Functional_boundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hr1 : r < 1) (hR : ToricSpace.SmallDrift C r)
    (a : SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2) :
    baseTorusH2Functional C r hr hC
        (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2 a) =
      0 := by
  change
    baseTorusH2Marking
        (((baseTorusProjectionHomologyMap C r hr hC 2).comp
            (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2))
          a) =
      0
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp,
    baseTorusProjection_boundary_homology_two_eq_zero C r hr hr1 hC hR, LinearMap.zero_apply,
    map_zero]

theorem CuspCentralHomology.baseTorusProjection_homology_one_injective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Injective (baseTorusProjectionHomologyMap C r hr hC 1) := by
  let := PeriodTorusHigherHomology.productTorus_homology_finite 2 1
  let e :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 1 :=
    (centralSingularH1Equiv C r hr hC).trans
      (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1).symm
  exact
    IsNoetherian.injective_of_surjective_of_injective e.toLinearMap
      (baseTorusProjectionHomologyMap C r hr hC 1) e.injective
      (baseTorusProjectionHomologyMap_surjective C r hr hC 1)

theorem CuspCentralHomology.baseTorusSection_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (baseTorusSectionHomologyMap C r hr 1) := by
  intro a
  refine ⟨baseTorusProjectionHomologyMap C r hr hC 1 a, ?_⟩
  apply baseTorusProjection_homology_one_injective C r hr hC
  exact baseTorusProjectionHomologyMap_section C r hr hC 1 _

def CuspSpecialization.productBaseTorusSection :
    C(PeriodTorusHigherHomology.ProductTorus 2,
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2)
    where
  toFun b := (1, b)
  continuous_toFun := continuous_const.prodMk continuous_id

theorem CuspSpecialization.productCollapse_comp_baseTorusSection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    (productCollapse C r hr).comp productBaseTorusSection =
      CuspCentralHomology.baseTorusSection C r hr :=
  ContinuousMap.ext fun _ => rfl

theorem CuspSpecialization.productCollapse_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (productCollapse C r hr) 1) := by
  intro a
  obtain ⟨b, hb⟩ := CuspCentralHomology.baseTorusSection_homology_one_surjective C r hr hC a
  refine ⟨SingularMayerVietoris.singularHomologyMap productBaseTorusSection 1 b, ?_⟩
  change
    ((SingularMayerVietoris.singularHomologyMap (productCollapse C r hr) 1).comp
          (SingularMayerVietoris.singularHomologyMap productBaseTorusSection 1))
        b =
      a
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, productCollapse_comp_baseTorusSection]
  exact hb

theorem CuspSpecialization.markedCollapse_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) :=
  markedCollapse_homology_surjective_of_product C r hr 1
    (productCollapse_homology_one_surjective C r hr hC)

private def CuspCoinvariants.integerLinearMapOfAdd_mo1973_14485 {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (g : M →+ N) : M →ₗ[ℤ] N
    where
  toFun := g
  map_add' := g.map_add
  map_smul' c x := by simpa only [Int.cast_id, RingHom.id_apply] using map_intCast_smul g ℤ ℤ c x

def CuspCoinvariants.quotientLiftMap {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (S : Submodule ℤ M) (f : M →ₗ[ℤ] N) (hS : S ≤ LinearMap.ker f) :
    (M ⧸ S) →ₗ[ℤ] N :=
  integerLinearMapOfAdd_mo1973_14485 (S.liftQ f hS).toAddMonoidHom

theorem CuspCoinvariants.quotientLift_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (S : Submodule ℤ M) (f : M →ₗ[ℤ] N) (hf : Function.Surjective f)
    (hS : S ≤ LinearMap.ker f) : Function.Surjective (S.liftQ f hS) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem CuspCoinvariants.quotientLift_bijective_of_finrank {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] [Module.Free ℤ N] [Module.Finite ℤ N]
    (S : Submodule ℤ M) {r : ℕ} (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : S ≤ LinearMap.ker f) (hrank : Module.finrank ℤ N = r) :
    Function.Bijective (S.liftQ f hS) := by
  let g : (Fin r → ℤ) →ₗ[ℤ] N := (quotientLiftMap S f hS).comp e.symm.toLinearMap
  have hgs : Function.Surjective g := (quotientLift_surjective S f hf hS).comp e.symm.surjective
  have hgb : Function.Bijective g := by
    apply OrzechProperty.bijective_of_surjective_of_finrank_le g hgs
    rw [Module.finrank_fin_fun, hrank]
  refine ⟨?_, quotientLift_surjective S f hf hS⟩
  intro x y hxy
  apply e.injective
  apply hgb.injective
  change S.liftQ f hS (e.symm (e x)) = S.liftQ f hS (e.symm (e y))
  simpa only [LinearEquiv.symm_apply_apply] using hxy

theorem CuspCoinvariants.kernel_eq_of_quotient_equiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] [Module.Free ℤ N] [Module.Finite ℤ N] (S : Submodule ℤ M)
    {r : ℕ} (e : (M ⧸ S) ≃ₗ[ℤ] (Fin r → ℤ)) (f : M →ₗ[ℤ] N) (hf : Function.Surjective f)
    (hS : S ≤ LinearMap.ker f) (hrank : Module.finrank ℤ N = r) : LinearMap.ker f = S := by
  apply le_antisymm ?_ hS
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero S).mp
  apply (quotientLift_bijective_of_finrank S e f hf hS hrank).injective
  rw [Submodule.liftQ_apply, map_zero]
  exact hx

theorem CuspSpecialization.markedCollapse_homology_one_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) =
      LinearMap.range (CuspCoinvariants.torusDifference 1) := by
  let := CuspCentralHomology.centralSingularH1_free C r hr hC
  let := CuspCentralHomology.centralSingularH1_finite C r hr hC
  exact
    CuspCoinvariants.kernel_eq_of_quotient_equiv
      (LinearMap.range (CuspCoinvariants.torusDifference 1)) torusOneCoinvariantEquiv
      (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1)
      (markedCollapse_homology_one_surjective C r hr hC)
      (markedCollapse_homology_range_variation C r hr 1)
      (CuspCentralHomology.centralSingularH1_finrank C r hr hC)

theorem CuspSpecialization.markedCollapse_homologyOne_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) :=
  markedCollapse_homology_one_surjective C r hr hC

theorem CuspSpecialization.markedCollapse_homologyOne_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 1) =
      LinearMap.range (CuspCoinvariants.torusDifference 1) :=
  markedCollapse_homology_one_kernel C r hr hC

theorem CuspCentralHomology.dualSidePoint_mem_frontier (k : Fin 6) (t : unitInterval) :
    dualSidePoint k t ∈ frontier CuspHoneycombTiling.baseCell := by
  rw [← edgeArcBase_eq_dualSidePoint (0 : Matrix (Fin 2) (Fin 2) ℂ) k t]
  exact edgeArcBase_mem_frontier (0 : Matrix (Fin 2) (Fin 2) ℂ) k t

theorem CuspCentralHomology.orientedEdgeBasePoint_mem_frontier (t : unitInterval) (j : Fin 3) :
    orientedEdgeBasePoint t j ∈ frontier CuspHoneycombTiling.baseCell :=
  dualSidePoint_mem_frontier (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)

def CuspCentralHomology.thetaProductMap :
    C(ToricSpace.CompactFibreTorus × Theta,
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :=
  (ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap thetaBaseMap

@[simp]
theorem CuspCentralHomology.thetaProductMap_mk (u : ToricSpace.CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    thetaProductMap (u, Suspension.mk t j) = (u, baseTorusPoint (orientedEdgeBasePoint t j)) :=
  rfl

theorem CuspCentralHomology.productCollapse_thetaProductMap_mk (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    CuspSpecialization.productCollapse C ε hε (thetaProductMap (u, Suspension.mk t j)) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) := by
  rw [thetaProductMap_mk, baseTorusPoint_apply,
    CuspSpecialization.productCollapse_coordinateProjection,
    CuspSpecialization.realCuspVector_neg_realCuspVector]

theorem CuspCentralHomology.productCollapse_thetaProductMap_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : ToricSpace.CompactFibreTorus × Theta) :
    CuspSpecialization.productCollapse C ε hε (thetaProductMap p) ∈ centralBoundary C ε hε := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [productCollapse_thetaProductMap_mk, centralBoundary_eq_image]
  exact
    ⟨(u * CuspSpecialization.sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
        orientedEdgeBasePoint t j),
      ⟨Set.mem_univ _, orientedEdgeBasePoint_mem_frontier t j⟩, rfl⟩

def CuspCentralHomology.boundaryLift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(ToricSpace.CompactFibreTorus × Theta, centralBoundary C ε hε)
    where
  toFun
    p :=
    ⟨CuspSpecialization.productCollapse C ε hε (thetaProductMap p),
      productCollapse_thetaProductMap_mem_centralBoundary C ε hε p⟩
  continuous_toFun :=
    ((CuspSpecialization.productCollapse C ε hε).continuous.comp
          thetaProductMap.continuous).subtype_mk
      _

theorem CuspCentralHomology.centralBoundaryInclusion_comp_boundaryLift
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    (centralBoundaryInclusion C ε hε).comp (boundaryLift C ε hε) =
      (CuspSpecialization.productCollapse C ε hε).comp thetaProductMap :=
  rfl

@[simp]
theorem CuspCentralHomology.boundaryLift_mk_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    (boundaryLift C ε hε (u, Suspension.mk t j) : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) (orientedEdgeBasePoint t j),
          orientedEdgeBasePoint t j) :=
  productCollapse_thetaProductMap_mk C ε hε u t j

theorem CuspCentralHomology.centralProject_edgeCylinder_character_dualSide
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (t, hexagonCharacter k u)) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (u, dualSidePoint k t) := by
  rw [edgeCylinder_character_all]
  change
    CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) =
      CuspCollapse.centralCollapseMap C ε hε
        (u, CuspHoneycomb.honeycombHomeomorph (C 0) (dualSidePoint k t))
  rw [← edgeArcBase_eq_dualSidePoint (C 0) k t, honeycombHomeomorph_edgeArcBase]

theorem CuspCentralHomology.doubleSuspensionMap_character_orientedEdge
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (t : unitInterval) (j : Fin 3) :
    doubleSuspensionMap C ε hε
        (Suspension.mk t (thetaCircleInclusion j (hexagonCharacter (thetaEdgeIndex j) u))) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (u, orientedEdgeBasePoint t j) := by
  fin_cases j
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 0 t u
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 1 (unitInterval.symm t) u
  · exact centralProject_edgeCylinder_character_dualSide C ε hε 2 t u

def CuspCentralHomology.thetaShearCylinder (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : unitInterval)
    (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) : ThreeCircleSuspension :=
  Suspension.mk t
    (thetaCircleInclusion j
      (hexagonCharacter (thetaEdgeIndex j)
        (u * CuspSpecialization.sourcePhaseCharacter C₀ ((s : ℝ) • orientedEdgeBasePoint t j))))

theorem CuspCentralHomology.thetaShearCylinder_respects (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : unitInterval) (u : ToricSpace.CompactFibreTorus) (p q : unitInterval × Fin 3)
    (hpq : (suspensionSetoid (Fin 3)).r p q) :
    thetaShearCylinder C₀ s u p.1 p.2 = thetaShearCylinder C₀ s u q.1 q.2 := by
  apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
  rcases hpq with ⟨ht, hzero | hone | hj⟩
  · exact ⟨ht, Or.inl hzero⟩
  · exact ⟨ht, Or.inr (Or.inl hone)⟩
  · refine ⟨ht, Or.inr (Or.inr ?_)⟩
    rw [ht, hj]

private def CuspCentralHomology.thetaShearLiftFun_mo1973_14554 (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : (unitInterval × ToricSpace.CompactFibreTorus) × Theta) : ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid (Fin 3))
    (fun q => thetaShearCylinder C₀ p.1.1 p.1.2 q.1 q.2)
    (thetaShearCylinder_respects C₀ p.1.1 p.1.2) p.2

theorem CuspCentralHomology.thetaShearCylinder_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous
      (fun p : (unitInterval × ToricSpace.CompactFibreTorus) × (unitInterval × Fin 3) =>
        thetaShearCylinder C₀ p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h :
    Continuous
      (fun p : ((unitInterval × ToricSpace.CompactFibreTorus) × unitInterval) × Fin 3 =>
        Suspension.mk p.1.2
          (thetaCircleInclusion p.2
            (hexagonCharacter (thetaEdgeIndex p.2)
              (p.1.1.2 *
                CuspSpecialization.sourcePhaseCharacter C₀
                  ((p.1.1.1 : ℝ) • orientedEdgeBasePoint p.1.2 p.2))))) := by
    apply continuous_prod_of_discrete_right.mpr
    intro j
    exact
      Suspension.continuous_mk.comp
        (continuous_snd.prodMk
          ((thetaCircleInclusion_continuous j).comp
            ((edgeCharacter_continuous (ToricComponent.hexagonRay (thetaEdgeIndex j))).comp
              ((continuous_snd.comp continuous_fst).mul
                ((CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp
                  ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
                    ((orientedEdgeBasePoint_continuous j).comp continuous_snd)))))))
  exact
    h.comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))

private theorem CuspCentralHomology.thetaShearLiftFun_continuous_mo1973_14557
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) : Continuous (thetaShearLiftFun_mo1973_14554 C₀) := by
  apply (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_lift_prod_right
  change
    Continuous
      (fun p : (unitInterval × ToricSpace.CompactFibreTorus) × (unitInterval × Fin 3) =>
        thetaShearCylinder C₀ p.1.1 p.1.2 p.2.1 p.2.2)
  exact thetaShearCylinder_continuous C₀

def CuspCentralHomology.thetaShearMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(unitInterval × (ToricSpace.CompactFibreTorus × Theta), ThreeCircleSuspension)
    where
  toFun p := thetaShearLiftFun_mo1973_14554 C₀ ((p.1, p.2.1), p.2.2)
  continuous_toFun :=
    (thetaShearLiftFun_continuous_mo1973_14557 C₀).comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))

@[simp]
theorem CuspCentralHomology.thetaShearMap_mk (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : unitInterval)
    (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    thetaShearMap C₀ (s, (u, Suspension.mk t j)) = thetaShearCylinder C₀ s u t j :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaShearMap_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (p : ToricSpace.CompactFibreTorus × Theta) :
    thetaShearMap C₀ (0, p) = thetaCharacterCollapse p := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [thetaShearMap_mk]
  simp [thetaShearCylinder]

def CuspCentralHomology.shearedThetaCollapse (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(ToricSpace.CompactFibreTorus × Theta, ThreeCircleSuspension) :=
  (thetaShearMap C₀).comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩

@[simp]
theorem CuspCentralHomology.shearedThetaCollapse_mk (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : ToricSpace.CompactFibreTorus) (t : unitInterval) (j : Fin 3) :
    shearedThetaCollapse C₀ (u, Suspension.mk t j) =
      Suspension.mk t
        (thetaCircleInclusion j
          (hexagonCharacter (thetaEdgeIndex j)
            (u * CuspSpecialization.sourcePhaseCharacter C₀ (orientedEdgeBasePoint t j)))) := by
  change
    Suspension.mk t
        (thetaCircleInclusion j
          (hexagonCharacter (thetaEdgeIndex j)
            (u *
              CuspSpecialization.sourcePhaseCharacter C₀
                ((1 : ℝ) • orientedEdgeBasePoint t j)))) =
      _
  rw [one_smul]

def CuspCentralHomology.thetaShearHomotopy (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    thetaCharacterCollapse.Homotopy (shearedThetaCollapse C₀)
    where
  toContinuousMap := thetaShearMap C₀
  map_zero_left := thetaShearMap_zero C₀
  map_one_left _ := rfl

def CuspCentralHomology.rightPreimageHomeomorph (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (S : Set Y) : (Prod.snd ⁻¹' S : Set (X × Y)) ≃ₜ X × S
    where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, p.2), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def CuspCentralHomology.rightPreimageProjection (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (S : Set Y) : C((Prod.snd ⁻¹' S : Set (X × Y)), X) :=
  ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

def CuspCentralHomology.rightPreimageContractibleHomotopyEquiv (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (S : Set Y) [ContractibleSpace S] :
    (Prod.snd ⁻¹' S : Set (X × Y)) ≃ₕ X :=
  (rightPreimageHomeomorph X Y S).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl X).prodCongr
          (Classical.choice (ContractibleSpace.hequiv_unit S))).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv)

theorem CuspCentralHomology.rightPreimageProjection_homology_injective (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (S : Set Y) [ContractibleSpace S] (n : ℕ) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (rightPreimageProjection X Y S) n) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
      (rightPreimageContractibleHomotopyEquiv X Y S) n).injective

def CuspCentralHomology.suspensionMiddleSection (Y : Type) [TopologicalSpace Y] :
    C(Y, Suspension.middleBand Y) :=
  ⟨fun y => Suspension.middleBandHomeomorph.symm (⟨1 / 2, by norm_num⟩, y),
    Suspension.middleBandHomeomorph.symm.continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp]
theorem CuspCentralHomology.suspensionMiddleSection_coe (Y : Type) [TopologicalSpace Y] (y : Y) :
    (suspensionMiddleSection Y y : Suspension Y) = Suspension.mk ⟨1 / 2, by norm_num⟩ y :=
  rfl

@[simp]
theorem CuspCentralHomology.suspensionMiddleSection_label (Y : Type) [TopologicalSpace Y]
    (y : Y) : Suspension.middleBandHomotopyEquiv (suspensionMiddleSection Y y) = y := by
  change
    (Suspension.middleBandHomeomorph
          (Suspension.middleBandHomeomorph.symm (⟨1 / 2, by norm_num⟩, y))).2 =
      y
  rw [Homeomorph.apply_symm_apply]

def CuspCentralHomology.suspensionProductMiddleSection (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (y : Y) :
    C(X, (Prod.snd ⁻¹' Suspension.middleBand Y : Set (X × Suspension Y))) :=
  ⟨fun x => ⟨(x, suspensionMiddleSection Y y), (suspensionMiddleSection Y y).2⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

theorem CuspCentralHomology.contractibleTargetCoverMap_homology_surjective (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (hU' : IsOpen U')
    (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) [ContractibleSpace U'] [ContractibleSpace V']
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (n : ℕ)
    (hlift :
      ∀ b : SingularMayerVietoris.SingularHomology (U' ∩ V' : Set Y) n,
        ∃ c : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n,
          SingularMayerVietoris.leftHomologyMap U V n c = 0 ∧
            SingularMayerVietoris.singularHomologyMap
                (SingularMayerVietoris.intersectionRestriction f U V U' V' hfU hfV) n c =
              b) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap f (n + 1)) := by
  intro b
  obtain ⟨c, hc, hcb⟩ :=
    hlift (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hcover' n b)
  have hr :
    c ∈ LinearMap.range (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
    rw [SingularMayerVietoris.exact_at_intersection]
    exact hc
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, contractibleCoverConnecting_injective U' V' hU' hV' hcover' n ?_⟩
  have hn :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply f U V U' V' hfU hfV hU hV hcover
      hU' hV' hcover' n a
  rw [ha, hcb] at hn
  exact hn.symm

abbrev CuspCentralHomology.ThetaBelt :=
  thetaNorth ∩ thetaSouth

def CuspCentralHomology.thetaBeltSection (j : Fin 3) :
    C(ToricSpace.CompactFibreTorus, ThetaBelt) :=
  suspensionProductMiddleSection ToricSpace.CompactFibreTorus (Fin 3) j

@[simp]
theorem CuspCentralHomology.thetaBeltSection_coe (j : Fin 3) (u : ToricSpace.CompactFibreTorus) :
    (thetaBeltSection j u : ToricSpace.CompactFibreTorus × Theta) =
      (u, Suspension.mk ⟨1 / 2, by norm_num⟩ j) :=
  rfl

def CuspCentralHomology.thetaBeltProjection : C(ThetaBelt, ToricSpace.CompactFibreTorus) :=
  rightPreimageProjection ToricSpace.CompactFibreTorus Theta (Suspension.middleBand (Fin 3))

@[simp]
theorem CuspCentralHomology.thetaBeltProjection_comp_section (j : Fin 3) :
    thetaBeltProjection.comp (thetaBeltSection j) =
      ContinuousMap.id ToricSpace.CompactFibreTorus :=
  rfl

@[simp]
theorem CuspCentralHomology.thetaBeltProjection_homology_section (j : Fin 3) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n) :
    SingularMayerVietoris.singularHomologyMap thetaBeltProjection n
        (SingularMayerVietoris.singularHomologyMap (thetaBeltSection j) n a) =
      a := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    thetaBeltProjection_comp_section, PeriodTorusHigherHomology.singularHomologyMap_id,
    LinearMap.id_apply]

def CuspCentralHomology.thetaBeltSum
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    SingularMayerVietoris.SingularHomology ThetaBelt 1 :=
  ∑ j, SingularMayerVietoris.singularHomologyMap (thetaBeltSection j) 1 (v j)

@[simp]
theorem CuspCentralHomology.thetaBeltProjection_homology_sum
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    SingularMayerVietoris.singularHomologyMap thetaBeltProjection 1 (thetaBeltSum v) = ∑ j, v j :=
  by simp only [thetaBeltSum, map_sum, thetaBeltProjection_homology_section]

theorem CuspCentralHomology.thetaBelt_mem_ker_of_projection_eq_zero (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ThetaBelt n)
    (ha : SingularMayerVietoris.singularHomologyMap thetaBeltProjection n a = 0) :
    SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth n a = 0 := by
  have hleft :
    SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_left : ThetaBelt ⊆ thetaNorth)) n a =
      0 := by
    let proj : C(thetaNorth, ToricSpace.CompactFibreTorus) :=
      rightPreimageProjection ToricSpace.CompactFibreTorus Theta Suspension.northOpen
    apply
      (show Function.Injective (SingularMayerVietoris.singularHomologyMap proj n) from
        rightPreimageProjection_homology_injective ToricSpace.CompactFibreTorus Theta
          Suspension.northOpen n)
    rw [map_zero, ← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact ha
  have hright :
    SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_right : ThetaBelt ⊆ thetaSouth)) n a =
      0 := by
    let proj : C(thetaSouth, ToricSpace.CompactFibreTorus) :=
      rightPreimageProjection ToricSpace.CompactFibreTorus Theta Suspension.southOpen
    apply
      (show Function.Injective (SingularMayerVietoris.singularHomologyMap proj n) from
        rightPreimageProjection_homology_injective ToricSpace.CompactFibreTorus Theta
          Suspension.southOpen n)
    rw [map_zero, ← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact ha
  rw [SingularMayerVietoris.leftHomologyMap_apply, hleft, hright, neg_zero]
  rfl

theorem CuspCentralHomology.thetaBeltSum_mem_ker
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1)
    (hv : ∑ j, v j = 0) :
    SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth 1 (thetaBeltSum v) = 0 := by
  apply thetaBelt_mem_ker_of_projection_eq_zero
  rw [thetaBeltProjection_homology_sum, hv]

def CuspCentralHomology.thetaCircleMap (j : Fin 3) : C(_root_.Circle, ThreeCircles) :=
  ⟨thetaCircleInclusion j, thetaCircleInclusion_continuous j⟩

theorem CuspCentralHomology.thetaCircleMap_zero :
    thetaCircleMap 0 =
      PeriodTorusHigherHomology.sumInlMap _root_.Circle (_root_.Circle ⊕ _root_.Circle) :=
  rfl

theorem CuspCentralHomology.thetaCircleMap_one :
    thetaCircleMap 1 =
      (PeriodTorusHigherHomology.sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle)).comp
        (PeriodTorusHigherHomology.sumInlMap _root_.Circle _root_.Circle) :=
  rfl

theorem CuspCentralHomology.thetaCircleMap_two :
    thetaCircleMap 2 =
      (PeriodTorusHigherHomology.sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle)).comp
        (PeriodTorusHigherHomology.sumInrMap _root_.Circle _root_.Circle) :=
  rfl

private theorem CuspCentralHomology.threeCirclesHomologySplit_apply_mo1973_14596 (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology ThreeCircles n) :
    threeCirclesHomologySplit n a =
      ((PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle) n
            a).1,
        PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle _root_.Circle n
          (PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle
              (_root_.Circle ⊕ _root_.Circle) n a).2) :=
  rfl

theorem CuspCentralHomology.thetaCircleMap_homologySplit (j : Fin 3) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology _root_.Circle n) :
    threeCirclesHomologySplit n
        (SingularMayerVietoris.singularHomologyMap (thetaCircleMap j) n a) =
      ![(a, (0, 0)), (0, (a, 0)), (0, (0, a))] j := by
  fin_cases j <;>
    simp [thetaCircleMap_zero, thetaCircleMap_one, thetaCircleMap_two,
      PeriodTorusHigherHomology.singularHomologyMap_comp,
      threeCirclesHomologySplit_apply_mo1973_14596]
  rfl

private theorem CuspCentralHomology.threeCirclesHomologyOneEquiv_apply_mo1973_14598
    (a : SingularMayerVietoris.SingularHomology ThreeCircles 1) :
    threeCirclesHomologyOneEquiv a =
      ![unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).1,
        unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).2.1,
        unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).2.2] :=
  rfl

theorem CuspCentralHomology.thetaCircleMap_homologyOne (j : Fin 3)
    (a : SingularMayerVietoris.SingularHomology _root_.Circle 1) :
    threeCirclesHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (thetaCircleMap j) 1 a) =
      Pi.single j (unitCircleHomologyOneEquiv a) := by
  rw [threeCirclesHomologyOneEquiv_apply_mo1973_14598, thetaCircleMap_homologySplit]
  fin_cases j <;> funext k <;> fin_cases k <;> simp

noncomputable def CuspCentralHomology.thetaTargetBeltHomologyEquiv :
    SingularMayerVietoris.SingularHomology (Suspension.middleBand ThreeCircles) 1 ≃ₗ[ℤ]
      (Fin 3 → ℤ) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)) 1).trans
    threeCirclesHomologyOneEquiv

theorem CuspCentralHomology.thetaTargetBeltHomologyEquiv_middleSection
    (a : SingularMayerVietoris.SingularHomology ThreeCircles 1) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap (suspensionMiddleSection ThreeCircles) 1 a) =
      threeCirclesHomologyOneEquiv a := by
  have hsection :
    (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun.comp
        (suspensionMiddleSection ThreeCircles) =
      ContinuousMap.id ThreeCircles := by
    apply ContinuousMap.ext
    exact suspensionMiddleSection_label ThreeCircles
  change
    threeCirclesHomologyOneEquiv
        (((SingularMayerVietoris.singularHomologyMap
                (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun 1).comp
            (SingularMayerVietoris.singularHomologyMap (suspensionMiddleSection ThreeCircles) 1))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, hsection,
    PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

def CuspCentralHomology.thetaEdgeCharacterMap (j : Fin 3) :
    C(ToricSpace.CompactFibreTorus, _root_.Circle) :=
  ⟨hexagonCharacter (thetaEdgeIndex j),
    edgeCharacter_continuous (ToricComponent.hexagonRay (thetaEdgeIndex j))⟩

def CuspCentralHomology.thetaBeltMap : C(ThetaBelt, Suspension.middleBand ThreeCircles) :=
  SingularMayerVietoris.intersectionRestriction thetaCharacterCollapse thetaNorth thetaSouth
    Suspension.northOpen Suspension.southOpen thetaCharacterCollapse_mapsTo_north
    thetaCharacterCollapse_mapsTo_south

theorem CuspCentralHomology.thetaBeltMap_comp_section (j : Fin 3) :
    thetaBeltMap.comp (thetaBeltSection j) =
      (suspensionMiddleSection ThreeCircles).comp
        ((thetaCircleMap j).comp (thetaEdgeCharacterMap j)) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change
    thetaCharacterCollapse (thetaBeltSection j u : ToricSpace.CompactFibreTorus × Theta) =
      (suspensionMiddleSection ThreeCircles (thetaCircleMap j (thetaEdgeCharacterMap j u)) :
        ThreeCircleSuspension)
  rw [thetaBeltSection_coe, suspensionMiddleSection_coe, thetaCharacterCollapse_mk]
  rfl

theorem CuspCentralHomology.thetaBeltMap_homologyOne_section (j : Fin 3)
    (a : SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap thetaBeltMap 1
          (SingularMayerVietoris.singularHomologyMap (thetaBeltSection j) 1 a)) =
      Pi.single j
        (unitCircleHomologyOneEquiv
          (SingularMayerVietoris.singularHomologyMap (thetaEdgeCharacterMap j) 1 a)) := by
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    thetaBeltMap_comp_section, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, thetaTargetBeltHomologyEquiv_middleSection,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    thetaCircleMap_homologyOne]

theorem CuspCentralHomology.thetaBeltMap_homologyOne_sum
    (v : Fin 3 → SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap thetaBeltMap 1 (thetaBeltSum v)) =
      fun j =>
      unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (thetaEdgeCharacterMap j) 1 (v j)) := by
  simp only [thetaBeltSum, map_sum, thetaBeltMap_homologyOne_section]
  funext j
  simp

theorem PeriodTorusHigherHomology.positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv
        (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm 1
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) :=
  crossProductHomology_pointClass_right (PeriodTorusHigherHomology.CircleTopology.Circle) Unit
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) ()

@[simp]
theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop :
    circleHomologyOneEquiv (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) = 1 := by
  rw [circleHomologyOneEquiv_apply, ← positiveCircleCross_pointClass,
    circleBoundary_positiveCircleCross]
  exact connectedHomologyZeroEquiv_pointClass ()

@[simp]
theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one :
    circleHomologyOneEquiv.symm 1 = FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, circleHomologyOneEquiv_positiveLoop]

theorem PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int (k : ℤ) :
    circleHomologyOneEquiv.symm k =
      k • FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop := by
  apply circleHomologyOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, map_zsmul, circleHomologyOneEquiv_positiveLoop]
  simp

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.compactPhaseH1IndexEquiv : Fin 2 ≃ Fin (Nat.choose 2 1) :=
  Fin.revPerm.trans (finCongr (by decide))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.compactPhaseH1OrderEquiv :
    PeriodTorusHigherHomology.binomialModule 2 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({    toFun v i := v (compactPhaseH1IndexEquiv i)
        invFun v i := v (compactPhaseH1IndexEquiv.symm i)
        left_inv v := by ext i; exact congrArg v (compactPhaseH1IndexEquiv.apply_symm_apply i)
        right_inv v := by ext i; exact congrArg v (compactPhaseH1IndexEquiv.symm_apply_apply i)
        map_add' _ _ := rfl } :
      PeriodTorusHigherHomology.binomialModule 2 1 ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.compactPhaseH1Equiv :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph 1).trans
        (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1)).trans
    compactPhaseH1OrderEquiv

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.compactPhaseCircleMap (v : Fin 2 → ℤ) :
    C(_root_.Circle, ToricSpace.CompactFibreTorus) :=
  ⟨ToricSpace.edgeCompactPhase v, ToricSpace.edgeCompactPhase_continuous v⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.compactPhaseCircleMap_coordinates (v : Fin 2 → ℤ) :
    (compactFibreTorusHomeomorph :
            C(ToricSpace.CompactFibreTorus, PeriodTorusHigherHomology.ProductTorus 2)).comp
        ((compactPhaseCircleMap v).comp
          (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))) =
      PeriodTorusHigherHomology.coordinateCircleMap v := by
  apply ContinuousMap.ext
  intro z
  ext i
  change circleCoordinateHomeomorph (circleCoordinateHomeomorph.symm z ^ v i) = v i • z
  rw [circleCoordinateHomeomorph_zpow, Homeomorph.apply_symm_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.compactPhaseCircleMap_positiveHomology (v : Fin 2 → ℤ) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph 1
        (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1
          (unitCircleHomologyOneEquiv.symm 1)) =
      FirstHurewicz.loopHomologyClass (PeriodTorusHigherHomology.coordinatePeriodLoop 2 v) := by
  change
    ((SingularMayerVietoris.singularHomologyMap
              (compactFibreTorusHomeomorph :
                C(ToricSpace.CompactFibreTorus, PeriodTorusHigherHomology.ProductTorus 2))
              1).comp
          ((SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1).comp
            (SingularMayerVietoris.singularHomologyMap
              (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle)) 1)))
        (PeriodTorusHigherHomology.circleHomologyOneEquiv.symm 1) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, compactPhaseCircleMap_coordinates,
    PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_one]
  exact PeriodTorusHigherHomology.coordinateCircleMap_positiveHomology v

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.compactPhase_coordinateTorusClass (i : Fin 2) :
    PeriodTorusHigherHomology.coordinateTorusClass 2 1 (compactPhaseH1IndexEquiv i) =
      FirstHurewicz.loopHomologyClass
        (PeriodTorusHigherHomology.coordinatePeriodLoop 2 (Pi.single i 1)) := by
  rw [PeriodTorusHigherHomology.coordinateTorusClass,
    PeriodTorusHigherHomology.productTorusTopClass_one,
    PeriodTorusHigherHomology.coordinateTorusMap_eq_torusMatrixMap]
  change
    FirstHurewicz.inducedHomology
        (PeriodTorusHigherHomology.torusMatrixMap
          (PeriodTorusHigherHomology.coordinateTorusMatrix 2 1 (compactPhaseH1IndexEquiv i)))
        (FirstHurewicz.loopHomologyClass
          (PeriodTorusHigherHomology.coordinatePeriodLoop 1 (Pi.single 0 1))) =
      _
  rw [PeriodTorusHigherHomology.torusMatrixMap_coordinatePeriodHomology]
  congr 2
  fin_cases i <;> decide

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.compactPhaseCoordinateClass (i : Fin 2) :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 :=
  SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap (Pi.single i 1)) 1
    (unitCircleHomologyOneEquiv.symm 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem CuspCentralHomology.compactPhaseH1Equiv_coordinateClass (i : Fin 2) :
    compactPhaseH1Equiv (compactPhaseCoordinateClass i) = Pi.single i 1 := by
  change
    compactPhaseH1OrderEquiv
        (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph 1
            (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap (Pi.single i 1)) 1
              (unitCircleHomologyOneEquiv.symm 1)))) =
      _
  rw [compactPhaseCircleMap_positiveHomology, ← compactPhase_coordinateTorusClass,
    PeriodTorusHigherHomology.productTorusHomologyEquiv_coordinateTorusClass]
  ext j
  fin_cases i <;> fin_cases j <;> rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem CuspCentralHomology.compactPhaseH1Equiv_symm_single (i : Fin 2) :
    compactPhaseH1Equiv.symm (Pi.single i 1) = compactPhaseCoordinateClass i := by
  apply compactPhaseH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, compactPhaseH1Equiv_coordinateClass]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.compactPhaseH1Equiv_symm_apply (v : Fin 2 → ℤ) :
    compactPhaseH1Equiv.symm v =
      v 0 • compactPhaseCoordinateClass 0 + v 1 • compactPhaseCoordinateClass 1 := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_zsmul, map_zsmul, compactPhaseH1Equiv_symm_single,
    compactPhaseH1Equiv_symm_single]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.compactPhaseCoordinateHomology :
    (Fin 2 → ℤ) →ₗ[ℤ] SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 :=
  compactPhaseH1Equiv.symm.toLinearMap

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.compactPhaseCoordinateHomology_apply (v : Fin 2 → ℤ) :
    compactPhaseCoordinateHomology v =
      v 0 • compactPhaseCoordinateClass 0 + v 1 • compactPhaseCoordinateClass 1 :=
  compactPhaseH1Equiv_symm_apply v

def CuspCentralHomology.circlePowerMap (k : ℤ) : C(_root_.Circle, _root_.Circle) :=
  ⟨fun z => z ^ k, continuous_id.zpow k⟩

private def CuspCentralHomology.additiveCirclePowerMap_mo1973_14639 (k : ℤ) :
    C(AddCircle (1 : ℝ), AddCircle (1 : ℝ)) :=
  ⟨fun z => k • z, continuous_id.zsmul k⟩

private def CuspCentralHomology.firstCircleProjection_mo1973_14640 :
    C(PeriodTorusHigherHomology.ProductTorus 4, AddCircle (1 : ℝ)) :=
  ⟨fun x => x 0, continuous_apply 0⟩

private theorem CuspCentralHomology.firstCircleProjection_positiveLoop_mo1973_14641 :
    (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) 1)).map
        firstCircleProjection_mo1973_14640.continuous =
      PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  apply Path.ext
  funext t
  change
    PeriodTorusHigherHomology.coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) 1) t 0 =
      PeriodTorusHigherHomology.CirclePaths.positiveLoop t
  simp only [PeriodTorusHigherHomology.coordinatePeriodLoop_apply, Pi.single_eq_same,
    Int.cast_one, mul_one, PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply]

private theorem CuspCentralHomology.firstCircleProjection_scalarLoop_mo1973_14642 (k : ℤ) :
    (PeriodTorusHigherHomology.coordinatePeriodLoop 4 (k • Pi.single (0 : Fin 4) 1)).map
        firstCircleProjection_mo1973_14640.continuous =
      (PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
            (additiveCirclePowerMap_mo1973_14639 k).continuous).cast
        (by simp [additiveCirclePowerMap_mo1973_14639, firstCircleProjection_mo1973_14640])
        (by simp [additiveCirclePowerMap_mo1973_14639, firstCircleProjection_mo1973_14640]) := by
  apply Path.ext
  funext t
  change
    PeriodTorusHigherHomology.coordinatePeriodLoop 4 (k • Pi.single (0 : Fin 4) 1) t 0 =
      k • PeriodTorusHigherHomology.CirclePaths.positiveLoop t
  rw [PeriodTorusHigherHomology.coordinatePeriodLoop_apply,
    PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply]
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  change (((t : ℝ) * (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = ((k • (t : ℝ) : ℝ) : AddCircle (1 : ℝ))
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

private theorem CuspCentralHomology.additiveCirclePowerMap_positiveClass_mo1973_14643 (k : ℤ) :
    SingularMayerVietoris.singularHomologyMap (additiveCirclePowerMap_mo1973_14639 k) 1
        (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) =
      k • FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  have h :=
    congrArg (FirstHurewicz.inducedHomology firstCircleProjection_mo1973_14640)
      (map_zsmul (PeriodTorusHigherHomology.coordinateH1 4) k (Pi.single (0 : Fin 4) 1))
  rw [PeriodTorusHigherHomology.coordinateH1_four_apply (Elliptic.examplePeriod .four),
    PeriodTorusHigherHomology.coordinateH1_single, map_zsmul,
    FirstHurewicz.inducedHomology_loopHomologyClass,
    FirstHurewicz.inducedHomology_loopHomologyClass,
    firstCircleProjection_scalarLoop_mo1973_14642,
    firstCircleProjection_positiveLoop_mo1973_14641] at h
  rw [SingularMayerVietoris.singularHomologyMap_one,
    FirstHurewicz.inducedHomology_loopHomologyClass]
  exact h

private theorem CuspCentralHomology.additiveCirclePowerMap_homology_mo1973_14644 (k : ℤ)
    (a : SingularMayerVietoris.SingularHomology (AddCircle (1 : ℝ)) 1) :
    PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (additiveCirclePowerMap_mo1973_14639 k) 1 a) =
      k * PeriodTorusHigherHomology.circleHomologyOneEquiv a := by
  obtain ⟨m, rfl⟩ := PeriodTorusHigherHomology.circleHomologyOneEquiv.symm.surjective a
  rw [LinearEquiv.apply_symm_apply, PeriodTorusHigherHomology.circleHomologyOneEquiv_symm_int,
    map_zsmul, additiveCirclePowerMap_positiveClass_mo1973_14643, map_zsmul, map_zsmul,
    PeriodTorusHigherHomology.circleHomologyOneEquiv_positiveLoop]
  simp [mul_comm]

private theorem CuspCentralHomology.circlePowerMap_coordinate_mo1973_14645 (k : ℤ) :
    (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))).comp (circlePowerMap k) =
      (additiveCirclePowerMap_mo1973_14639 k).comp
        (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) := by
  apply ContinuousMap.ext
  intro z
  exact circleCoordinateHomeomorph_zpow z k

theorem CuspCentralHomology.unitCircleHomologyOneEquiv_circlePowerMap (k : ℤ)
    (a : SingularMayerVietoris.SingularHomology _root_.Circle 1) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (circlePowerMap k) 1 a) =
      k * unitCircleHomologyOneEquiv a := by
  change
    PeriodTorusHigherHomology.circleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap
          (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) 1
          (SingularMayerVietoris.singularHomologyMap (circlePowerMap k) 1 a)) =
      k *
        PeriodTorusHigherHomology.circleHomologyOneEquiv
          (SingularMayerVietoris.singularHomologyMap
            (circleCoordinateHomeomorph : C(_root_.Circle, AddCircle (1 : ℝ))) 1 a)
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    circlePowerMap_coordinate_mo1973_14645, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]
  exact additiveCirclePowerMap_homology_mo1973_14644 k _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.edgeCharacterMap (n : Fin 2 → ℤ) :
    C(ToricSpace.CompactFibreTorus, _root_.Circle) :=
  ⟨edgeCharacter n, edgeCharacter_continuous n⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.edgeCharacterMap_comp_circle (n v : Fin 2 → ℤ) :
    (edgeCharacterMap n).comp (compactPhaseCircleMap v) =
      circlePowerMap (n 0 * v 1 - n 1 * v 0) := by
  apply ContinuousMap.ext
  intro z
  exact edgeCharacter_edgeCompactPhase n v z

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.edgeCharacter_circleHomology (n v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1
            (unitCircleHomologyOneEquiv.symm 1))) =
      -n 1 * v 0 + n 0 * v 1 := by
  change
    unitCircleHomologyOneEquiv
        (((SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1).comp
            (SingularMayerVietoris.singularHomologyMap (compactPhaseCircleMap v) 1))
          (unitCircleHomologyOneEquiv.symm 1)) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, edgeCharacterMap_comp_circle,
    unitCircleHomologyOneEquiv_circlePowerMap, LinearEquiv.apply_symm_apply, mul_one]
  ring

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem CuspCentralHomology.edgeCharacter_coordinateClass_zero (n : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (compactPhaseCoordinateClass 0)) =
      -n 1 := by
  simpa only [compactPhaseCoordinateClass, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, MulZeroClass.mul_zero,
    add_zero] using edgeCharacter_circleHomology n (Pi.single 0 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem CuspCentralHomology.edgeCharacter_coordinateClass_one (n : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (compactPhaseCoordinateClass 1)) =
      n 0 := by
  simpa only [compactPhaseCoordinateClass, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one, MulZeroClass.mul_zero,
    zero_add] using edgeCharacter_circleHomology n (Pi.single 1 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.edgeCharacter_coordinateHomology (n v : Fin 2 → ℤ) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (edgeCharacterMap n) 1
          (compactPhaseCoordinateHomology v)) =
      -n 1 * v 0 + n 0 * v 1 := by
  rw [compactPhaseCoordinateHomology_apply]
  simp only [map_add, map_zsmul, edgeCharacter_coordinateClass_zero,
    edgeCharacter_coordinateClass_one, zsmul_eq_mul, Int.cast_id]
  ring

def CuspCentralHomology.thetaPhaseTripleSum : (Fin 3 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)
    where
  toFun v := ∑ j, v j
  map_add' v w := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

theorem CuspCentralHomology.thetaPhaseTripleSum_apply (v : Fin 3 → Fin 2 → ℤ) (i : Fin 2) :
    thetaPhaseTripleSum v i = v 0 i + v 1 i + v 2 i := by
  simp [thetaPhaseTripleSum, Fin.sum_univ_succ, add_assoc]

def CuspCentralHomology.thetaPhaseTripleCharacters : (Fin 3 → Fin 2 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ)
    where
  toFun v := ![v 0 1, -(v 1 0), -(v 2 0) - v 2 1]
  map_add' v
    w := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' c
    v := by
    funext j
    fin_cases j <;> simp
    ring

theorem CuspCentralHomology.thetaPhaseTripleCharacters_eq_det (v : Fin 3 → Fin 2 → ℤ)
    (j : Fin 3) :
    thetaPhaseTripleCharacters v j =
      ToricComponent.hexagonRay (j.castLE (by decide)) 0 * v j 1 -
        ToricComponent.hexagonRay (j.castLE (by decide)) 1 * v j 0 := by
  fin_cases j <;> simp [thetaPhaseTripleCharacters, ToricComponent.hexagonRay]
  ring

def CuspCentralHomology.thetaPhaseTripleSection : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → Fin 2 → ℤ)
    where
  toFun z := ![![z 2 + z 1 - z 0, z 0], ![-z 1, 0], ![z 0 - z 2, -z 0] ]
  map_add' z
    w := by
    funext j i
    fin_cases j <;> fin_cases i <;> simp <;> ring
  map_smul' c
    z := by
    funext j i
    fin_cases j <;> fin_cases i <;> simp <;> ring

theorem CuspCentralHomology.thetaPhaseTripleSum_section (z : Fin 3 → ℤ) :
    thetaPhaseTripleSum (thetaPhaseTripleSection z) = 0 := by
  funext i
  rw [thetaPhaseTripleSum_apply]
  fin_cases i <;> simp [thetaPhaseTripleSection]
  ring

theorem CuspCentralHomology.thetaPhaseTripleCharacters_section (z : Fin 3 → ℤ) :
    thetaPhaseTripleCharacters (thetaPhaseTripleSection z) = z := by
  funext j
  fin_cases j <;> simp [thetaPhaseTripleCharacters, thetaPhaseTripleSection]

def CuspCentralHomology.thetaBeltPhaseClasses (z : Fin 3 → ℤ) (j : Fin 3) :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 1 :=
  compactPhaseCoordinateHomology (thetaPhaseTripleSection z j)

theorem CuspCentralHomology.thetaBeltPhaseClasses_sum (z : Fin 3 → ℤ) :
    ∑ j, thetaBeltPhaseClasses z j = 0 := by
  change (∑ j, compactPhaseCoordinateHomology (thetaPhaseTripleSection z j)) = 0
  rw [← map_sum]
  change compactPhaseCoordinateHomology (thetaPhaseTripleSum (thetaPhaseTripleSection z)) = 0
  rw [thetaPhaseTripleSum_section, map_zero]

def CuspCentralHomology.thetaBeltLift (z : Fin 3 → ℤ) :
    SingularMayerVietoris.SingularHomology ThetaBelt 1 :=
  thetaBeltSum (thetaBeltPhaseClasses z)

theorem CuspCentralHomology.thetaBeltLift_mem_ker (z : Fin 3 → ℤ) :
    SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth 1 (thetaBeltLift z) = 0 :=
  thetaBeltSum_mem_ker (thetaBeltPhaseClasses z) (thetaBeltPhaseClasses_sum z)

theorem CuspCentralHomology.thetaBeltPhaseClasses_character (z : Fin 3 → ℤ) (j : Fin 3) :
    unitCircleHomologyOneEquiv
        (SingularMayerVietoris.singularHomologyMap (thetaEdgeCharacterMap j) 1
          (thetaBeltPhaseClasses z j)) =
      thetaPhaseTripleCharacters (thetaPhaseTripleSection z) j := by
  rw [thetaPhaseTripleCharacters_eq_det]
  calc
    _ =
        -ToricComponent.hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0 +
          ToricComponent.hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 :=
      edgeCharacter_coordinateHomology (ToricComponent.hexagonRay (thetaEdgeIndex j))
        (thetaPhaseTripleSection z j)
    _ = _ := by
      change
        -ToricComponent.hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0 +
            ToricComponent.hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 =
          ToricComponent.hexagonRay (thetaEdgeIndex j) 0 * thetaPhaseTripleSection z j 1 -
            ToricComponent.hexagonRay (thetaEdgeIndex j) 1 * thetaPhaseTripleSection z j 0
      ring

theorem CuspCentralHomology.thetaBeltLift_image (z : Fin 3 → ℤ) :
    thetaTargetBeltHomologyEquiv
        (SingularMayerVietoris.singularHomologyMap thetaBeltMap 1 (thetaBeltLift z)) =
      z := by
  rw [thetaBeltLift, thetaBeltMap_homologyOne_sum]
  funext j
  rw [thetaBeltPhaseClasses_character, thetaPhaseTripleCharacters_section]

theorem CuspCentralHomology.thetaBelt_kernel_lifts
    (b : SingularMayerVietoris.SingularHomology (Suspension.middleBand ThreeCircles) 1) :
    ∃ c : SingularMayerVietoris.SingularHomology ThetaBelt 1,
      SingularMayerVietoris.leftHomologyMap thetaNorth thetaSouth 1 c = 0 ∧
        SingularMayerVietoris.singularHomologyMap thetaBeltMap 1 c = b := by
  refine ⟨thetaBeltLift (thetaTargetBeltHomologyEquiv b), thetaBeltLift_mem_ker _, ?_⟩
  apply thetaTargetBeltHomologyEquiv.injective
  exact thetaBeltLift_image (thetaTargetBeltHomologyEquiv b)

theorem CuspCentralHomology.thetaCharacterCollapse_homologyTwo_surjective :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap thetaCharacterCollapse 2) :=
  contractibleTargetCoverMap_homology_surjective (ToricSpace.CompactFibreTorus × Theta)
    ThreeCircleSuspension thetaCharacterCollapse thetaNorth thetaSouth Suspension.northOpen
    Suspension.southOpen thetaNorth_isOpen thetaSouth_isOpen theta_open_cover
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
    thetaCharacterCollapse_mapsTo_north thetaCharacterCollapse_mapsTo_south 1
    thetaBelt_kernel_lifts

def CuspCentralHomology.doubleSuspensionBoundaryContinuousMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : C(ThreeCircleSuspension, centralBoundary C ε hε) :=
  ⟨doubleSuspensionBoundaryMap C ε hε, doubleSuspensionBoundaryMap_continuous C ε hε⟩

theorem CuspCentralHomology.boundaryLift_coe_eq_doubleSuspensionMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : ToricSpace.CompactFibreTorus × Theta) :
    (boundaryLift C ε hε p : CuspRetraction.QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε (shearedThetaCollapse (C 0) p) := by
  rcases p with ⟨u, q⟩
  obtain ⟨⟨t, j⟩, rfl⟩ := Suspension.mk_surjective q
  rw [boundaryLift_mk_coe, shearedThetaCollapse_mk, doubleSuspensionMap_character_orientedEdge]

theorem CuspCentralHomology.boundaryLift_eq_doubleSuspensionBoundaryMap_comp
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    boundaryLift C ε hε =
      (doubleSuspensionBoundaryContinuousMap C ε hε).comp (shearedThetaCollapse (C 0)) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact boundaryLift_coe_eq_doubleSuspensionMap C ε hε p

def CuspCentralHomology.boundaryLiftCharacterHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    ((doubleSuspensionBoundaryContinuousMap C ε hε).comp thetaCharacterCollapse).Homotopy
      (boundaryLift C ε hε) :=
  ((ContinuousMap.Homotopy.refl (doubleSuspensionBoundaryContinuousMap C ε hε)).comp
        (thetaShearHomotopy (C 0))).cast
    rfl (boundaryLift_eq_doubleSuspensionBoundaryMap_comp C ε hε).symm

theorem CuspCentralHomology.boundaryLift_homology_eq (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (boundaryLift C ε hε) n =
      (SingularMayerVietoris.singularHomologyMap (doubleSuspensionBoundaryContinuousMap C ε hε)
            n).comp
        (SingularMayerVietoris.singularHomologyMap thetaCharacterCollapse n) := by
  rw [← PeriodTorusHigherHomology.homotopy_homologyMap (boundaryLiftCharacterHomotopy C ε hε) n]
  exact
    PeriodTorusHigherHomology.singularHomologyMap_comp thetaCharacterCollapse
      (doubleSuspensionBoundaryContinuousMap C ε hε) n

theorem CuspCentralHomology.doubleSuspensionBoundaryContinuousMap_eq_homeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    doubleSuspensionBoundaryContinuousMap C ε hε =
      (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR :
        C(ThreeCircleSuspension, centralBoundary C ε hε)) :=
  rfl

theorem CuspCentralHomology.boundaryLift_homologyTwo_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (boundaryLift C ε hε) 2) := by
  rw [boundaryLift_homology_eq,
    doubleSuspensionBoundaryContinuousMap_eq_homeomorph C ε hε hε1 hC hR]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR) 2).surjective.comp
      thetaCharacterCollapse_homologyTwo_surjective

theorem CuspCentralHomology.boundaryInclusion_homologyTwo_range_le_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2) ≤
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          2) := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := boundaryLift_homologyTwo_surjective C ε hε hε1 hC hR b
  refine ⟨SingularMayerVietoris.singularHomologyMap thetaProductMap 2 c, ?_⟩
  have h :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f 2)
      (centralBoundaryInclusion_comp_boundaryLift C ε hε)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h c
  change
    SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2
        (SingularMayerVietoris.singularHomologyMap (boundaryLift C ε hε) 2 c) =
      SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε) 2
        (SingularMayerVietoris.singularHomologyMap thetaProductMap 2 c) at he
  rw [hc] at he
  exact he.symm

def CuspCentralHomology.productBaseSection :
    C(PeriodTorusHigherHomology.ProductTorus 2,
      ToricSpace.CompactFibreTorus × PeriodTorusHigherHomology.ProductTorus 2) :=
  ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩

theorem CuspCentralHomology.productCollapse_comp_productBaseSection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    (CuspSpecialization.productCollapse C ε hε).comp productBaseSection =
      baseTorusSection C ε hε :=
  rfl

theorem CuspCentralHomology.baseTorusSection_homology_factorization
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) n =
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
            n).comp
        (SingularMayerVietoris.singularHomologyMap productBaseSection n) := by
  rw [← productCollapse_comp_productBaseSection,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

theorem CuspCentralHomology.baseTorusSection_homology_range_le_productCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    LinearMap.range (SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) n) ≤
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          n) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨SingularMayerVietoris.singularHomologyMap productBaseSection n x, ?_⟩
  exact (LinearMap.congr_fun (baseTorusSection_homology_factorization C ε hε n) x).symm

theorem CuspCentralHomology.integerExtension_quotient_factorization {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (hpi : ∀ a, p (i a) = 0) (x : B) :
    p x = d x * p (integerExtensionLift d hd) := by
  calc
    p x =
        p
          ((splitIntegerExtensionEquiv i d hi hd hexact).symm
            (splitIntegerExtensionEquiv i d hi hd hexact x)) := by rw [LinearEquiv.symm_apply_apply]
    _ = d x * p (integerExtensionLift d hd) := by
      rw [splitIntegerExtensionEquiv_symm_apply, map_add, hpi, map_zsmul,
        splitIntegerExtensionEquiv_snd]
      simp only [zero_add, zsmul_eq_mul, Int.cast_id]

theorem CuspCentralHomology.integerExtension_quotient_coefficient_isUnit {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (hpi : ∀ a, p (i a) = 0)
    (hp : Function.Surjective p) : IsUnit (p (integerExtensionLift d hd)) := by
  obtain ⟨x, hx⟩ := hp 1
  have he : d x * p (integerExtensionLift d hd) = 1 :=
    (integerExtension_quotient_factorization i d p hi hd hexact hpi x).symm.trans hx
  exact ⟨⟨p (integerExtensionLift d hd), d x, (mul_comm _ _).trans he, he⟩, rfl⟩

theorem CuspCentralHomology.integerExtension_replaceQuotient {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d p : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (hpi : ∀ a, p (i a) = 0)
    (hp : Function.Surjective p) : LinearMap.range i = LinearMap.ker p := by
  have hc : p (integerExtensionLift d hd) ≠ 0 :=
    (integerExtension_quotient_coefficient_isUnit i d p hi hd hexact hpi hp).ne_zero
  rw [hexact]
  ext x
  change d x = 0 ↔ p x = 0
  rw [integerExtension_quotient_factorization i d p hi hd hexact hpi x, mul_eq_zero]
  simp only [hc, or_false]

def CuspCentralHomology.actualSectionAssembly {A B T : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B) (s : T →ₗ[ℤ] B) :
    (A × T) →ₗ[ℤ] B :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom (i.coprod s).toAddMonoidHom

theorem CuspCentralHomology.coprod_projection_of_exact_section {A B T : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) (az : A × T) : p (i.coprod s az) = az.2 := by
  have hi : p (i az.1) = 0 := by
    have ha : i az.1 ∈ LinearMap.range i := ⟨az.1, rfl⟩
    rw [hexact] at ha
    exact ha
  rw [LinearMap.coprod_apply, map_add, hi, hps, zero_add]

theorem CuspCentralHomology.coprod_injective_of_exact_section {A B T : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker p) (hps : ∀ t, p (s t) = t) :
    Function.Injective (i.coprod s) := by
  intro az au h
  have hsnd : az.2 = au.2 := by
    have hp := congrArg p h
    simpa only [coprod_projection_of_exact_section i p s hexact hps] using hp
  apply Prod.ext _ hsnd
  apply hi
  apply add_right_cancel (b := s au.2)
  simpa only [LinearMap.coprod_apply, hsnd] using h

theorem CuspCentralHomology.coprod_surjective_of_exact_section {A B T : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B)
    (p : B →ₗ[ℤ] T) (s : T →ₗ[ℤ] B) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : Function.Surjective (i.coprod s) := by
  intro b
  have hk : b - s (p b) ∈ LinearMap.ker p := by
    change p (b - s (p b)) = 0
    rw [map_sub, hps, sub_self]
  rw [← hexact] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨(a, p b), ?_⟩
  change i a + s (p b) = b
  rw [ha, sub_add_cancel]

def CuspCentralHomology.splitFromActualSection {A B T : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup T] [Module ℤ A] [Module ℤ B] [Module ℤ T] (i : A →ₗ[ℤ] B) (p : B →ₗ[ℤ] T)
    (s : T →ₗ[ℤ] B) (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker p)
    (hps : ∀ t, p (s t) = t) : (A × T) ≃ₗ[ℤ] B :=
  LinearEquiv.ofBijective (actualSectionAssembly i s)
    ⟨coprod_injective_of_exact_section i p s hi hexact hps,
      coprod_surjective_of_exact_section i p s hexact hps⟩

abbrev CuspCentralHomology.boundaryH2Inclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 :=
  SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2

def CuspCentralHomology.boundaryH2Quotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 →ₗ[ℤ] ℤ :=
  middleQuotientMap C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

theorem CuspCentralHomology.boundaryH2Inclusion_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) : Function.Injective (boundaryH2Inclusion C r hr) := by
  let e := outerRegionBoundaryHomotopyEquiv C r hr (1 / 2) (by norm_num) (by norm_num) hr1 hC hR
  have he :
    (SingularMayerVietoris.subtypeInclusion (outerRegion C r hr (1 / 2))).comp e.symm.toFun =
      centralBoundaryInclusion C r hr := by
    apply ContinuousMap.ext
    intro q
    rfl
  change
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2)
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  intro x y hxy
  have hE :
    SingularMayerVietoris.singularHomologyMap e.symm.toFun 2 x =
      SingularMayerVietoris.singularHomologyMap e.symm.toFun 2 y :=
    (middleOuterInclusion_injective C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)) hxy
  apply (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 2).symm.injective
  simpa only [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply] using hE

theorem CuspCentralHomology.boundaryH2Inclusion_range_eq_outer (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C r hr (1 / 2))) 2) := by
  let e := outerRegionBoundaryHomotopyEquiv C r hr (1 / 2) (by norm_num) (by norm_num) hr1 hC hR
  have he :
    (SingularMayerVietoris.subtypeInclusion (outerRegion C r hr (1 / 2))).comp e.symm.toFun =
      centralBoundaryInclusion C r hr := by
    apply ContinuousMap.ext
    intro q
    rfl
  change
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2) =
      _
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    LinearMap.range_comp_of_range_eq_top _
      (LinearEquiv.range (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 2).symm)

theorem CuspCentralHomology.boundaryH2Quotient_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    Function.Surjective (boundaryH2Quotient C r hr hr1 hC hR) :=
  middleQuotientMap_surjective C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

theorem CuspCentralHomology.boundaryH2Inclusion_range_eq_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.ker (boundaryH2Quotient C r hr hr1 hC hR) := by
  rw [boundaryH2Inclusion_range_eq_outer C r hr hr1 hC hR]
  exact middleSecondHomology_exact C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

theorem CuspCentralHomology.baseTorusH2Functional_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (baseTorusH2Functional C r hr hC) :=
  baseTorusH2Marking.surjective.comp (baseTorusProjectionHomologyMap_surjective C r hr hC 2)

theorem CuspCentralHomology.baseTorusH2Functional_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (baseTorusH2Functional C r hr hC) =
      LinearMap.ker (baseTorusProjectionHomologyMap C r hr hC 2) := by
  ext x
  change
    baseTorusH2Marking (baseTorusProjectionHomologyMap C r hr hC 2 x) = 0 ↔
      baseTorusProjectionHomologyMap C r hr hC 2 x = 0
  constructor
  · intro h
    apply baseTorusH2Marking.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

theorem CuspCentralHomology.boundaryH2Inclusion_range_eq_ker_baseFunctional
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.ker (baseTorusH2Functional C r hr hC) :=
  integerExtension_replaceQuotient (boundaryH2Inclusion C r hr)
    (boundaryH2Quotient C r hr hr1 hC hR) (baseTorusH2Functional C r hr hC)
    (boundaryH2Inclusion_injective C r hr hr1 hC hR)
    (boundaryH2Quotient_surjective C r hr hr1 hC hR)
    (boundaryH2Inclusion_range_eq_ker C r hr hr1 hC hR)
    (baseTorusH2Functional_boundary C r hr hC hr1 hR) (baseTorusH2Functional_surjective C r hr hC)

theorem CuspCentralHomology.baseTorusProjectionHomologyMap_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    LinearMap.ker (baseTorusProjectionHomologyMap C r hr hC 2) =
      LinearMap.range (boundaryH2Inclusion C r hr) := by
  rw [← baseTorusH2Functional_ker, ←
    boundaryH2Inclusion_range_eq_ker_baseFunctional C r hr hr1 hC hR]

def CuspCentralHomology.baseTorusH2Split (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) :
    (SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2 ×
        SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2 :=
  splitFromActualSection (boundaryH2Inclusion C r hr) (baseTorusProjectionHomologyMap C r hr hC 2)
    (baseTorusSectionHomologyMap C r hr 2) (boundaryH2Inclusion_injective C r hr hr1 hC hR)
    (baseTorusProjectionHomologyMap_ker C r hr hr1 hC hR).symm
    (baseTorusProjectionHomologyMap_section C r hr hC 2)

theorem CuspCentralHomology.baseTorusH2_generated (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r)
    (x : SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 2) :
    ∃ a : SingularMayerVietoris.SingularHomology (centralBoundary C r hr) 2,
      ∃ b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 2) 2,
        SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C r hr) 2 a +
            baseTorusSectionHomologyMap C r hr 2 b =
          x := by
  obtain ⟨⟨a, b⟩, h⟩ := (baseTorusH2Split C r hr hr1 hC hR).surjective x
  exact ⟨a, b, h⟩

theorem CuspCentralHomology.productCollapse_homologyTwo_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε) 2) :=
  by
  intro x
  obtain ⟨a, b, hab⟩ := baseTorusH2_generated C ε hε hε1 hC hR x
  change
    SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2 a +
        SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) 2 b =
      x at hab
  have ha :
    SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 2 a ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          2) :=
    boundaryInclusion_homologyTwo_range_le_productCollapse C ε hε hε1 hC hR ⟨a, rfl⟩
  have hb :
    SingularMayerVietoris.singularHomologyMap (baseTorusSection C ε hε) 2 b ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          2) :=
    baseTorusSection_homology_range_le_productCollapse C ε hε 2 ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨c + d, ?_⟩
  rw [map_add, hc, hd]
  exact hab

theorem CuspCentralHomology.productCollapse_homologyTwo_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr) 2) :=
  by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, _hRDδ⟩ :=
    CuspRetraction.exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr.le)
  have he :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f 2)
      (centralRadiusHomeomorph_comp_productCollapse C r δ hδr.le hC hδ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at he
  rw [← he]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hδr.le hC hδ) 2).surjective.comp
      (productCollapse_homologyTwo_surjective C δ hδ hδ1 hCδ hRCδ)

def CuspCoinvariants.exteriorSquareDifference :
    PeriodTorusHigherHomologyExterior.latticeExterior 2 →ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 2 :=
  exteriorPower.map 2 M₀.mulVecLin - LinearMap.id

def CuspCoinvariants.exteriorCubeDifference :
    PeriodTorusHigherHomologyExterior.latticeExterior 3 →ₗ[ℤ]
      PeriodTorusHigherHomologyExterior.latticeExterior 3 :=
  exteriorPower.map 3 M₀.mulVecLin - LinearMap.id

theorem CuspCoinvariants.range_difference_le_ker_of_invariant {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (A : M →ₗ[ℤ] M) (f : M →ₗ[ℤ] N)
    (h : ∀ x, f (A x) = f x) : LinearMap.range (A - LinearMap.id) ≤ LinearMap.ker f := by
  rintro x ⟨y, rfl⟩
  change f (A y - y) = 0
  rw [map_sub, h, sub_self]

theorem CuspCoinvariants.torusTwo_kernel_eq {N : Type*} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : LinearMap.range (torusDifference 2) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 4) : LinearMap.ker f = LinearMap.range (torusDifference 2) :=
  kernel_eq_of_quotient_equiv _ torusTwoCoinvariantEquiv f hf hS hrank

theorem CuspCoinvariants.torusThree_kernel_eq {N : Type*} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f) (hS : LinearMap.range (torusDifference 3) ≤ LinearMap.ker f)
    (hrank : Module.finrank ℤ N = 2) : LinearMap.ker f = LinearMap.range (torusDifference 3) :=
  kernel_eq_of_quotient_equiv _ torusThreeCoinvariantEquiv f hf hS hrank

theorem CuspCoinvariants.torusTwo_kernel_eq_of_invariant {N : Type*} [AddCommGroup N] [Module ℤ N]
    [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv :
      ∀ x,
        f
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.torusMatrixMap M₀) 2 x) =
          f x)
    (hrank : Module.finrank ℤ N = 4) : LinearMap.ker f = LinearMap.range (torusDifference 2) :=
  torusTwo_kernel_eq f hf (range_difference_le_ker_of_invariant _ f hinv) hrank

theorem CuspCoinvariants.torusThree_kernel_eq_of_invariant {N : Type*} [AddCommGroup N]
    [Module ℤ N] [Module.Free ℤ N] [Module.Finite ℤ N]
    (f :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3 →ₗ[ℤ] N)
    (hf : Function.Surjective f)
    (hinv :
      ∀ x,
        f
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.torusMatrixMap M₀) 3 x) =
          f x)
    (hrank : Module.finrank ℤ N = 2) : LinearMap.ker f = LinearMap.range (torusDifference 3) :=
  torusThree_kernel_eq f hf (range_difference_le_ker_of_invariant _ f hinv) hrank

theorem CuspSpecialization.torusDifference_two_exterior
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (CuspCoinvariants.torusDifference 2 a) =
      CuspCoinvariants.exteriorSquareDifference
        (PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a) := by
  change
    PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 2
            a -
          a) =
      exteriorPower.map 2 M₀.mulVecLin
          (PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a) -
        PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a
  rw [map_sub, PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv_matrix]

theorem CuspSpecialization.markedCollapse_homologyTwo_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2) :=
  markedCollapse_homology_surjective_of_product C ε hε 2
    (CuspCentralHomology.productCollapse_homologyTwo_surjective_of_holomorphic C ε hε hC)

theorem CuspSpecialization.markedCollapse_homologyTwo_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2) =
      LinearMap.range (CuspCoinvariants.torusDifference 2) := by
  let := CuspCentralHomology.centralSingularH2_free C ε hε hC
  let := CuspCentralHomology.centralSingularH2_finite C ε hε hC
  exact
    CuspCoinvariants.torusTwo_kernel_eq_of_invariant _
      (markedCollapse_homologyTwo_surjective C ε hε hC)
      (markedCollapse_homology_invariant C ε hε 2)
      (CuspCentralHomology.centralSingularH2_finrank C ε hε hC)

theorem CuspSpecialization.markedCollapse_homologyTwo_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 2) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 2,
        exteriorPower.map 2 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a := by
  change
    a ∈ LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 2) ↔
      PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv a ∈
        LinearMap.range CuspCoinvariants.exteriorSquareDifference
  rw [markedCollapse_homologyTwo_kernel C ε hε hC]
  exact
    CuspCoinvariants.mem_range_iff_of_intertwines
      PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
      (CuspCoinvariants.torusDifference 2) CuspCoinvariants.exteriorSquareDifference
      torusDifference_two_exterior a

abbrev CuspCentralHomology.BaseCover.BaseTorus :=
  PeriodTorusHigherHomology.ProductTorus 2

abbrev CuspCentralHomology.BaseCover.basePoint :=
  CuspCentralHomology.baseTorusPoint

theorem CuspCentralHomology.BaseCover.basePoint_eq_iff (y z : (CuspHoneycombTiling.Plane)) :
    basePoint y = basePoint z ↔
      ∃ v : (CuspHoneycombTiling.Lattice), y = z + CuspHoneycombTiling.latticePoint v := by
  rw [CuspCentralHomology.baseTorusPoint_eq_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨ToricSpace.cuspVector v, hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨-ToricSpace.cuspVector v, ?_⟩
    simpa only [ToricSpace.cuspVector_neg, ToricSpace.cuspVector_cuspVector, neg_neg] using hv

theorem CuspCentralHomology.BaseCover.basePoint_add_latticePoint
    (v : (CuspHoneycombTiling.Lattice)) (y : (CuspHoneycombTiling.Plane)) :
    basePoint (y + CuspHoneycombTiling.latticePoint v) = basePoint y :=
  (basePoint_eq_iff _ _).mpr ⟨v, rfl⟩

theorem CuspCentralHomology.BaseCover.basePoint_sub_latticePoint
    (v : (CuspHoneycombTiling.Lattice)) (y : (CuspHoneycombTiling.Plane)) :
    basePoint (y - CuspHoneycombTiling.latticePoint v) = basePoint y := by
  simpa only [CuspHoneycombTiling.latticePoint_neg, sub_eq_add_neg] using
    basePoint_add_latticePoint (-v) y

def CuspCentralHomology.BaseCover.cellMap : C(CuspHoneycombTiling.baseCell, BaseTorus) :=
  ⟨fun y => basePoint (y : (CuspHoneycombTiling.Plane)),
    CuspCentralHomology.baseTorusPoint_continuous.comp continuous_subtype_val⟩

theorem CuspCentralHomology.BaseCover.cellMap_surjective : Function.Surjective cellMap := by
  intro q
  obtain ⟨y, hy⟩ := CuspCentralHomology.baseTorusPoint_surjective q
  exact
    ⟨⟨y - CuspHoneycombTiling.latticePoint (CuspHoneycombTiling.floorCenter y),
        CuspHoneycombTiling.mem_cell_floorCenter y⟩,
      (basePoint_sub_latticePoint (CuspHoneycombTiling.floorCenter y) y).trans hy⟩

theorem CuspCentralHomology.BaseCover.cellMap_eq_iff (y z : CuspHoneycombTiling.baseCell) :
    cellMap y = cellMap z ↔
      ∃ v : (CuspHoneycombTiling.Lattice),
        (y : (CuspHoneycombTiling.Plane)) =
          (z : (CuspHoneycombTiling.Plane)) + CuspHoneycombTiling.latticePoint v :=
  basePoint_eq_iff y z

theorem CuspCentralHomology.BaseCover.cellMap_isProperMap : IsProperMap cellMap := by
  let : CompactSpace CuspHoneycombTiling.baseCell :=
    isCompact_iff_compactSpace.mp CuspHoneycombTiling.baseCell_isCompact
  exact cellMap.continuous.isProperMap

theorem CuspCentralHomology.BaseCover.cellMap_isClosedMap : IsClosedMap cellMap :=
  cellMap_isProperMap.isClosedMap

theorem CuspCentralHomology.BaseCover.cellMap_isQuotientMap : Topology.IsQuotientMap cellMap :=
  cellMap_isClosedMap.isQuotientMap cellMap.continuous cellMap_surjective

theorem CuspCentralHomology.BaseCover.cellMap_eq_of_interior (y z : CuspHoneycombTiling.baseCell)
    (hy : (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell)
    (h : cellMap y = cellMap z) : y = z := by
  obtain ⟨v, hv⟩ := (cellMap_eq_iff y z).mp h
  have hyv : (y : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell v := by
    rw [hv, CuspHoneycombTiling.mem_cell, add_sub_cancel_right]
    exact z.property
  have hv0 : v = 0 := ((CuspHoneycombTiling.mem_interior_baseCell_iff _).mp hy v).mp hyv
  apply Subtype.ext
  simpa only [hv0, CuspHoneycombTiling.latticePoint_zero, add_zero] using hv

theorem CuspCentralHomology.BaseCover.cellMap_interior_iff_of_eq
    (y z : CuspHoneycombTiling.baseCell) (h : cellMap y = cellMap z) :
    (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell ↔
      (z : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  constructor
  · intro hy
    simpa only [← cellMap_eq_of_interior y z hy h] using hy
  · intro hz
    simpa only [← cellMap_eq_of_interior z y hz h.symm] using hz

theorem CuspCentralHomology.BaseCover.cellMap_eq_or_frontier (y z : CuspHoneycombTiling.baseCell)
    (h : cellMap y = cellMap z) :
    y = z ∨
      ((y : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell ∧
        (z : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) := by
  by_cases hy : (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell
  · exact Or.inl (cellMap_eq_of_interior y z hy h)
  · right
    rw [CuspHoneycombTiling.baseCell_isClosed.frontier_eq]
    refine ⟨⟨y.property, hy⟩, z.property, ?_⟩
    intro hz
    exact hy ((cellMap_interior_iff_of_eq y z h).mpr hz)

theorem CuspCentralHomology.BaseCover.cellGauge_eq_of_cellMap_eq
    (y z : CuspHoneycombTiling.baseCell) (h : cellMap y = cellMap z) :
    CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) =
      CuspCentralHomology.Radial.cellGauge (z : (CuspHoneycombTiling.Plane)) := by
  rcases cellMap_eq_or_frontier y z h with rfl | ⟨hy, hz⟩
  · rfl
  · rw [(CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).mp hy,
      (CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).mp hz]

def CuspCentralHomology.BaseCover.cellRadius : C(CuspHoneycombTiling.baseCell, ℝ) :=
  ⟨fun y => CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)),
    CuspCentralHomology.Radial.cellGauge_continuous.comp continuous_subtype_val⟩

def CuspCentralHomology.BaseCover.radius : C(BaseTorus, ℝ)
    where
  toFun := CuspHoneycombHexagon.CommonFibres.descend cellMap cellRadius cellMap_surjective
  continuous_toFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous cellMap cellRadius cellMap_surjective
      cellMap_isQuotientMap cellRadius.continuous cellGauge_eq_of_cellMap_eq

@[simp]
theorem CuspCentralHomology.BaseCover.radius_cellMap (y : CuspHoneycombTiling.baseCell) :
    radius (cellMap y) = CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply cellMap cellRadius cellMap_surjective
    cellGauge_eq_of_cellMap_eq y

def CuspCentralHomology.BaseCover.boundary : Set BaseTorus :=
  {q | radius q = 1}

def CuspCentralHomology.BaseCover.innerRegion : Set BaseTorus :=
  {q | radius q < 1}

def CuspCentralHomology.BaseCover.outerRegion (a : ℝ) : Set BaseTorus :=
  {q | a < radius q}

theorem CuspCentralHomology.BaseCover.cellMap_mem_boundary_iff
    (y : CuspHoneycombTiling.baseCell) :
    cellMap y ∈ boundary ↔
      (y : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
  change radius (cellMap y) = 1 ↔ _
  rw [radius_cellMap]
  exact (CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).symm

theorem CuspCentralHomology.BaseCover.cellMap_mem_innerRegion_iff
    (y : CuspHoneycombTiling.baseCell) :
    cellMap y ∈ innerRegion ↔
      (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  change radius (cellMap y) < 1 ↔ _
  rw [radius_cellMap]
  exact (CuspCentralHomology.Radial.mem_interior_baseCell_iff _).symm

theorem CuspCentralHomology.BaseCover.cellMap_mem_outerRegion_iff (a : ℝ)
    (y : CuspHoneycombTiling.baseCell) :
    cellMap y ∈ outerRegion a ↔
      a < CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) := by
  change a < radius (cellMap y) ↔ _
  rw [radius_cellMap]

theorem CuspCentralHomology.BaseCover.innerRegion_isOpen : IsOpen innerRegion :=
  isOpen_lt radius.continuous continuous_const

theorem CuspCentralHomology.BaseCover.outerRegion_isOpen (a : ℝ) : IsOpen (outerRegion a) :=
  isOpen_lt continuous_const radius.continuous

theorem CuspCentralHomology.BaseCover.boundary_subset_outerRegion (a : ℝ) (ha : a < 1) :
    boundary ⊆ outerRegion a := by
  intro q hq
  change a < radius q
  change radius q = 1 at hq
  rwa [hq]

theorem CuspCentralHomology.BaseCover.outerRegion_union_innerRegion (a : ℝ) (ha : a < 1) :
    outerRegion a ∪ innerRegion = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  by_cases hq : radius q < 1
  · exact Or.inr hq
  · exact Or.inl (ha.trans_le (le_of_not_gt hq))

theorem CuspCentralHomology.BaseCover.dualSidePoint_mem_frontier (k : Fin 6) (t : unitInterval) :
    CuspCentralHomology.dualSidePoint k t ∈ frontier CuspHoneycombTiling.baseCell := by
  rw [← CuspCentralHomology.edgeArcBase_eq_dualSidePoint (0 : Matrix (Fin 2) (Fin 2) ℂ)]
  exact CuspCentralHomology.edgeArcBase_mem_frontier 0 k t

theorem CuspCentralHomology.BaseCover.exists_dualSidePoint_of_mem_frontier
    (y : (CuspHoneycombTiling.Plane)) (hy : y ∈ frontier CuspHoneycombTiling.baseCell) :
    ∃ k : Fin 6, ∃ t : unitInterval, CuspCentralHomology.dualSidePoint k t = y := by
  obtain ⟨k, t, ht⟩ :=
    CuspCentralHomology.exists_edgeArcBase_of_mem_frontier (0 : Matrix (Fin 2) (Fin 2) ℂ) y hy
  exact ⟨k, t, (CuspCentralHomology.edgeArcBase_eq_dualSidePoint 0 k t).symm.trans ht⟩

theorem CuspCentralHomology.BaseCover.dualSidePoint_opposite (k : Fin 6) (t : unitInterval) :
    CuspCentralHomology.dualSidePoint (k + 3) (unitInterval.symm t) =
      CuspCentralHomology.dualSidePoint k t -
        CuspHoneycombTiling.latticePoint (ToricComponent.hexagonRay k) :=
  CuspHoneycombTiling.dual_sideInterval_opposite k t

theorem CuspCentralHomology.BaseCover.basePoint_dualSidePoint_opposite (k : Fin 6)
    (t : unitInterval) :
    CuspCentralHomology.baseTorusPoint
        (CuspCentralHomology.dualSidePoint (k + 3) (unitInterval.symm t)) =
      CuspCentralHomology.baseTorusPoint (CuspCentralHomology.dualSidePoint k t) := by
  rw [dualSidePoint_opposite]
  exact
    basePoint_sub_latticePoint (ToricComponent.hexagonRay k)
      (CuspCentralHomology.dualSidePoint k t)

theorem CuspCentralHomology.BaseCover.thetaBaseMap_mem_boundary (q : CuspCentralHomology.Theta) :
    CuspCentralHomology.thetaBaseMap q ∈ boundary := by
  obtain ⟨⟨t, j⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective q
  rw [CuspCentralHomology.thetaBaseMap_mk_point]
  let y :=
    CuspCentralHomology.dualSidePoint (CuspCentralHomology.thetaEdgeIndex j)
      (if j = 1 then unitInterval.symm t else t)
  have hy : y ∈ frontier CuspHoneycombTiling.baseCell := dualSidePoint_mem_frontier _ _
  exact
    (cellMap_mem_boundary_iff ⟨y, CuspHoneycombTiling.baseCell_isClosed.frontier_subset hy⟩).mpr
      hy

theorem CuspCentralHomology.BaseCover.dualSidePoint_basePoint_mem_range (k : Fin 6)
    (t : unitInterval) :
    CuspCentralHomology.baseTorusPoint (CuspCentralHomology.dualSidePoint k t) ∈
      Set.range CuspCentralHomology.thetaBaseMap := by
  fin_cases k
  · exact
      ⟨CuspCentralHomology.Suspension.mk t (0 : Fin 3),
        CuspCentralHomology.thetaBaseMap_mk_zero t⟩
  · refine ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm t) (1 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_one, unitInterval.symm_symm]
    rfl
  · exact
      ⟨CuspCentralHomology.Suspension.mk t (2 : Fin 3), CuspCentralHomology.thetaBaseMap_mk_two t⟩
  · refine ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm t) (0 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_zero]
    have hi : (0 : Fin 6) + 3 = ⟨3, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 0 (unitInterval.symm t)).symm
  · refine ⟨CuspCentralHomology.Suspension.mk t (1 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_one]
    have hi : (1 : Fin 6) + 3 = ⟨4, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 1 (unitInterval.symm t)).symm
  · refine ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm t) (2 : Fin 3), ?_⟩
    rw [CuspCentralHomology.thetaBaseMap_mk_two]
    have hi : (2 : Fin 6) + 3 = ⟨5, by decide⟩ := by decide
    simpa only [unitInterval.symm_symm, hi] using
      (basePoint_dualSidePoint_opposite 2 (unitInterval.symm t)).symm

theorem CuspCentralHomology.BaseCover.range_thetaBaseMap :
    Set.range CuspCentralHomology.thetaBaseMap = boundary := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact thetaBaseMap_mem_boundary x
  · intro hq
    obtain ⟨y, rfl⟩ := cellMap_surjective q
    obtain ⟨k, t, ht⟩ :=
      exists_dualSidePoint_of_mem_frontier (y : (CuspHoneycombTiling.Plane))
        ((cellMap_mem_boundary_iff y).mp hq)
    change
      CuspCentralHomology.baseTorusPoint (y : (CuspHoneycombTiling.Plane)) ∈
        Set.range CuspCentralHomology.thetaBaseMap
    rw [← ht]
    exact dualSidePoint_basePoint_mem_range k t

def CuspCentralHomology.BaseCover.thetaBoundaryMap : C(CuspCentralHomology.Theta, boundary) :=
  ⟨fun q => ⟨CuspCentralHomology.thetaBaseMap q, thetaBaseMap_mem_boundary q⟩,
    CuspCentralHomology.thetaBaseMap.continuous.subtype_mk _⟩

theorem CuspCentralHomology.BaseCover.thetaBoundaryMap_surjective :
    Function.Surjective thetaBoundaryMap := by
  intro q
  have hq : (q : BaseTorus) ∈ Set.range CuspCentralHomology.thetaBaseMap :=
    range_thetaBaseMap.symm.le q.2
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, Subtype.ext hx⟩

private theorem CuspCentralHomology.BaseCover.zeroCorrection_deckFibrePhase_mo1973_14847
    (v : Fin 2 → ℤ) : CuspCollapse.deckFibrePhase (0 : Matrix (Fin 2) (Fin 2) ℂ) v = 1 := by
  funext i
  simp [CuspCollapse.deckFibrePhase, CuspPositive.frozenPhaseCoordinate_eq_exp]

private theorem CuspCentralHomology.BaseCover.phaseOneCollapse_eq_of_base_eq_mo1973_14848
    {y z : (CuspHoneycombTiling.Plane)}
    (h : CuspCentralHomology.baseTorusPoint y = CuspCentralHomology.baseTorusPoint z) :
    CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, y) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one (1, z) := by
  obtain ⟨v, hv⟩ := (CuspCentralHomology.baseTorusPoint_eq_iff y z).mp h
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff (fun _ => 0) 1 zero_lt_one _ _).mpr
  refine ⟨v, hv, ?_⟩
  simp only [zeroCorrection_deckFibrePhase_mo1973_14847, inv_one, mul_one]
  exact
    (MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((CuspHoneycomb.honeycombHomeomorph 0 y).1 : ToricSpace.Space)).one_mem

private theorem CuspCentralHomology.BaseCover.phaseOne_edgeCylinder_mo1973_14849 (k : Fin 6)
    (t : unitInterval) :
    CuspCollapse.centralProject (fun _ => 0) 1 zero_lt_one
        (CuspCentralHomology.edgeCylinder 0 k (t, 1)) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (1, CuspCentralHomology.dualSidePoint k t) := by
  have h :
    CuspCollapse.centralProject (fun _ => 0) 1 zero_lt_one
        (CuspCentralHomology.edgeCylinder 0 k (t, 1)) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (CuspCentralHomology.hexagonCharacterSection k 1,
          (CuspCentralHomology.edgeArcBase 0 k t : (CuspHoneycombTiling.Plane))) := by
    change
      CuspCollapse.centralCollapseMap (fun _ => 0) 1 zero_lt_one
          (CuspCentralHomology.hexagonCharacterSection k 1,
            CuspCentralHomology.edgeArcPositive 0 k t) =
        CuspCollapse.centralCollapseMap (fun _ => 0) 1 zero_lt_one
          (CuspCentralHomology.hexagonCharacterSection k 1,
            CuspHoneycomb.honeycombHomeomorph 0
              (CuspCentralHomology.edgeArcBase 0 k t : (CuspHoneycombTiling.Plane)))
    rw [CuspCentralHomology.honeycombHomeomorph_edgeArcBase]
  simpa only [map_one, CuspCentralHomology.edgeArcBase_eq_dualSidePoint] using h

private theorem CuspCentralHomology.BaseCover.phaseOne_doubleCylinder_mo1973_14850
    (t : unitInterval) (j : Fin 3) :
    CuspCentralHomology.doubleCylinder (fun _ => 0) 1 zero_lt_one
        (t, CuspCentralHomology.thetaCircleInclusion j 1) =
      CuspHoneycomb.honeycombCollapseMap (fun _ => 0) 1 zero_lt_one
        (1, CuspCentralHomology.orientedEdgeBasePoint t j) := by
  fin_cases j
  · exact phaseOne_edgeCylinder_mo1973_14849 0 t
  · exact phaseOne_edgeCylinder_mo1973_14849 1 (unitInterval.symm t)
  · exact phaseOne_edgeCylinder_mo1973_14849 2 t

theorem CuspCentralHomology.BaseCover.thetaBaseCylinder_eq_iff (p q : unitInterval × Fin 3) :
    CuspCentralHomology.thetaBaseCylinder p = CuspCentralHomology.thetaBaseCylinder q ↔
      (CuspCentralHomology.suspensionSetoid (Fin 3)).r p q := by
  rcases p with ⟨s, j⟩
  rcases q with ⟨t, k⟩
  constructor
  · intro h
    have he :
      CuspCentralHomology.doubleCylinder (fun _ => 0) 1 zero_lt_one
          (s, CuspCentralHomology.thetaCircleInclusion j 1) =
        CuspCentralHomology.doubleCylinder (fun _ => 0) 1 zero_lt_one
          (t, CuspCentralHomology.thetaCircleInclusion k 1) := by
      rw [phaseOne_doubleCylinder_mo1973_14850, phaseOne_doubleCylinder_mo1973_14850]
      exact phaseOneCollapse_eq_of_base_eq_mo1973_14848 h
    obtain ⟨hst, hzero | hone | hlabel⟩ :=
      (CuspCentralHomology.doubleCylinder_eq_iff (fun _ => 0) 1 zero_lt_one
            (s, CuspCentralHomology.thetaCircleInclusion j 1)
            (t, CuspCentralHomology.thetaCircleInclusion k 1)).mp
        he
    · exact ⟨hst, Or.inl hzero⟩
    · exact ⟨hst, Or.inr (Or.inl hone)⟩
    · refine ⟨hst, Or.inr (Or.inr ?_)⟩
      simpa only [CuspCentralHomology.thetaCircleLabel_inclusion] using
        congrArg CuspCentralHomology.thetaCircleLabel hlabel
  · exact CuspCentralHomology.thetaBaseCylinder_respects _ _

theorem CuspCentralHomology.BaseCover.thetaBaseMap_injective :
    Function.Injective CuspCentralHomology.thetaBaseMap := by
  intro x y h
  obtain ⟨⟨s, j⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective x
  obtain ⟨⟨t, k⟩, rfl⟩ := CuspCentralHomology.Suspension.mk_surjective y
  exact Quotient.sound ((thetaBaseCylinder_eq_iff (s, j) (t, k)).mp h)

theorem CuspCentralHomology.BaseCover.thetaBoundaryMap_injective :
    Function.Injective thetaBoundaryMap := by
  intro x y h
  exact thetaBaseMap_injective (congrArg Subtype.val h)

def CuspCentralHomology.BaseCover.thetaBoundaryHomeomorph :
    CuspCentralHomology.Theta ≃ₜ boundary :=
  (thetaBoundaryMap.continuous.isClosedEmbedding
        thetaBoundaryMap_injective).toIsEmbedding |>.toHomeomorphOfSurjective
    thetaBoundaryMap_surjective

def CuspCentralHomology.BaseCover.boundaryThetaHomeomorph :
    boundary ≃ₜ CuspCentralHomology.Theta :=
  thetaBoundaryHomeomorph.symm

theorem CuspCentralHomology.BaseCover.thetaBaseMap_boundaryThetaHomeomorph (q : boundary) :
    CuspCentralHomology.thetaBaseMap (boundaryThetaHomeomorph q) = (q : BaseTorus) :=
  congrArg Subtype.val (thetaBoundaryHomeomorph.apply_symm_apply q)

def CuspCentralHomology.BaseCover.boundaryInclusion : C(boundary, BaseTorus) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def CuspCentralHomology.BaseCover.frontierBoundaryMap :
    C(frontier CuspHoneycombTiling.baseCell, boundary) :=
  ⟨fun y =>
    ⟨cellMap
        ⟨(y : (CuspHoneycombTiling.Plane)),
          CuspHoneycombTiling.baseCell_isClosed.frontier_subset y.2⟩,
      (cellMap_mem_boundary_iff _).mpr y.2⟩,
    (cellMap.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

def CuspCentralHomology.BaseCover.circleBoundaryMap : C(Circle, boundary) :=
  frontierBoundaryMap.comp
    (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm :
      C(Circle, frontier CuspHoneycombTiling.baseCell))

@[simp]
theorem CuspCentralHomology.BaseCover.circleBoundaryMap_coe (z : Circle) :
    (circleBoundaryMap z : BaseTorus) =
      CuspCentralHomology.baseTorusPoint
        (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm z :
          (CuspHoneycombTiling.Plane)) :=
  rfl

def CuspCentralHomology.BaseCover.circleThetaMap : C(Circle, CuspCentralHomology.Theta) :=
  (boundaryThetaHomeomorph : C(boundary, CuspCentralHomology.Theta)).comp circleBoundaryMap

theorem CuspCentralHomology.BaseCover.thetaBaseMap_circleThetaMap :
    CuspCentralHomology.thetaBaseMap.comp circleThetaMap =
      boundaryInclusion.comp circleBoundaryMap := by
  apply ContinuousMap.ext
  intro z
  exact thetaBaseMap_boundaryThetaHomeomorph (circleBoundaryMap z)

def CuspCentralHomology.BaseCover.collarCellInclusion (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) : CuspHoneycombTiling.baseCell :=
  ⟨(p : (CuspHoneycombTiling.Plane)), (CuspCentralHomology.Radial.mem_baseCell_iff _).mpr p.2.2⟩

theorem CuspCentralHomology.BaseCover.collarCellInclusion_continuous (a : ℝ) :
    Continuous (collarCellInclusion a) :=
  continuous_subtype_val.subtype_mk _

theorem CuspCentralHomology.BaseCover.collarCellInclusion_injective (a : ℝ) :
    Function.Injective (collarCellInclusion a) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun y : CuspHoneycombTiling.baseCell => (y : (CuspHoneycombTiling.Plane))) h

def CuspCentralHomology.BaseCover.collarCellMap (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) : outerRegion a :=
  ⟨cellMap (collarCellInclusion a p), (cellMap_mem_outerRegion_iff a _).mpr p.2.1⟩

@[simp]
theorem CuspCentralHomology.BaseCover.collarCellMap_coe (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) :
    (collarCellMap a p : BaseTorus) = basePoint (p : (CuspHoneycombTiling.Plane)) :=
  rfl

@[simp]
theorem CuspCentralHomology.BaseCover.radius_collarCellMap (a : ℝ)
    (p : CuspCentralHomology.Radial.OpenCollar a) :
    radius (collarCellMap a p) =
      CuspCentralHomology.Radial.cellGauge (p : (CuspHoneycombTiling.Plane)) :=
  radius_cellMap (collarCellInclusion a p)

theorem CuspCentralHomology.BaseCover.collarCellMap_continuous (a : ℝ) :
    Continuous (collarCellMap a) :=
  (cellMap.continuous.comp (collarCellInclusion_continuous a)).subtype_mk _

theorem CuspCentralHomology.BaseCover.collarCellMap_surjective (a : ℝ) :
    Function.Surjective (collarCellMap a) := by
  rintro ⟨q, hq⟩
  obtain ⟨y, hy⟩ := cellMap_surjective q
  have hg : a < CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) := by
    apply (cellMap_mem_outerRegion_iff a y).mp
    rwa [hy]
  refine
    ⟨⟨(y : (CuspHoneycombTiling.Plane)), hg,
        (CuspCentralHomology.Radial.mem_baseCell_iff _).mp y.2⟩,
      ?_⟩
  apply Subtype.ext
  exact hy

def CuspCentralHomology.BaseCover.collarPreimageHomeomorph (a : ℝ) :
    CuspCentralHomology.Radial.OpenCollar a ≃ₜ (cellMap ⁻¹' outerRegion a)
    where
  toFun p := ⟨collarCellInclusion a p, (cellMap_mem_outerRegion_iff a _).mpr p.2.1⟩
  invFun
    p :=
    ⟨(p.1 : (CuspHoneycombTiling.Plane)), (cellMap_mem_outerRegion_iff a p.1).mp p.2,
      (CuspCentralHomology.Radial.mem_baseCell_iff _).mp p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (collarCellInclusion_continuous a).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem CuspCentralHomology.BaseCover.collarCellMap_isProperMap (a : ℝ) :
    IsProperMap (collarCellMap a) := by
  have hf := cellMap_isProperMap.restrictPreimage (outerRegion a)
  have hc := hf.comp (collarPreimageHomeomorph a).isProperMap
  have he :
    (outerRegion a).restrictPreimage cellMap ∘ collarPreimageHomeomorph a = collarCellMap a := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

theorem CuspCentralHomology.BaseCover.collarCellMap_isClosedMap (a : ℝ) :
    IsClosedMap (collarCellMap a) :=
  (collarCellMap_isProperMap a).isClosedMap

theorem CuspCentralHomology.BaseCover.collarCellMap_isQuotientMap (a : ℝ) :
    Topology.IsQuotientMap (collarCellMap a) :=
  (collarCellMap_isClosedMap a).isQuotientMap (collarCellMap_continuous a)
    (collarCellMap_surjective a)

theorem CuspCentralHomology.BaseCover.collarCellHomotopy_compatible (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (p q : CuspCentralHomology.Radial.OpenCollar a)
    (h : collarCellMap a p = collarCellMap a q) :
    collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)) =
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, q)) := by
  have he : cellMap (collarCellInclusion a p) = cellMap (collarCellInclusion a q) :=
    congrArg Subtype.val h
  rcases cellMap_eq_or_frontier (collarCellInclusion a p) (collarCellInclusion a q) he with hpq |
    ⟨hp, hq⟩
  · rw [collarCellInclusion_injective a hpq]
  · rw [CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p hp,
      CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s q hq]
    exact h

def CuspCentralHomology.BaseCover.outerRegionBoundaryInclusion (a : ℝ) (ha1 : a < 1) :
    C(boundary, outerRegion a)
    where
  toFun x := ⟨x, boundary_subset_outerRegion a ha1 x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def CuspCentralHomology.BaseCover.outerRegionDeformation (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : outerRegion a) : outerRegion a :=
  CuspHoneycombHexagon.CommonFibres.descend (collarCellMap a)
    (fun p =>
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective a) x

@[simp]
theorem CuspCentralHomology.BaseCover.outerRegionDeformation_collarCellMap (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (p : CuspCentralHomology.Radial.OpenCollar a) :
    outerRegionDeformation a ha ha1 s (collarCellMap a p) =
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (collarCellMap a)
    (fun p =>
      collarCellMap a (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective a) (collarCellHomotopy_compatible a ha ha1 s) p

theorem CuspCentralHomology.BaseCover.outerRegionDeformation_collarCellMap_coe (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval) (p : CuspCentralHomology.Radial.OpenCollar a) :
    (outerRegionDeformation a ha ha1 s (collarCellMap a p) : BaseTorus) =
      basePoint
        (((1 - (s : ℝ)) + (s : ℝ) / CuspCentralHomology.Radial.cellGauge p) •
          (p : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionDeformation_collarCellMap, collarCellMap_coe,
    CuspCentralHomology.Radial.outwardOpenCollarHomotopy_coe]

@[simp]
theorem CuspCentralHomology.BaseCover.outerRegionDeformation_zero (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (x : outerRegion a) : outerRegionDeformation a ha ha1 0 x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  rw [outerRegionDeformation_collarCellMap,
    (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1).apply_zero]
  rfl

theorem CuspCentralHomology.BaseCover.outerRegionDeformation_radius (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : outerRegion a) :
    radius (outerRegionDeformation a ha ha1 s x) = (1 - (s : ℝ)) * radius x + (s : ℝ) := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  rw [outerRegionDeformation_collarCellMap, radius_collarCellMap, radius_collarCellMap]
  exact CuspCentralHomology.Radial.outwardOpenCollarHomotopy_gauge a ha ha1 s p

theorem CuspCentralHomology.BaseCover.outerRegionDeformation_one_mem_boundary (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (x : outerRegion a) :
    (outerRegionDeformation a ha ha1 1 x : BaseTorus) ∈ boundary := by
  change radius (outerRegionDeformation a ha ha1 1 x) = 1
  rw [outerRegionDeformation_radius]
  simp

theorem CuspCentralHomology.BaseCover.outerRegionDeformation_fixed (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : outerRegion a) (hx : (x : BaseTorus) ∈ boundary) :
    outerRegionDeformation a ha ha1 s x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective a x
  have hp : (p : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
    apply (CuspCentralHomology.Radial.mem_frontier_baseCell_iff _).mpr
    change radius (collarCellMap a p) = 1 at hx
    rwa [radius_collarCellMap] at hx
  rw [outerRegionDeformation_collarCellMap,
    CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p hp]

theorem CuspCentralHomology.BaseCover.outerRegionDeformation_continuous (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    Continuous
      (fun p : unitInterval × outerRegion a => outerRegionDeformation a ha ha1 p.1 p.2) := by
  apply (collarCellMap_isQuotientMap a).continuous_lift_prod_right
  have hc :=
    (collarCellMap_continuous a).comp
      (CuspCentralHomology.Radial.outwardOpenCollarHomotopy a ha ha1).continuous
  simpa only [outerRegionDeformation_collarCellMap, Function.comp_def, Prod.eta] using hc

def CuspCentralHomology.BaseCover.outerRegionRetraction (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    C(outerRegion a, boundary)
    where
  toFun
    x := ⟨outerRegionDeformation a ha ha1 1 x, outerRegionDeformation_one_mem_boundary a ha ha1 x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((outerRegionDeformation_continuous a ha ha1).comp
            (continuous_const.prodMk continuous_id))).subtype_mk
      _

@[simp]
theorem CuspCentralHomology.BaseCover.outerRegionRetraction_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : outerRegion a) :
    (outerRegionRetraction a ha ha1 x : BaseTorus) = outerRegionDeformation a ha ha1 1 x :=
  rfl

theorem CuspCentralHomology.BaseCover.outerRegionRetraction_collarCellMap (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (p : CuspCentralHomology.Radial.OpenCollar a) :
    (outerRegionRetraction a ha ha1 (collarCellMap a p) : BaseTorus) =
      basePoint
        ((CuspCentralHomology.Radial.cellGauge p)⁻¹ • (p : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionRetraction_coe, outerRegionDeformation_collarCellMap_coe]
  simp

@[simp]
theorem CuspCentralHomology.BaseCover.outerRegionRetraction_comp_inclusion (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (outerRegionRetraction a ha ha1).comp (outerRegionBoundaryInclusion a ha1) =
      ContinuousMap.id boundary := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    (outerRegionDeformation a ha ha1 1 (outerRegionBoundaryInclusion a ha1 x) : BaseTorus) = x
  exact
    congrArg Subtype.val
      (outerRegionDeformation_fixed a ha ha1 1 (outerRegionBoundaryInclusion a ha1 x) x.2)

def CuspCentralHomology.BaseCover.outerRegionHomotopyRel (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (ContinuousMap.id (outerRegion a)).HomotopyRel
      ((outerRegionBoundaryInclusion a ha1).comp (outerRegionRetraction a ha ha1))
      {x : outerRegion a | (x : BaseTorus) ∈ boundary}
    where
  toFun p := outerRegionDeformation a ha ha1 p.1 p.2
  continuous_toFun := outerRegionDeformation_continuous a ha ha1
  map_zero_left := outerRegionDeformation_zero a ha ha1
  map_one_left _ := rfl
  prop' := outerRegionDeformation_fixed a ha ha1

def CuspCentralHomology.BaseCover.outerRegionBoundaryHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : outerRegion a ≃ₕ boundary
    where
  toFun := outerRegionRetraction a ha ha1
  invFun := outerRegionBoundaryInclusion a ha1
  left_inv := ⟨(outerRegionHomotopyRel a ha ha1).toHomotopy.symm⟩
  right_inv := by
    refine ⟨?_⟩
    rw [outerRegionRetraction_comp_inclusion]
    exact ContinuousMap.Homotopy.refl _

def CuspCentralHomology.BaseCover.interiorCellInclusion :
    C(CuspCentralHomology.Radial.InteriorCell, CuspHoneycombTiling.baseCell)
    where
  toFun y := ⟨(y : (CuspHoneycombTiling.Plane)), interior_subset y.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def CuspCentralHomology.BaseCover.interiorCellMap :
    C(CuspCentralHomology.Radial.InteriorCell, BaseTorus) :=
  cellMap.comp interiorCellInclusion

def CuspCentralHomology.BaseCover.interiorCellToInnerRegion :
    C(CuspCentralHomology.Radial.InteriorCell, innerRegion)
    where
  toFun
    y :=
    ⟨cellMap (interiorCellInclusion y),
      (cellMap_mem_innerRegion_iff (interiorCellInclusion y)).mpr y.property⟩
  continuous_toFun := interiorCellMap.continuous.subtype_mk _

theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_injective :
    Function.Injective interiorCellToInnerRegion := by
  intro y z h
  have he : interiorCellInclusion y = interiorCellInclusion z :=
    cellMap_eq_of_interior (interiorCellInclusion y) (interiorCellInclusion z) y.property
      (congrArg Subtype.val h)
  apply Subtype.ext
  exact congrArg (fun x : CuspHoneycombTiling.baseCell => (x : (CuspHoneycombTiling.Plane))) he

theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_surjective :
    Function.Surjective interiorCellToInnerRegion := by
  intro q
  obtain ⟨y, hy⟩ := cellMap_surjective (q : BaseTorus)
  have hyinner : (y : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
    apply (cellMap_mem_innerRegion_iff y).mp
    rw [hy]
    exact q.property
  refine ⟨⟨(y : (CuspHoneycombTiling.Plane)), hyinner⟩, ?_⟩
  apply Subtype.ext
  exact hy

def CuspCentralHomology.BaseCover.interiorPreimageHomeomorph :
    CuspCentralHomology.Radial.InteriorCell ≃ₜ (cellMap ⁻¹' innerRegion)
    where
  toFun
    y :=
    ⟨interiorCellInclusion y,
      (cellMap_mem_innerRegion_iff (interiorCellInclusion y)).mpr y.property⟩
  invFun
    y := ⟨(y.1 : (CuspHoneycombTiling.Plane)), (cellMap_mem_innerRegion_iff y.1).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := interiorCellInclusion.continuous.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_isProperMap :
    IsProperMap interiorCellToInnerRegion := by
  have h :=
    (cellMap_isProperMap.restrictPreimage innerRegion).comp interiorPreimageHomeomorph.isProperMap
  have he :
    innerRegion.restrictPreimage cellMap ∘ interiorPreimageHomeomorph =
      interiorCellToInnerRegion := by
    funext y
    apply Subtype.ext
    rfl
  rw [he] at h
  exact h

theorem CuspCentralHomology.BaseCover.interiorCellToInnerRegion_isClosedMap :
    IsClosedMap interiorCellToInnerRegion :=
  interiorCellToInnerRegion_isProperMap.isClosedMap

def CuspCentralHomology.BaseCover.interiorCellHomeomorph :
    CuspCentralHomology.Radial.InteriorCell ≃ₜ innerRegion :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective interiorCellToInnerRegion
      ⟨interiorCellToInnerRegion_injective, interiorCellToInnerRegion_surjective⟩)
    interiorCellToInnerRegion.continuous interiorCellToInnerRegion_isClosedMap

@[simp]
theorem CuspCentralHomology.BaseCover.interiorCellHomeomorph_coe
    (y : CuspCentralHomology.Radial.InteriorCell) :
    (interiorCellHomeomorph y : BaseTorus) = cellMap (interiorCellInclusion y) :=
  rfl

def CuspCentralHomology.BaseCover.innerRegionCellHomeomorph :
    innerRegion ≃ₜ CuspCentralHomology.Radial.InteriorCell :=
  interiorCellHomeomorph.symm

def CuspCentralHomology.BaseCover.innerRegionPointHomotopyEquiv : innerRegion ≃ₕ Unit :=
  innerRegionCellHomeomorph.toHomotopyEquiv.trans
    CuspCentralHomology.Radial.interiorCellPointHomotopyEquiv

instance CuspCentralHomology.BaseCover.innerRegion_contractibleSpace :
    ContractibleSpace innerRegion :=
  innerRegionPointHomotopyEquiv.contractibleSpace

def CuspCentralHomology.BaseCover.overlapRegion (a : ℝ) : Set BaseTorus :=
  outerRegion a ∩ innerRegion

def CuspCentralHomology.BaseCover.overlapIntoInner (a : ℝ) : C(overlapRegion a, innerRegion) :=
  ⟨fun q => ⟨(q : BaseTorus), q.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def CuspCentralHomology.BaseCover.overlapIntoOuter (a : ℝ) : C(overlapRegion a, outerRegion a) :=
  ⟨fun q => ⟨(q : BaseTorus), q.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def CuspCentralHomology.BaseCover.annulusCellInclusion (a : ℝ) :
    C(CuspCentralHomology.Radial.Annulus a, CuspCentralHomology.Radial.InteriorCell) :=
  ⟨fun y =>
    ⟨(y : (CuspHoneycombTiling.Plane)),
      (CuspCentralHomology.Radial.mem_interior_baseCell_iff _).mpr y.property.2⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem CuspCentralHomology.BaseCover.annulusCellInclusion_coe (a : ℝ)
    (y : CuspCentralHomology.Radial.Annulus a) :
    (annulusCellInclusion a y : (CuspHoneycombTiling.Plane)) =
      (y : (CuspHoneycombTiling.Plane)) :=
  rfl

theorem CuspCentralHomology.BaseCover.annulusCellInclusion_injective (a : ℝ) :
    Function.Injective (annulusCellInclusion a) := by
  intro y z h
  apply Subtype.ext
  exact
    congrArg
      (fun x : CuspCentralHomology.Radial.InteriorCell => (x : (CuspHoneycombTiling.Plane))) h

@[simp]
theorem CuspCentralHomology.BaseCover.interiorCellHomeomorph_radius
    (y : CuspCentralHomology.Radial.InteriorCell) :
    radius (interiorCellHomeomorph y : BaseTorus) =
      CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)) := by
  rw [interiorCellHomeomorph_coe, radius_cellMap]
  rfl

def CuspCentralHomology.BaseCover.overlapCellMap (a : ℝ) :
    C(CuspCentralHomology.Radial.Annulus a, overlapRegion a)
    where
  toFun
    y :=
    ⟨(interiorCellHomeomorph (annulusCellInclusion a y) : BaseTorus),
      by
      constructor
      · change a < radius (interiorCellHomeomorph (annulusCellInclusion a y) : BaseTorus)
        rw [interiorCellHomeomorph_radius, annulusCellInclusion_coe]
        exact y.property.1
      · exact (interiorCellHomeomorph (annulusCellInclusion a y)).property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (interiorCellHomeomorph.continuous.comp (annulusCellInclusion a).continuous)).subtype_mk
      _

theorem CuspCentralHomology.BaseCover.overlapCellMap_intoInner (a : ℝ)
    (y : CuspCentralHomology.Radial.Annulus a) :
    overlapIntoInner a (overlapCellMap a y) = interiorCellHomeomorph (annulusCellInclusion a y) :=
  rfl

def CuspCentralHomology.BaseCover.overlapCellInverse (a : ℝ) :
    C(overlapRegion a, CuspCentralHomology.Radial.Annulus a)
    where
  toFun
    q :=
    let y := interiorCellHomeomorph.symm (overlapIntoInner a q)
    ⟨(y : (CuspHoneycombTiling.Plane)), by
      constructor
      · rw [← interiorCellHomeomorph_radius y]
        dsimp only [y]
        rw [Homeomorph.apply_symm_apply]
        exact q.property.1
      · exact (CuspCentralHomology.Radial.mem_interior_baseCell_iff _).mp y.property⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (interiorCellHomeomorph.symm.continuous.comp
            (overlapIntoInner a).continuous)).subtype_mk
      _

theorem CuspCentralHomology.BaseCover.overlapCellInverse_interior (a : ℝ) (q : overlapRegion a) :
    annulusCellInclusion a (overlapCellInverse a q) =
      interiorCellHomeomorph.symm (overlapIntoInner a q) :=
  rfl

def CuspCentralHomology.BaseCover.annulusOverlapHomeomorph (a : ℝ) :
    CuspCentralHomology.Radial.Annulus a ≃ₜ overlapRegion a
    where
  toFun := overlapCellMap a
  invFun := overlapCellInverse a
  left_inv
    y := by
    apply annulusCellInclusion_injective a
    rw [overlapCellInverse_interior, overlapCellMap_intoInner, Homeomorph.symm_apply_apply]
  right_inv
    q := by
    apply Subtype.ext
    change
      (interiorCellHomeomorph (annulusCellInclusion a (overlapCellInverse a q)) : BaseTorus) =
        (q : BaseTorus)
    rw [overlapCellInverse_interior, Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := (overlapCellMap a).continuous
  continuous_invFun := (overlapCellInverse a).continuous

def CuspCentralHomology.BaseCover.overlapHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    overlapRegion a ≃ₜ CuspCentralHomology.Radial.CellFrontier × Set.Ioo a 1 :=
  (annulusOverlapHomeomorph a).symm.trans (CuspCentralHomology.Radial.annulusHomeomorph a ha)

def CuspCentralHomology.BaseCover.overlapDirection (a : ℝ) (ha : 0 ≤ a) :
    C(overlapRegion a, CuspCentralHomology.Radial.CellFrontier) :=
  ⟨fun q => (overlapHomeomorph a ha q).1, continuous_fst.comp (overlapHomeomorph a ha).continuous⟩

theorem CuspCentralHomology.BaseCover.overlapDirection_annulus (a : ℝ) (ha : 0 ≤ a)
    (y : CuspCentralHomology.Radial.Annulus a) :
    (overlapDirection a ha (annulusOverlapHomeomorph a y) : (CuspHoneycombTiling.Plane)) =
      (CuspCentralHomology.Radial.cellGauge (y : (CuspHoneycombTiling.Plane)))⁻¹ •
        (y : (CuspHoneycombTiling.Plane)) := by
  change
    ((CuspCentralHomology.Radial.annulusHomeomorph a ha
            ((annulusOverlapHomeomorph a).symm (annulusOverlapHomeomorph a y))).1 :
        (CuspHoneycombTiling.Plane)) =
      _
  rw [Homeomorph.symm_apply_apply]
  rfl

def CuspCentralHomology.BaseCover.overlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    overlapRegion a ≃ₕ _root_.Circle :=
  (annulusOverlapHomeomorph a).symm.toHomotopyEquiv.trans
    (CuspCentralHomology.Radial.annulusCircleHomotopyEquiv a ha ha1)

theorem CuspCentralHomology.BaseCover.overlapCircleHomotopyEquiv_eq_direction (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (q : overlapRegion a) :
    overlapCircleHomotopyEquiv a ha ha1 q =
      CuspCentralHomology.Radial.frontierCellCircleHomeomorph (overlapDirection a ha q) :=
  rfl

theorem CuspCentralHomology.BaseCover.overlapIntoOuter_boundary_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (outerRegionRetraction a ha ha1).comp (overlapIntoOuter a) =
      circleBoundaryMap.comp (overlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨y, rfl⟩ := (annulusOverlapHomeomorph a).surjective q
  apply Subtype.ext
  have hin :
    overlapIntoOuter a (annulusOverlapHomeomorph a y) =
      collarCellMap a ⟨(y : (CuspHoneycombTiling.Plane)), y.2.1, y.2.2.le⟩ :=
    rfl
  change
    (outerRegionRetraction a ha ha1 (overlapIntoOuter a (annulusOverlapHomeomorph a y)) :
        BaseTorus) =
      (circleBoundaryMap (overlapCircleHomotopyEquiv a ha ha1 (annulusOverlapHomeomorph a y)) :
        BaseTorus)
  rw [hin, outerRegionRetraction_collarCellMap, circleBoundaryMap_coe,
    overlapCircleHomotopyEquiv_eq_direction, Homeomorph.symm_apply_apply,
    overlapDirection_annulus]

def CuspCentralHomology.BaseCover.outerRegionThetaHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : outerRegion a ≃ₕ CuspCentralHomology.Theta :=
  (outerRegionBoundaryHomotopyEquiv a ha ha1).trans boundaryThetaHomeomorph.toHomotopyEquiv

theorem CuspCentralHomology.BaseCover.overlapIntoOuter_theta_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (outerRegionThetaHomotopyEquiv a ha ha1).toFun.comp (overlapIntoOuter a) =
      circleThetaMap.comp (overlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  exact
    congrArg (fun f : C(overlapRegion a, boundary) => boundaryThetaHomeomorph (f q))
      (overlapIntoOuter_boundary_map a ha ha1)

def CuspCentralHomology.BaseCover.baseBoundaryNullhomotopy :
    (boundaryInclusion.comp circleBoundaryMap).Homotopy
      (ContinuousMap.const Circle
        (CuspCentralHomology.baseTorusPoint (0 : (CuspHoneycombTiling.Plane))))
    where
  toFun
    p :=
    CuspCentralHomology.baseTorusPoint
      ((1 - (p.1 : ℝ)) •
        (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm p.2 :
          (CuspHoneycombTiling.Plane)))
  continuous_toFun :=
    CuspCentralHomology.baseTorusPoint_continuous.comp
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp
          (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm.continuous.comp
            continuous_snd)))
  map_zero_left
    z := by
    change
      CuspCentralHomology.baseTorusPoint
          ((1 - (0 : ℝ)) •
            (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm z :
              (CuspHoneycombTiling.Plane))) =
        _
    rw [sub_zero, one_smul]
    rfl
  map_one_left
    z := by
    change
      CuspCentralHomology.baseTorusPoint
          ((1 - (1 : ℝ)) •
            (CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm z :
              (CuspHoneycombTiling.Plane))) =
        _
    rw [sub_self, zero_smul]
    rfl

theorem CuspCentralHomology.BaseCover.baseBoundary_homotopic_const :
    (boundaryInclusion.comp circleBoundaryMap).Homotopic
      (ContinuousMap.const Circle
        (CuspCentralHomology.baseTorusPoint (0 : (CuspHoneycombTiling.Plane)))) :=
  ⟨baseBoundaryNullhomotopy⟩

theorem CuspCentralHomology.BaseCover.thetaBaseMap_circleThetaMap_homotopic_const :
    (CuspCentralHomology.thetaBaseMap.comp circleThetaMap).Homotopic
      (ContinuousMap.const Circle
        (CuspCentralHomology.baseTorusPoint (0 : (CuspHoneycombTiling.Plane)))) := by
  rw [thetaBaseMap_circleThetaMap]
  exact baseBoundary_homotopic_const

abbrev CuspCentralHomology.BaseCover.PhaseBase :=
  ToricSpace.CompactFibreTorus × BaseTorus

def CuspCentralHomology.BaseCover.phaseOuterRegion (a : ℝ) : Set PhaseBase :=
  Prod.snd ⁻¹' outerRegion a

def CuspCentralHomology.BaseCover.phaseInnerRegion : Set PhaseBase :=
  Prod.snd ⁻¹' innerRegion

def CuspCentralHomology.BaseCover.phaseOverlapRegion (a : ℝ) : Set PhaseBase :=
  phaseOuterRegion a ∩ phaseInnerRegion

theorem CuspCentralHomology.BaseCover.phaseOuterRegion_isOpen (a : ℝ) :
    IsOpen (phaseOuterRegion a) :=
  (outerRegion_isOpen a).preimage continuous_snd

theorem CuspCentralHomology.BaseCover.phaseInnerRegion_isOpen : IsOpen phaseInnerRegion :=
  innerRegion_isOpen.preimage continuous_snd

theorem CuspCentralHomology.BaseCover.phaseOuterRegion_union_phaseInnerRegion (a : ℝ)
    (ha1 : a < 1) : phaseOuterRegion a ∪ phaseInnerRegion = Set.univ := by
  change Prod.snd ⁻¹' outerRegion a ∪ Prod.snd ⁻¹' innerRegion = Set.univ
  rw [← Set.preimage_union, outerRegion_union_innerRegion a ha1, Set.preimage_univ]

private def CuspCentralHomology.BaseCover.phaseRegionProductHomeomorph_mo1973_14992
    (s : Set BaseTorus) : (Prod.snd ⁻¹' s : Set PhaseBase) ≃ₜ ToricSpace.CompactFibreTorus × s
    where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, (p.2 : BaseTorus)), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def CuspCentralHomology.BaseCover.phaseOuterRegionHomeomorph (a : ℝ) :
    phaseOuterRegion a ≃ₜ ToricSpace.CompactFibreTorus × outerRegion a :=
  phaseRegionProductHomeomorph_mo1973_14992 (outerRegion a)

def CuspCentralHomology.BaseCover.phaseInnerRegionHomeomorph :
    phaseInnerRegion ≃ₜ ToricSpace.CompactFibreTorus × innerRegion :=
  phaseRegionProductHomeomorph_mo1973_14992 innerRegion

def CuspCentralHomology.BaseCover.phaseOverlapRegionHomeomorph (a : ℝ) :
    phaseOverlapRegion a ≃ₜ ToricSpace.CompactFibreTorus × overlapRegion a :=
  phaseRegionProductHomeomorph_mo1973_14992 (overlapRegion a)

def CuspCentralHomology.BaseCover.phaseOverlapIntoInner (a : ℝ) :
    C(phaseOverlapRegion a, phaseInnerRegion) :=
  ⟨fun p => ⟨(p : PhaseBase), p.property.2⟩, continuous_subtype_val.subtype_mk _⟩

def CuspCentralHomology.BaseCover.phaseOverlapIntoOuter (a : ℝ) :
    C(phaseOverlapRegion a, phaseOuterRegion a) :=
  ⟨fun p => ⟨(p : PhaseBase), p.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def CuspCentralHomology.BaseCover.phaseOuterThetaHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    phaseOuterRegion a ≃ₕ ToricSpace.CompactFibreTorus × CuspCentralHomology.Theta :=
  (phaseOuterRegionHomeomorph a).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl ToricSpace.CompactFibreTorus).prodCongr
      (outerRegionThetaHomotopyEquiv a ha ha1))

def CuspCentralHomology.BaseCover.phaseInnerHomotopyEquiv :
    phaseInnerRegion ≃ₕ ToricSpace.CompactFibreTorus :=
  phaseInnerRegionHomeomorph.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl ToricSpace.CompactFibreTorus).prodCongr
          innerRegionPointHomotopyEquiv).trans
      (Homeomorph.prodUnique ToricSpace.CompactFibreTorus Unit).toHomotopyEquiv)

def CuspCentralHomology.BaseCover.phaseOverlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : phaseOverlapRegion a ≃ₕ ToricSpace.CompactFibreTorus × Circle :=
  (phaseOverlapRegionHomeomorph a).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl ToricSpace.CompactFibreTorus).prodCongr
      (overlapCircleHomotopyEquiv a ha ha1))

theorem CuspCentralHomology.BaseCover.phaseOverlapIntoInner_phase_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    phaseInnerHomotopyEquiv.toFun.comp (phaseOverlapIntoInner a) =
      (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus)).comp
        (phaseOverlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro p
  rfl

theorem CuspCentralHomology.BaseCover.phaseOverlapIntoOuter_theta_map (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (phaseOuterThetaHomotopyEquiv a ha ha1).toFun.comp (phaseOverlapIntoOuter a) =
      ((ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap circleThetaMap).comp
        (phaseOverlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · exact
      congrArg
        (fun f : C(overlapRegion a, CuspCentralHomology.Theta) =>
          f (phaseOverlapRegionHomeomorph a p).2)
        (overlapIntoOuter_theta_map a ha ha1)

theorem CuspCentralHomology.SpecializationCover.productCollapse_basePoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (y : (CuspHoneycombTiling.Plane)) :
    CuspSpecialization.productCollapse C ε hε (u, CuspCentralHomology.BaseCover.basePoint y) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) y, y) := by
  change
    CuspSpecialization.productCollapse C ε hε
        (u, PeriodTorusHigherHomology.coordinateProjection 2 (-ToricSpace.realCuspVector y)) =
      _
  rw [CuspSpecialization.productCollapse_coordinateProjection,
    CuspSpecialization.realCuspVector_neg_realCuspVector]

theorem CuspCentralHomology.SpecializationCover.productCollapse_cellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (y : CuspHoneycombTiling.baseCell) :
    CuspSpecialization.productCollapse C ε hε (u, CuspCentralHomology.BaseCover.cellMap y) =
      CuspCentralHomology.fundamentalCellMap C ε hε
        (u * CuspSpecialization.sourcePhaseCharacter (C 0) (y : (CuspHoneycombTiling.Plane)),
          y) :=
  productCollapse_basePoint C ε hε u y

theorem CuspCentralHomology.SpecializationCover.productCollapse_radius
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspCentralHomology.centralRadius C ε hε (CuspSpecialization.productCollapse C ε hε p) =
      CuspCentralHomology.BaseCover.radius p.2 := by
  rcases p with ⟨u, b⟩
  obtain ⟨y, rfl⟩ := CuspCentralHomology.BaseCover.cellMap_surjective b
  rw [productCollapse_cellMap, CuspCentralHomology.centralRadius_fundamentalCellMap,
    CuspCentralHomology.BaseCover.radius_cellMap]

@[simp]
theorem CuspCentralHomology.SpecializationCover.productCollapse_mem_outer_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspSpecialization.productCollapse C ε hε p ∈ CuspCentralHomology.outerRegion C ε hε a ↔
      p ∈ CuspCentralHomology.BaseCover.phaseOuterRegion a := by
  change
    a < CuspCentralHomology.centralRadius C ε hε (CuspSpecialization.productCollapse C ε hε p) ↔
      a < CuspCentralHomology.BaseCover.radius p.2
  rw [productCollapse_radius]

@[simp]
theorem CuspCentralHomology.SpecializationCover.productCollapse_mem_inner_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspSpecialization.productCollapse C ε hε p ∈ CuspCentralHomology.innerRegion C ε hε ↔
      p ∈ CuspCentralHomology.BaseCover.phaseInnerRegion := by
  change
    CuspCentralHomology.centralRadius C ε hε (CuspSpecialization.productCollapse C ε hε p) < 1 ↔
      CuspCentralHomology.BaseCover.radius p.2 < 1
  rw [productCollapse_radius]

@[simp]
theorem CuspCentralHomology.SpecializationCover.productCollapse_mem_overlap_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ)
    (p : CuspCentralHomology.BaseCover.PhaseBase) :
    CuspSpecialization.productCollapse C ε hε p ∈ CuspCentralHomology.overlapRegion C ε hε a ↔
      p ∈ CuspCentralHomology.BaseCover.phaseOverlapRegion a := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [productCollapse_mem_outer_iff, productCollapse_mem_inner_iff]

theorem CuspCentralHomology.SpecializationCover.productCollapse_mapsTo_outer
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) :
    Set.MapsTo (CuspSpecialization.productCollapse C ε hε)
      (CuspCentralHomology.BaseCover.phaseOuterRegion a)
      (CuspCentralHomology.outerRegion C ε hε a) :=
  fun p hp => (productCollapse_mem_outer_iff C ε hε a p).mpr hp

theorem CuspCentralHomology.SpecializationCover.productCollapse_mapsTo_inner
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set.MapsTo (CuspSpecialization.productCollapse C ε hε)
      CuspCentralHomology.BaseCover.phaseInnerRegion (CuspCentralHomology.innerRegion C ε hε) :=
  fun p hp => (productCollapse_mem_inner_iff C ε hε p).mpr hp

def CuspCentralHomology.SpecializationCover.overlapMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) :
    C(CuspCentralHomology.BaseCover.phaseOverlapRegion a,
      CuspCentralHomology.overlapRegion C ε hε a)
    where
  toFun
    p :=
    ⟨CuspSpecialization.productCollapse C ε hε p,
      (productCollapse_mem_overlap_iff C ε hε a p).mpr p.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (CuspSpecialization.productCollapse C ε hε).continuous.comp continuous_subtype_val

@[simp]
theorem CuspCentralHomology.SpecializationCover.overlapMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (p : CuspCentralHomology.BaseCover.phaseOverlapRegion a) :
    (overlapMap C ε hε a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspSpecialization.productCollapse C ε hε p :=
  rfl

theorem CuspCentralHomology.productCollapse_connecting_naturality
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha1 : a < 1) (n : ℕ)
    (x : SingularMayerVietoris.SingularHomology BaseCover.PhaseBase (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (SpecializationCover.overlapMap C ε hε a) n
        (SingularMayerVietoris.connectingHomomorphism (BaseCover.phaseOuterRegion a)
          BaseCover.phaseInnerRegion (BaseCover.phaseOuterRegion_isOpen a)
          BaseCover.phaseInnerRegion_isOpen
          (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1) n x) =
      SingularMayerVietoris.connectingHomomorphism (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) n
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          (n + 1) x) :=
  SingularMayerVietoris.connectingHomomorphism_naturality_apply
    (CuspSpecialization.productCollapse C ε hε) (BaseCover.phaseOuterRegion a)
    BaseCover.phaseInnerRegion (outerRegion C ε hε a) (innerRegion C ε hε)
    (SpecializationCover.productCollapse_mapsTo_outer C ε hε a)
    (SpecializationCover.productCollapse_mapsTo_inner C ε hε)
    (BaseCover.phaseOuterRegion_isOpen a) BaseCover.phaseInnerRegion_isOpen
    (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1)
    (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) n x

def CuspCentralHomology.SpecializationCover.phaseCellShear (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Set (CuspHoneycombTiling.Plane)) :
    (ToricSpace.CompactFibreTorus × s) ≃ₜ (ToricSpace.CompactFibreTorus × s)
    where
  toFun
    p :=
    (p.1 * CuspSpecialization.sourcePhaseCharacter C₀ (p.2 : (CuspHoneycombTiling.Plane)), p.2)
  invFun
    p :=
    (p.1 * (CuspSpecialization.sourcePhaseCharacter C₀ (p.2 : (CuspHoneycombTiling.Plane)))⁻¹,
      p.2)
  left_inv p := by simp only [mul_inv_cancel_right, Prod.eta]
  right_inv p := by simp only [mul_assoc, inv_mul_cancel, mul_one, Prod.eta]
  continuous_toFun :=
    (continuous_fst.mul
          ((CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp
            (continuous_subtype_val.comp continuous_snd))).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul
          (((CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp
              (continuous_subtype_val.comp continuous_snd)).inv)).prodMk
      continuous_snd

@[simp]
theorem CuspCentralHomology.SpecializationCover.phaseCellShear_apply
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : Set (CuspHoneycombTiling.Plane))
    (p : ToricSpace.CompactFibreTorus × s) :
    phaseCellShear C₀ s p =
      (p.1 * CuspSpecialization.sourcePhaseCharacter C₀ (p.2 : (CuspHoneycombTiling.Plane)),
        p.2) :=
  rfl

def CuspCentralHomology.SpecializationCover.phaseCellShearHomotopy (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Set (CuspHoneycombTiling.Plane)) :
    (ContinuousMap.id (ToricSpace.CompactFibreTorus × s)).Homotopy
      (phaseCellShear C₀ s :
        C(ToricSpace.CompactFibreTorus × s, ToricSpace.CompactFibreTorus × s))
    where
  toFun
    p :=
    (p.2.1 *
        CuspSpecialization.sourcePhaseCharacter C₀
          ((p.1 : ℝ) • (p.2.2 : (CuspHoneycombTiling.Plane))),
      p.2.2)
  continuous_toFun := by
    have hy :
      Continuous
        (fun p : unitInterval × (ToricSpace.CompactFibreTorus × s) =>
          (p.1 : ℝ) • (p.2.2 : (CuspHoneycombTiling.Plane))) :=
      (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
    have hχ :
      Continuous
        (fun p : unitInterval × (ToricSpace.CompactFibreTorus × s) =>
          CuspSpecialization.sourcePhaseCharacter C₀
            ((p.1 : ℝ) • (p.2.2 : (CuspHoneycombTiling.Plane)))) := by
      simpa only [Function.comp_def] using
        (CuspSpecialization.sourcePhaseCharacter_continuous C₀).comp hy
    exact
      ((continuous_fst.comp continuous_snd).mul hχ).prodMk (continuous_snd.comp continuous_snd)
  map_zero_left p := by simp [CuspSpecialization.sourcePhaseCharacter_zero]
  map_one_left p := by simp [phaseCellShear_apply]

theorem CuspCentralHomology.BaseCover.overlapRegion_pathConnectedSpace (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) : PathConnectedSpace (overlapRegion a) := by
  let : PathConnectedSpace CuspCentralHomology.Radial.CellFrontier :=
    CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm.surjective.pathConnectedSpace
      CuspCentralHomology.Radial.frontierCellCircleHomeomorph.symm.continuous
  let : PathConnectedSpace (Set.Ioo a 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo a 1).isPathConnected (Set.nonempty_Ioo.mpr ha1))
  exact
    (overlapHomeomorph a ha).symm.surjective.pathConnectedSpace
      (overlapHomeomorph a ha).symm.continuous

theorem CuspCentralHomology.BaseCover.halfCoverLeftHomologyZero_injective :
    Function.Injective
      (SingularMayerVietoris.leftHomologyMap (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
        (CuspCentralHomology.BaseCover.innerRegion) 0) := by
  let := overlapRegion_pathConnectedSpace (1 / 2) (by norm_num) (by norm_num)
  let i :
    C((CuspCentralHomology.BaseCover.overlapRegion (1 / 2)),
      (CuspCentralHomology.BaseCover.innerRegion)) :=
    ContinuousMap.inclusion
      (Set.inter_subset_right :
        (CuspCentralHomology.BaseCover.outerRegion (1 / 2)) ∩
            (CuspCentralHomology.BaseCover.innerRegion) ⊆
          (CuspCentralHomology.BaseCover.innerRegion))
  intro x y hxy
  have hi :
    SingularMayerVietoris.singularHomologyMap i 0 x =
      SingularMayerVietoris.singularHomologyMap i 0 y := by
    have h := congrArg Prod.snd hxy
    simp only [SingularMayerVietoris.leftHomologyMap_apply, neg_inj] at h
    change
      SingularMayerVietoris.singularHomologyMap i 0 x =
        SingularMayerVietoris.singularHomologyMap i 0 y at h
    exact h
  apply
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (CuspCentralHomology.BaseCover.overlapRegion (1 / 2))).injective
  have h :=
    congrArg
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (CuspCentralHomology.BaseCover.innerRegion))
      hi
  exact
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural i x).symm.trans
      (h.trans (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural i y))

theorem CuspCentralHomology.BaseCover.halfCoverRightHomologyOne_surjective :
    Function.Surjective
      (SingularMayerVietoris.rightHomologyMap (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
        (CuspCentralHomology.BaseCover.innerRegion) 1) := by
  let hU := outerRegion_isOpen (1 / 2)
  let hV := innerRegion_isOpen
  let hc := outerRegion_union_innerRegion (1 / 2) (by norm_num)
  intro x
  have hz :
    SingularMayerVietoris.connectingHomomorphism
        (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
        (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0 x =
      0 := by
    apply halfCoverLeftHomologyZero_injective
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.connectingHomomorphism_comp_left
          (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
          (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0)
        x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h
  have hm :
    x ∈
      LinearMap.ker
        (SingularMayerVietoris.connectingHomomorphism
          (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
          (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0) :=
    hz
  rw [←
    SingularMayerVietoris.exact_at_ambient (CuspCentralHomology.BaseCover.outerRegion (1 / 2))
      (CuspCentralHomology.BaseCover.innerRegion) hU hV hc 0] at hm
  exact hm

theorem CuspCentralHomology.BaseCover.thetaBaseMap_homology_one_surjective :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaBaseMap 1) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspCentralHomology.BaseCover.innerRegion) 1) :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton
      (CuspCentralHomology.BaseCover.innerRegion) 1 (by decide)
  let e := outerRegionThetaHomotopyEquiv (1 / 2) (by norm_num) (by norm_num)
  let E := PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 1
  have he :
    (SingularMayerVietoris.subtypeInclusion
            (CuspCentralHomology.BaseCover.outerRegion (1 / 2))).comp
        e.symm.toFun =
      CuspCentralHomology.thetaBaseMap := by
    apply ContinuousMap.ext
    intro q
    rfl
  intro z
  obtain ⟨⟨x, y⟩, hxy⟩ := halfCoverRightHomologyOne_surjective z
  refine ⟨E x, ?_⟩
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion
          (CuspCentralHomology.BaseCover.outerRegion (1 / 2)))
        1 (E.symm (E x)) =
      z
  rw [E.symm_apply_apply]
  have hy : y = 0 := Subsingleton.elim _ _
  simpa only [SingularMayerVietoris.rightHomologyMap_apply, hy, map_zero, add_zero] using hxy

def CuspCentralHomology.BaseCover.thetaForgetSection :
    C(CuspCentralHomology.Theta, CuspCentralHomology.ThreeCircleSuspension) :=
  ⟨fun q => CuspCentralHomology.thetaCharacterCollapse (1, q),
    CuspCentralHomology.thetaCharacterCollapse.continuous.comp
      (continuous_const.prodMk continuous_id)⟩

@[simp]
theorem CuspCentralHomology.BaseCover.thetaForgetCircle_section (q : CuspCentralHomology.Theta) :
    CuspCentralHomology.thetaForgetCircle (thetaForgetSection q) = q :=
  CuspCentralHomology.thetaForgetCircle_collapse 1 q

theorem CuspCentralHomology.BaseCover.thetaForgetCircle_comp_section :
    CuspCentralHomology.thetaForgetCircle.comp thetaForgetSection =
      ContinuousMap.id CuspCentralHomology.Theta := by
  apply ContinuousMap.ext
  exact thetaForgetCircle_section

theorem CuspCentralHomology.BaseCover.thetaForgetCircle_homology_surjective (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle n) := by
  have h :
    (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle n).comp
        (SingularMayerVietoris.singularHomologyMap thetaForgetSection n) =
      LinearMap.id := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, thetaForgetCircle_comp_section,
      PeriodTorusHigherHomology.singularHomologyMap_id]
  intro x
  exact
    ⟨SingularMayerVietoris.singularHomologyMap thetaForgetSection n x, LinearMap.congr_fun h x⟩

theorem CuspCentralHomology.BaseCover.thetaBaseMap_comp_forget_homology_one_injective :
    Function.Injective
      ((SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaBaseMap 1).comp
        (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle 1)) := by
  let : Module.Finite ℤ (SingularMayerVietoris.SingularHomology BaseTorus 1) :=
    PeriodTorusHigherHomology.productTorus_homology_finite 2 1
  let e : SingularMayerVietoris.SingularHomology BaseTorus 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    PeriodTorusHigherHomology.productTorusHomologyEquiv 2 1
  let i := CuspCentralHomology.threeCircleSuspensionHomologyOneEquiv.trans e.symm
  exact
    IsNoetherian.injective_of_surjective_of_injective i.toLinearMap _ i.injective
      (thetaBaseMap_homology_one_surjective.comp (thetaForgetCircle_homology_surjective 1))

theorem CuspCentralHomology.BaseCover.thetaBaseMap_homology_one_injective :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaBaseMap 1) := by
  intro x y hxy
  obtain ⟨x', rfl⟩ := thetaForgetCircle_homology_surjective 1 x
  obtain ⟨y', rfl⟩ := thetaForgetCircle_homology_surjective 1 y
  exact
    congrArg (SingularMayerVietoris.singularHomologyMap CuspCentralHomology.thetaForgetCircle 1)
      (thetaBaseMap_comp_forget_homology_one_injective hxy)

theorem CuspCentralHomology.BaseCover.circleThetaMap_homology_one_eq_zero :
    SingularMayerVietoris.singularHomologyMap circleThetaMap 1 = 0 := by
  have hzero :=
    CuspCentralHomology.singularHomologyMap_eq_zero_of_nullhomotopic
      (CuspCentralHomology.thetaBaseMap.comp circleThetaMap)
      ⟨CuspCentralHomology.baseTorusPoint 0, thetaBaseMap_circleThetaMap_homotopic_const⟩ 1
      (by decide)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at hzero
  apply LinearMap.ext
  intro x
  apply thetaBaseMap_homology_one_injective
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hzero x

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def CuspCentralHomology.productParameterSection {D : Type} [TopologicalSpace D] (X : Type)
    [TopologicalSpace X] (d : D) : C(X, X × D) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X d)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.additiveProductParameter_homology_factor {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (β : C(AddCircle (1 : ℝ), D))
    (hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1) =
      (SingularMayerVietoris.singularHomologyMap
            ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) (n + 1)).comp
        (PeriodTorusHigherHomology.circleProjectionHomology X (n + 1)) := by
  have hs (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
        (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) (n + 1) a := by
    change
      ((SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)).comp
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.CircleTopology.productSection X) (n + 1)))
          a =
        _
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
    rfl
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := (PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm.surjective a
  have hp :
    PeriodTorusHigherHomology.circleProjectionHomology X (n + 1)
        ((PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm p) =
      p.1 := by
    change
      (PeriodTorusHigherHomology.circleProductHomologyEquiv X n
            ((PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm p)).1 =
        p.1
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.comp_apply, hp,
    PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross, map_add, hs,
    parameterMap_positiveCircleCross_eq_zero β hβ, add_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.productParameter_homology_factor {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1) =
      (SingularMayerVietoris.singularHomologyMap (productParameterSection X (α 1)) (n + 1)).comp
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
          (n + 1)) := by
  let β : C(AddCircle (1 : ℝ), D) :=
    α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
  have hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0 := by
    rw [show β = α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
        from rfl,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hα, LinearMap.zero_comp]
  let g : C(AddCircle (1 : ℝ) × X, X × _root_.Circle) :=
    (circleParametrizedSourceHomeomorph X : C(AddCircle (1 : ℝ) × X, X × _root_.Circle))
  have hmap :
    ((ContinuousMap.id X).prodMap α).comp g =
      (Homeomorph.prodComm D X : C(D × X, X × D)).comp (β.prodMap (ContinuousMap.id X)) :=
    rfl
  have hsection :
    (Homeomorph.prodComm D X : C(D × X, X × D)).comp
        ((ContinuousMap.const X (β 0)).prodMk (ContinuousMap.id X)) =
      productParameterSection X (α 1) := by
    apply ContinuousMap.ext
    intro x
    change (x, α (circleCoordinateHomeomorph.symm 0)) = (x, α 1)
    rw [circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]
  have hprojection :
    (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
            (n + 1)).comp
        (SingularMayerVietoris.singularHomologyMap g (n + 1)) =
      PeriodTorusHigherHomology.circleProjectionHomology X (n + 1) := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
    rfl
  have hpre :
    (SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1)).comp
        (SingularMayerVietoris.singularHomologyMap g (n + 1)) =
      ((SingularMayerVietoris.singularHomologyMap (productParameterSection X (α 1)) (n + 1)).comp
            (SingularMayerVietoris.singularHomologyMap
              (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1))).comp
        (SingularMayerVietoris.singularHomologyMap g (n + 1)) := by
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, hmap,
      PeriodTorusHigherHomology.singularHomologyMap_comp,
      additiveProductParameter_homology_factor β hβ n, ← LinearMap.comp_assoc, ←
      PeriodTorusHigherHomology.singularHomologyMap_comp, hsection, LinearMap.comp_assoc,
      hprojection]
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X)
          (n + 1)).surjective
      a
  exact LinearMap.congr_fun hpre b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem CuspCentralHomology.productParameter_homology_eq_zero_of_projection {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X × _root_.Circle) (n + 1))
    (ha :
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
          (n + 1) a =
        0) :
    SingularMayerVietoris.singularHomologyMap ((ContinuousMap.id X).prodMap α) (n + 1) a = 0 := by
  rw [productParameter_homology_factor α hα n, LinearMap.comp_apply, ha, map_zero]

def CuspCentralHomology.BaseCover.phaseOverlapHomologyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (phaseOverlapCircleHomotopyEquiv a ha ha1)
    n

def CuspCentralHomology.BaseCover.phaseOuterHomologyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (phaseOuterRegion a) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (ToricSpace.CompactFibreTorus × CuspCentralHomology.Theta) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (phaseOuterThetaHomotopyEquiv a ha ha1) n

def CuspCentralHomology.BaseCover.phaseInnerHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (CuspCentralHomology.BaseCover.phaseInnerRegion)
        n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv phaseInnerHomotopyEquiv n

theorem CuspCentralHomology.BaseCover.phaseInnerProjection_natural (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (n : ℕ) (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) n) :
    phaseInnerHomologyEquiv n
        (SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) n z) =
      SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.fst :
          C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
        n (phaseOverlapHomologyEquiv a ha ha1 n z) := by
  have hm :=
    congrArg
      (fun f : C((phaseOverlapRegion a), ToricSpace.CompactFibreTorus) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (phaseOverlapIntoInner_phase_map a ha ha1)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    phaseInnerHomologyEquiv, phaseOverlapHomologyEquiv,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply] using LinearMap.congr_fun hm z

theorem CuspCentralHomology.BaseCover.phaseOuterParameter_natural (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (n : ℕ) (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) n) :
    phaseOuterHomologyEquiv a ha ha1 n
        (SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoOuter a) n z) =
      SingularMayerVietoris.singularHomologyMap
        ((ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap circleThetaMap) n
        (phaseOverlapHomologyEquiv a ha ha1 n z) := by
  have hm :=
    congrArg
      (fun f :
          C((phaseOverlapRegion a), ToricSpace.CompactFibreTorus × CuspCentralHomology.Theta) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (phaseOverlapIntoOuter_theta_map a ha ha1)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    phaseOuterHomologyEquiv, phaseOverlapHomologyEquiv,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply] using LinearMap.congr_fun hm z

theorem CuspCentralHomology.BaseCover.phaseOverlapIntoOuter_homology_eq_zero_of_projection (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) (n + 1))
    (hz :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (phaseOverlapHomologyEquiv a ha ha1 (n + 1) z) =
        0) :
    SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoOuter a) (n + 1) z = 0 := by
  apply (phaseOuterHomologyEquiv a ha ha1 (n + 1)).injective
  rw [map_zero, phaseOuterParameter_natural]
  exact
    CuspCentralHomology.productParameter_homology_eq_zero_of_projection circleThetaMap
      circleThetaMap_homology_one_eq_zero n _ hz

theorem CuspCentralHomology.BaseCover.phaseLeftHomologyMap_eq_zero_iff_projection (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (phaseOverlapRegion a) (n + 1)) :
    SingularMayerVietoris.leftHomologyMap (phaseOuterRegion a)
          (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1) z =
        0 ↔
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (phaseOverlapHomologyEquiv a ha ha1 (n + 1) z) =
        0 := by
  have hleft :
    SingularMayerVietoris.leftHomologyMap (phaseOuterRegion a)
        (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1) z =
      (SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoOuter a) (n + 1) z,
        -SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z) :=
    SingularMayerVietoris.leftHomologyMap_apply (phaseOuterRegion a)
      (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1) z
  constructor
  · intro hz
    have hi : SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z = 0 :=
      by
      apply neg_eq_zero.mp
      exact congrArg Prod.snd (hleft.symm.trans hz)
    rw [← phaseInnerProjection_natural a ha ha1 (n + 1) z, hi, map_zero]
  · intro hz
    have hi : SingularMayerVietoris.singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z = 0 :=
      by
      apply (phaseInnerHomologyEquiv (n + 1)).injective
      rw [map_zero, phaseInnerProjection_natural a ha ha1 (n + 1) z]
      exact hz
    have ho := phaseOverlapIntoOuter_homology_eq_zero_of_projection a ha ha1 n z hz
    exact hleft.trans (by rw [ho, hi, neg_zero]; rfl)

theorem CuspCentralHomology.BaseCover.phaseConnecting_lift (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ)
    (x : SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) (n + 1))
    (hx :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) x =
        0) :
    ∃ y : SingularMayerVietoris.SingularHomology PhaseBase (n + 2),
      phaseOverlapHomologyEquiv a ha ha1 (n + 1)
          (SingularMayerVietoris.connectingHomomorphism (phaseOuterRegion a)
            (CuspCentralHomology.BaseCover.phaseInnerRegion) (phaseOuterRegion_isOpen a)
            phaseInnerRegion_isOpen (phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 1) y) =
        x := by
  let e := phaseOverlapHomologyEquiv a ha ha1 (n + 1)
  have hz :
    e.symm x ∈
      LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (phaseOuterRegion a)
          (CuspCentralHomology.BaseCover.phaseInnerRegion) (n + 1)) := by
    apply (phaseLeftHomologyMap_eq_zero_iff_projection a ha ha1 n (e.symm x)).mpr
    change
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (e (e.symm x)) =
        0
    rw [e.apply_symm_apply]
    exact hx
  have hmem :=
    (SingularMayerVietoris.exact_at_intersection (phaseOuterRegion a)
          (CuspCentralHomology.BaseCover.phaseInnerRegion) (phaseOuterRegion_isOpen a)
          phaseInnerRegion_isOpen (phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 1)).symm.le
      hz
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, (congrArg e hy).trans (e.apply_symm_apply x)⟩

abbrev CuspCentralHomology.SpecializationCover.annulusSet (a : ℝ) :
    Set (CuspHoneycombTiling.Plane) :=
  {y | a < CuspCentralHomology.Radial.cellGauge y ∧ CuspCentralHomology.Radial.cellGauge y < 1}

def CuspCentralHomology.SpecializationCover.sourceOverlapPhaseHomeomorph (a : ℝ) :
    CuspCentralHomology.BaseCover.phaseOverlapRegion a ≃ₜ
      CuspCentralHomology.OverlapPhaseCell a :=
  (CuspCentralHomology.BaseCover.phaseOverlapRegionHomeomorph a).trans
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr
      (CuspCentralHomology.BaseCover.annulusOverlapHomeomorph a).symm)

@[simp]
theorem CuspCentralHomology.SpecializationCover.sourceOverlapPhaseHomeomorph_symm_coe (a : ℝ)
    (p : CuspCentralHomology.OverlapPhaseCell a) :
    ((sourceOverlapPhaseHomeomorph a).symm p : CuspCentralHomology.BaseCover.PhaseBase) =
      (p.1, CuspCentralHomology.BaseCover.basePoint (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

theorem CuspCentralHomology.SpecializationCover.sourceOverlapCircle_factor (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (CuspCentralHomology.BaseCover.phaseOverlapCircleHomotopyEquiv a ha ha1).toFun =
      (CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha
            ha1).toFun.comp
        (sourceOverlapPhaseHomeomorph a :
          C(CuspCentralHomology.BaseCover.phaseOverlapRegion a,
            CuspCentralHomology.OverlapPhaseCell a)) :=
  rfl

theorem CuspCentralHomology.SpecializationCover.phaseCellShear_homologyMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : Set (CuspHoneycombTiling.Plane)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap
        (phaseCellShear C₀ s :
          C(ToricSpace.CompactFibreTorus × s, ToricSpace.CompactFibreTorus × s))
        n =
      LinearMap.id := by
  have h := PeriodTorusHigherHomology.homotopy_homologyMap (phaseCellShearHomotopy C₀ s) n
  rw [PeriodTorusHigherHomology.singularHomologyMap_id] at h
  exact h.symm

def CuspCentralHomology.SpecializationCover.collapseOverlapHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) :
    CuspCentralHomology.BaseCover.phaseOverlapRegion a ≃ₜ
      CuspCentralHomology.overlapRegion C ε hε a :=
  (sourceOverlapPhaseHomeomorph a).trans
    ((phaseCellShear (C 0) (annulusSet a)).trans
      (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a))

theorem CuspCentralHomology.SpecializationCover.collapseOverlapHomeomorph_apply
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ)
    (q : CuspCentralHomology.BaseCover.phaseOverlapRegion a) :
    collapseOverlapHomeomorph C ε hε hε1 hC hR a q = overlapMap C ε hε a q := by
  obtain ⟨p, rfl⟩ := (sourceOverlapPhaseHomeomorph a).symm.surjective q
  apply Subtype.ext
  rw [overlapMap_coe, sourceOverlapPhaseHomeomorph_symm_coe, productCollapse_basePoint]
  change
    (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a
          (phaseCellShear (C 0) (annulusSet a)
            (sourceOverlapPhaseHomeomorph a ((sourceOverlapPhaseHomeomorph a).symm p))) :
        CuspRetraction.QuotientCentralFibre C ε) =
      _
  rw [Homeomorph.apply_symm_apply, CuspCentralHomology.overlapPhaseHomeomorph_coe]
  rfl

theorem CuspCentralHomology.SpecializationCover.overlapMap_phase_coordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ)
    (q : CuspCentralHomology.BaseCover.phaseOverlapRegion a) :
    (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm (overlapMap C ε hε a q) =
      phaseCellShear (C 0) (annulusSet a) (sourceOverlapPhaseHomeomorph a q) := by
  apply (CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a).injective
  rw [Homeomorph.apply_symm_apply]
  exact (collapseOverlapHomeomorph_apply C ε hε hε1 hC hR a q).symm

theorem CuspCentralHomology.SpecializationCover.targetOverlapCircle_factor
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun.comp
        (overlapMap C ε hε a) =
      (CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha
            ha1).toFun.comp
        ((phaseCellShear (C 0) (annulusSet a) :
              C(ToricSpace.CompactFibreTorus × annulusSet a,
                ToricSpace.CompactFibreTorus × annulusSet a)).comp
          (sourceOverlapPhaseHomeomorph a :
            C(CuspCentralHomology.BaseCover.phaseOverlapRegion a,
              CuspCentralHomology.OverlapPhaseCell a))) := by
  apply ContinuousMap.ext
  intro q
  change
    CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha ha1
        ((CuspCentralHomology.overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
          (overlapMap C ε hε a q)) =
      _
  rw [overlapMap_phase_coordinates]
  rfl

theorem CuspCentralHomology.SpecializationCover.overlapMap_homology_intertwining
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
            (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (overlapMap C ε hε a) n) =
      (CuspCentralHomology.BaseCover.phaseOverlapHomologyEquiv a ha ha1 n).toLinearMap := by
  change
    (SingularMayerVietoris.singularHomologyMap
            (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun
            n).comp
        (SingularMayerVietoris.singularHomologyMap (overlapMap C ε hε a) n) =
      SingularMayerVietoris.singularHomologyMap
        (CuspCentralHomology.BaseCover.phaseOverlapCircleHomotopyEquiv a ha ha1).toFun n
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, targetOverlapCircle_factor,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp, phaseCellShear_homologyMap,
    LinearMap.id_comp, sourceOverlapCircle_factor,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

theorem CuspCentralHomology.SpecializationCover.overlapMap_homology_coordinates
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (x :
      SingularMayerVietoris.SingularHomology (CuspCentralHomology.BaseCover.phaseOverlapRegion a)
        n) :
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (CuspCentralHomology.overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n
        (SingularMayerVietoris.singularHomologyMap (overlapMap C ε hε a) n x) =
      CuspCentralHomology.BaseCover.phaseOverlapHomologyEquiv a ha ha1 n x :=
  LinearMap.congr_fun (overlapMap_homology_intertwining C ε hε hε1 hC hR a ha ha1 n) x

theorem CuspCentralHomology.productCollapse_homology_three_add_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
        (n + 3)) := by
  let a : ℝ := 1 / 2
  have ha : 0 ≤ a := by norm_num [a]
  have ha1 : a < 1 := by norm_num [a]
  let U := outerRegion C ε hε a
  let V := innerRegion C ε hε
  let hU := outerRegion_isOpen C ε hε hε1 hC hR a
  let hV := innerRegion_isOpen C ε hε hε1 hC hR
  let hc := outerRegion_union_innerRegion C ε hε a ha1
  let δT := SingularMayerVietoris.connectingHomomorphism U V hU hV hc (n + 2)
  let δS :=
    SingularMayerVietoris.connectingHomomorphism (BaseCover.phaseOuterRegion a)
      BaseCover.phaseInnerRegion (BaseCover.phaseOuterRegion_isOpen a)
      BaseCover.phaseInnerRegion_isOpen (BaseCover.phaseOuterRegion_union_phaseInnerRegion a ha1)
      (n + 2)
  let eT := middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 2)
  let : Subsingleton (SingularMayerVietoris.SingularHomology U (n + 3)) :=
    outerRegion_homology_subsingleton C ε hε hε1 hC hR a ha ha1 n
  let : Subsingleton (SingularMayerVietoris.SingularHomology V (n + 3)) :=
    innerRegion_homology_subsingleton C ε hε hε1 hC hR n
  have hδT : Function.Injective δT := coverConnecting_injective_of_vanishing U V hU hV hc (n + 2)
  intro b
  have hk : δT b ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V (n + 2)) := by
    change SingularMayerVietoris.leftHomologyMap U V (n + 2) (δT b) = 0
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.connectingHomomorphism_comp_left U V hU hV hc (n + 2)) b
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hx :
    SingularMayerVietoris.singularHomologyMap
        (ContinuousMap.fst :
          C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
        (n + 2) (eT (δT b)) =
      0 :=
    (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 (n + 1) (δT b)).mp hk
  obtain ⟨s, hs⟩ := BaseCover.phaseConnecting_lift a ha ha1 (n + 1) (eT (δT b)) hx
  refine ⟨s, hδT (eT.injective ?_)⟩
  have hnat :
    SingularMayerVietoris.singularHomologyMap (SpecializationCover.overlapMap C ε hε a) (n + 2)
        (δS s) =
      δT
        (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
          (n + 3) s) :=
    productCollapse_connecting_naturality C ε hε hε1 hC hR a ha1 (n + 2) s
  calc
    eT
          (δT
            (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C ε hε)
              (n + 3) s)) =
        eT
          (SingularMayerVietoris.singularHomologyMap (SpecializationCover.overlapMap C ε hε a)
            (n + 2) (δS s)) :=
      congrArg eT hnat.symm
    _ = BaseCover.phaseOverlapHomologyEquiv a ha ha1 (n + 2) (δS s) :=
      (SpecializationCover.overlapMap_homology_coordinates C ε hε hε1 hC hR a ha ha1 (n + 2)
        (δS s))
    _ = eT (δT b) := hs

theorem CuspCentralHomology.productCollapse_homology_three_add_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr)
        (n + 3)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, _hRDδ⟩ :=
    CuspRetraction.exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr.le)
  have he :=
    congrArg (fun f => SingularMayerVietoris.singularHomologyMap f (n + 3))
      (centralRadiusHomeomorph_comp_productCollapse C r δ hδr.le hC hδ)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at he
  rw [← he]
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
          (centralRadiusHomeomorph C r δ hδr.le hC hδ) (n + 3)).surjective.comp
      (productCollapse_homology_three_add_surjective C δ hδ hδ1 hCδ hRCδ n)

theorem CuspCentralHomology.productCollapse_homologyThree_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr) 3) :=
  productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 0

theorem CuspCentralHomology.productCollapse_homologyFour_surjective_of_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (CuspSpecialization.productCollapse C r hr) 4) :=
  productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 1

theorem CuspSpecialization.torusDifference_three_exterior
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (CuspCoinvariants.torusDifference 3 a) =
      CuspCoinvariants.exteriorCubeDifference
        (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a) := by
  change
    PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 3
            a -
          a) =
      exteriorPower.map 3 M₀.mulVecLin
          (PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a) -
        PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a
  rw [map_sub, PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv_matrix]

theorem CuspSpecialization.markedCollapse_homologyThree_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3) :=
  markedCollapse_homology_surjective_of_product C ε hε 3
    (CuspCentralHomology.productCollapse_homologyThree_surjective_of_holomorphic C ε hε hC)

theorem CuspSpecialization.markedCollapse_homologyThree_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3) =
      LinearMap.range (CuspCoinvariants.torusDifference 3) := by
  let := CuspCentralHomology.centralSingularH3_free C ε hε hC
  let := CuspCentralHomology.centralSingularH3_finite C ε hε hC
  exact
    CuspCoinvariants.torusThree_kernel_eq_of_invariant _
      (markedCollapse_homologyThree_surjective C ε hε hC)
      (markedCollapse_homology_invariant C ε hε 3)
      (CuspCentralHomology.centralSingularH3_finrank C ε hε hC)

theorem CuspSpecialization.markedCollapse_homologyThree_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 3) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 3,
        exteriorPower.map 3 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a := by
  change
    a ∈ LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C ε hε) 3) ↔
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv a ∈
        LinearMap.range CuspCoinvariants.exteriorCubeDifference
  rw [markedCollapse_homologyThree_kernel C ε hε hC]
  exact
    CuspCoinvariants.mem_range_iff_of_intertwines
      PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
      (CuspCoinvariants.torusDifference 3) CuspCoinvariants.exteriorCubeDifference
      torusDifference_three_exterior a

theorem CuspSpecialization.markedCollapse_homologyZero_augmentation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) 0) :
    CuspCentralHomology.centralSingularH0Equiv C r hr
        (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0 a) =
      PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (PeriodTorusHigherHomology.ProductTorus 4) a :=
  CuspCentralHomology.centralSingularH0Equiv_natural C r hr (markedCollapse C r hr) a

theorem CuspSpecialization.markedCollapse_homologyZero_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0) := by
  constructor
  · intro a b hab
    apply
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
          (PeriodTorusHigherHomology.ProductTorus 4)).injective
    rw [← markedCollapse_homologyZero_augmentation C r hr a, ←
      markedCollapse_homologyZero_augmentation C r hr b, hab]
  · intro b
    obtain ⟨a, ha⟩ :=
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
            (PeriodTorusHigherHomology.ProductTorus 4)).surjective
        (CuspCentralHomology.centralSingularH0Equiv C r hr b)
    refine ⟨a, ?_⟩
    apply (CuspCentralHomology.centralSingularH0Equiv C r hr).injective
    rw [markedCollapse_homologyZero_augmentation]
    exact ha

theorem CuspSpecialization.markedCollapse_homologyZero_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyZero_bijective C r hr).injective

theorem CuspSpecialization.markedMonodromy_homologyZero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 0 =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (markedCollapse_homologyZero_bijective C r hr).injective
  exact markedCollapse_homology_invariant C r hr 0 a

theorem CuspSpecialization.markedMonodromy_homologyZero_variation_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 0 -
        LinearMap.id =
      0 := by rw [markedMonodromy_homologyZero C r hr, sub_self]

theorem CuspSpecialization.markedMonodromy_homologyZero_variation_range
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            0 -
          LinearMap.id) =
      ⊥ := by rw [markedMonodromy_homologyZero_variation_zero C r hr, LinearMap.range_zero]

theorem CuspSpecialization.markedCollapse_homologyZero_kernel_eq_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 0) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            0 -
          LinearMap.id) := by
  rw [markedCollapse_homologyZero_kernel, markedMonodromy_homologyZero_variation_range C r hr]

theorem CuspSpecialization.markedCollapse_homologyFour_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) :=
  markedCollapse_homology_surjective_of_product C r hr 4
    (CuspCentralHomology.productCollapse_homologyFour_surjective_of_holomorphic C r hr hC)

theorem CuspSpecialization.markedCollapse_homologyFour_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) := by
  let := PeriodTorusHigherHomology.productTorus_homology_free 4 4
  let := PeriodTorusHigherHomology.productTorus_homology_finite 4 4
  let := CuspCentralHomology.centralSingularH4_free C r hr hC
  let := CuspCentralHomology.centralSingularH4_finite C r hr hC
  apply
    OrzechProperty.bijective_of_surjective_of_finrank_le
      (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4)
      (markedCollapse_homologyFour_surjective C r hr hC)
  rw [PeriodTorusHigherHomology.productTorus_homology_finrank,
    CuspCentralHomology.centralSingularH4_finrank C r hr hC]
  simp

theorem CuspSpecialization.markedCollapse_homologyFour_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyFour_bijective C r hr hC).injective

theorem CuspSpecialization.markedMonodromy_homologyFour (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 4 =
      LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (markedCollapse_homologyFour_bijective C r hr hC).injective
  exact markedCollapse_homology_invariant C r hr 4 a

theorem CuspSpecialization.markedMonodromy_homologyFour_variation_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) 4 -
        LinearMap.id =
      0 := by rw [markedMonodromy_homologyFour C r hr hC, sub_self]

theorem CuspSpecialization.markedMonodromy_homologyFour_variation_range
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            4 -
          LinearMap.id) =
      ⊥ := by rw [markedMonodromy_homologyFour_variation_zero C r hr hC, LinearMap.range_zero]

theorem CuspSpecialization.markedCollapse_homologyFour_kernel_eq_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) 4) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            4 -
          LinearMap.id) := by
  rw [markedCollapse_homologyFour_kernel C r hr hC,
    markedMonodromy_homologyFour_variation_range C r hr hC]

theorem CuspSpecialization.markedCollapse_homologyHigher_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) (hn : 4 < n) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  let := CuspCentralHomology.centralSingularHomology_subsingleton_of_four_lt C r hr hC hn
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

theorem CuspSpecialization.markedCollapse_homologyHigher_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ)
    (hn : 4 < n) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (markedCollapse_homologyHigher_bijective C r hr hC n hn).injective

theorem CuspSpecialization.markedCollapse_homologyHigher_kernel_eq_variation
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) (hn : 4 < n) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            n -
          LinearMap.id) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  have hvariation :
    SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n -
        LinearMap.id =
      0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  rw [markedCollapse_homologyHigher_kernel C r hr hC n hn, hvariation, LinearMap.range_zero]

theorem CuspSpecialization.markedCollapse_homology_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    Function.Surjective (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) := by
  rcases n with _ | (_ | (_ | n))
  · exact (markedCollapse_homologyZero_bijective C r hr).surjective
  · exact markedCollapse_homologyOne_surjective C r hr hC
  · exact markedCollapse_homologyTwo_surjective C r hr hC
  · exact
      markedCollapse_homology_surjective_of_product C r hr (n + 3)
        (CuspCentralHomology.productCollapse_homology_three_add_surjective_of_holomorphic C r hr
          hC n)

theorem CuspSpecialization.markedCollapse_homology_kernel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (n : ℕ) :
    LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) =
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀)
            n -
          LinearMap.id) := by
  rcases n with _ | (_ | (_ | (_ | (_ | n))))
  · exact markedCollapse_homologyZero_kernel_eq_variation C r hr
  · simpa only [CuspCoinvariants.torusDifference] using
      markedCollapse_homologyOne_kernel C r hr hC
  · simpa only [CuspCoinvariants.torusDifference] using
      markedCollapse_homologyTwo_kernel C r hr hC
  · simpa only [CuspCoinvariants.torusDifference] using
      markedCollapse_homologyThree_kernel C r hr hC
  · exact markedCollapse_homologyFour_kernel_eq_variation C r hr hC
  · exact markedCollapse_homologyHigher_kernel_eq_variation C r hr hC (n + 5) (by omega)

theorem CuspSpecialization.markedCollapse_homology_eq_zero_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n) :
    SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n a = 0 ↔
      ∃ b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n,
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
              b -
            b =
          a := by
  change
    a ∈ LinearMap.ker (SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n) ↔ _
  rw [markedCollapse_homology_kernel C r hr hC n]
  rfl

theorem CuspSpecialization.markedSpecialization_homology_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {X : Type} [TopologicalSpace X]
    (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap f n a =
      SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n
        ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a) := by
  have heq := PeriodTorusHigherHomology.homotopic_homologyMap h n
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at heq
  have ha :=
    LinearMap.congr_fun heq ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a)
  change
    SingularMayerVietoris.singularHomologyMap (markedCollapse C r hr) n
        ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a) =
      SingularMayerVietoris.singularHomologyMap f n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n
          ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a)) at ha
  rw [LinearEquiv.apply_symm_apply] at ha
  exact ha.symm

theorem CuspSpecialization.markedSpecialization_homology_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (n : ℕ) : Function.Surjective (SingularMayerVietoris.singularHomologyMap f n) := by
  intro b
  obtain ⟨a, ha⟩ := markedCollapse_homology_surjective C r hr hC n b
  refine ⟨PeriodTorusHigherHomology.homeomorphHomologyEquiv E n a, ?_⟩
  rw [markedSpecialization_homology_map C r hr E f h n, LinearEquiv.symm_apply_apply]
  exact ha

theorem CuspSpecialization.markedSpecialization_homology_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap f n a = 0 ↔
      ∃ b : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 4) n,
        SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.torusMatrixMap M₀) n
              b -
            b =
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm a := by
  rw [markedSpecialization_homology_map C r hr E f h n,
    markedCollapse_homology_eq_zero_iff C r hr hC n]

theorem CuspSpecialization.markedSpecialization_homologyTwo_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (a : SingularMayerVietoris.SingularHomology X 2) :
    SingularMayerVietoris.singularHomologyMap f 2 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 2,
        exteriorPower.map 2 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
            ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 2).symm a) := by
  rw [markedSpecialization_homology_map C r hr E f h 2,
    markedCollapse_homologyTwo_eq_zero_iff C r hr hC]

theorem CuspSpecialization.markedSpecialization_homologyThree_eq_zero_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) {X : Type}
    [TopologicalSpace X] (E : PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ X)
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (h :
      (markedCollapse C r hr).Homotopic
        (f.comp (E : C(PeriodTorusHigherHomology.ProductTorus 4, X))))
    (a : SingularMayerVietoris.SingularHomology X 3) :
    SingularMayerVietoris.singularHomologyMap f 3 a = 0 ↔
      ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 3,
        exteriorPower.map 3 M₀.mulVecLin v - v =
          PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
            ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 3).symm a) := by
  rw [markedSpecialization_homology_map C r hr E f h 3,
    markedCollapse_homologyThree_eq_zero_iff C r hr hC]

theorem CuspCentralHomology.exists_actual_specialization_homology
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ (η₀ : ℝ) (_hη₀ : 0 < η₀),
      η₀ < r ∧
        η₀ < 1 ∧
          ∀ (t : ℂ) (ht : t ≠ 0),
            ‖t‖ ≤ η₀ →
              ∃ E :
                PeriodTorusHigherHomology.ProductTorus 4 ≃ₜ
                  CuspControlledRetraction.ActualQuotientFibre C r t,
                ∀ (η : ℝ) (_hη : η ≤ η₀) (htη : ‖t‖ ≤ η) (hηr : η < r),
                  ∃ hc :
                    Continuous
                      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
                        htη),
                    let f :
                      C(CuspControlledRetraction.ActualQuotientFibre C r t,
                        CuspRetraction.QuotientCentralFibre C r) :=
                      ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη,
                        hc⟩
                    (CuspSpecialization.markedCollapse C r hr).Homotopic
                        (f.comp
                          (E :
                            C(PeriodTorusHigherHomology.ProductTorus 4,
                              CuspControlledRetraction.ActualQuotientFibre C r t))) ∧
                      (∀ n : ℕ,
                          Function.Surjective (SingularMayerVietoris.singularHomologyMap f n) ∧
                            ∀ a :
                              SingularMayerVietoris.SingularHomology
                                (CuspControlledRetraction.ActualQuotientFibre C r t) n,
                              SingularMayerVietoris.singularHomologyMap f n a = 0 ↔
                                ∃ b :
                                  SingularMayerVietoris.SingularHomology
                                    (PeriodTorusHigherHomology.ProductTorus 4) n,
                                  SingularMayerVietoris.singularHomologyMap
                                        (PeriodTorusHigherHomology.torusMatrixMap M₀) n b -
                                      b =
                                    (PeriodTorusHigherHomology.homeomorphHomologyEquiv E n).symm
                                      a) ∧
                        (∀ a :
                            SingularMayerVietoris.SingularHomology
                              (CuspControlledRetraction.ActualQuotientFibre C r t) 2,
                            SingularMayerVietoris.singularHomologyMap f 2 a = 0 ↔
                              ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 2,
                                exteriorPower.map 2 M₀.mulVecLin v - v =
                                  PeriodTorusHigherHomology.coordinateTorusH2ExteriorEquiv
                                    ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 2).symm
                                      a)) ∧
                          (∀ a :
                            SingularMayerVietoris.SingularHomology
                              (CuspControlledRetraction.ActualQuotientFibre C r t) 3,
                            SingularMayerVietoris.singularHomologyMap f 3 a = 0 ↔
                              ∃ v : PeriodTorusHigherHomologyExterior.latticeExterior 3,
                                exteriorPower.map 3 M₀.mulVecLin v - v =
                                  PeriodTorusHigherHomology.coordinateTorusH3ExteriorEquiv
                                    ((PeriodTorusHigherHomology.homeomorphHomologyEquiv E 3).symm
                                      a)) := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hmodels⟩ :=
    CuspSpecialization.exists_original_marked_specialization_models C r hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro t ht ht₀
  obtain ⟨E, hE⟩ := hmodels t ht ht₀
  refine ⟨E, ?_⟩
  intro η hη htη hηr
  obtain ⟨hc, hh, _⟩ := hE η hη htη hηr
  let f :
    C(CuspControlledRetraction.ActualQuotientFibre C r t,
      CuspRetraction.QuotientCentralFibre C r) :=
    ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩
  refine ⟨hc, hh, ?_, ?_, ?_⟩
  · intro n
    exact
      ⟨CuspSpecialization.markedSpecialization_homology_surjective C r hr hC E f hh n,
        CuspSpecialization.markedSpecialization_homology_eq_zero_iff C r hr hC E f hh n⟩
  · exact CuspSpecialization.markedSpecialization_homologyTwo_eq_zero_iff C r hr hC E f hh
  · exact CuspSpecialization.markedSpecialization_homologyThree_eq_zero_iff C r hr hC E f hh

def CuspCentralHomology.retractionEndpointHomotopy {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (i : C(A, X)) (R S : C(X, A)) (hR : R.comp i = ContinuousMap.id A)
    (H : (ContinuousMap.id X).Homotopy (i.comp S)) : R.Homotopy S
    where
  toFun p := R (H p)
  continuous_toFun := R.continuous.comp H.continuous
  map_zero_left x := congrArg R (H.map_zero_left x)
  map_one_left x := (congrArg R (H.map_one_left x)).trans (ContinuousMap.congr_fun hR (S x))

def CuspCentralHomology.actualFibreIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η : ℝ) (t : ℂ)
    (htη : ‖t‖ ≤ η) :
    C(CuspControlledRetraction.ActualQuotientFibre C r t, CuspRetraction.ClosedQuotient C r η)
    where
  toFun q := ⟨q.1, by rw [q.2]; exact htη⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

theorem CuspCentralHomology.exists_controlled_retraction_all_levels
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ (hηr : η < r) (t₀ : ℂ) (ht₀ : t₀ ≠ 0) (ht₀η : ‖t₀‖ ≤ η),
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
                          ∃ hc₀ :
                            Continuous
                              (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr
                                t₀ ht₀ ht₀η),
                            R.comp (actualFibreIntoClosed C r η t₀ ht₀η) =
                                ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr
                                    t₀ ht₀ ht₀η,
                                  hc₀⟩ ∧
                              ∀ (t : ℂ) (ht : t ≠ 0) (htη : ‖t‖ ≤ η),
                                ∃ hc :
                                  Continuous
                                    (CuspControlledRetraction.prescribedActualFibreCollapse C r hr
                                      hηr t ht htη),
                                  (R.comp (actualFibreIntoClosed C r η t htη)).Homotopic
                                      ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r
                                          hr hηr t ht htη,
                                        hc⟩ ∧
                                    ∀ n,
                                      SingularMayerVietoris.singularHomologyMap
                                          (R.comp (actualFibreIntoClosed C r η t htη)) n =
                                        SingularMayerVietoris.singularHomologyMap
                                          ⟨CuspControlledRetraction.prescribedActualFibreCollapse
                                              C r hr hηr t ht htη,
                                            hc⟩
                                          n := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hret⟩ :=
    CuspControlledRetraction.exists_controlled_actual_fibre_retraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ hηr t₀ ht₀ ht₀η
  obtain ⟨R, hR, H, hmono, hendpoint⟩ := hret η hη hηη₀ t₀ ht₀ ht₀η
  obtain ⟨hc₀, he₀, _hrep₀⟩ := hendpoint hηr
  refine ⟨R, hR, H, hmono, hc₀, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro q
    exact he₀ q
  · intro t ht htη
    obtain ⟨S, _hS, HS, _hmonoS, hendpointS⟩ := hret η hη hηη₀ t ht htη
    obtain ⟨hc, he, _hrep⟩ := hendpointS hηr
    have hemap :
      S.comp (actualFibreIntoClosed C r η t htη) =
        (⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :
          C(CuspControlledRetraction.ActualQuotientFibre C r t,
            CuspRetraction.QuotientCentralFibre C r)) := by
      apply ContinuousMap.ext
      intro q
      exact he q
    let K :=
      retractionEndpointHomotopy (CuspRetraction.quotientCentralIntoClosed C r η hη.le) R S hR
        HS.toHomotopy
    have hk :
      (R.comp (actualFibreIntoClosed C r η t htη)).Homotopic
        ⟨CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht htη, hc⟩ :=
      ⟨(K.comp (ContinuousMap.Homotopy.refl (actualFibreIntoClosed C r η t htη))).cast rfl hemap⟩
    exact ⟨hc, hk, fun n => PeriodTorusHigherHomology.homotopic_homologyMap hk n⟩

def ThreefoldHomologyCuspFibre.actualFibreInclusion (D : SpecialPeriods.CuspFamily.Data) (t : ℂ) :
    C(CuspControlledRetraction.ActualQuotientFibre D.correction D.radius t,
      ThreefoldHomologyFinitenessCusp.FullSpace D) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def ThreefoldHomologyCuspFibre.fibreCentralHomotopy (D : SpecialPeriods.CuspFamily.Data) (η : ℝ)
    (hη : 0 ≤ η)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient D.correction D.radius η)).Homotopy
        ((CuspRetraction.quotientCentralIntoClosed D.correction D.radius η hη).comp R))
    (t : ℂ) (htη : ‖t‖ ≤ η) :
    (actualFibreInclusion D t).Homotopy
      ((ThreefoldHomologyFinitenessCusp.fullCentralInclusion D).comp
        (R.comp (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη)))
    where
  toFun
    p :=
    (H (p.1, CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη p.2)).val
  continuous_toFun :=
    continuous_subtype_val.comp
      (H.continuous.comp
        (continuous_fst.prodMk
          ((CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t
                htη).continuous.comp
            continuous_snd)))
  map_zero_left
    q :=
    congrArg Subtype.val
      (H.map_zero_left
        (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη q))
  map_one_left
    q :=
    congrArg Subtype.val
      (H.map_one_left (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius η t htη q))

theorem ThreefoldHomologyCuspFibre.exists_smallFibreInclusion_homology_surjective
    (D : SpecialPeriods.CuspFamily.Data) :
    ∃ δ : ℝ,
      0 < δ ∧
        δ < D.radius ∧
          ∀ (t : ℂ),
            t ≠ 0 →
              ‖t‖ ≤ δ →
                ∀ n : ℕ,
                  Function.Surjective
                    (SingularMayerVietoris.singularHomologyMap (actualFibreInclusion D t) n) := by
  obtain ⟨δs, hδs, hδsr, _hδs1, hspec⟩ :=
    CuspCentralHomology.exists_actual_specialization_homology D.correction D.radius D.radius_pos
      D.holomorphic
  obtain ⟨δr, hδr, _hδrr, _hδr1, hret⟩ :=
    CuspCentralHomology.exists_controlled_retraction_all_levels D.correction D.radius_pos
      D.holomorphic
  let δ := Min.min δs δr
  have hδ : 0 < δ := lt_min hδs hδr
  have hδradius : δ < D.radius := (min_le_left δs δr).trans_lt hδsr
  refine ⟨δ, hδ, hδradius, ?_⟩
  intro t ht htδ n
  obtain ⟨E, hE⟩ := hspec t ht (htδ.trans (min_le_left δs δr))
  obtain ⟨hc, _hmarked, hsurj, _h2, _h3⟩ := hE δ (min_le_left δs δr) htδ hδradius
  let c :
    C(CuspControlledRetraction.ActualQuotientFibre D.correction D.radius t,
      CuspRetraction.QuotientCentralFibre D.correction D.radius) :=
    ⟨CuspControlledRetraction.prescribedActualFibreCollapse D.correction D.radius D.radius_pos
        hδradius t ht htδ,
      hc⟩
  obtain ⟨R, _hR, H, _hmono, hc', hend, _hall⟩ := hret δ hδ (min_le_right δs δr) hδradius t ht htδ
  have hend' :
    R.comp (CuspCentralHomology.actualFibreIntoClosed D.correction D.radius δ t htδ) = c := hend
  have hm :
    SingularMayerVietoris.singularHomologyMap (actualFibreInclusion D t) n =
      (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomologyFinitenessCusp.fullCentralInclusion D) n).comp
        (SingularMayerVietoris.singularHomologyMap c n) := by
    rw [PeriodTorusHigherHomology.homotopy_homologyMap
        (fibreCentralHomotopy D δ hδ.le R H.toHomotopy t htδ) n,
      hend', PeriodTorusHigherHomology.singularHomologyMap_comp]
  rw [hm, ← ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv_toLinearMap]
  exact (ThreefoldHomologyFinitenessCusp.fullCentralHomologyEquiv D n).surjective.comp (hsurj n).1

def ThreefoldHomologyCuspFibre.heightParameter (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) : ℂ :=
  CuspUniformization.exponential
    (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h)

theorem ThreefoldHomologyCuspFibre.heightParameter_ne_zero (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) : heightParameter D h ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

theorem ThreefoldHomologyCuspFibre.heightParameter_norm (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    ‖heightParameter D h‖ = Real.exp (-2 * Real.pi * (h : ℝ)) := by
  change
    ‖CuspUniformization.exponential
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h)‖ =
      _
  calc
    _ =
        Real.exp
          (Real.log
            ‖CuspUniformization.exponential
                (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h)‖) :=
      (Real.exp_log (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))).symm
    _ = _ := by
      rw [CuspUniformization.log_norm_exponential, ThreefoldOverlapMappingTorus.Cusp.logPoint_im]

def ThreefoldHomologyCuspFibre.fibreToFull (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    C(RealTorus₄, ThreefoldHomologyFinitenessCusp.FullSpace D) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
        C(CuspUniformization.PuncturedQuotient D.correction D.radius,
          ThreefoldHomologyFinitenessCusp.FullSpace D)).comp
    (ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h)

theorem ThreefoldHomologyCuspFibre.fibreToFull_projection (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius (fibreToFull D h x) = heightParameter D h :=
  ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_base D h 0 x

theorem ThreefoldHomologyCuspFibre.fibreToFull_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (x : RealPlane₄) :
    fibreToFull D h (standardLattice.mkQ x) =
      (CuspUniformization.puncturedCuspCover D.correction D.radius
          ⟨((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h : ℂ),
              D.periods.periodEquiv
                (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h) x),
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0
                h).property⟩).val :=
  congrArg Subtype.val (ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured_realCoordinates D h x)

def ThreefoldHomologyCuspFibre.fibreAtHeight (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    C(RealTorus₄,
      CuspControlledRetraction.ActualQuotientFibre D.correction D.radius (heightParameter D h))
    where
  toFun x := ⟨fibreToFull D h x, fibreToFull_projection D h x⟩
  continuous_toFun := (fibreToFull D h).continuous.subtype_mk _

theorem ThreefoldHomologyCuspFibre.fibreToPunctured_product (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D
        (ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h x) =
      (h,
        MappingTorus.HomologyCover.fibreInclusion ThreefoldOverlapMappingTorus.Cusp.monodromy
          x) :=
  (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).apply_symm_apply _

theorem ThreefoldHomologyCuspFibre.fibreAtHeight_injective (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    Function.Injective (fibreAtHeight D h) := by
  intro x y hxy
  have hfull : fibreToFull D h x = fibreToFull D h y :=
    congrArg
      (fun q :
          CuspControlledRetraction.ActualQuotientFibre D.correction D.radius
            (heightParameter D h) =>
        q.val)
      hxy
  have hp :
    ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h x =
      ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured D h y :=
    Subtype.ext hfull
  have hm :=
    congrArg Prod.snd
      (congrArg (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D) hp)
  rw [fibreToPunctured_product, fibreToPunctured_product] at hm
  change
    MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (0, x) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (0, y) at hm
  obtain ⟨k, hk, he⟩ :=
    (MappingTorus.mk_eq_mk_iff ThreefoldOverlapMappingTorus.Cusp.monodromy _ _).mp hm
  have hk0 : k = 0 := by
    have hk' : (k : ℝ) = 0 := by
      change (0 : ℝ) = 0 + (k : ℝ) at hk
      linarith
    exact_mod_cast hk'
  subst k
  simpa using he.symm

theorem ThreefoldHomologyCuspFibre.fibreAtHeight_surjective (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    Function.Surjective (fibreAtHeight D h) := by
  intro q
  let s := ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos 0 h
  have hs : ‖CuspUniformization.exponential (s : ℂ)‖ < D.radius :=
    (SpecialPeriods.CuspFamily.mem_logBase _ _).mp s.property
  have hq :
    q.val ∈
      Set.range
        (CuspUniformization.fibreMap D.correction D.radius s hs (D.logarithmic_height s)
          (D.logarithmic_drift s)) := by
    rw [CuspUniformization.fibreMap_range]
    exact q.property
  obtain ⟨y, hy⟩ := hq
  obtain ⟨z, rfl⟩ :=
    (CuspUniformization.periodData D.correction s (D.logarithmic_height s)
          (D.logarithmic_drift s)).lattice.mkQ_surjective
      y
  refine ⟨standardLattice.mkQ ((D.periods.periodEquiv s).symm z), Subtype.ext ?_⟩
  change fibreToFull D h (standardLattice.mkQ ((D.periods.periodEquiv s).symm z)) = q.val
  rw [fibreToFull_realCoordinates]
  change
    CuspUniformization.fibreCover D.correction D.radius s hs
        (D.periods.periodEquiv s ((D.periods.periodEquiv s).symm z)) =
      q.val
  rw [LinearEquiv.apply_symm_apply]
  exact hy

def ThreefoldHomologyCuspFibre.heightFibreHomeomorph (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    RealTorus₄ ≃ₜ
      CuspControlledRetraction.ActualQuotientFibre D.correction D.radius (heightParameter D h) := by
  letI :=
    CuspQuotient.quotient_t2Space D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact
    Continuous.homeoOfEquivCompactToT2 (f :=
      Equiv.ofBijective (fibreAtHeight D h)
        ⟨fibreAtHeight_injective D h, fibreAtHeight_surjective D h⟩)
      (fibreAtHeight D h).continuous

theorem ThreefoldHomologyCuspFibre.heightFibreHomeomorph_inclusion
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    (actualFibreInclusion D (heightParameter D h)).comp
        (heightFibreHomeomorph D h : C(RealTorus₄, _)) =
      fibreToFull D h :=
  rfl

def ThreefoldHomologyCuspFibre.fibreHeightHomotopy (D : SpecialPeriods.CuspFamily.Data)
    (h₀ h₁ : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    (fibreToFull D h₀).Homotopy (fibreToFull D h₁)
    where
  toFun
    p :=
    ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
        (ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀ (p.1, h₁),
          MappingTorus.HomologyCover.fibreInclusion ThreefoldOverlapMappingTorus.Cusp.monodromy
            p.2)).val
  continuous_toFun :=
    continuous_subtype_val.comp
      ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm.continuous.comp
        (((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).continuous.comp
              (continuous_fst.prodMk continuous_const)).prodMk
          ((MappingTorus.HomologyCover.fibreInclusion
                ThreefoldOverlapMappingTorus.Cusp.monodromy).continuous.comp
            continuous_snd)))
  map_zero_left
    x :=
    congrArg
      (fun h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius =>
        ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
            (h,
              MappingTorus.HomologyCover.fibreInclusion
                ThreefoldOverlapMappingTorus.Cusp.monodromy x)).val)
      ((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).map_zero_left h₁)
  map_one_left
    x :=
    congrArg
      (fun h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius =>
        ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
            (h,
              MappingTorus.HomologyCover.fibreInclusion
                ThreefoldOverlapMappingTorus.Cusp.monodromy x)).val)
      ((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).map_one_left h₁)

def SpecialPeriods.rho : ℂ :=
  (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

@[simp]
theorem SpecialPeriods.rho_re : rho.re = 1 / 2 := by
  norm_num [rho, Complex.div_re, Complex.normSq_apply]

@[simp]
theorem SpecialPeriods.rho_im : rho.im = Real.sqrt 3 / 2 := by
  norm_num [rho, Complex.div_im, Complex.normSq_apply]

theorem SpecialPeriods.rho_im_pos : 0 < rho.im := by
  rw [rho_im]
  positivity

theorem SpecialPeriods.rho_eq_exp : rho = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  unfold rho
  ring

theorem SpecialPeriods.rho_sq : rho ^ 2 = rho - 1 := by
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, rho_re, rho_im, Complex.sub_re, Complex.one_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · simp only [pow_two, Complex.mul_im, rho_re, rho_im, Complex.sub_im, Complex.one_im]
    ring

theorem SpecialPeriods.norm_rho : ‖rho‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply, rho_re,
    rho_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem SpecialPeriods.rho_cube : rho ^ 3 = -1 := by
  calc
    rho ^ 3 = rho * rho ^ 2 := by ring
    _ = rho * (rho - 1) := by rw [rho_sq]
    _ = -1 := by linear_combination rho_sq

theorem SpecialPeriods.conj_rho : starRingEnd ℂ rho = 1 - rho := by
  apply Complex.ext <;> simp
  ring

def SpecialPeriods.cayley (a z : ℂ) : ℂ :=
  (a - starRingEnd ℂ a * z) / (1 - z)

@[simp]
theorem SpecialPeriods.cayley_zero (a : ℂ) : cayley a 0 = a := by simp [cayley]

theorem SpecialPeriods.one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := (sub_eq_zero.mp h).symm
  simp [this] at hz

theorem SpecialPeriods.cayley_im (a z : ℂ) :
    (cayley a z).im = a.im * (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_im, Complex.sub_im, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.normSq_apply]
  ring

theorem SpecialPeriods.cayley_im_pos {a z : ℂ} (ha : 0 < a.im) (hz : ‖z‖ < 1) :
    0 < (cayley a z).im := by
  rw [cayley_im]
  apply div_pos
  · apply mul_pos ha
    rw [sub_pos, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  · exact Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz)

theorem SpecialPeriods.cayley_contDiffOn (a : ℂ) : ContDiffOn ℂ ω (cayley a) (Metric.ball 0 1) := by
  apply ContDiffOn.div
  · exact contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id)
  · exact contDiffOn_const.sub contDiffOn_id
  · intro z hz
    exact one_sub_ne_zero_of_norm_lt_one (by simpa using hz)

def SpecialPeriods.sectionThree (τ : ℂ) : PeriodPoint :=
  ⟨τ, (2 - τ) / 3, 2 * τ / 3 - Complex.I⟩

def SpecialPeriods.sectionFour (τ : ℂ) : PeriodPoint :=
  ⟨τ, (1 - τ) / 2, 3 * τ / 2 - Complex.I⟩

theorem SpecialPeriods.sectionThree_discriminant (τ : ℂ) (hτ : τ.im ≠ 0) :
    (sectionThree τ).discriminant = -1 := by
  apply mul_left_cancel₀ hτ
  simp [sectionThree, PeriodPoint.discriminant]
  field_simp
  ring

theorem SpecialPeriods.sectionFour_discriminant (τ : ℂ) (hτ : τ.im ≠ 0) :
    (sectionFour τ).discriminant = -1 := by
  apply mul_left_cancel₀ hτ
  simp [sectionFour, PeriodPoint.discriminant]
  field_simp
  ring

theorem SpecialPeriods.sectionThree_admissible {τ : ℂ} (hτ : 0 < τ.im) :
    (sectionThree τ).Admissible := by
  refine ⟨hτ, ?_⟩
  rw [sectionThree_discriminant τ hτ.ne']
  norm_num

theorem SpecialPeriods.sectionFour_admissible {τ : ℂ} (hτ : 0 < τ.im) :
    (sectionFour τ).Admissible := by
  refine ⟨hτ, ?_⟩
  rw [sectionFour_discriminant τ hτ.ne']
  norm_num

theorem SpecialPeriods.sectionThree_step (τ : ℂ) (hτ : τ ≠ 0) :
    (sectionThree τ).step₁ = sectionThree ((τ - 1) / τ) := by
  apply PeriodPoint.ext <;> simp [sectionThree, PeriodPoint.step₁] <;> field_simp <;> ring

theorem SpecialPeriods.sectionFour_step (τ : ℂ) (hτ : τ ≠ 0) :
    (sectionFour τ).step₂ = sectionFour (-1 / τ) := by
  apply PeriodPoint.ext <;> simp [sectionFour, PeriodPoint.step₂] <;> field_simp <;> ring

def SpecialPeriods.rotateThree (z : ℂ) : ℂ :=
  -rho * z

def SpecialPeriods.rotateFour (z : ℂ) : ℂ :=
  -Complex.I * z

@[simp]
theorem SpecialPeriods.norm_rotateThree (z : ℂ) : ‖rotateThree z‖ = ‖z‖ := by
  simp [rotateThree, norm_rho]

theorem SpecialPeriods.rotateThree_cube (z : ℂ) : rotateThree (rotateThree (rotateThree z)) = z :=
  by
  change -rho * (-rho * (-rho * z)) = z
  calc
    -rho * (-rho * (-rho * z)) = -(rho ^ 3) * z := by ring
    _ = z := by rw [rho_cube]; ring

theorem SpecialPeriods.rotateFour_fourth (z : ℂ) :
    rotateFour (rotateFour (rotateFour (rotateFour z))) = z := by simp [rotateFour, ← mul_assoc]

def SpecialPeriods.tauThree (z : ℂ) : ℂ :=
  cayley rho z

def SpecialPeriods.tauFour (z : ℂ) : ℂ :=
  cayley Complex.I (z ^ 2)

theorem SpecialPeriods.tauThree_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tauThree z).im :=
  cayley_im_pos rho_im_pos hz

theorem SpecialPeriods.tauFour_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tauFour z).im := by
  apply cayley_im_pos (by simp)
  rw [norm_pow]
  nlinarith [norm_nonneg z]

theorem SpecialPeriods.tauThree_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : tauThree z ≠ 0 := by
  intro he
  have := tauThree_im_pos hz
  simp [he] at this

theorem SpecialPeriods.tauFour_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : tauFour z ≠ 0 := by
  intro he
  have := tauFour_im_pos hz
  simp [he] at this

theorem SpecialPeriods.tauThree_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    tauThree (rotateThree z) = (tauThree z - 1) / tauThree z := by
  have hd : 1 - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz
  have hr : 1 + rho * z ≠ 0 := by
    simpa only [rotateThree, neg_mul, sub_neg_eq_add] using
      one_sub_ne_zero_of_norm_lt_one (show ‖rotateThree z‖ < 1 by simpa using hz)
  have hn : rho - (1 - rho) * (-rho * z) = rho + z := by linear_combination -z * rho_sq
  rw [eq_div_iff (tauThree_ne_zero hz)]
  simp only [tauThree, cayley, conj_rho, rotateThree]
  rw [hn]
  simp only [neg_mul, sub_neg_eq_add]
  field_simp
  linear_combination (1 - z ^ 2) * rho_sq

theorem SpecialPeriods.tauFour_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    tauFour (rotateFour z) = -1 / tauFour z := by
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hd : 1 - z ^ 2 ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz2
  have hp : 1 + z ^ 2 ≠ 0 := by
    intro h
    have he : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right h
    simp [he] at hz2
  simp [tauFour, cayley, rotateFour, mul_pow, Complex.I_sq]
  field_simp
  ring_nf
  simp

theorem SpecialPeriods.tauThree_contDiffOn : ContDiffOn ℂ ω tauThree (Metric.ball 0 1) :=
  cayley_contDiffOn rho

theorem SpecialPeriods.tauFour_contDiffOn : ContDiffOn ℂ ω tauFour (Metric.ball 0 1) := by
  apply (cayley_contDiffOn Complex.I).comp (contDiffOn_id.pow 2)
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right, norm_pow, id_eq] at *
  nlinarith [norm_nonneg z]

def SpecialPeriods.localThree (z : ℂ) : PeriodPoint :=
  sectionThree (tauThree z)

def SpecialPeriods.localFour (z : ℂ) : PeriodPoint :=
  sectionFour (tauFour z)

theorem SpecialPeriods.localThree_admissible {z : ℂ} (hz : ‖z‖ < 1) : (localThree z).Admissible :=
  sectionThree_admissible (tauThree_im_pos hz)

theorem SpecialPeriods.localFour_admissible {z : ℂ} (hz : ‖z‖ < 1) : (localFour z).Admissible :=
  sectionFour_admissible (tauFour_im_pos hz)

theorem SpecialPeriods.localThree_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    localThree (rotateThree z) = (localThree z).step₁ := by
  rw [localThree, tauThree_rotate hz]
  exact (sectionThree_step _ (tauThree_ne_zero hz)).symm

theorem SpecialPeriods.localFour_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    localFour (rotateFour z) = (localFour z).step₂ := by
  rw [localFour, tauFour_rotate hz]
  exact (sectionFour_step _ (tauFour_ne_zero hz)).symm

def SpecialPeriods.unitDisc : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

abbrev SpecialPeriods.Disc :=
  unitDisc

theorem SpecialPeriods.disc_norm_lt_one (z : Disc) : ‖(z : ℂ)‖ < 1 := by
  simpa [unitDisc] using z.property

theorem SpecialPeriods.tauThree_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Disc => tauThree z) :=
  tauThree_contDiffOn.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

theorem SpecialPeriods.tauFour_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Disc => tauFour z) :=
  tauFour_contDiffOn.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

def SpecialPeriods.threePeriodMap : HolomorphicPeriodMap ℂ Disc
    where
  point z := ⟨localThree z, localThree_admissible (disc_norm_lt_one z)⟩
  holomorphic_tau := tauThree_holomorphic
  holomorphic_mu := (contMDiff_const.sub tauThree_holomorphic).div_const 3
  holomorphic_beta := ((contMDiff_const.mul tauThree_holomorphic).div_const 3).sub contMDiff_const

def SpecialPeriods.fourPeriodMap : HolomorphicPeriodMap ℂ Disc
    where
  point z := ⟨localFour z, localFour_admissible (disc_norm_lt_one z)⟩
  holomorphic_tau := tauFour_holomorphic
  holomorphic_mu := (contMDiff_const.sub tauFour_holomorphic).div_const 2
  holomorphic_beta := ((contMDiff_const.mul tauFour_holomorphic).div_const 2).sub contMDiff_const

def SpecialPeriods.discZero : Disc :=
  ⟨0, by simp [unitDisc]⟩

@[simp]
theorem SpecialPeriods.discZero_val : (discZero : ℂ) = 0 :=
  rfl

def SpecialPeriods.discScalar (c : ℂ) (hc : ‖c‖ = 1) (z : Disc) : Disc :=
  ⟨c * z, by
    have hn : ‖c * (z : ℂ)‖ < 1 := by simpa [norm_mul, hc] using disc_norm_lt_one z
    simpa [unitDisc] using hn⟩

@[simp]
theorem SpecialPeriods.discScalar_val (c : ℂ) (hc : ‖c‖ = 1) (z : Disc) :
    (discScalar c hc z : ℂ) = c * z :=
  rfl

theorem SpecialPeriods.discScalar_holomorphic (c : ℂ) (hc : ‖c‖ = 1) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discScalar c hc) := by
  intro z
  have he :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun w : Disc => (discScalar c hc w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discScalar c hc) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_const.mul contMDiff_subtype_val) z)

theorem SpecialPeriods.discScalar_iterate_val (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) (z : Disc) :
    ((discScalar c hc)^[n] z : ℂ) = c ^ n * z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', discScalar_val, ih, pow_succ']
    rw [mul_assoc]

def SpecialPeriods.discRotateThree : Disc → Disc :=
  discScalar (-rho) (by simpa using norm_rho)

def SpecialPeriods.discRotateFour : Disc → Disc :=
  discScalar (-Complex.I) (by simp)

theorem SpecialPeriods.discRotateThree_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω discRotateThree :=
  discScalar_holomorphic _ _

theorem SpecialPeriods.discRotateFour_holomorphic : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω discRotateFour :=
  discScalar_holomorphic _ _

theorem SpecialPeriods.discRotateThree_cube (z : Disc) :
    discRotateThree (discRotateThree (discRotateThree z)) = z :=
  Subtype.ext (rotateThree_cube z)

theorem SpecialPeriods.discRotateFour_fourth (z : Disc) :
    discRotateFour (discRotateFour (discRotateFour (discRotateFour z))) = z :=
  Subtype.ext (rotateFour_fourth z)

theorem SpecialPeriods.discRotateThree_iterate_order : discRotateThree^[3] = id := by
  funext z
  exact discRotateThree_cube z

theorem SpecialPeriods.discRotateFour_iterate_order : discRotateFour^[4] = id := by
  funext z
  exact discRotateFour_fourth z

def SpecialPeriods.threeRotation : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Disc Disc ω
    where
  toFun := discRotateThree
  invFun := discRotateThree ∘ discRotateThree
  left_inv := discRotateThree_cube
  right_inv := discRotateThree_cube
  contMDiff_toFun := discRotateThree_holomorphic
  contMDiff_invFun := discRotateThree_holomorphic.comp discRotateThree_holomorphic

def SpecialPeriods.fourRotation : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) Disc Disc ω
    where
  toFun := discRotateFour
  invFun := discRotateFour ∘ discRotateFour ∘ discRotateFour
  left_inv := discRotateFour_fourth
  right_inv := discRotateFour_fourth
  contMDiff_toFun := discRotateFour_holomorphic
  contMDiff_invFun :=
    discRotateFour_holomorphic.comp (discRotateFour_holomorphic.comp discRotateFour_holomorphic)

theorem SpecialPeriods.neg_rho_pow_ne_one {n : ℕ} (hn : 0 < n) (hn' : n < 3) : (-rho) ^ n ≠ 1 := by
  interval_cases n
  · simp only [pow_one]
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.neg_im, Complex.one_im] at hh
    linarith [rho_im_pos]
  · rw [neg_sq, rho_sq]
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at hh
    linarith [rho_im_pos]

theorem SpecialPeriods.neg_I_pow_ne_one {n : ℕ} (hn : 0 < n) (hn' : n < 4) :
    (-Complex.I) ^ n ≠ 1 := by
  interval_cases n
  · intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  · norm_num
  · intro he
    have hh := congrArg Complex.im he
    norm_num [pow_succ] at hh

theorem SpecialPeriods.discScalar_iterate_fixed_iff (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ)
    (hn : c ^ n ≠ 1) (z : Disc) : (discScalar c hc)^[n] z = z ↔ z = discZero := by
  constructor
  · intro he
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    rw [discScalar_iterate_val] at hv
    by_contra hz
    apply hn
    exact mul_right_cancel₀ hz (by simpa using hv)
  · intro he
    subst z
    apply Subtype.ext
    rw [discScalar_iterate_val]
    simp

theorem SpecialPeriods.discRotateThree_iterate_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3)
    (z : Disc) : discRotateThree^[n] z = z ↔ z = discZero :=
  discScalar_iterate_fixed_iff _ _ n (neg_rho_pow_ne_one hn hn') z

theorem SpecialPeriods.discRotateFour_iterate_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4)
    (z : Disc) : discRotateFour^[n] z = z ↔ z = discZero :=
  discScalar_iterate_fixed_iff _ _ n (neg_I_pow_ne_one hn hn') z

theorem SpecialPeriods.threePeriodMap_rotate (z : Disc) :
    threePeriodMap.point (discRotateThree z) = (threePeriodMap.point z).step₁ :=
  Subtype.ext (localThree_rotate (disc_norm_lt_one z))

theorem SpecialPeriods.fourPeriodMap_rotate (z : Disc) :
    fourPeriodMap.point (discRotateFour z) = (fourPeriodMap.point z).step₂ :=
  Subtype.ext (localFour_rotate (disc_norm_lt_one z))

theorem SpecialPeriods.threePeriodMap_matrix_covariance (z : Disc) :
    (threePeriodMap.point (discRotateThree z)).val.matrix * A₁.map (Int.castRingHom ℂ) =
      (threePeriodMap.point z).val.R₁ * (threePeriodMap.point z).val.matrix := by
  rw [threePeriodMap_rotate]
  change (threePeriodMap.point z).val.step₁.matrix * _ = _
  rw [PeriodPoint.step₁_matrix _
      ((threePeriodMap.point z).val.τ_ne_zero (threePeriodMap.point z).property.1),
    Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

theorem SpecialPeriods.fourPeriodMap_matrix_covariance (z : Disc) :
    (fourPeriodMap.point (discRotateFour z)).val.matrix * A₂.map (Int.castRingHom ℂ) =
      (fourPeriodMap.point z).val.R₂ * (fourPeriodMap.point z).val.matrix := by
  rw [fourPeriodMap_rotate]
  change (fourPeriodMap.point z).val.step₂.matrix * _ = _
  rw [PeriodPoint.step₂_matrix _
      ((fourPeriodMap.point z).val.τ_ne_zero (fourPeriodMap.point z).property.1),
    Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

def Elliptic.familyPeriods (j : Kind) : HolomorphicPeriodMap ℂ SpecialPeriods.Disc :=
  match j with
  | .three => SpecialPeriods.threePeriodMap
  | .four => SpecialPeriods.fourPeriodMap

def Elliptic.familyRotation (j : Kind) :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) SpecialPeriods.Disc
      SpecialPeriods.Disc ω :=
  match j with
  | .three => SpecialPeriods.threeRotation
  | .four => SpecialPeriods.fourRotation

theorem Elliptic.familyRotation_iterate_order (j : Kind) : (familyRotation j)^[j.order] = id := by
  cases j
  · exact SpecialPeriods.discRotateThree_iterate_order
  · exact SpecialPeriods.discRotateFour_iterate_order

abbrev Elliptic.Family (j : Kind) :=
  (familyPeriods j).TotalSpace

abbrev Elliptic.FamilyModel :=
  ℂ × ComplexPlane₂

@[instance_reducible]
def Elliptic.familyCoveringChartedSpace :
    ChartedSpace FamilyModel (SpecialPeriods.Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (SpecialPeriods.Disc × ComplexPlane₂))

attribute [local instance] Elliptic.familyCoveringChartedSpace in
theorem Elliptic.familyCoveringManifold :
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (SpecialPeriods.Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ComplexPlane₂)
      SpecialPeriods.Disc ComplexPlane₂

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyPeriodEquiv_matrix (j : Kind) (z : SpecialPeriods.Disc)
    (x : RealCoordinates) :
    (familyPeriods j).periodEquiv z x =
      ((familyPeriods j).point z).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyPeriods_matrix_covariance (j : Kind) (z : SpecialPeriods.Disc) :
    ((familyPeriods j).point (familyRotation j z)).val.matrix * j.matrix.map (Int.castRingHom ℂ) =
      linearMatrix j ((familyPeriods j).point z) * ((familyPeriods j).point z).val.matrix := by
  cases j
  · exact SpecialPeriods.threePeriodMap_matrix_covariance z
  · exact SpecialPeriods.fourPeriodMap_matrix_covariance z

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyPeriodEquiv_flatLinear (j : Kind) (z : SpecialPeriods.Disc)
    (x : RealCoordinates) :
    (familyPeriods j).periodEquiv (familyRotation j z) (flatLinear j x) =
      linearMatrix j ((familyPeriods j).point z) *ᵥ (familyPeriods j).periodEquiv z x := by
  rw [familyPeriodEquiv_matrix, flatLinear_complexCast, Matrix.mulVec_mulVec,
    familyPeriodEquiv_matrix, Matrix.mulVec_mulVec, familyPeriods_matrix_covariance]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyPeriodEquiv_symm_linearMatrix (j : Kind) (z : SpecialPeriods.Disc)
    (w : ComplexPlane₂) :
    ((familyPeriods j).periodEquiv (familyRotation j z)).symm
        (linearMatrix j ((familyPeriods j).point z) *ᵥ w) =
      flatLinear j (((familyPeriods j).periodEquiv z).symm w) := by
  apply ((familyPeriods j).periodEquiv (familyRotation j z)).injective
  rw [LinearEquiv.apply_symm_apply, familyPeriodEquiv_flatLinear, LinearEquiv.apply_symm_apply]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
def Elliptic.familyPermutation (j : Kind) (v : Lattice) : Equiv.Perm (Family j) :=
  (familyRotation j).toEquiv.prodCongr (flatTorusAffine j v).toEquiv

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
@[simp]
theorem Elliptic.familyPermutation_apply (j : Kind) (v : Lattice) (x : Family j) :
    familyPermutation j v x = (familyRotation j x.1, flatTorusAffine j v x.2) :=
  rfl

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
def Elliptic.familyLift (j : Kind) (v : Lattice) (x : SpecialPeriods.Disc × ComplexPlane₂) :
    SpecialPeriods.Disc × ComplexPlane₂ :=
  (familyRotation j x.1,
    linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2 +
      (familyPeriods j).periodEquiv (familyRotation j x.1) ((1 / (j.order : ℝ)) • realCast v))

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyLift_quotientMap (j : Kind) (v : Lattice)
    (x : SpecialPeriods.Disc × ComplexPlane₂) :
    (familyPeriods j).quotientMap (familyLift j v x) =
      familyPermutation j v ((familyPeriods j).quotientMap x) := by
  change
    (familyRotation j x.1,
        standardLattice.mkQ
          (((familyPeriods j).periodEquiv (familyRotation j x.1)).symm
            (linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2 +
              (familyPeriods j).periodEquiv (familyRotation j x.1)
                ((1 / (j.order : ℝ)) • realCast v)))) =
      (familyRotation j x.1,
        flatTorusAffine j v (standardLattice.mkQ (((familyPeriods j).periodEquiv x.1).symm x.2)))
  rw [flatTorusAffine_mkQ, map_add, LinearEquiv.symm_apply_apply,
    familyPeriodEquiv_symm_linearMatrix]
  rfl

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyLinearLift_holomorphic (j : Kind) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ =>
        linearMatrix j ((familyPeriods j).point x.1) *ᵥ x.2) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : SpecialPeriods.Disc × ComplexPlane₂ → SpecialPeriods.Disc) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hs :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (Prod.snd : SpecialPeriods.Disc × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hτ := (familyPeriods j).holomorphic_tau.comp hf
  have hμ := (familyPeriods j).holomorphic_mu.comp hf
  have hτ0 : ∀ x : SpecialPeriods.Disc × ComplexPlane₂, ((familyPeriods j).point x.1).val.τ ≠ 0 :=
    fun x => ((familyPeriods j).point x.1).val.τ_ne_zero ((familyPeriods j).point x.1).property.1
  have h₀ := (contMDiff_pi_space.mp hs) 0
  have h₁ := (contMDiff_pi_space.mp hs) 1
  cases j
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (-1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((((contMDiff_const (c := (1 : ℂ))).sub hμ).div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
  · apply contMDiff_pi_space.mpr
    intro i
    fin_cases i
    · convert (((contMDiff_const (c := (1 : ℂ))).div₀ hτ hτ0).mul h₀) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]
    · convert (((hμ.neg.div₀ hτ hτ0).mul h₀).add h₁) using 1
      funext x
      simp [linearMatrix, PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Function.comp_def]

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyLift_holomorphic (j : Kind) (v : Lattice) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (familyLift j v) := by
  have hf :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fun x : SpecialPeriods.Disc × ComplexPlane₂ => familyRotation j x.1) := by
    rw [modelWithCornersSelf_prod]
    exact (familyRotation j).contMDiff_toFun.comp contMDiff_fst
  have hw :=
    (familyLinearLift_holomorphic j).add
      (((familyPeriods j).holomorphic_periodEquiv_const ((1 / (j.order : ℝ)) • realCast v)).comp
        hf)
  rw [modelWithCornersSelf_prod] at hf hw ⊢
  exact hf.prodMk hw

attribute [local instance] Elliptic.familyCoveringChartedSpace Elliptic.familyCoveringManifold in
theorem Elliptic.familyPermutation_holomorphic (j : Kind) (v : Lattice) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (familyPermutation j v) := by
  let := (familyPeriods j).coveringAction
  let := (familyPeriods j).totalChartedSpace
  apply
    CoveringQuotient.contMDiff_of_comp (E := FamilyModel) (familyPeriods j).quotientCoveringMap
      (modelWithCornersSelf ℂ FamilyModel) ω
  have h := ((familyPeriods j).quotientMap_holomorphic).comp (familyLift_holomorphic j v)
  convert! h using 1
  funext x
  exact (familyLift_quotientMap j v x).symm

theorem Elliptic.LogGauge.exponential_neg_one_third :
    CuspUniformization.exponential (-(1 / (3 : ℂ))) = -SpecialPeriods.rho := by
  have hρ : Complex.exp ((Real.pi : ℂ) / 3 * Complex.I) = SpecialPeriods.rho := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using SpecialPeriods.rho_eq_exp.symm
  rw [CuspUniformization.exponential,
    show
      (2 * Real.pi * Complex.I : ℂ) * -(1 / 3) =
        (Real.pi : ℂ) / 3 * Complex.I - Real.pi * Complex.I
      by ring,
    Complex.exp_sub_pi_mul_I, hρ]

theorem Elliptic.LogGauge.exponential_neg_one_fourth :
    CuspUniformization.exponential (-(1 / (4 : ℂ))) = -Complex.I := by
  rw [CuspUniformization.exponential,
    show (2 * Real.pi * Complex.I : ℂ) * -(1 / 4) = -(Real.pi : ℂ) / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

theorem Elliptic.LogGauge.familyRotation_val_exponential (j : Elliptic.Kind)
    (z : SpecialPeriods.Disc) :
    (Elliptic.familyRotation j z : ℂ) =
      CuspUniformization.exponential (-(1 / (j.order : ℂ))) * (z : ℂ) := by
  cases j
  · change
      -SpecialPeriods.rho * (z : ℂ) = CuspUniformization.exponential (-(1 / (3 : ℂ))) * (z : ℂ)
    rw [exponential_neg_one_third]
  · change -Complex.I * (z : ℂ) = CuspUniformization.exponential (-(1 / (4 : ℂ))) * (z : ℂ)
    rw [exponential_neg_one_fourth]

theorem Elliptic.LogGauge.familyRotation_ne_zero (j : Elliptic.Kind) (z : SpecialPeriods.Disc)
    (hz : (z : ℂ) ≠ 0) : (Elliptic.familyRotation j z : ℂ) ≠ 0 := by
  rw [familyRotation_val_exponential]
  exact mul_ne_zero (CuspUniformization.exponential_ne_zero _) hz

theorem Elliptic.LogGauge.familyRotation_logarithms (j : Elliptic.Kind) (z : SpecialPeriods.Disc)
    (s r : ℂ) (hs : CuspUniformization.exponential s = (z : ℂ))
    (hr : CuspUniformization.exponential r = (Elliptic.familyRotation j z : ℂ)) :
    ∃ n : ℤ, r = s - 1 / (j.order : ℂ) + n := by
  apply (CuspUniformization.exponential_eq_iff r (s - 1 / (j.order : ℂ))).mp
  rw [hr, familyRotation_val_exponential, sub_eq_add_neg, CuspUniformization.exponential_add, hs]
  exact mul_comm _ _

theorem Elliptic.LogGauge.logarithm_familyRotation (j : Elliptic.Kind) (z : SpecialPeriods.Disc)
    (hz : (z : ℂ) ≠ 0) :
    ∃ n : ℤ,
      CuspUniformization.logarithm (Elliptic.familyRotation j z : ℂ) =
        CuspUniformization.logarithm (z : ℂ) - 1 / (j.order : ℂ) + n :=
  familyRotation_logarithms j z _ _ (CuspUniformization.exponential_logarithm hz)
    (CuspUniformization.exponential_logarithm (familyRotation_ne_zero j z hz))

abbrev ThreefoldOverlapMappingTorus.Circle :=
  AddCircle (1 : ℝ)

abbrev ThreefoldOverlapMappingTorus.Radius (n : ℕ) (r : ℝ) :=
  { a : ℝ // 0 < a ∧ a < 1 ∧ a ^ n < r }

abbrev ThreefoldOverlapMappingTorus.RootDisc (n : ℕ) (r : ℝ) :=
  { z : SpecialPeriods.Disc // (z : ℂ) ≠ 0 ∧ ‖(z : ℂ)‖ ^ n < r }

def ThreefoldOverlapMappingTorus.phase (t : ThreefoldOverlapMappingTorus.Circle) :
    _root_.Circle :=
  AddCircle.toCircle t

theorem ThreefoldOverlapMappingTorus.phase_continuous : Continuous phase :=
  AddCircle.continuous_toCircle

theorem ThreefoldOverlapMappingTorus.phase_add (s t : ThreefoldOverlapMappingTorus.Circle) :
    phase (s + t) = phase s * phase t :=
  AddCircle.toCircle_add s t

theorem ThreefoldOverlapMappingTorus.phase_real (t : ℝ) :
    (phase (t : ThreefoldOverlapMappingTorus.Circle) : ℂ) =
      CuspUniformization.exponential (t : ℂ) := by
  rw [phase, AddCircle.toCircle_apply_mk, _root_.Circle.coe_exp, CuspUniformization.exponential]
  congr 1
  push_cast
  ring

def ThreefoldOverlapMappingTorus.root (n : ℕ) (r : ℝ) (a : Radius n r)
    (t : ThreefoldOverlapMappingTorus.Circle) : SpecialPeriods.Disc :=
  ⟨(a : ℝ) • (phase t : ℂ),
    by
    have hn : ‖(a : ℝ) • (phase t : ℂ)‖ < 1 := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos a.property.1, _root_.Circle.norm_coe,
        mul_one] using a.property.2.1
    simpa [SpecialPeriods.unitDisc] using hn⟩

@[simp]
theorem ThreefoldOverlapMappingTorus.root_norm (n : ℕ) (r : ℝ) (a : Radius n r)
    (t : ThreefoldOverlapMappingTorus.Circle) : ‖(root n r a t : ℂ)‖ = (a : ℝ) := by
  simp only [root, norm_smul, Real.norm_eq_abs, abs_of_pos a.property.1, _root_.Circle.norm_coe,
    mul_one]

theorem ThreefoldOverlapMappingTorus.root_ne_zero (n : ℕ) (r : ℝ) (a : Radius n r)
    (t : ThreefoldOverlapMappingTorus.Circle) : (root n r a t : ℂ) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [root_norm]
  exact a.property.1.ne'

theorem ThreefoldOverlapMappingTorus.root_continuous (n : ℕ) (r : ℝ) :
    Continuous (fun p : Radius n r × ThreefoldOverlapMappingTorus.Circle => root n r p.1 p.2) :=
  ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (phase_continuous.comp continuous_snd))).subtype_mk
    _

def ThreefoldOverlapMappingTorus.polarRoot (n : ℕ) (r : ℝ)
    (p : Radius n r × ThreefoldOverlapMappingTorus.Circle) : RootDisc n r :=
  ⟨root n r p.1 p.2, root_ne_zero n r p.1 p.2,
    by
    rw [root_norm]
    exact p.1.property.2.2⟩

theorem ThreefoldOverlapMappingTorus.polarRoot_continuous (n : ℕ) (r : ℝ) :
    Continuous (polarRoot n r) :=
  (root_continuous n r).subtype_mk _

def ThreefoldOverlapMappingTorus.rootRadius (n : ℕ) (r : ℝ) (z : RootDisc n r) : Radius n r :=
  ⟨‖((z : SpecialPeriods.Disc) : ℂ)‖, norm_pos_iff.mpr z.property.1,
    SpecialPeriods.disc_norm_lt_one z.val, z.property.2⟩

theorem ThreefoldOverlapMappingTorus.rootRadius_continuous (n : ℕ) (r : ℝ) :
    Continuous (rootRadius n r) :=
  (continuous_subtype_val.comp continuous_subtype_val).norm.subtype_mk _

def ThreefoldOverlapMappingTorus.unitPhase (n : ℕ) (r : ℝ) (z : RootDisc n r) : _root_.Circle :=
  ⟨‖((z : SpecialPeriods.Disc) : ℂ)‖⁻¹ • ((z : SpecialPeriods.Disc) : ℂ),
    by
    change
      ‖((z : SpecialPeriods.Disc) : ℂ)‖⁻¹ • ((z : SpecialPeriods.Disc) : ℂ) ∈
        Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr z.property.1))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr z.property.1)⟩

theorem ThreefoldOverlapMappingTorus.unitPhase_continuous (n : ℕ) (r : ℝ) :
    Continuous (unitPhase n r) := by
  have hz : Continuous (fun z : RootDisc n r => ((z : SpecialPeriods.Disc) : ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((hz.norm.inv₀ fun z => norm_ne_zero_iff.mpr z.property.1).smul hz).subtype_mk _

def ThreefoldOverlapMappingTorus.rootAngle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    ThreefoldOverlapMappingTorus.Circle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (unitPhase n r z)

theorem ThreefoldOverlapMappingTorus.rootAngle_continuous (n : ℕ) (r : ℝ) :
    Continuous (rootAngle n r) :=
  (AddCircle.homeomorphCircle one_ne_zero).symm.continuous.comp (unitPhase_continuous n r)

@[simp]
theorem ThreefoldOverlapMappingTorus.phase_rootAngle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    phase (rootAngle n r z) = unitPhase n r z := by
  rw [phase, ← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _

theorem ThreefoldOverlapMappingTorus.polarRoot_radius_angle (n : ℕ) (r : ℝ) (z : RootDisc n r) :
    polarRoot n r (rootRadius n r z, rootAngle n r z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ‖((z : SpecialPeriods.Disc) : ℂ)‖ • (phase (rootAngle n r z) : ℂ) =
      ((z : SpecialPeriods.Disc) : ℂ)
  rw [phase_rootAngle]
  change
    ‖((z : SpecialPeriods.Disc) : ℂ)‖ •
        (‖((z : SpecialPeriods.Disc) : ℂ)‖⁻¹ • ((z : SpecialPeriods.Disc) : ℂ)) =
      _
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr z.property.1), one_smul]

@[simp]
theorem ThreefoldOverlapMappingTorus.rootRadius_polarRoot (n : ℕ) (r : ℝ)
    (p : Radius n r × ThreefoldOverlapMappingTorus.Circle) :
    rootRadius n r (polarRoot n r p) = p.1 :=
  Subtype.ext (root_norm n r p.1 p.2)

@[simp]
theorem ThreefoldOverlapMappingTorus.rootAngle_polarRoot (n : ℕ) (r : ℝ)
    (p : Radius n r × ThreefoldOverlapMappingTorus.Circle) :
    rootAngle n r (polarRoot n r p) = p.2 := by
  apply (AddCircle.injective_toCircle one_ne_zero)
  change phase (rootAngle n r (polarRoot n r p)) = phase p.2
  rw [phase_rootAngle]
  apply Subtype.ext
  change ‖(root n r p.1 p.2 : ℂ)‖⁻¹ • ((p.1 : ℝ) • (phase p.2 : ℂ)) = _
  rw [root_norm, smul_smul, inv_mul_cancel₀ p.1.property.1.ne', one_smul]

def ThreefoldOverlapMappingTorus.polarHomeomorph (n : ℕ) (r : ℝ) :
    RootDisc n r ≃ₜ Radius n r × ThreefoldOverlapMappingTorus.Circle
    where
  toFun z := (rootRadius n r z, rootAngle n r z)
  invFun := polarRoot n r
  left_inv := polarRoot_radius_angle n r
  right_inv p := Prod.ext (rootRadius_polarRoot n r p) (rootAngle_polarRoot n r p)
  continuous_toFun := (rootRadius_continuous n r).prodMk (rootAngle_continuous n r)
  continuous_invFun := polarRoot_continuous n r

theorem ThreefoldOverlapMappingTorus.radius_nonempty (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    Nonempty (Radius n r) := by
  let a : ℝ := Min.min r 1 / 2
  have ha0 : 0 < a := half_pos (lt_min hr zero_lt_one)
  have ha1 : a < 1 := by
    have h := min_le_right r (1 : ℝ)
    dsimp only [a]
    linarith
  have har : a < r := by
    have h := min_le_left r (1 : ℝ)
    dsimp only [a] at ha0 ⊢
    linarith
  have hpow : a ^ n ≤ a := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1.le) ha0.le).trans_eq (one_mul a)
  exact ⟨⟨a, ha0, ha1, hpow.trans_lt har⟩⟩

def ThreefoldOverlapMappingTorus.radiusSegment {n : ℕ} {r : ℝ} (a b : Radius n r)
    (t : unitInterval) : Radius n r :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ),
    by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have ha := a.property
    have hb := b.property
    have hmax : (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤ Max.max (a : ℝ) (b : ℝ) := by
      have h₁ := le_max_left (a : ℝ) (b : ℝ)
      have h₂ := le_max_right (a : ℝ) (b : ℝ)
      nlinarith
    have hpos : 0 < (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) := by
      by_cases ht : (t : ℝ) = 1
      · simp only [ht, sub_self, MulZeroClass.zero_mul, one_mul, zero_add]
        exact hb.1
      · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht') ha.1) (mul_nonneg ht0 hb.1.le)
    refine ⟨hpos, hmax.trans_lt (max_lt ha.2.1 hb.2.1), ?_⟩
    apply (pow_le_pow_left₀ hpos.le hmax n).trans_lt
    rcases le_total (a : ℝ) (b : ℝ) with hab | hba
    · rw [max_eq_right hab]
      exact hb.2.2
    · rw [max_eq_left hba]
      exact ha.2.2⟩

@[simp]
theorem ThreefoldOverlapMappingTorus.radiusSegment_zero {n : ℕ} {r : ℝ} (a b : Radius n r) :
    radiusSegment a b 0 = a := by
  apply Subtype.ext
  simp [radiusSegment]

@[simp]
theorem ThreefoldOverlapMappingTorus.radiusSegment_one {n : ℕ} {r : ℝ} (a b : Radius n r) :
    radiusSegment a b 1 = b := by
  apply Subtype.ext
  simp [radiusSegment]

theorem ThreefoldOverlapMappingTorus.radiusSegment_continuous {n : ℕ} {r : ℝ} (a : Radius n r) :
    Continuous (fun p : unitInterval × Radius n r => radiusSegment a p.2 p.1) := by
  exact
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _

def ThreefoldOverlapMappingTorus.radiusProductHomotopyEquiv {n : ℕ} {r : ℝ} (a : Radius n r)
    (X : Type*) [TopologicalSpace X] : (Radius n r × X) ≃ₕ X
    where
  toFun := ContinuousMap.snd
  invFun := ⟨fun x => (a, x), continuous_const.prodMk continuous_id⟩
  left_inv :=
    ⟨{  toFun := fun p => (radiusSegment a p.2.1 p.1, p.2.2)
        continuous_toFun :=
          ((radiusSegment_continuous a).comp
                (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
            (continuous_snd.comp continuous_snd)
        map_zero_left := fun p => Prod.ext (radiusSegment_zero a p.1) rfl
        map_one_left := fun p => Prod.ext (radiusSegment_one a p.1) rfl }⟩
  right_inv := ContinuousMap.Homotopic.refl _

@[instance_reducible]
def Elliptic.CyclicAction.action {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) : MulAction (Multiplicative (ZMod m)) M
    where
  smul g x := (σ ^ g.toAdd.val) x
  one_smul
    x := by
    change (σ ^ (0 : ZMod m).val) x = x
    simp
  mul_smul g h
    x := by
    change (σ ^ (g.toAdd + h.toAdd).val) x = (σ ^ g.toAdd.val) ((σ ^ h.toAdd.val) x)
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hσ, pow_add]
    rfl

def Elliptic.CyclicAction.generator (m : ℕ) : Multiplicative (ZMod m) :=
  Multiplicative.ofAdd 1

theorem Elliptic.CyclicAction.smul_eq_iterate {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (g : Multiplicative (ZMod m)) (x : M) :
    letI := action σ hσ
    g • x = (σ : M → M)^[g.toAdd.val] x := by
  change (σ ^ g.toAdd.val) x = _
  rw [Equiv.Perm.coe_pow]

theorem Elliptic.CyclicAction.ofAdd_natCast_smul {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (r : ℕ) (x : M) :
    letI := action σ hσ
    Multiplicative.ofAdd (r : ZMod m) • x = (σ : M → M)^[r] x := by
  change (σ ^ (r : ZMod m).val) x = _
  rw [ZMod.val_natCast, ← pow_eq_pow_mod r hσ, Equiv.Perm.coe_pow]

@[simp]
theorem Elliptic.CyclicAction.generator_smul {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (x : M) :
    letI := action σ hσ
    generator m • x = σ x := by simpa [generator] using ofAdd_natCast_smul σ hσ 1 x

theorem Elliptic.CyclicAction.isCancelSMul {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (hfree : ∀ r : ℕ, 0 < r → r < m → ∀ x : M, (σ : M → M)^[r] x ≠ x) :
    letI := action σ hσ
    IsCancelSMul (Multiplicative (ZMod m)) M := by
  let := action σ hσ
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  have hval : g.toAdd.val = 0 := by
    by_contra hval
    exact
      hfree g.toAdd.val (Nat.pos_of_ne_zero hval) (ZMod.val_lt _) x
        ((smul_eq_iterate σ hσ g x).symm.trans hx)
  apply Multiplicative.ext
  exact (ZMod.val_eq_zero _).mp hval

theorem Elliptic.CyclicAction.isCancelSMul_iff {M : Type*} {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) :
    letI := action σ hσ
    IsCancelSMul (Multiplicative (ZMod m)) M ↔
      ∀ r : ℕ, 0 < r → r < m → ∀ x : M, (σ : M → M)^[r] x ≠ x := by
  let := action σ hσ
  constructor
  · intro hcancel r hr hrm x hx
    let := hcancel
    have hg : Multiplicative.ofAdd (r : ZMod m) = (1 : Multiplicative (ZMod m)) :=
      IsCancelSMul.eq_one_of_smul ((ofAdd_natCast_smul σ hσ r x).trans hx)
    have hz : (r : ZMod m) = 0 := congrArg Multiplicative.toAdd hg
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hrm, ZMod.val_zero] at hv
    omega
  · exact isCancelSMul σ hσ

theorem Elliptic.CyclicAction.continuousConstSMul {M : Type*} {m : ℕ} [NeZero m]
    [TopologicalSpace M] (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (hcont : Continuous (σ : M → M)) :
    letI := action σ hσ
    ContinuousConstSMul (Multiplicative (ZMod m)) M := by
  let := action σ hσ
  refine ⟨fun g => ?_⟩
  simpa only [smul_eq_iterate σ hσ] using hcont.iterate g.toAdd.val

theorem Elliptic.CyclicAction.smul_contMDiff {M : Type*} {m : ℕ} [NeZero m] {𝕜 E H : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M]
    (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (hreg : ContMDiff I I n (σ : M → M))
    (g : Multiplicative (ZMod m)) :
    letI := action σ hσ
    ContMDiff I I n (fun x : M => g • x) := by
  let := action σ hσ
  simpa only [smul_eq_iterate σ hσ] using hreg.iterate g.toAdd.val

abbrev Elliptic.FiniteQuotient.Space (G M : Type*) [Group G] [MulAction G M] :=
  MulAction.orbitRel.Quotient G M

def Elliptic.FiniteQuotient.project (G M : Type*) [Group G] [MulAction G M] : M → Space G M :=
  Quotient.mk (MulAction.orbitRel G M)

theorem Elliptic.FiniteQuotient.project_surjective (G M : Type*) [Group G] [MulAction G M] :
    Function.Surjective (project G M) :=
  Quotient.mk_surjective

theorem Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (G M : Type*) [Group G] [MulAction G M]
    (x y : M) : project G M x = project G M y ↔ x ∈ MulAction.orbit G y :=
  Quotient.eq''

@[simp]
theorem Elliptic.FiniteQuotient.project_smul (G M : Type*) [Group G] [MulAction G M] (g : G)
    (x : M) : project G M (g • x) = project G M x :=
  (project_eq_iff_mem_orbit G M _ _).mpr ⟨g, rfl⟩

theorem Elliptic.FiniteQuotient.project_isQuotientMap (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] : Topology.IsQuotientMap (project G M) :=
  isQuotientMap_quotient_mk'

theorem Elliptic.FiniteQuotient.project_continuous (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] : Continuous (project G M) :=
  (project_isQuotientMap G M).continuous

theorem Elliptic.FiniteQuotient.project_isOpenQuotientMap (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [ContinuousConstSMul G M] : IsOpenQuotientMap (project G M) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem Elliptic.FiniteQuotient.spaceCompactSpace (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [CompactSpace M] : CompactSpace (Space G M) :=
  inferInstance

theorem Elliptic.FiniteQuotient.spaceSecondCountableTopology (G M : Type*) [Group G]
    [MulAction G M] [TopologicalSpace M] [SecondCountableTopology M] [ContinuousConstSMul G M] :
    SecondCountableTopology (Space G M) :=
  (project_isQuotientMap G M).secondCountableTopology (project_isOpenQuotientMap G M).isOpenMap

theorem Elliptic.FiniteQuotient.spaceT2Space (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] : T2Space (Space G M) :=
  inferInstance

theorem Elliptic.FiniteQuotient.project_isQuotientCoveringMap (G M : Type*) [Group G]
    [MulAction G M] [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] [IsCancelSMul G M] : IsQuotientCoveringMap (project G M) G :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem Elliptic.FiniteQuotient.project_isCoveringMap (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] : IsCoveringMap (project G M) :=
  (project_isQuotientCoveringMap G M).isCoveringMap

def Elliptic.FiniteQuotient.fibreEquivGroup (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] (x : Space G M) : (project G M ⁻¹' { x }) ≃ G :=
  (project_isQuotientCoveringMap G M).fiberEquivGroup
    ⟨(project_surjective G M x).choose, (project_surjective G M x).choose_spec⟩

theorem Elliptic.FiniteQuotient.fibre_card (G M : Type*) [Group G] [MulAction G M]
    [TopologicalSpace M] [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M]
    [IsCancelSMul G M] (x : Space G M) : Nat.card (project G M ⁻¹' { x }) = Nat.card G :=
  Nat.card_congr (fibreEquivGroup G M x)

@[instance_reducible]
def Elliptic.FiniteQuotient.chartedSpace (G M : Type*) [Group G] [MulAction G M] {E : Type*}
    [NormedAddCommGroup E] [TopologicalSpace M] [ChartedSpace E M] [Finite G]
    [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M] :
    ChartedSpace E (Space G M) :=
  CoveringQuotient.chartedSpace (E := E) (project_isQuotientCoveringMap G M)

theorem Elliptic.FiniteQuotient.project_holomorphic (G M : Type*) [Group G] [MulAction G M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [Finite G] [LocallyCompactSpace M] [T2Space M] [ContinuousConstSMul G M] [IsCancelSMul G M]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    (hG :
      ∀ g : G,
        ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (fun x : M => g • x)) :
    letI := chartedSpace (E := E) G M
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (project G M) :=
  CoveringQuotient.contMDiff_project (project_isQuotientCoveringMap G M) ω hG

instance Elliptic.instLocal2 (j : Kind) : NeZero j.order :=
  ⟨Nat.ne_of_gt j.order_pos⟩

abbrev Elliptic.CyclicGroup (j : Kind) :=
  Multiplicative (ZMod j.order)

@[instance_reducible]
def Elliptic.affineAction (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (CyclicGroup j) p.val.Torus :=
  CyclicAction.action (affinePermutation j p v) (affinePermutation_pow_order j p v hv)

theorem Elliptic.affineAction_generator_smul (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : p.val.Torus) :
    letI := affineAction j p v hv
    CyclicAction.generator j.order • x = affineBiholomorph j p v x :=
  CyclicAction.generator_smul (affinePermutation j p v) (affinePermutation_pow_order j p v hv) x

theorem Elliptic.affineAction_free_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    letI := affineAction j p v hv
    IsCancelSMul (CyclicGroup j) p.val.Torus ↔ AdmissibleTwist j v := by
  refine
    (CyclicAction.isCancelSMul_iff (affinePermutation j p v)
          (affinePermutation_pow_order j p v hv)).trans
      ?_
  simpa only [Equiv.Perm.coe_pow] using affinePermutation_free_iff j p v hv

theorem Elliptic.affineAction_free (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := affineAction j p v hv.1
    IsCancelSMul (CyclicGroup j) p.val.Torus :=
  (affineAction_free_iff j p v hv.1).mpr hv

theorem Elliptic.affineAction_continuous (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    letI := affineAction j p v hv
    ContinuousConstSMul (CyclicGroup j) p.val.Torus :=
  CyclicAction.continuousConstSMul (affinePermutation j p v)
    (affinePermutation_pow_order j p v hv) (affineBiholomorph j p v).continuous

abbrev Elliptic.Surface (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v) :=
  @FiniteQuotient.Space (CyclicGroup j) p.val.Torus _ (affineAction j p v hv.1)

def Elliptic.surfaceProjection (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : p.val.Torus → Surface j p v hv :=
  @FiniteQuotient.project (CyclicGroup j) p.val.Torus _ (affineAction j p v hv.1)

theorem Elliptic.surfaceProjection_surjective (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Surjective (surfaceProjection j p v hv) :=
  Quotient.mk_surjective

theorem Elliptic.surfaceProjection_continuous (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : Continuous (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) p.val.Torus

instance Elliptic.surfaceCompact (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : CompactSpace (Surface j p v hv) := by
  let := affineAction j p v hv.1
  exact FiniteQuotient.spaceCompactSpace (CyclicGroup j) p.val.Torus

instance Elliptic.surfacePathConnected (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : PathConnectedSpace (Surface j p v hv) :=
  (surfaceProjection_surjective j p v hv).pathConnectedSpace
    (surfaceProjection_continuous j p v hv)

theorem Elliptic.surfaceProjection_isCoveringMap (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (surfaceProjection j p v hv) := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) p.val.Torus

theorem Elliptic.surfaceProjection_fibre_card (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Surface j p v hv) :
    Nat.card (surfaceProjection j p v hv ⁻¹' { y }) = j.order := by
  let := affineAction j p v hv.1
  let := affineAction_continuous j p v hv.1
  let := affineAction_free j p v hv
  change Nat.card (FiniteQuotient.project (CyclicGroup j) p.val.Torus ⁻¹' { y }) = j.order
  rw [FiniteQuotient.fibre_card (CyclicGroup j) p.val.Torus]
  simp [CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

theorem Elliptic.pow_mem_unitDisc_iff (m : ℕ) (hm : 0 < m) (z : ℂ) :
    z ^ m ∈ SpecialPeriods.unitDisc ↔ z ∈ SpecialPeriods.unitDisc := by
  change Dist.dist (z ^ m) 0 < 1 ↔ Dist.dist z 0 < 1
  rw [dist_zero_right, dist_zero_right, norm_pow]
  exact pow_lt_one_iff_of_nonneg (norm_nonneg z) hm.ne'

theorem Elliptic.complexPower_preimage_unitDisc (m : ℕ) (hm : 0 < m) :
    (fun z : ℂ => z ^ m) ⁻¹' (SpecialPeriods.unitDisc : Set ℂ) =
      (SpecialPeriods.unitDisc : Set ℂ) := by
  ext z
  exact pow_mem_unitDisc_iff m hm z

def Elliptic.discPower (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) : SpecialPeriods.Disc :=
  ⟨(z : ℂ) ^ m, (pow_mem_unitDisc_iff m hm z).mpr z.property⟩

@[simp]
theorem Elliptic.discPower_coe (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) :
    (discPower m hm z : ℂ) = (z : ℂ) ^ m :=
  rfl

theorem Elliptic.discPower_holomorphic (m : ℕ) (hm : 0 < m) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discPower m hm) := by
  intro z
  have he :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun w : SpecialPeriods.Disc => (discPower m hm w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (discPower m hm) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.pow m) z)

theorem Elliptic.discPower_continuous (m : ℕ) (hm : 0 < m) : Continuous (discPower m hm) :=
  (discPower_holomorphic m hm).continuous

theorem Elliptic.discPower_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (discPower m hm) := by
  intro w
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) hm
  have hmem : z ∈ SpecialPeriods.unitDisc := (pow_mem_unitDisc_iff m hm z).mp (hz ▸ w.property)
  exact ⟨⟨z, hmem⟩, Subtype.ext hz⟩

theorem Elliptic.complexPower_isProperMap (m : ℕ) (hm : 0 < m) :
    IsProperMap (fun z : ℂ => z ^ m) := by
  have hp : 0 < (Polynomial.X ^ m : Polynomial ℂ).degree := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast hm
  simpa only [Polynomial.eval_X_pow] using (Polynomial.X ^ m : Polynomial ℂ).isProperMap_eval hp

theorem Elliptic.discPower_isProperMap (m : ℕ) (hm : 0 < m) : IsProperMap (discPower m hm) := by
  let e : SpecialPeriods.Disc ≃ₜ ((fun z : ℂ => z ^ m) ⁻¹' (SpecialPeriods.unitDisc : Set ℂ)) :=
    Homeomorph.setCongr (complexPower_preimage_unitDisc m hm).symm
  have hp :=
    ((complexPower_isProperMap m hm).restrictPreimage (SpecialPeriods.unitDisc : Set ℂ)).comp
      e.isProperMap
  have he :
    (SpecialPeriods.unitDisc : Set ℂ).restrictPreimage (fun z : ℂ => z ^ m) ∘ e =
      discPower m hm := by
    funext z
    rfl
  rwa [he] at hp

def Elliptic.discZero : SpecialPeriods.Disc :=
  ⟨0, by simp [SpecialPeriods.unitDisc]⟩

@[simp]
theorem Elliptic.discPower_coe_eq_zero_iff (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) :
    (discPower m hm z : ℂ) = 0 ↔ (z : ℂ) = 0 := by
  simp only [discPower_coe, pow_eq_zero_iff hm.ne']

@[simp]
theorem Elliptic.discPower_eq_zero_iff (m : ℕ) (hm : 0 < m) (z : SpecialPeriods.Disc) :
    discPower m hm z = discZero ↔ z = discZero := by
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact discPower_coe_eq_zero_iff m hm z

theorem Elliptic.familyPermutation_iterate (j : Kind) (v : Lattice) (r : ℕ) (x : Family j) :
    (familyPermutation j v)^[r] x = ((familyRotation j)^[r] x.1, (flatTorusAffine j v)^[r] x.2) :=
  by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Function.iterate_succ_apply', ih, familyPermutation_apply]

theorem Elliptic.familyPermutation_pow_apply (j : Kind) (v : Lattice) (r : ℕ) (x : Family j) :
    (familyPermutation j v ^ r) x = ((familyRotation j)^[r] x.1, (flatTorusAffine j v)^[r] x.2) :=
  by
  rw [Equiv.Perm.coe_pow]
  exact familyPermutation_iterate j v r x

theorem Elliptic.familyPermutation_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    familyPermutation j v ^ j.order = 1 := by
  apply Equiv.ext
  intro x
  rw [familyPermutation_pow_apply, familyRotation_iterate_order,
    flatTorusAffine_iterate_order j v hv]
  rfl

theorem Elliptic.familyPermutation_pow_ne (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (x : Family j) : (familyPermutation j v ^ r) x ≠ x :=
  by
  intro hx
  rw [familyPermutation_pow_apply] at hx
  exact flatTorusAffine_iterate_ne j v hv r hr hrm x.2 (congrArg Prod.snd hx)

@[simp]
theorem Elliptic.familyRotation_zero (j : Kind) : familyRotation j discZero = discZero := by
  cases j <;> apply Subtype.ext
  · change -SpecialPeriods.rho * (0 : ℂ) = 0
    exact MulZeroClass.mul_zero _
  · change -Complex.I * (0 : ℂ) = 0
    exact MulZeroClass.mul_zero _

theorem Elliptic.familyRotation_iterate_fixed_iff (j : Kind) (r : ℕ) (hr : 0 < r)
    (hrm : r < j.order) (z : SpecialPeriods.Disc) : (familyRotation j)^[r] z = z ↔ z = discZero :=
  by
  cases j
  · exact SpecialPeriods.discRotateThree_iterate_fixed_iff r hr hrm z
  · exact SpecialPeriods.discRotateFour_iterate_fixed_iff r hr hrm z

theorem Elliptic.familyPermutation_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ x : Family j, (familyPermutation j v ^ r) x ≠ x) ↔
      AdmissibleTwist j v := by
  constructor
  · intro hf
    apply (flatTorusPermutation_free_iff j v hv).mp
    intro r hr hrm y hy
    apply hf r hr hrm (discZero, y)
    rw [familyPermutation_pow_apply]
    apply Prod.ext (Function.iterate_fixed (familyRotation_zero j) r)
    simpa only [Equiv.Perm.coe_pow, flatTorusPermutation, Homeomorph.coe_toEquiv] using hy
  · intro ha
    exact familyPermutation_pow_ne j v ha

@[instance_reducible]
def Elliptic.familyAction (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (CyclicGroup j) (Family j) :=
  CyclicAction.action (familyPermutation j v) (familyPermutation_pow_order j v hv)

theorem Elliptic.familyAction_generator_smul (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : Family j) :
    letI := familyAction j v hv
    CyclicAction.generator j.order • x = familyPermutation j v x :=
  CyclicAction.generator_smul (familyPermutation j v) (familyPermutation_pow_order j v hv) x

theorem Elliptic.familyAction_apply (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    g • x = ((familyRotation j)^[g.toAdd.val] x.1, (flatTorusAffine j v)^[g.toAdd.val] x.2) :=
  (CyclicAction.smul_eq_iterate (familyPermutation j v) (familyPermutation_pow_order j v hv) g
        x).trans
    (familyPermutation_iterate j v g.toAdd.val x)

theorem Elliptic.familyAction_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := familyAction j v hv
    IsCancelSMul (CyclicGroup j) (Family j) ↔ AdmissibleTwist j v := by
  refine
    (CyclicAction.isCancelSMul_iff (familyPermutation j v)
          (familyPermutation_pow_order j v hv)).trans
      ?_
  simpa only [Equiv.Perm.coe_pow] using familyPermutation_free_iff j v hv

theorem Elliptic.familyAction_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := familyAction j v hv.1
    IsCancelSMul (CyclicGroup j) (Family j) :=
  (familyAction_free_iff j v hv.1).mpr hv

theorem Elliptic.familyAction_holomorphic (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) :
    letI := (familyPeriods j).totalChartedSpace
    letI := familyAction j v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fun x : Family j => g • x) := by
  let := (familyPeriods j).totalChartedSpace
  exact
    CyclicAction.smul_contMDiff (familyPermutation j v) (familyPermutation_pow_order j v hv)
      (familyPermutation_holomorphic j v) g

theorem Elliptic.familyAction_continuous (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := familyAction j v hv
    ContinuousConstSMul (CyclicGroup j) (Family j) := by
  apply
    CyclicAction.continuousConstSMul (familyPermutation j v) (familyPermutation_pow_order j v hv)
  let := (familyPeriods j).totalChartedSpace
  exact (familyPermutation_holomorphic j v).continuous

theorem Elliptic.discPower_familyRotation (j : Kind) (z : SpecialPeriods.Disc) :
    discPower j.order j.order_pos (familyRotation j z) = discPower j.order j.order_pos z := by
  cases j <;> apply Subtype.ext
  · change (-SpecialPeriods.rho * (z : ℂ)) ^ 3 = (z : ℂ) ^ 3
    rw [mul_pow, neg_pow, SpecialPeriods.rho_cube]
    norm_num
  · change (-Complex.I * (z : ℂ)) ^ 4 = (z : ℂ) ^ 4
    norm_num [mul_pow]

theorem Elliptic.discPower_familyRotation_iterate (j : Kind) (r : ℕ) (z : SpecialPeriods.Disc) :
    discPower j.order j.order_pos ((familyRotation j)^[r] z) = discPower j.order j.order_pos z := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', discPower_familyRotation, ih]

theorem Elliptic.familyAction_discPower (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    discPower j.order j.order_pos (g • x).1 = discPower j.order j.order_pos x.1 := by
  let := familyAction j v hv
  rw [familyAction_apply]
  exact discPower_familyRotation_iterate j g.toAdd.val x.1

def Elliptic.FiniteQuotient.descend {G M B : Type*} [Group G] [MulAction G M] (f : M → B)
    (hf : ∀ (g : G) (x : M), f (g • x) = f x) : Space G M → B :=
  Quotient.lift f
    (by
      rintro x y ⟨g, hg⟩
      rw [← hg]
      exact hf g y)

@[simp]
theorem Elliptic.FiniteQuotient.descend_project {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) (x : M) :
    descend f hf (project G M x) = f x :=
  rfl

theorem Elliptic.FiniteQuotient.descend_surjective {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) (hs : Function.Surjective f) :
    Function.Surjective (descend f hf) := by
  intro b
  obtain ⟨x, hx⟩ := hs b
  exact ⟨project G M x, hx⟩

theorem Elliptic.FiniteQuotient.descend_preimage_eq_image {G M B : Type*} [Group G]
    [MulAction G M] (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) (K : Set B) :
    descend f hf ⁻¹' K = project G M '' (f ⁻¹' K) := by
  ext q
  obtain ⟨x, rfl⟩ := project_surjective G M q
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    change descend f hf (project G M x) ∈ K
    rw [← hxy, descend_project]
    exact hy

theorem Elliptic.FiniteQuotient.descend_continuous {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) [TopologicalSpace M]
    [TopologicalSpace B] (hc : Continuous f) : Continuous (descend f hf) :=
  (project_isQuotientMap G M).continuous_iff.mpr hc

theorem Elliptic.FiniteQuotient.descend_isProperMap {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x) [TopologicalSpace M]
    [TopologicalSpace B] (hp : IsProperMap f) : IsProperMap (descend f hf) :=
  isProperMap_of_comp_of_surj (project_continuous G M) (descend_continuous f hf hp.continuous) hp
    (project_surjective G M)

instance Elliptic.discLocallyCompact : LocallyCompactSpace SpecialPeriods.Disc :=
  SpecialPeriods.unitDisc.isOpen.locallyCompactSpace

def Elliptic.upstairsProjection (j : Kind) (x : Family j) : SpecialPeriods.Disc :=
  discPower j.order j.order_pos x.1

theorem Elliptic.upstairsProjection_invariant (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    upstairsProjection j (g • x) = upstairsProjection j x :=
  familyAction_discPower j v hv g x

abbrev Elliptic.Filling (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :=
  @FiniteQuotient.Space (CyclicGroup j) (Family j) _ (familyAction j v hv.1)

def Elliptic.fillingQuotient (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Family j → Filling j v hv :=
  @FiniteQuotient.project (CyclicGroup j) (Family j) _ (familyAction j v hv.1)

theorem Elliptic.fillingQuotient_surjective (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (fillingQuotient j v hv) :=
  Quotient.mk_surjective

theorem Elliptic.fillingQuotient_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (fillingQuotient j v hv) := by
  let := familyAction j v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) (Family j)

instance Elliptic.fillingChartedSpace (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ChartedSpace FamilyModel (Filling j v hv) := by
  letI := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.chartedSpace (E := FamilyModel) (CyclicGroup j) (Family j)

theorem Elliptic.fillingQuotient_isCoveringMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (fillingQuotient j v hv) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) (Family j)

theorem Elliptic.fillingQuotient_holomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fillingQuotient j v hv) := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact
    FiniteQuotient.project_holomorphic (CyclicGroup j) (Family j)
      (familyAction_holomorphic j v hv.1)

def Elliptic.fillingProjection (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Filling j v hv → SpecialPeriods.Disc := by
  letI := familyAction j v hv.1
  exact FiniteQuotient.descend (upstairsProjection j) (upstairsProjection_invariant j v hv.1)

abbrev Elliptic.HigherHomology.MappingTorusQuotient.Circle :=
  MappingTorus.Circle

def Elliptic.HigherHomology.MappingTorusQuotient.twist {X : Type*} [TopologicalSpace X] (m : ℕ)
    (B : X ≃ₜ X) :
    (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) ≃ₜ
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) :=
  (Homeomorph.addRight
        (((1 : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)).prodCongr
    B

@[simp]
theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_apply {X : Type*} [TopologicalSpace X]
    (m : ℕ) (B : X ≃ₜ X) (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    twist m B (a, x) =
      (a + (((1 : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), B x) :=
  rfl

theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_pow_apply {X : Type*}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (n : ℕ)
    (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    (twist m B ^ n) (a, x) =
      (a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
        (B ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Homeomorph.mul_apply, ih, twist_apply]
    apply Prod.ext
    · change
        a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
            (((1 : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
          a + ((((n + 1 : ℕ) : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)
      rw [add_assoc, ← AddCircle.coe_add]
      congr 2
      push_cast
      ring
    · simp only [pow_succ', Homeomorph.mul_apply]

theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_zpow_apply {X : Type*}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (n : ℤ)
    (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    (twist m B ^ n) (a, x) =
      (a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
        (B ^ n) x) := by
  cases n with
  | ofNat
    n =>
    change
      (twist m B ^ (n : ℤ)) (a, x) =
        (a + ((((n : ℤ) : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
          (B ^ (n : ℤ)) x)
    simpa only [Int.cast_natCast, zpow_natCast] using twist_pow_apply m B n a x
  | negSucc n =>
    rw [zpow_negSucc]
    apply (twist m B ^ (n + 1)).injective
    change (twist m B ^ (n + 1)) ((twist m B ^ (n + 1)).symm (a, x)) = _
    rw [Homeomorph.apply_symm_apply, twist_pow_apply]
    apply Prod.ext
    · change
        a =
          a +
              ((((Int.negSucc n : ℤ) : ℝ) / m : ℝ) :
                Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
            ((((n + 1 : ℕ) : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)
      have ht : (((Int.negSucc n : ℤ) : ℝ) / m : ℝ) + (((n + 1 : ℕ) : ℝ) / m : ℝ) = 0 := by
        push_cast
        ring
      rw [add_assoc, ← AddCircle.coe_add, ht, AddCircle.coe_zero, add_zero]
    · change x = (B ^ (n + 1)) ((B ^ (Int.negSucc n : ℤ)) x)
      rw [zpow_negSucc, Homeomorph.inv_apply, Homeomorph.apply_symm_apply]

private def Elliptic.HigherHomology.MappingTorusQuotient.homeomorphPermHom_mo1973_15464
    {X : Type*} [TopologicalSpace X] : (X ≃ₜ X) →* Equiv.Perm X
    where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem Elliptic.HigherHomology.MappingTorusQuotient.twist_pow_order {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) : twist m B ^ m = 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hc : ((1 : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) = 0 := by
    simpa only [Int.cast_one] using MappingTorus.circle_intCast 1
  apply Homeomorph.ext
  rintro ⟨a, x⟩
  rw [twist_pow_apply]
  simp only [div_self hm, hc, add_zero, hB, Homeomorph.one_apply]

theorem Elliptic.HigherHomology.MappingTorusQuotient.twistPerm_pow_order {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    (twist m B).toEquiv ^ m = 1 := by
  change homeomorphPermHom_mo1973_15464 (twist m B) ^ m = 1
  rw [← map_pow, twist_pow_order m B hB, map_one]

@[instance_reducible]
def Elliptic.HigherHomology.MappingTorusQuotient.productAction {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    MulAction (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) :=
  Elliptic.CyclicAction.action (twist m B).toEquiv (twistPerm_pow_order m B hB)

theorem Elliptic.HigherHomology.MappingTorusQuotient.productAction_continuousConstSMul {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    letI := productAction m B hB
    ContinuousConstSMul (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) := by
  exact
    Elliptic.CyclicAction.continuousConstSMul (twist m B).toEquiv (twistPerm_pow_order m B hB)
      (twist m B).continuous

theorem Elliptic.HigherHomology.MappingTorusQuotient.cyclicAction_ofAdd_intCast_smul {M : Type*}
    (m : ℕ) [NeZero m] (σ : Equiv.Perm M) (hσ : σ ^ m = 1) (n : ℤ) (x : M) :
    letI := Elliptic.CyclicAction.action σ hσ
    Multiplicative.ofAdd (n : ZMod m) • x = (σ ^ n) x := by
  change (σ ^ (n : ZMod m).val) x = (σ ^ n) x
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' n hσ]

theorem Elliptic.HigherHomology.MappingTorusQuotient.ofAdd_intCast_smul {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℤ)
    (a : Elliptic.HigherHomology.MappingTorusQuotient.Circle) (x : X) :
    letI := productAction m B hB
    Multiplicative.ofAdd (n : ZMod m) • (a, x) =
      (a + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
        (B ^ n) x) := by
  change ((twist m B).toEquiv ^ (n : ZMod m).val) (a, x) = _
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' n (twistPerm_pow_order m B hB)]
  have hp : (twist m B).toEquiv ^ n = (twist m B ^ n).toEquiv :=
    (homeomorphPermHom_mo1973_15464.map_zpow (twist m B) n).symm
  rw [hp]
  exact twist_zpow_apply m B n a x

theorem Elliptic.HigherHomology.MappingTorusQuotient.fibre_zpow_add_mul_period {X : Type*}
    [TopologicalSpace X] (m : ℕ) (B : X ≃ₜ X) (hB : B ^ m = 1) (k n : ℤ) :
    B ^ (k + (m : ℤ) * n) = B ^ k := by
  rw [zpow_add, zpow_mul, zpow_natCast, hB, one_zpow, mul_one]

theorem MappingTorus.mk_unitCylinder_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    MappingTorus.mk f '' ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ : Set X)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective f q
  refine ⟨deck f (-⌊t⌋) (t, x), ?_, mk_deck f (-⌊t⌋) (t, x)⟩
  change (0 ≤ t + ((-⌊t⌋ : ℤ) : ℝ) ∧ t + ((-⌊t⌋ : ℤ) : ℝ) ≤ 1) ∧ True
  push_cast
  exact ⟨⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩, trivial⟩

instance MappingTorus.compactSpace {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X ≃ₜ X) : CompactSpace (Torus f) where
  isCompact_univ := by
    rw [← mk_unitCylinder_surjective f]
    exact (CompactIccSpace.isCompact_Icc.prod isCompact_univ).image (mk_continuous f)

theorem Elliptic.HigherHomology.MappingTorusQuotient.circle_scaled_eq_iff (m : ℕ) [NeZero m]
    (s t : ℝ) (n : ℤ) :
    ((s / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
        ((t / m + (n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) ↔
      ∃ k : ℤ, s = t + ((n + (m : ℤ) * k : ℤ) : ℝ) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (MappingTorus.circle_coe_eq_iff _ _).mp h.symm
    refine ⟨k, ?_⟩
    push_cast
    calc
      s = (s / m) * m := (div_mul_cancel₀ s hm).symm
      _ = (t / m + (n : ℝ) / m + (k : ℝ)) * m := by rw [hk]
      _ = t + ((n : ℝ) + (m : ℝ) * k) := by
        rw [add_mul, add_mul, div_mul_cancel₀ _ hm, div_mul_cancel₀ _ hm]
        ring
  · rintro ⟨k, hk⟩
    apply Eq.symm
    apply (MappingTorus.circle_coe_eq_iff _ _).mpr
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    field_simp [hm]
    ring

theorem Elliptic.HigherHomology.MappingTorusQuotient.symm_zpow_neg {X : Type*}
    [TopologicalSpace X] (B : X ≃ₜ X) (n : ℤ) : B.symm ^ (-n) = B ^ n := by
  change (B⁻¹) ^ (-n) = B ^ n
  rw [inv_zpow, zpow_neg, inv_inv]

def Elliptic.LogGauge.quotientEquiv (G : Type*) [Group G] {M N : Type*} [MulAction G M]
    [MulAction G N] (e : M ≃ N) (heq : ∀ (g : G) (x : M), e (g • x) = g • e x) :
    Elliptic.FiniteQuotient.Space G M ≃ Elliptic.FiniteQuotient.Space G N :=
  Quotient.congr e
    (by
      intro x y
      change (x ∈ MulAction.orbit G y) ↔ (e x ∈ MulAction.orbit G (e y))
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, (heq g y).symm.trans (congrArg e hg)⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, e.injective ((heq g y).trans hg)⟩)

theorem Elliptic.HigherHomology.MappingTorusQuotient.cyclicConjugacy_smul {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) (g : Multiplicative (ZMod m)) (x : M) :
    letI := Elliptic.CyclicAction.action σ hσ
    letI := Elliptic.CyclicAction.action τ hτ
    e (g • x) = g • e x := by
  let := Elliptic.CyclicAction.action σ hσ
  let := Elliptic.CyclicAction.action τ hτ
  rw [Elliptic.CyclicAction.smul_eq_iterate σ hσ, Elliptic.CyclicAction.smul_eq_iterate τ hτ]
  exact Function.Semiconj.iterate_right he g.toAdd.val x

def Elliptic.HigherHomology.MappingTorusQuotient.cyclicQuotientCongr {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] {m : ℕ} [NeZero m] (σ : Equiv.Perm M)
    (hσ : σ ^ m = 1) (τ : Equiv.Perm N) (hτ : τ ^ m = 1) (e : M ≃ₜ N)
    (he : ∀ x, e (σ x) = τ (e x)) :
    letI := Elliptic.CyclicAction.action σ hσ
    letI := Elliptic.CyclicAction.action τ hτ
    Elliptic.FiniteQuotient.Space (Multiplicative (ZMod m)) M ≃ₜ
      Elliptic.FiniteQuotient.Space (Multiplicative (ZMod m)) N := by
  let := Elliptic.CyclicAction.action σ hσ
  let := Elliptic.CyclicAction.action τ hτ
  refine
    { toEquiv :=
        Elliptic.LogGauge.quotientEquiv (Multiplicative (ZMod m)) e.toEquiv
          (cyclicConjugacy_smul σ hσ τ hτ e he)
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply
      (Elliptic.FiniteQuotient.project_isQuotientMap (Multiplicative (ZMod m))
          M).continuous_iff.mpr
    exact
      (Elliptic.FiniteQuotient.project_continuous (Multiplicative (ZMod m)) N).comp e.continuous
  · apply
      (Elliptic.FiniteQuotient.project_isQuotientMap (Multiplicative (ZMod m))
          N).continuous_iff.mpr
    exact
      (Elliptic.FiniteQuotient.project_continuous (Multiplicative (ZMod m)) M).comp
        e.symm.continuous

abbrev Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :=
  letI := productAction m B hB
  Elliptic.FiniteQuotient.Space (Multiplicative (ZMod m))
    (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

def Elliptic.HigherHomology.MappingTorusQuotient.project {X : Type*} [TopologicalSpace X] (m : ℕ)
    [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p : Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) : ProductQuotient m B hB := by
  letI := productAction m B hB
  exact
    Elliptic.FiniteQuotient.project (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) p

theorem Elliptic.HigherHomology.MappingTorusQuotient.project_surjective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Surjective (project m B hB) := by
  let := productAction m B hB
  exact
    Elliptic.FiniteQuotient.project_surjective (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

theorem Elliptic.HigherHomology.MappingTorusQuotient.project_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (project m B hB) := by
  let := productAction m B hB
  exact
    Elliptic.FiniteQuotient.project_continuous (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

theorem Elliptic.HigherHomology.MappingTorusQuotient.project_eq_iff {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p q : Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) :
    project m B hB p = project m B hB q ↔
      ∃ n : ℤ,
        p =
          (q.1 + (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle),
            (B ^ n) q.2) := by
  let := productAction m B hB
  change
    Elliptic.FiniteQuotient.project (Multiplicative (ZMod m))
          (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) p =
        Elliptic.FiniteQuotient.project (Multiplicative (ZMod m))
          (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X) q ↔
      _
  rw [Elliptic.FiniteQuotient.project_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    have he : Multiplicative.ofAdd ((g.toAdd.val : ℤ) : ZMod m) = g := by
      apply Multiplicative.ext
      simp
    have hs := ofAdd_intCast_smul m B hB (g.toAdd.val : ℤ) q.1 q.2
    rw [he] at hs
    exact ⟨g.toAdd.val, hg.symm.trans hs⟩
  · rintro ⟨n, hp⟩
    refine ⟨Multiplicative.ofAdd (n : ZMod m), ?_⟩
    change Multiplicative.ofAdd (n : ZMod m) • (q.1, q.2) = p
    rw [ofAdd_intCast_smul]
    exact hp.symm

def Elliptic.HigherHomology.MappingTorusQuotient.cylinderMap {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (p : ℝ × X) : ProductQuotient m B hB :=
  project m B hB (((p.1 / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), p.2)

theorem Elliptic.HigherHomology.MappingTorusQuotient.cylinderMap_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (cylinderMap m B hB) :=
  (project_continuous m B hB).comp
    (((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_fst.div_const (m : ℝ))).prodMk
      continuous_snd)

theorem Elliptic.HigherHomology.MappingTorusQuotient.cylinderMap_deck {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℤ) (p : ℝ × X) :
    cylinderMap m B hB (MappingTorus.deck B.symm n p) = cylinderMap m B hB p := by
  apply (project_eq_iff m B hB _ _).mpr
  refine ⟨n, ?_⟩
  apply Prod.ext
  · change
      (((p.1 + (n : ℝ)) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
        ((p.1 / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
          (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle)
    rw [add_div, AddCircle.coe_add]
  · change (B.symm ^ (-n)) p.2 = (B ^ n) p.2
    rw [symm_zpow_neg]

def Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    MappingTorus.Torus B.symm → ProductQuotient m B hB :=
  Quotient.lift (cylinderMap m B hB)
    (by
      rintro p q ⟨n, rfl⟩
      exact (cylinderMap_deck m B hB n p).symm)

@[simp]
theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_mk {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (t : ℝ) (x : X) :
    mappingTorusMap m B hB (MappingTorus.mk B.symm (t, x)) =
      project m B hB (((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x) :=
  rfl

theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (mappingTorusMap m B hB) :=
  (cylinderMap_continuous m B hB).quotient_lift _

theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_injective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Injective (mappingTorusMap m B hB) := by
  intro p q h
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective B.symm p
  obtain ⟨⟨s, y⟩, rfl⟩ := MappingTorus.mk_surjective B.symm q
  change
    project m B hB (((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x) =
      project m B hB (((s / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), y) at h
  obtain ⟨n, hn⟩ := (project_eq_iff m B hB _ _).mp h
  have hf := congrArg Prod.fst hn
  change
    ((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) =
      ((s / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) +
        (((n : ℝ) / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle) at hf
  rw [← AddCircle.coe_add] at hf
  obtain ⟨k, hk⟩ := (circle_scaled_eq_iff m t s n).mp hf
  have hx : x = (B ^ n) y := congrArg Prod.snd hn
  apply Eq.symm
  apply (MappingTorus.mk_eq_mk_iff B.symm (s, y) (t, x)).mpr
  refine ⟨n + (m : ℤ) * k, hk, ?_⟩
  rw [symm_zpow_neg, fibre_zpow_add_mul_period m B hB]
  exact hx

theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusMap_surjective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Surjective (mappingTorusMap m B hB) := by
  intro q
  obtain ⟨⟨a, x⟩, rfl⟩ := project_surjective m B hB q
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
  refine ⟨MappingTorus.mk B.symm (t * m, x), ?_⟩
  rw [mappingTorusMap_mk]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hm, mul_one]

instance Elliptic.HigherHomology.MappingTorusQuotient.productQuotient_t2 {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] : T2Space (ProductQuotient m B hB) := by
  let := productAction m B hB
  let := productAction_continuousConstSMul m B hB
  exact
    Elliptic.FiniteQuotient.spaceT2Space (Multiplicative (ZMod m))
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle × X)

def Elliptic.HigherHomology.MappingTorusQuotient.toProductHomeomorph {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] : MappingTorus.Torus B.symm ≃ₜ ProductQuotient m B hB :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (mappingTorusMap m B hB)
      ⟨mappingTorusMap_injective m B hB, mappingTorusMap_surjective m B hB⟩)
    (mappingTorusMap_continuous m B hB)

def Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] : ProductQuotient m B hB ≃ₜ MappingTorus.Torus B.symm :=
  (toProductHomeomorph m B hB).symm

@[simp]
theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_symm_mk {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] (t : ℝ) (x : X) :
    (mappingTorusHomeomorph m B hB).symm (MappingTorus.mk B.symm (t, x)) =
      project m B hB (((t / m : ℝ) : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x) :=
  rfl

theorem Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_project {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] (t : ℝ) (x : X) :
    mappingTorusHomeomorph m B hB
        (project m B hB ((t : Elliptic.HigherHomology.MappingTorusQuotient.Circle), x)) =
      MappingTorus.mk B.symm (t * m, x) := by
  apply (mappingTorusHomeomorph m B hB).symm.injective
  rw [Homeomorph.symm_apply_apply, mappingTorusHomeomorph_symm_mk]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hm, mul_one]

private def ThreefoldOverlapMappingTorus.Elliptic.homeomorphToPerm_mo1973_15505 :
    (RealTorus₄ ≃ₜ RealTorus₄) →* Equiv.Perm RealTorus₄
    where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ThreefoldOverlapMappingTorus.Elliptic.affine_pow_order (j : Elliptic.Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : Elliptic.flatTorusAffine j v ^ j.order = 1 := by
  apply Homeomorph.ext
  intro x
  exact
    congrArg (fun e : Equiv.Perm RealTorus₄ => e x)
      ((homeomorphToPerm_mo1973_15505.map_pow (Elliptic.flatTorusAffine j v) j.order).trans
        (Elliptic.flatTorusPermutation_pow_order j v hv))

theorem ThreefoldOverlapMappingTorus.Elliptic.affine_symm_pow_order (j : Elliptic.Kind)
    (v : Lattice) (hv : j.matrix *ᵥ v = v) : (Elliptic.flatTorusAffine j v).symm ^ j.order = 1 := by
  change (Elliptic.flatTorusAffine j v)⁻¹ ^ j.order = 1
  rw [inv_pow, affine_pow_order j v hv, inv_one]

theorem ThreefoldOverlapMappingTorus.Elliptic.root_sub_order (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (t : ThreefoldOverlapMappingTorus.Circle) :
    ThreefoldOverlapMappingTorus.root j.order r a
        (t - (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)) =
      Elliptic.familyRotation j (ThreefoldOverlapMappingTorus.root j.order r a t) := by
  apply Subtype.ext
  rw [Elliptic.LogGauge.familyRotation_val_exponential]
  change
    (a : ℝ) •
        (ThreefoldOverlapMappingTorus.phase
            (t - (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)) :
          ℂ) =
      CuspUniformization.exponential (-(1 / (j.order : ℂ))) *
        ((a : ℝ) • (ThreefoldOverlapMappingTorus.phase t : ℂ))
  rw [sub_eq_add_neg, ← AddCircle.coe_neg, ThreefoldOverlapMappingTorus.phase_add,
    _root_.Circle.coe_mul, ThreefoldOverlapMappingTorus.phase_real]
  have he : (((-(1 / (j.order : ℝ))) : ℝ) : ℂ) = -(1 / (j.order : ℂ)) := by
    push_cast
    rfl
  rw [he, Complex.real_smul, Complex.real_smul]
  ring

theorem ThreefoldOverlapMappingTorus.Elliptic.root_add_order (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (t : ThreefoldOverlapMappingTorus.Circle) :
    ThreefoldOverlapMappingTorus.root j.order r a
        (t + (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)) =
      (Elliptic.familyRotation j).symm (ThreefoldOverlapMappingTorus.root j.order r a t) := by
  apply (Elliptic.familyRotation j).injective
  exact
    ((root_sub_order j r a
              (t + (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle))).symm.trans
          (congrArg (ThreefoldOverlapMappingTorus.root j.order r a)
            (add_sub_cancel_right _ _))).trans
      ((Elliptic.familyRotation j).apply_symm_apply _).symm

def ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (p : ThreefoldOverlapMappingTorus.Circle × RealTorus₄) : Elliptic.Family j :=
  (ThreefoldOverlapMappingTorus.root j.order r a p.1, p.2)

theorem ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt_injective (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) :
    Function.Injective (polarFamilyAt j r a) := by
  intro p q hpq
  apply Prod.ext
  · have hz :
      ThreefoldOverlapMappingTorus.polarRoot j.order r (a, p.1) =
        ThreefoldOverlapMappingTorus.polarRoot j.order r (a, q.1) :=
      Subtype.ext (congrArg Prod.fst hpq)
    have he := congrArg (ThreefoldOverlapMappingTorus.rootAngle j.order r) hz
    simpa only [ThreefoldOverlapMappingTorus.rootAngle_polarRoot] using he
  · exact congrArg (fun y : Elliptic.Family j => y.2) hpq

theorem ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt_twist (j : Elliptic.Kind)
    (v : Lattice) (r : ℝ) (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (p : ThreefoldOverlapMappingTorus.Circle × RealTorus₄) :
    polarFamilyAt j r a
        (Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
          (Elliptic.flatTorusAffine j v).symm p) =
      (Elliptic.familyPermutation j v).symm (polarFamilyAt j r a p) := by
  change
    (ThreefoldOverlapMappingTorus.root j.order r a
          (p.1 + (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)),
        (Elliptic.flatTorusAffine j v).symm p.2) =
      ((Elliptic.familyRotation j).symm (ThreefoldOverlapMappingTorus.root j.order r a p.1),
        (Elliptic.flatTorusAffine j v).symm p.2)
  exact Prod.ext (root_add_order j r a p.1) rfl

theorem ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt_smul (j : Elliptic.Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (r : ℝ) (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (g : Elliptic.CyclicGroup j) (p : ThreefoldOverlapMappingTorus.Circle × RealTorus₄) :
    letI :=
      Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
        (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv)
    letI := Elliptic.familyAction j v hv
    polarFamilyAt j r a (g • p) = g⁻¹ • polarFamilyAt j r a p := by
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv)
  let := Elliptic.familyAction j v hv
  have he : g⁻¹ = Multiplicative.ofAdd (-(g.toAdd.val : ℤ) : ZMod j.order) := by
    apply Multiplicative.ext
    simp
  have hright :
    g⁻¹ • polarFamilyAt j r a p =
      ((Elliptic.familyPermutation j v).symm :
            Elliptic.Family j → Elliptic.Family j)^[g.toAdd.val]
        (polarFamilyAt j r a p) := by
    rw [he]
    have hc :=
      Elliptic.HigherHomology.MappingTorusQuotient.cyclicAction_ofAdd_intCast_smul j.order
        (Elliptic.familyPermutation j v) (Elliptic.familyPermutation_pow_order j v hv)
        (-(g.toAdd.val : ℤ)) (polarFamilyAt j r a p)
    simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] at hc
    rw [← inv_pow, Equiv.Perm.coe_pow] at hc
    simpa only [Int.cast_natCast, Equiv.Perm.inv_def] using hc
  rw [hright]
  change
    polarFamilyAt j r a
        ((Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
                (Elliptic.flatTorusAffine j v).symm :
              _ → _)^[g.toAdd.val]
          p) =
      _
  exact Function.Semiconj.iterate_right (polarFamilyAt_twist j v r a) g.toAdd.val p

def ThreefoldOverlapMappingTorus.quotientComparison {X Y Z : Type*} (q : X → Y) (p : X → Z)
    (hq : Function.Surjective q) : Y → Z := fun y => p (hq y).choose

theorem ThreefoldOverlapMappingTorus.quotientComparison_apply {X Y Z : Type*} (q : X → Y)
    (p : X → Z) (hq : Function.Surjective q) (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    quotientComparison q p hq (q x) = p x :=
  (h _ _).mp (hq (q x)).choose_spec

theorem ThreefoldOverlapMappingTorus.quotientComparison_continuous {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (q : X → Y) (p : X → Z)
    (hq : Topology.IsQuotientMap q) (hp : Continuous p) (h : ∀ x x', q x = q x' ↔ p x = p x') :
    Continuous (quotientComparison q p hq.surjective) := by
  apply hq.continuous_iff.mpr
  have he : quotientComparison q p hq.surjective ∘ q = p :=
    funext (quotientComparison_apply q p hq.surjective h)
  rw [he]
  exact hp

def ThreefoldOverlapMappingTorus.quotientHomeomorph {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (q : X → Y) (p : X → Z)
    (hq : Topology.IsQuotientMap q) (hp : Topology.IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') : Y ≃ₜ Z
    where
  toFun := quotientComparison q p hq.surjective
  invFun := quotientComparison p q hp.surjective
  left_inv
    y := by
    obtain ⟨x, rfl⟩ := hq.surjective y
    rw [quotientComparison_apply q p hq.surjective h,
      quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm)]
  right_inv
    z := by
    obtain ⟨x, rfl⟩ := hp.surjective z
    rw [quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm),
      quotientComparison_apply q p hq.surjective h]
  continuous_toFun := quotientComparison_continuous q p hq hp.continuous h
  continuous_invFun :=
    quotientComparison_continuous p q hp hq.continuous (fun x x' => (h x x').symm)

@[simp]
theorem ThreefoldOverlapMappingTorus.quotientHomeomorph_symm_apply {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (q : X → Y) (p : X → Z)
    (hq : Topology.IsQuotientMap q) (hp : Topology.IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    (quotientHomeomorph q p hq hp h).symm (p x) = q x :=
  quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm) x

def ThreefoldOverlapMappingTorus.Elliptic.puncturedSet (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) : Set (Elliptic.Filling j v hv) :=
  {y |
    (Elliptic.fillingProjection j v hv y : ℂ) ≠ 0 ∧
      ‖(Elliptic.fillingProjection j v hv y : ℂ)‖ < r}

abbrev ThreefoldOverlapMappingTorus.Elliptic.PuncturedFilling (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :=
  puncturedSet j v hv r

abbrev ThreefoldOverlapMappingTorus.Elliptic.PuncturedUpstairs (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :=
  Elliptic.fillingQuotient j v hv ⁻¹' puncturedSet j v hv r

theorem ThreefoldOverlapMappingTorus.Elliptic.puncturedUpstairs_mem (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) (x : Elliptic.Family j) :
    x ∈ PuncturedUpstairs j v hv r ↔ (x.1 : ℂ) ≠ 0 ∧ ‖(x.1 : ℂ)‖ ^ j.order < r := by
  change ((x.1 : ℂ) ^ j.order ≠ 0 ∧ ‖(x.1 : ℂ) ^ j.order‖ < r) ↔ _
  rw [norm_pow]
  constructor
  · rintro ⟨hne, hnorm⟩
    exact ⟨fun hz => hne (by rw [hz, zero_pow j.order_pos.ne']), hnorm⟩
  · rintro ⟨hne, hnorm⟩
    exact ⟨pow_ne_zero _ hne, hnorm⟩

def ThreefoldOverlapMappingTorus.Elliptic.upstairsRootHomeomorph (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedUpstairs j v hv r ≃ₜ ThreefoldOverlapMappingTorus.RootDisc j.order r × RealTorus₄
    where
  toFun y := (⟨y.val.1, (puncturedUpstairs_mem j v hv r y.val).mp y.property⟩, y.val.2)
  invFun p := ⟨(p.1.val, p.2), (puncturedUpstairs_mem j v hv r (p.1.val, p.2)).mpr p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

def ThreefoldOverlapMappingTorus.Elliptic.upstairsPolarHomeomorph (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedUpstairs j v hv r ≃ₜ
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄) :=
  (upstairsRootHomeomorph j v hv r).trans
    (((ThreefoldOverlapMappingTorus.polarHomeomorph j.order r).prodCongr
          (Homeomorph.refl RealTorus₄)).trans
      (Homeomorph.prodAssoc _ _ _))

def ThreefoldOverlapMappingTorus.Elliptic.polarQuotient (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    PuncturedFilling j v hv r :=
  (puncturedSet j v hv r).restrictPreimage (Elliptic.fillingQuotient j v hv)
    ((upstairsPolarHomeomorph j v hv r).symm p)

theorem ThreefoldOverlapMappingTorus.Elliptic.polarQuotient_isOpenQuotientMap (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    IsOpenQuotientMap (polarQuotient j v hv r) := by
  have hq : IsOpenQuotientMap (Elliptic.fillingQuotient j v hv) :=
    ⟨Elliptic.fillingQuotient_surjective j v hv, Elliptic.fillingQuotient_continuous j v hv,
      (Elliptic.fillingQuotient_isCoveringMap j v hv).isOpenMap⟩
  have hr := hq.restrictPreimage (puncturedSet j v hv r)
  let e := (upstairsPolarHomeomorph j v hv r).symm
  exact
    ⟨hr.surjective.comp e.surjective, hr.continuous.comp e.continuous,
      hr.isOpenMap.comp e.isOpenMap⟩

@[simp]
theorem ThreefoldOverlapMappingTorus.Elliptic.polarQuotient_projection_norm (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    ‖(Elliptic.fillingProjection j v hv (polarQuotient j v hv r p) : ℂ)‖ = (p.1 : ℝ) ^ j.order := by
  change ‖(ThreefoldOverlapMappingTorus.root j.order r p.1 p.2.1 : ℂ) ^ j.order‖ = _
  rw [norm_pow, ThreefoldOverlapMappingTorus.root_norm]

abbrev ThreefoldOverlapMappingTorus.Elliptic.BoundaryQuotient (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) :=
  Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient j.order
    (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)

def ThreefoldOverlapMappingTorus.Elliptic.radialQuotient (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    ThreefoldOverlapMappingTorus.Radius j.order r × BoundaryQuotient j v hv :=
  (p.1,
    Elliptic.HigherHomology.MappingTorusQuotient.project j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) p.2)

theorem ThreefoldOverlapMappingTorus.Elliptic.radialQuotient_isOpenQuotientMap (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    IsOpenQuotientMap (radialQuotient j v hv r) := by
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction_continuousConstSMul j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  exact
    IsOpenQuotientMap.id.prodMap
      (Elliptic.FiniteQuotient.project_isOpenQuotientMap (Elliptic.CyclicGroup j)
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄))

theorem ThreefoldOverlapMappingTorus.Elliptic.polarQuotient_eq_iff (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p q :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    polarQuotient j v hv r p = polarQuotient j v hv r q ↔
      radialQuotient j v hv r p = radialQuotient j v hv r q := by
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  let := Elliptic.familyAction j v hv.1
  rcases p with ⟨a, p⟩
  rcases q with ⟨b, q⟩
  constructor
  · intro h
    have hpow :=
      congrArg (fun y : PuncturedFilling j v hv r => ‖(Elliptic.fillingProjection j v hv y : ℂ)‖)
        h
    simp only [polarQuotient_projection_norm] at hpow
    have hab : a = b :=
      Subtype.ext ((pow_left_inj₀ a.property.1.le b.property.1.le j.order_pos.ne').mp hpow)
    subst b
    apply Prod.ext
    · rfl
    have hq :
      Elliptic.fillingQuotient j v hv (polarFamilyAt j r a p) =
        Elliptic.fillingQuotient j v hv (polarFamilyAt j r a q) :=
      congrArg Subtype.val h
    obtain ⟨g, hg⟩ :=
      (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
            (Elliptic.Family j) _ _).mp
        hq
    apply
      (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
          (ThreefoldOverlapMappingTorus.Circle × RealTorus₄) _ _).mpr
    refine ⟨g⁻¹, (polarFamilyAt_injective j r a) ?_⟩
    have he := polarFamilyAt_smul j v hv.1 r a g⁻¹ q
    have he' : polarFamilyAt j r a (g⁻¹ • q) = g • polarFamilyAt j r a q := by
      simpa only [inv_inv] using he
    exact he'.trans hg
  · intro h
    have hab : a = b := congrArg Prod.fst h
    subst b
    have hp :
      Elliptic.HigherHomology.MappingTorusQuotient.project j.order
          (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) p =
        Elliptic.HigherHomology.MappingTorusQuotient.project j.order
          (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) q :=
      congrArg Prod.snd h
    obtain ⟨g, hg⟩ :=
      (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
            (ThreefoldOverlapMappingTorus.Circle × RealTorus₄) _ _).mp
        hp
    apply Subtype.ext
    change
      Elliptic.fillingQuotient j v hv (polarFamilyAt j r a p) =
        Elliptic.fillingQuotient j v hv (polarFamilyAt j r a q)
    rw [← hg, polarFamilyAt_smul j v hv.1]
    exact Elliptic.FiniteQuotient.project_smul (Elliptic.CyclicGroup j) (Elliptic.Family j) g⁻¹ _

def ThreefoldOverlapMappingTorus.Elliptic.puncturedPolarHomeomorph (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedFilling j v hv r ≃ₜ
      ThreefoldOverlapMappingTorus.Radius j.order r × BoundaryQuotient j v hv :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph (polarQuotient j v hv r)
    (radialQuotient j v hv r) (polarQuotient_isOpenQuotientMap j v hv r).isQuotientMap
    (radialQuotient_isOpenQuotientMap j v hv r).isQuotientMap (polarQuotient_eq_iff j v hv r)

@[simp]
theorem ThreefoldOverlapMappingTorus.Elliptic.puncturedPolarHomeomorph_symm_radialQuotient
    (j : Elliptic.Kind) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    (puncturedPolarHomeomorph j v hv r).symm (radialQuotient j v hv r p) =
      polarQuotient j v hv r p :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_symm_apply _ _ _ _ _ p

abbrev ThreefoldOverlapMappingTorus.Elliptic.Boundary (j : Elliptic.Kind) (v : Lattice) :=
  MappingTorus.Torus (Elliptic.flatTorusAffine j v)

def ThreefoldOverlapMappingTorus.Elliptic.puncturedProductHomeomorph (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedFilling j v hv r ≃ₜ ThreefoldOverlapMappingTorus.Radius j.order r × Boundary j v :=
  (puncturedPolarHomeomorph j v hv r).trans
    ((Homeomorph.refl _).prodCongr
      (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph j.order
        (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)))

theorem ThreefoldOverlapMappingTorus.Elliptic.puncturedProductHomeomorph_symm_mk
    (j : Elliptic.Kind) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) (t : ℝ) (x : RealTorus₄) :
    (puncturedProductHomeomorph j v hv r).symm
        (a, MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r
        (a, (((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x)) := by
  change
    (puncturedPolarHomeomorph j v hv r).symm
        (a,
          (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph j.order
                (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)).symm
            (MappingTorus.mk _ (t, x))) =
      _
  rw [Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_symm_mk]
  exact
    puncturedPolarHomeomorph_symm_radialQuotient j v hv r
      (a, (((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x))

def ThreefoldOverlapMappingTorus.Elliptic.puncturedMappingTorusHomotopyEquiv (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) :
    PuncturedFilling j v hv r ≃ₕ Boundary j v :=
  (puncturedProductHomeomorph j v hv r).toHomotopyEquiv.trans
    (ThreefoldOverlapMappingTorus.radiusProductHomotopyEquiv a (Boundary j v))

def ThreefoldOverlapMappingTorus.Elliptic.boundaryInclusion (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) :
    C(Boundary j v, PuncturedFilling j v hv r) :=
  ⟨(puncturedMappingTorusHomotopyEquiv j v hv r a).symm,
    (puncturedMappingTorusHomotopyEquiv j v hv r a).symm.continuous⟩

@[simp]
theorem ThreefoldOverlapMappingTorus.Elliptic.boundaryInclusion_mk (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) (t : ℝ) (x : RealTorus₄) :
    boundaryInclusion j v hv r a (MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r
        (a, (((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x)) :=
  puncturedProductHomeomorph_symm_mk j v hv r a t x

theorem BranchedQuotientAtlas.project_localInverse_eventuallyEq {E M Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace Q] {q : M → Q} (hq : Continuous q) (e : OpenPartialHomeomorph Q E) {z : E}
    (hz : z ∈ e.target) {a : M} (ha : q a = e.symm z)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (e ∘ q) a) :
    q ∘ hf.localInverse =ᶠ[𝓝 z] e.symm := by
  have hcoord : (e ∘ q) a = z := by simp only [Function.comp_apply, ha, e.right_inv hz]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hcont : ContinuousAt (q ∘ hf.localInverse) z := by
    have h := hq.continuousAt.comp hf.localInverse_contMDiffAt.continuousAt
    simpa only [hcoord] using h
  have hsource : ∀ᶠ w in 𝓝 z, q (hf.localInverse w) ∈ e.source :=
    hcont
      (e.open_source.mem_nhds
        (by simpa only [Function.comp_apply, hinv, ha] using e.map_target hz))
  have hright : ∀ᶠ w in 𝓝 z, e (q (hf.localInverse w)) = w := by
    rw [← hcoord]
    exact hf.localInverse_eventuallyEq_right
  filter_upwards [hsource, hright] with w hw he
  change q (hf.localInverse w) = e.symm w
  exact (e.left_inv hw).symm.trans (congrArg e.symm he)

theorem BranchedQuotientAtlas.contDiffAt_transition_of_lift {E M Q : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q] {q : M → Q}
    (hq : Continuous q) (e f : OpenPartialHomeomorph Q E)
    (hhol :
      ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (f ∘ q)
        (q ⁻¹' f.source))
    {z : E} (hz : z ∈ (e.symm.trans f).source) {a : M} (ha : q a = e.symm z)
    (hf :
      IsLocalDiffeomorphAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (e ∘ q) a) :
    ContDiffAt ℂ ω (e.symm.trans f) z := by
  have hcoord : (e ∘ q) a = z := by simp only [Function.comp_apply, ha, e.right_inv hz.1]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hfirst :
    ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω hf.localInverse z := by
    simpa only [hcoord] using hf.localInverse_contMDiffAt
  have hsecond : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω (f ∘ q) a :=
    hhol.contMDiffAt
      ((f.open_source.preimage hq).mem_nhds
        (by
          change q a ∈ f.source
          rw [ha]
          exact hz.2))
  have hcomp : ContDiffAt ℂ ω ((f ∘ q) ∘ hf.localInverse) z :=
    (hsecond.comp_of_eq hfirst hinv).contDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [project_localInverse_eventuallyEq hq e hz.1 ha hf] with w hw
  change f (e.symm w) = f (q (hf.localInverse w))
  exact congrArg f hw.symm


end Mathoverflow1973

end
