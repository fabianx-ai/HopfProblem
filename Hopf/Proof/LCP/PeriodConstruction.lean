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
Original source lines 148197--168788; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.LCP.PeriodConstruction
import Hopf.Proof.LCP.Specialization
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

/-! Proof-specific part of `Hopf.LCP.PeriodConstruction` (split by lean-agent-ide `split_module`); the stock part that is
still to be moved into `Lib/` stays in `Hopf/LCP/PeriodConstruction.lean`. Declarations, names and namespaces are unchanged. -/

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


def SpecialPeriods.Triangle.width : ℝ :=
  1 + Real.sqrt 2

theorem SpecialPeriods.Triangle.width_pos : 0 < width := by
  unfold width
  positivity

theorem SpecialPeriods.Triangle.one_lt_width : 1 < width := by
  unfold width
  have : 0 < Real.sqrt 2 := by positivity
  linarith

theorem SpecialPeriods.Triangle.width_ne_zero : width ≠ 0 :=
  width_pos.ne'

theorem SpecialPeriods.Triangle.width_sq : width ^ 2 = 2 * width + 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold width
  nlinarith

theorem SpecialPeriods.Triangle.width_sub_one_sq : (width - 1) ^ 2 = 2 := by nlinarith [width_sq]

def SpecialPeriods.Triangle.generatorOneSL : SL(2, ℝ) :=
  ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

def SpecialPeriods.Triangle.generatorTwoSL : SL(2, ℝ) :=
  ⟨!![1, width + 1; -1, -width], by simp [Matrix.det_fin_two_of]⟩

def SpecialPeriods.Triangle.cuspInverseSL : SL(2, ℝ) :=
  ⟨!![1, width; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def SpecialPeriods.Triangle.cuspSL : SL(2, ℝ) :=
  cuspInverseSL⁻¹

@[simp]
theorem SpecialPeriods.Triangle.coe_generatorOneSL :
    (generatorOneSL : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 1] :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.coe_generatorTwoSL :
    (generatorTwoSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, width + 1; -1, -width] :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.coe_cuspSL :
    (cuspSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -width; 0, 1] := by
  have hco : (cuspInverseSL : Matrix (Fin 2) (Fin 2) ℝ) = !![1, width; 0, 1] := rfl
  simp [hco, cuspSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem SpecialPeriods.Triangle.coe_generatorOneSL_sq :
    ((generatorOneSL ^ 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -1; 1, 0] := by
  norm_num [Matrix.SpecialLinearGroup.coe_pow, pow_two, Matrix.mul_fin_two]

theorem SpecialPeriods.Triangle.generatorOneSL_cube : generatorOneSL ^ 3 = -1 := by
  apply Subtype.ext
  norm_num [Matrix.SpecialLinearGroup.coe_pow, pow_succ, Matrix.mul_fin_two, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem SpecialPeriods.Triangle.coe_generatorTwoSL_sq :
    ((generatorTwoSL ^ 2 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-width, -2 * width; width - 1, width] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_generatorTwoSL, pow_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]

theorem SpecialPeriods.Triangle.generatorTwoSL_fourth : generatorTwoSL ^ 4 = -1 := by
  have hsq : (generatorTwoSL ^ 2) ^ 2 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_generatorTwoSL_sq,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, pow_two,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]
  simpa only [← pow_mul] using hsq

theorem SpecialPeriods.Triangle.generatorOneSL_mul_generatorTwoSL :
    generatorOneSL * generatorTwoSL = cuspInverseSL := by
  apply Subtype.ext
  simp [cuspInverseSL]

theorem SpecialPeriods.Triangle.generatorOneSL_mul_generatorTwoSL_mul_cuspSL :
    generatorOneSL * generatorTwoSL * cuspSL = 1 := by
  rw [generatorOneSL_mul_generatorTwoSL, cuspSL, mul_inv_cancel]

theorem SpecialPeriods.Triangle.cuspSL_inv : cuspSL⁻¹ = cuspInverseSL :=
  inv_inv _

theorem SpecialPeriods.Triangle.sub_conj_ne_zero (a z : ℍ) :
    (z : ℂ) - starRingEnd ℂ (a : ℂ) ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at him
  linarith [a.im_pos, z.im_pos]

def SpecialPeriods.Triangle.cayleyCoordinate (a z : ℍ) : ℂ :=
  ((z : ℂ) - a) / ((z : ℂ) - starRingEnd ℂ (a : ℂ))

theorem SpecialPeriods.Triangle.cayleyCoordinate_norm_lt_one (a z : ℍ) :
    ‖cayleyCoordinate a z‖ < 1 := by
  rw [cayleyCoordinate, norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (sub_conj_ne_zero a z))).mpr
  have hsq : Complex.normSq ((z : ℂ) - a) < Complex.normSq ((z : ℂ) - starRingEnd ℂ (a : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, UpperHalfPlane.coe_im]
    nlinarith [mul_pos a.im_pos z.im_pos]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((z : ℂ) - a), norm_nonneg ((z : ℂ) - starRingEnd ℂ (a : ℂ))]

def SpecialPeriods.Triangle.toDisc (a z : ℍ) : SpecialPeriods.Disc :=
  ⟨cayleyCoordinate a z, by
    simpa [SpecialPeriods.unitDisc] using cayleyCoordinate_norm_lt_one a z⟩

@[simp]
theorem SpecialPeriods.Triangle.toDisc_val (a z : ℍ) : (toDisc a z : ℂ) = cayleyCoordinate a z :=
  rfl

def SpecialPeriods.Triangle.fromDisc (a : ℍ) (z : SpecialPeriods.Disc) : ℍ :=
  UpperHalfPlane.ofComplex (SpecialPeriods.cayley a z)

@[simp]
theorem SpecialPeriods.Triangle.fromDisc_val (a : ℍ) (z : SpecialPeriods.Disc) :
    (fromDisc a z : ℂ) = SpecialPeriods.cayley a z := by
  simp only [fromDisc,
    UpperHalfPlane.ofComplex_apply_of_im_pos
        (SpecialPeriods.cayley_im_pos a.im_pos (SpecialPeriods.disc_norm_lt_one z))]

@[simp]
theorem SpecialPeriods.Triangle.toDisc_center (a : ℍ) :
    toDisc a a = (⟨0, by simp [SpecialPeriods.unitDisc]⟩ : SpecialPeriods.Disc) := by
  apply Subtype.ext
  simp [toDisc, cayleyCoordinate]

theorem SpecialPeriods.Triangle.cayleyCoordinate_holomorphic (a : ℍ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyCoordinate a) :=
  (UpperHalfPlane.contMDiff_coe.sub contMDiff_const).div₀
    (UpperHalfPlane.contMDiff_coe.sub contMDiff_const) (sub_conj_ne_zero a)

theorem SpecialPeriods.Triangle.toDisc_holomorphic (a : ℍ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toDisc a) := by
  intro z
  have he :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℍ => (toDisc a w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (toDisc a) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (cayleyCoordinate_holomorphic a z)

theorem SpecialPeriods.Triangle.fromDisc_holomorphic (a : ℍ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fromDisc a) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : SpecialPeriods.Disc => SpecialPeriods.cayley a z) :=
    (SpecialPeriods.cayley_contDiffOn (a : ℂ)).contMDiffOn.comp_contMDiff contMDiff_subtype_val
      (fun z => z.property)
  intro z
  exact
    (UpperHalfPlane.contMDiffAt_ofComplex
          (SpecialPeriods.cayley_im_pos a.im_pos (SpecialPeriods.disc_norm_lt_one z))).comp
      z (hc z)

theorem SpecialPeriods.Triangle.fromDisc_toDisc (a z : ℍ) : fromDisc a (toDisc a z) = z := by
  apply UpperHalfPlane.ext
  rw [fromDisc_val, toDisc_val]
  have hd := sub_conj_ne_zero a z
  have ha := sub_conj_ne_zero a a
  have hc := SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (cayleyCoordinate_norm_lt_one a z)
  unfold SpecialPeriods.cayley cayleyCoordinate at *
  field_simp [hd, ha, hc]
  ring

theorem SpecialPeriods.Triangle.toDisc_fromDisc (a : ℍ) (z : SpecialPeriods.Disc) :
    toDisc a (fromDisc a z) = z := by
  apply Subtype.ext
  rw [toDisc_val]
  unfold cayleyCoordinate
  rw [fromDisc_val]
  have hd := SpecialPeriods.one_sub_ne_zero_of_norm_lt_one (SpecialPeriods.disc_norm_lt_one z)
  have ha := sub_conj_ne_zero a a
  have hz := sub_conj_ne_zero a (fromDisc a z)
  rw [fromDisc_val] at hz
  unfold SpecialPeriods.cayley at *
  field_simp [hd, ha, hz]
  ring_nf
  field_simp [ha]

def SpecialPeriods.Triangle.cayleyBiholomorph (a : ℍ) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ SpecialPeriods.Disc ω
    where
  toFun := toDisc a
  invFun := fromDisc a
  left_inv := fromDisc_toDisc a
  right_inv := toDisc_fromDisc a
  contMDiff_toFun := toDisc_holomorphic a
  contMDiff_invFun := fromDisc_holomorphic a

def SpecialPeriods.Triangle.slDenom (g : SL(2, ℝ)) (z : ℂ) : ℂ :=
  (g 1 0 : ℂ) * z + (g 1 1 : ℂ)

theorem SpecialPeriods.Triangle.slDenom_ne_zero (g : SL(2, ℝ)) (z : ℍ) : slDenom g z ≠ 0 :=
  UpperHalfPlane.linear_ne_zero z (g.row_ne_zero 1)

theorem SpecialPeriods.Triangle.sl_fixed_equation (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) * a + (g 0 1 : ℂ) = (a : ℂ) * slDenom g a := by
  have he := congrArg (fun z : ℍ => (z : ℂ)) hfix
  apply (div_eq_iff (slDenom_ne_zero g a)).mp
  simpa only [UpperHalfPlane.coe_specialLinearGroup_apply, Algebra.algebraMap_self,
    RingHom.id_apply, slDenom] using he

theorem SpecialPeriods.Triangle.sl_fixed_conj_equation (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    (g 0 0 : ℂ) * starRingEnd ℂ (a : ℂ) + (g 0 1 : ℂ) =
      starRingEnd ℂ (a : ℂ) * slDenom g (starRingEnd ℂ (a : ℂ)) := by
  simpa [slDenom] using congrArg (starRingEnd ℂ) (sl_fixed_equation g a hfix)

theorem SpecialPeriods.Triangle.sl_fixed_denominator_identity (g : SL(2, ℝ)) (a : ℍ)
    (hfix : g • a = a) : ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) * slDenom g a = 1 := by
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast
      (show g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 from
        (Matrix.det_fin_two g.val).symm.trans g.property)
  have hf := sl_fixed_equation g a hfix
  unfold slDenom at *
  linear_combination (g 1 0 : ℂ) * hf + hdet

theorem SpecialPeriods.Triangle.sl_fixed_conj_denominator (g : SL(2, ℝ)) (a : ℍ)
    (hfix : g • a = a) : (g 0 0 : ℂ) - (g 1 0 : ℂ) * starRingEnd ℂ (a : ℂ) = slDenom g a := by
  have hf := sl_fixed_equation g a hfix
  have him := congrArg Complex.im hf
  simp only [slDenom, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    MulZeroClass.zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him
  have hr : g 0 0 = 2 * g 1 0 * (a : ℂ).re + g 1 1 := by
    apply mul_right_cancel₀ (show (a : ℂ).im ≠ 0 from a.im_ne_zero)
    calc
      g 0 0 * (a : ℂ).im =
          (a : ℂ).re * (g 1 0 * (a : ℂ).im) + (a : ℂ).im * (g 1 0 * (a : ℂ).re + g 1 1) :=
        him
      _ = (2 * g 1 0 * (a : ℂ).re + g 1 1) * (a : ℂ).im := by ring
  apply Complex.ext <;>
      simp only [slDenom, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im] <;>
    nlinarith [hr]

theorem SpecialPeriods.Triangle.sl_fixed_denominator_norm (g : SL(2, ℝ)) (a : ℍ)
    (hfix : g • a = a) : ‖slDenom g a‖ = 1 := by
  have hc : starRingEnd ℂ (slDenom g a) = (g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ) := by
    simpa only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_conj] using
      (congrArg (starRingEnd ℂ) (sl_fixed_conj_denominator g a hfix)).symm
  have hm : starRingEnd ℂ (slDenom g a) * slDenom g a = 1 := by
    rw [hc, sl_fixed_denominator_identity g a hfix]
  have hn := congrArg Norm.norm hm
  simp only [norm_mul, Complex.norm_conj, NormOneClass.norm_one] at hn
  nlinarith [norm_nonneg (slDenom g a)]

def SpecialPeriods.Triangle.slMultiplier (g : SL(2, ℝ)) (a : ℍ) : ℂ :=
  1 / slDenom g a ^ 2

theorem SpecialPeriods.Triangle.sl_hasStrictDerivAt_smul (g : SL(2, ℝ)) (a : ℍ) :
    HasStrictDerivAt (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (slMultiplier g a)
      (a : ℂ) := by
  have h :=
    UpperHalfPlane.hasStrictDerivAt_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) a
  simpa [MulAction.compHom_smul_def, slMultiplier, slDenom, UpperHalfPlane.denom] using h

theorem SpecialPeriods.Triangle.sl_deriv_smul (g : SL(2, ℝ)) (a : ℍ) :
    deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) = slMultiplier g a :=
  (sl_hasStrictDerivAt_smul g a).hasDerivAt.deriv

theorem SpecialPeriods.Triangle.slMultiplier_norm (g : SL(2, ℝ)) (a : ℍ) (hfix : g • a = a) :
    ‖slMultiplier g a‖ = 1 := by simp [slMultiplier, sl_fixed_denominator_norm g a hfix]

theorem SpecialPeriods.Triangle.cayleyCoordinate_smul (g : SL(2, ℝ)) (a z : ℍ)
    (hfix : g • a = a) : cayleyCoordinate a (g • z) = slMultiplier g a * cayleyCoordinate a z := by
  have hd := slDenom_ne_zero g z
  have ha := slDenom_ne_zero g a
  have hn :
    ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - (a : ℂ) =
      ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) * ((z : ℂ) - a) / slDenom g z := by
    have hf := sl_fixed_equation g a hfix
    field_simp [hd]
    unfold slDenom at *
    linear_combination hf
  have hnbar :
    ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - starRingEnd ℂ (a : ℂ) =
      ((g 0 0 : ℂ) - (g 1 0 : ℂ) * starRingEnd ℂ (a : ℂ)) * ((z : ℂ) - starRingEnd ℂ (a : ℂ)) /
        slDenom g z := by
    have hf := sl_fixed_conj_equation g a hfix
    field_simp [hd]
    unfold slDenom at *
    linear_combination hf
  have hcoef : ((g 0 0 : ℂ) - (g 1 0 : ℂ) * (a : ℂ)) / slDenom g a = slMultiplier g a := by
    rw [slMultiplier, div_eq_div_iff ha (pow_ne_zero 2 ha)]
    have hf := sl_fixed_denominator_identity g a hfix
    linear_combination slDenom g a * hf
  unfold cayleyCoordinate
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  change
    (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - (a : ℂ)) /
        (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / slDenom g z - starRingEnd ℂ (a : ℂ)) =
      _
  rw [hn, hnbar, div_div_div_cancel_right₀ hd, sl_fixed_conj_denominator g a hfix,
    mul_div_mul_comm, hcoef]

def SpecialPeriods.cyclicPowerHom {G : Type*} [Group G] (n : ℕ) (a : G) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  (ZMod.lift n
      ⟨zmultiplesHom (Additive G) (Additive.ofMul a),
        by
        change a ^ (n : ℤ) = 1
        simpa only [zpow_natCast] using ha⟩).toMultiplicativeLeft

@[simp]
theorem SpecialPeriods.cyclicPowerHom_intCast {G : Type*} [Group G] (n : ℕ) (a : G)
    (ha : a ^ n = 1) (k : ℤ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (k : ZMod n)) = a ^ k := by simp [cyclicPowerHom]

@[simp]
theorem SpecialPeriods.cyclicPowerHom_one {G : Type*} [Group G] (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (1 : ZMod n)) = a := by
  simpa using cyclicPowerHom_intCast n a ha 1

private theorem SpecialPeriods.cyclic_eq_generator_zpow_mo1973_15645 {n : ℕ}
    (x : Multiplicative (ZMod n)) : ∃ k : ℤ, x = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨k, ?_⟩
  change x.toAdd = k • (1 : ZMod n)
  simpa using hk.symm

private theorem SpecialPeriods.cyclic_hom_ext_mo1973_15646 {G : Type*} [Group G] {n : ℕ}
    {f g : Multiplicative (ZMod n) →* G}
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow_mo1973_15645 x
  rw [map_zpow, map_zpow, h]

abbrev SpecialPeriods.TriangleGroup :=
  Monoid.Coprod (Multiplicative (ZMod 3)) (Multiplicative (ZMod 4))

def SpecialPeriods.triangleGenerator₁ : TriangleGroup :=
  Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3))

def SpecialPeriods.triangleGenerator₂ : TriangleGroup :=
  Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4))

def SpecialPeriods.triangleCuspGenerator : TriangleGroup :=
  (triangleGenerator₁ * triangleGenerator₂)⁻¹

theorem SpecialPeriods.triangleGenerator₁_order : orderOf triangleGenerator₁ = 3 := by
  rw [triangleGenerator₁, orderOf_injective _ Monoid.Coprod.inl_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem SpecialPeriods.triangleGenerator₂_order : orderOf triangleGenerator₂ = 4 := by
  rw [triangleGenerator₂, orderOf_injective _ Monoid.Coprod.inr_injective,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

@[simp]
theorem SpecialPeriods.triangleGenerator₁_cube : triangleGenerator₁ ^ 3 = 1 := by
  simpa only [triangleGenerator₁_order] using pow_orderOf_eq_one triangleGenerator₁

theorem SpecialPeriods.triangle_generators_generate :
    Subgroup.closure ({ triangleGenerator₁, triangleGenerator₂ } : Set TriangleGroup) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using Monoid.Coprod.induction_on with
  | inl x =>
    obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow_mo1973_15645 x
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp [triangleGenerator₁])) k
  | inr x =>
    obtain ⟨k, rfl⟩ := cyclic_eq_generator_zpow_mo1973_15645 x
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp [triangleGenerator₂])) k
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

def SpecialPeriods.triangleLift {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : TriangleGroup →* G :=
  Monoid.Coprod.lift (cyclicPowerHom 3 a ha) (cyclicPowerHom 4 b hb)

@[simp]
theorem SpecialPeriods.triangleLift_generator₁ {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : triangleLift a b ha hb triangleGenerator₁ = a := by
  simp [triangleLift, triangleGenerator₁]

@[simp]
theorem SpecialPeriods.triangleLift_generator₂ {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : triangleLift a b ha hb triangleGenerator₂ = b := by
  simp [triangleLift, triangleGenerator₂]

@[simp]
theorem SpecialPeriods.triangleLift_cusp {G : Type*} [Group G] (a b : G) (ha : a ^ 3 = 1)
    (hb : b ^ 4 = 1) : triangleLift a b ha hb triangleCuspGenerator = (a * b)⁻¹ := by
  simp [triangleCuspGenerator]

theorem SpecialPeriods.triangle_hom_ext {G : Type*} [Group G] {f g : TriangleGroup →* G}
    (h₁ : f triangleGenerator₁ = g triangleGenerator₁)
    (h₂ : f triangleGenerator₂ = g triangleGenerator₂) : f = g := by
  apply Monoid.Coprod.hom_ext
  · exact cyclic_hom_ext_mo1973_15646 h₁
  · exact cyclic_hom_ext_mo1973_15646 h₂

theorem SpecialPeriods.triangle_range {G : Type*} [Group G] (f : TriangleGroup →* G) :
    f.range = Subgroup.closure ({f triangleGenerator₁, f triangleGenerator₂} : Set G) := by
  rw [MonoidHom.range_eq_map, ← triangle_generators_generate, MonoidHom.map_closure,
    Set.image_pair]

def SpecialPeriods.triangleLatticeT₁ : SL(4, ℤ) :=
  ⟨T₁, det_T₁⟩

def SpecialPeriods.triangleLatticeT₂ : SL(4, ℤ) :=
  ⟨T₂, det_T₂⟩

theorem SpecialPeriods.triangleLatticeT₁_cube : triangleLatticeT₁ ^ 3 = 1 :=
  Subtype.ext T₁_cube

theorem SpecialPeriods.triangleLatticeT₂_fourth : triangleLatticeT₂ ^ 4 = 1 :=
  Subtype.ext T₂_fourth

def SpecialPeriods.triangleLatticeRepresentation : TriangleGroup →* SL(4, ℤ) :=
  triangleLift triangleLatticeT₁ triangleLatticeT₂ triangleLatticeT₁_cube triangleLatticeT₂_fourth

@[simp]
theorem SpecialPeriods.triangleLatticeRepresentation_generator₁ :
    triangleLatticeRepresentation triangleGenerator₁ = triangleLatticeT₁ :=
  triangleLift_generator₁ ..

@[simp]
theorem SpecialPeriods.triangleLatticeRepresentation_generator₂ :
    triangleLatticeRepresentation triangleGenerator₂ = triangleLatticeT₂ :=
  triangleLift_generator₂ ..

theorem SpecialPeriods.triangleLatticeRepresentation_cusp_matrix :
    (triangleLatticeRepresentation triangleCuspGenerator : LatticeMatrix) = T₀ := by
  rw [triangleLatticeRepresentation, triangleLift_cusp]
  decide

def SpecialPeriods.latticeContragredient : SL(4, ℤ) →* SL(4, ℤ)
    where
  toFun A := Matrix.SpecialLinearGroup.transpose A⁻¹
  map_one' := Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])
  map_mul' A
    B :=
    Subtype.ext
      (by
        change
          (((A * B)⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose =
            ((A⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose *
              ((B⁻¹ : SL(4, ℤ)) : LatticeMatrix).transpose
        simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

def SpecialPeriods.triangleDualRepresentation : TriangleGroup →* SL(4, ℤ) :=
  latticeContragredient.comp triangleLatticeRepresentation

theorem SpecialPeriods.triangleDualRepresentation_generator₁_matrix :
    (triangleDualRepresentation triangleGenerator₁ : LatticeMatrix) = A₁ := by
  rw [triangleDualRepresentation, MonoidHom.comp_apply, triangleLatticeRepresentation_generator₁]
  decide

theorem SpecialPeriods.triangleDualRepresentation_generator₂_matrix :
    (triangleDualRepresentation triangleGenerator₂ : LatticeMatrix) = A₂ := by
  rw [triangleDualRepresentation, MonoidHom.comp_apply, triangleLatticeRepresentation_generator₂]
  decide

theorem SpecialPeriods.triangleDualRepresentation_cusp_matrix :
    (triangleDualRepresentation triangleCuspGenerator : LatticeMatrix) = M₀ := by
  change
    (Matrix.adjugate
          (triangleLatticeRepresentation triangleCuspGenerator : LatticeMatrix)).transpose =
      M₀
  rw [triangleLatticeRepresentation_cusp_matrix]
  decide

def SpecialPeriods.Triangle.realSLPermutation : SL(2, ℝ) →* Equiv.Perm ℍ :=
  MulAction.toPermHom (SL(2, ℝ)) ℍ

@[simp]
theorem SpecialPeriods.Triangle.realSLPermutation_apply (A : SL(2, ℝ)) (z : ℍ) :
    realSLPermutation A z = A • z :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.realSLPermutation_neg_one : realSLPermutation (-1) = 1 := by
  apply Equiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (((-1 : SL(2, ℝ)) • z : ℍ) : ℂ) = z
  norm_num [UpperHalfPlane.coe_specialLinearGroup_apply, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

def SpecialPeriods.Triangle.generatorOnePerm : Equiv.Perm ℍ :=
  realSLPermutation generatorOneSL

def SpecialPeriods.Triangle.generatorTwoPerm : Equiv.Perm ℍ :=
  realSLPermutation generatorTwoSL

theorem SpecialPeriods.Triangle.generatorOnePerm_cube : generatorOnePerm ^ 3 = 1 := by
  rw [generatorOnePerm, ← map_pow, generatorOneSL_cube, realSLPermutation_neg_one]

theorem SpecialPeriods.Triangle.generatorTwoPerm_fourth : generatorTwoPerm ^ 4 = 1 := by
  rw [generatorTwoPerm, ← map_pow, generatorTwoSL_fourth, realSLPermutation_neg_one]

def SpecialPeriods.Triangle.horizontalTranslation : Multiplicative ℝ →* Equiv.Perm ℍ :=
  (AddAction.toPermHom ℝ ℍ).toMultiplicativeLeft

@[simp]
theorem SpecialPeriods.Triangle.horizontalTranslation_apply (t : ℝ) (z : ℍ) :
    horizontalTranslation (Multiplicative.ofAdd t) z = t +ᵥ z :=
  rfl

theorem SpecialPeriods.Triangle.cuspSL_apply (z : ℍ) : cuspSL • z = (-width) +ᵥ z := by
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_specialLinearGroup_apply, coe_cuspSL, add_comm]

theorem SpecialPeriods.Triangle.cuspSL_permutation_eq_translation :
    realSLPermutation cuspSL = horizontalTranslation (Multiplicative.ofAdd (-width)) := by
  apply Equiv.ext
  exact cuspSL_apply

def SpecialPeriods.triangleGeometricRepresentation : TriangleGroup →* Equiv.Perm ℍ :=
  triangleLift Triangle.generatorOnePerm Triangle.generatorTwoPerm Triangle.generatorOnePerm_cube
    Triangle.generatorTwoPerm_fourth

@[instance_reducible]
def SpecialPeriods.triangleGeometricAction : MulAction TriangleGroup ℍ :=
  MulAction.compHom ℍ triangleGeometricRepresentation

theorem SpecialPeriods.triangleGeometricAction_smul (g : TriangleGroup) (z : ℍ) :
    letI := triangleGeometricAction
    g • z = triangleGeometricRepresentation g z :=
  rfl

@[simp]
theorem SpecialPeriods.triangleGeometricRepresentation_generator₁ :
    triangleGeometricRepresentation triangleGenerator₁ = Triangle.generatorOnePerm :=
  triangleLift_generator₁ ..

@[simp]
theorem SpecialPeriods.triangleGeometricRepresentation_generator₂ :
    triangleGeometricRepresentation triangleGenerator₂ = Triangle.generatorTwoPerm :=
  triangleLift_generator₂ ..

@[simp]
theorem SpecialPeriods.triangleGeometricRepresentation_generator₁_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₁ z = Triangle.generatorOneSL • z := by
  rw [triangleGeometricRepresentation_generator₁]
  rfl

@[simp]
theorem SpecialPeriods.triangleGeometricRepresentation_generator₂_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₂ z = Triangle.generatorTwoSL • z := by
  rw [triangleGeometricRepresentation_generator₂]
  rfl

theorem SpecialPeriods.triangleGeometricRepresentation_has_SL_lift (g : TriangleGroup) :
    ∃ A : SL(2, ℝ), Triangle.realSLPermutation A = triangleGeometricRepresentation g := by
  have hr : triangleGeometricRepresentation.range ≤ Triangle.realSLPermutation.range := by
    rw [triangle_range]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    rcases hp with rfl | rfl
    · exact ⟨Triangle.generatorOneSL, triangleGeometricRepresentation_generator₁.symm⟩
    · exact ⟨Triangle.generatorTwoSL, triangleGeometricRepresentation_generator₂.symm⟩
  exact hr ⟨g, rfl⟩

theorem SpecialPeriods.triangleGeometricRepresentation_cusp :
    triangleGeometricRepresentation triangleCuspGenerator =
      Triangle.realSLPermutation Triangle.cuspSL := by
  rw [triangleGeometricRepresentation, triangleLift_cusp, Triangle.generatorOnePerm,
    Triangle.generatorTwoPerm, ← map_mul, Triangle.generatorOneSL_mul_generatorTwoSL, ← map_inv]
  rfl

theorem SpecialPeriods.triangleGeometricRepresentation_cusp_eq_translation :
    triangleGeometricRepresentation triangleCuspGenerator =
      Triangle.horizontalTranslation (Multiplicative.ofAdd (-Triangle.width)) :=
  triangleGeometricRepresentation_cusp.trans Triangle.cuspSL_permutation_eq_translation

@[simp]
theorem SpecialPeriods.triangleGeometricRepresentation_cusp_apply (z : ℍ) :
    triangleGeometricRepresentation triangleCuspGenerator z = (-Triangle.width) +ᵥ z := by
  rw [triangleGeometricRepresentation_cusp_eq_translation]
  rfl

theorem SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_apply (n : ℤ) (z : ℍ) :
    triangleGeometricRepresentation (triangleCuspGenerator ^ n) z =
      (-(n : ℝ) * Triangle.width) +ᵥ z := by
  rw [map_zpow, triangleGeometricRepresentation_cusp_eq_translation, ← map_zpow, ← ofAdd_zsmul,
    Triangle.horizontalTranslation_apply]
  congr 1
  simp only [zsmul_eq_mul, mul_neg, neg_mul]

theorem SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe (n : ℤ) (z : ℍ) :
    (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z : ℂ) =
      z - (n : ℂ) * Triangle.width := by
  rw [triangleGeometricRepresentation_cusp_zpow_apply, UpperHalfPlane.coe_vadd]
  push_cast
  ring

theorem SpecialPeriods.triangleGeometricRepresentation_cusp_orbit_injective (z : ℍ) :
    Function.Injective
      (fun n : ℤ => triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) := by
  intro m n h
  simp only [triangleGeometricRepresentation_cusp_zpow_apply] at h
  have he := (UpperHalfPlane.vadd_right_cancel_iff z).mp h
  have hmn := neg_injective (mul_right_cancel₀ Triangle.width_ne_zero he)
  exact_mod_cast hmn

theorem SpecialPeriods.Triangle.specialLinear_holomorphic (g : SL(2, ℝ)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => g • z) := by
  exact UpperHalfPlane.contMDiff_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp)

def SpecialPeriods.Triangle.centerOne : ℍ :=
  ⟨SpecialPeriods.rho - 1, by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using SpecialPeriods.rho_im_pos⟩

def SpecialPeriods.Triangle.centerTwo : ℍ :=
  ⟨-((width : ℂ) + 1) / 2 + ((width : ℂ) - 1) / 2 * Complex.I,
    by
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.neg_im, Complex.add_im,
      Complex.ofReal_im, Complex.one_im, Complex.sub_im, Complex.mul_im, Complex.div_ofNat_re,
      Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.I_im, Complex.I_re]
    linarith [one_lt_width]⟩

@[simp]
theorem SpecialPeriods.Triangle.centerOne_val : (centerOne : ℂ) = SpecialPeriods.rho - 1 :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.centerTwo_val :
    (centerTwo : ℂ) = -((width : ℂ) + 1) / 2 + ((width : ℂ) - 1) / 2 * Complex.I :=
  rfl

theorem SpecialPeriods.Triangle.centerTwo_re : centerTwo.re = -(width + 1) / 2 := by
  simp [UpperHalfPlane.re, centerTwo]

theorem SpecialPeriods.Triangle.centerTwo_im : centerTwo.im = (width - 1) / 2 := by
  simp [UpperHalfPlane.im, centerTwo]

theorem SpecialPeriods.Triangle.width_complex_sq : (width : ℂ) ^ 2 = 2 * width + 1 := by
  exact_mod_cast width_sq

theorem SpecialPeriods.Triangle.generatorOne_coe (z : ℍ) :
    ((generatorOneSL • z : ℍ) : ℂ) = -1 / ((z : ℂ) + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [generatorOneSL]

theorem SpecialPeriods.Triangle.generatorTwo_coe (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) = ((z : ℂ) + (width : ℂ) + 1) / (-(z : ℂ) - width) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [generatorTwoSL, add_assoc, sub_eq_add_neg]

theorem SpecialPeriods.Triangle.denominatorOne_ne_zero (z : ℍ) : (z : ℂ) + 1 ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.one_im, Complex.zero_im, add_zero,
    UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem SpecialPeriods.Triangle.denominatorTwo_ne_zero (z : ℍ) : -(z : ℂ) - width ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, sub_zero, Complex.zero_im,
    neg_eq_zero, UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem SpecialPeriods.Triangle.centerTwo_polynomial :
    (centerTwo : ℂ) ^ 2 + ((width : ℂ) + 1) * centerTwo + ((width : ℂ) + 1) = 0 := by
  rw [centerTwo_val]
  calc
    _ =
        -((width : ℂ) + 1) ^ 2 / 4 + ((width : ℂ) - 1) ^ 2 / 4 * Complex.I ^ 2 +
          ((width : ℂ) + 1) := by ring
    _ = -((width : ℂ) ^ 2 - 2 * width - 1) / 2 := by rw [Complex.I_sq]; ring
    _ = 0 := by rw [width_complex_sq]; ring

@[simp]
theorem SpecialPeriods.Triangle.generatorOne_fix : generatorOneSL • centerOne = centerOne := by
  apply UpperHalfPlane.ext
  rw [generatorOne_coe, centerOne_val]
  have hd : SpecialPeriods.rho ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_im] at hi
    exact (ne_of_gt SpecialPeriods.rho_im_pos) hi
  simp only [sub_add_cancel]
  apply (div_eq_iff hd).mpr
  linear_combination -SpecialPeriods.rho_sq

@[simp]
theorem SpecialPeriods.Triangle.generatorTwo_fix : generatorTwoSL • centerTwo = centerTwo := by
  apply UpperHalfPlane.ext
  rw [generatorTwo_coe]
  apply (div_eq_iff (denominatorTwo_ne_zero centerTwo)).mpr
  linear_combination centerTwo_polynomial

theorem SpecialPeriods.Triangle.generatorOne_derivative_coefficient :
    1 / ((centerOne : ℂ) + 1) ^ 2 = -SpecialPeriods.rho := by
  rw [centerOne_val, sub_add_cancel]
  apply
    (div_eq_iff
        (pow_ne_zero 2
          (by
            intro he
            have hi := congrArg Complex.im he
            simp only [Complex.zero_im] at hi
            exact (ne_of_gt SpecialPeriods.rho_im_pos) hi))).mpr
  linear_combination SpecialPeriods.rho_cube

theorem SpecialPeriods.Triangle.generatorTwo_denominator_sq :
    (-(centerTwo : ℂ) - width) ^ 2 = Complex.I := by
  rw [centerTwo_val]
  calc
    _ = ((width : ℂ) - 1) ^ 2 / 4 * (1 + 2 * Complex.I + Complex.I ^ 2) := by ring
    _ = Complex.I := by
      rw [Complex.I_sq]
      have hs : ((width : ℂ) - 1) ^ 2 = 2 := by exact_mod_cast width_sub_one_sq
      rw [hs]
      ring

theorem SpecialPeriods.Triangle.generatorTwo_derivative_coefficient :
    1 / (-(centerTwo : ℂ) - width) ^ 2 = -Complex.I := by
  rw [generatorTwo_denominator_sq]
  simp

theorem SpecialPeriods.Triangle.generatorOne_multiplier :
    slMultiplier generatorOneSL centerOne = -SpecialPeriods.rho := by
  simpa [slMultiplier, slDenom, generatorOneSL] using generatorOne_derivative_coefficient

theorem SpecialPeriods.Triangle.generatorTwo_multiplier :
    slMultiplier generatorTwoSL centerTwo = -Complex.I := by
  simpa [slMultiplier, slDenom, generatorTwoSL, sub_eq_add_neg] using
    generatorTwo_derivative_coefficient

theorem SpecialPeriods.Triangle.generatorTwo_hasStrictDerivAt :
    HasStrictDerivAt (fun z : ℂ => ((generatorTwoSL • UpperHalfPlane.ofComplex z : ℍ) : ℂ))
      (-Complex.I) (centerTwo : ℂ) := by
  rw [← generatorTwo_multiplier]
  exact sl_hasStrictDerivAt_smul _ _

theorem SpecialPeriods.Triangle.generatorOne_cayley (z : ℍ) :
    cayleyCoordinate centerOne (generatorOneSL • z) =
      -SpecialPeriods.rho * cayleyCoordinate centerOne z := by
  rw [cayleyCoordinate_smul _ _ _ generatorOne_fix, generatorOne_multiplier]

theorem SpecialPeriods.Triangle.generatorTwo_cayley (z : ℍ) :
    cayleyCoordinate centerTwo (generatorTwoSL • z) = -Complex.I * cayleyCoordinate centerTwo z :=
  by rw [cayleyCoordinate_smul _ _ _ generatorTwo_fix, generatorTwo_multiplier]

theorem SpecialPeriods.Triangle.generatorOne_toDisc (z : ℍ) :
    toDisc centerOne (generatorOneSL • z) = SpecialPeriods.discRotateThree (toDisc centerOne z) :=
  by
  apply Subtype.ext
  exact generatorOne_cayley z

theorem SpecialPeriods.Triangle.generatorTwo_toDisc (z : ℍ) :
    toDisc centerTwo (generatorTwoSL • z) = SpecialPeriods.discRotateFour (toDisc centerTwo z) := by
  apply Subtype.ext
  exact generatorTwo_cayley z

theorem SpecialPeriods.Triangle.generatorOne_pow_toDisc (n : ℕ) (z : ℍ) :
    toDisc centerOne (generatorOneSL ^ n • z) =
      SpecialPeriods.discRotateThree^[n] (toDisc centerOne z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', SemigroupAction.mul_smul, generatorOne_toDisc, ih,
      Function.iterate_succ_apply']

theorem SpecialPeriods.Triangle.generatorTwo_pow_toDisc (n : ℕ) (z : ℍ) :
    toDisc centerTwo (generatorTwoSL ^ n • z) =
      SpecialPeriods.discRotateFour^[n] (toDisc centerTwo z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', SemigroupAction.mul_smul, generatorTwo_toDisc, ih,
      Function.iterate_succ_apply']

theorem SpecialPeriods.Triangle.generatorOne_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3)
    (z : ℍ) : generatorOneSL ^ n • z = z ↔ z = centerOne := by
  have he :
    generatorOneSL ^ n • z = z ↔ toDisc centerOne (generatorOneSL ^ n • z) = toDisc centerOne z :=
    (cayleyBiholomorph centerOne).injective.eq_iff.symm
  rw [he, generatorOne_pow_toDisc, SpecialPeriods.discRotateThree_iterate_fixed_iff n hn hn']
  have hc : toDisc centerOne centerOne = SpecialPeriods.discZero := toDisc_center _
  rw [← hc]
  exact (cayleyBiholomorph centerOne).injective.eq_iff

theorem SpecialPeriods.Triangle.generatorTwo_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4)
    (z : ℍ) : generatorTwoSL ^ n • z = z ↔ z = centerTwo := by
  have he :
    generatorTwoSL ^ n • z = z ↔ toDisc centerTwo (generatorTwoSL ^ n • z) = toDisc centerTwo z :=
    (cayleyBiholomorph centerTwo).injective.eq_iff.symm
  rw [he, generatorTwo_pow_toDisc, SpecialPeriods.discRotateFour_iterate_fixed_iff n hn hn']
  have hc : toDisc centerTwo centerTwo = SpecialPeriods.discZero := toDisc_center _
  rw [← hc]
  exact (cayleyBiholomorph centerTwo).injective.eq_iff

theorem SpecialPeriods.triangleGeometricRepresentation_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (triangleGeometricRepresentation g : ℍ → ℍ) := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_has_SL_lift g
  rw [← hA]
  exact Triangle.specialLinear_holomorphic A

def SpecialPeriods.triangleGeometricBiholomorph (g : TriangleGroup) : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℍ ω
    where
  toEquiv := triangleGeometricRepresentation g
  contMDiff_toFun := triangleGeometricRepresentation_holomorphic g
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (((triangleGeometricRepresentation g)⁻¹ : Equiv.Perm ℍ) : ℍ → ℍ)
    rw [← map_inv]
    exact triangleGeometricRepresentation_holomorphic g⁻¹

def SpecialPeriods.Triangle.stripLeft : ℝ :=
  -(width + 1) / 2

def SpecialPeriods.Triangle.stripRight : ℝ :=
  (width - 1) / 2

theorem SpecialPeriods.Triangle.strip_width : stripRight - stripLeft = width := by
  unfold stripRight stripLeft
  ring

theorem SpecialPeriods.Triangle.stripRight_pos : 0 < stripRight := by
  unfold stripRight
  linarith [one_lt_width]

theorem SpecialPeriods.Triangle.stripRight_sq : stripRight ^ 2 = 1 / 2 := by
  unfold stripRight
  nlinarith [width_sub_one_sq]

theorem SpecialPeriods.Triangle.half_lt_stripRight : 1 / 2 < stripRight := by
  nlinarith [stripRight_sq, stripRight_pos]

def SpecialPeriods.Triangle.fordRegion : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ 1 ≤ ‖(z : ℂ) + 1‖ ∧ 1 ≤ ‖(z : ℂ)‖}

theorem SpecialPeriods.Triangle.fordRegion_closed : IsClosed fordRegion :=
  (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
    ((isClosed_le UpperHalfPlane.continuous_re continuous_const).inter
      ((isClosed_le continuous_const
            ((UpperHalfPlane.continuous_coe.add continuous_const).norm)).inter
        (isClosed_le continuous_const UpperHalfPlane.continuous_coe.norm)))

theorem SpecialPeriods.Triangle.mem_fordRegion_of_one_le_im (z : ℍ) (hl : stripLeft ≤ z.re)
    (hr : z.re ≤ stripRight) (hi : 1 ≤ z.im) : z ∈ fordRegion := by
  refine ⟨hl, hr, ?_, ?_⟩
  · have hh := Complex.im_le_norm ((z : ℂ) + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im] at hh
    exact hi.trans hh
  · exact hi.trans (Complex.im_le_norm (z : ℂ))

theorem SpecialPeriods.Triangle.exists_cusp_translate_in_strip (z : ℍ) :
    ∃ n : ℤ,
      stripLeft ≤ ((-(n : ℝ) * width) +ᵥ z).re ∧ ((-(n : ℝ) * width) +ᵥ z).re < stripRight := by
  let n : ℤ := ⌊(z.re - stripLeft) / width⌋
  have hlo : (n : ℝ) ≤ (z.re - stripLeft) / width := Int.floor_le _
  have hhi : (z.re - stripLeft) / width < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hlo' := (le_div_iff₀ width_pos).mp hlo
  have hhi' := (div_lt_iff₀ width_pos).mp hhi
  refine ⟨n, ?_, ?_⟩ <;> simp only [UpperHalfPlane.vadd_re] <;> nlinarith [strip_width]

theorem SpecialPeriods.Triangle.sl_im (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (slDenom g z) := by
  have h := UpperHalfPlane.im_smul_eq_div_normSq (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  simpa [MulAction.compHom_smul_def, UpperHalfPlane.denom, slDenom] using h

theorem SpecialPeriods.Triangle.generatorOne_im (z : ℍ) :
    (generatorOneSL • z).im = z.im / Complex.normSq ((z : ℂ) + 1) := by
  rw [sl_im]
  simp [slDenom, generatorOneSL]

theorem SpecialPeriods.Triangle.generatorOne_sq_im (z : ℍ) :
    (generatorOneSL ^ 2 • z).im = z.im / Complex.normSq (z : ℂ) := by
  rw [sl_im]
  have h0 : (generatorOneSL ^ 2 : SL(2, ℝ)) 1 0 = 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) coe_generatorOneSL_sq
  have h1 : (generatorOneSL ^ 2 : SL(2, ℝ)) 1 1 = 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) coe_generatorOneSL_sq
  simp [slDenom, h0, h1]

theorem SpecialPeriods.Triangle.im_lt_generatorOne_im (z : ℍ) (hz : ‖(z : ℂ) + 1‖ < 1) :
    z.im < (generatorOneSL • z).im := by
  rw [generatorOne_im]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hs : Complex.normSq ((z : ℂ) + 1) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  apply (lt_div_iff₀ hd).mpr
  nlinarith [z.im_pos]

theorem SpecialPeriods.Triangle.im_lt_generatorOne_sq_im (z : ℍ) (hz : ‖(z : ℂ)‖ < 1) :
    z.im < (generatorOneSL ^ 2 • z).im := by
  rw [generatorOne_sq_im]
  have hs : Complex.normSq (z : ℂ) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  apply (lt_div_iff₀ z.normSq_pos).mpr
  nlinarith [z.im_pos]

theorem SpecialPeriods.Triangle.outside_fordRegion_increases_height (z : ℍ)
    (hl : stripLeft ≤ z.re) (hr : z.re ≤ stripRight) (hz : z ∉ fordRegion) :
    z.im < (generatorOneSL • z).im ∨ z.im < (generatorOneSL ^ 2 • z).im := by
  by_cases h : 1 ≤ ‖(z : ℂ) + 1‖
  · right
    apply im_lt_generatorOne_sq_im
    exact lt_of_not_ge (fun hh => hz ⟨hl, hr, h, hh⟩)
  · exact Or.inl (im_lt_generatorOne_im z (lt_of_not_ge h))

theorem SpecialPeriods.Triangle.fordRegion_im_lower_bound (z : ℍ) (hz : z ∈ fordRegion) :
    stripRight ≤ z.im := by
  obtain ⟨hl, hr, hleft, hright⟩ := hz
  have hnorm_left : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  have hnorm_right : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
    add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hnorm_left hnorm_right
  by_cases hx : z.re ≤ -(1 / 2)
  · have hlow : -stripRight ≤ z.re + 1 := by
      unfold stripLeft stripRight at *
      linarith
    have hupp : z.re + 1 ≤ stripRight := by linarith [half_lt_stripRight]
    have hsq : (z.re + 1) ^ 2 ≤ stripRight ^ 2 := sq_le_sq' hlow hupp
    nlinarith [stripRight_sq, stripRight_pos, z.im_pos]
  · have hlow : -stripRight ≤ z.re := by linarith [half_lt_stripRight]
    have hsq : z.re ^ 2 ≤ stripRight ^ 2 := sq_le_sq' hlow hr
    nlinarith [stripRight_sq, stripRight_pos, z.im_pos]

def SpecialPeriods.Triangle.reductionBox (lo hi : ℝ) : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ lo ≤ z.im ∧ z.im ≤ hi}

theorem SpecialPeriods.Triangle.coe_reductionBox (lo hi : ℝ) (hlo : 0 < lo) :
    ((↑) : ℍ → ℂ) '' reductionBox lo hi = (Set.Icc stripLeft stripRight) ×ℂ (Set.Icc lo hi) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  · rintro ⟨⟨hl, hr⟩, hlow, hupp⟩
    exact ⟨⟨z, hlo.trans_le hlow⟩, ⟨hl, hr, hlow, hupp⟩, rfl⟩

theorem SpecialPeriods.Triangle.reductionBox_compact (lo hi : ℝ) (hlo : 0 < lo) :
    IsCompact (reductionBox lo hi) := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff, coe_reductionBox lo hi hlo]
  exact CompactIccSpace.isCompact_Icc.reProdIm CompactIccSpace.isCompact_Icc

def SpecialPeriods.Triangle.truncatedFordRegion (hi : ℝ) : Set ℍ :=
  {z | z ∈ fordRegion ∧ z.im ≤ hi}

theorem SpecialPeriods.Triangle.truncatedFordRegion_compact (hi : ℝ) :
    IsCompact (truncatedFordRegion hi) := by
  refine
    (reductionBox_compact stripRight hi stripRight_pos).of_isClosed_subset
      (fordRegion_closed.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)) ?_
  intro z hz
  exact ⟨hz.1.1, hz.1.2.1, fordRegion_im_lower_bound z hz.1, hz.2⟩

theorem SpecialPeriods.Triangle.cuspSL_zpow_translate (n : ℤ) (z : ℍ) :
    (cuspSL ^ n : SL(2, ℝ)) • z = (-(n : ℝ) * width) +ᵥ z := by
  change realSLPermutation (cuspSL ^ n) z = _
  rw [map_zpow, cuspSL_permutation_eq_translation, ← map_zpow, ← ofAdd_zsmul,
    horizontalTranslation_apply]
  congr 1
  simp only [zsmul_eq_mul, mul_neg, neg_mul]

theorem SpecialPeriods.Triangle.subgroup_normalize_strip (Γ : Subgroup SL(2, ℝ)) (hc : cuspSL ∈ Γ)
    (z : ℍ) : ∃ g : Γ, stripLeft ≤ (g • z).re ∧ (g • z).re ≤ stripRight ∧ (g • z).im = z.im := by
  obtain ⟨n, hl, hr⟩ := exists_cusp_translate_in_strip z
  let g : Γ := (⟨cuspSL, hc⟩ : Γ) ^ n
  have he : g • z = (-(n : ℝ) * width) +ᵥ z := by
    change ((g : SL(2, ℝ)) • z) = _
    simpa [g] using cuspSL_zpow_translate n z
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [he] using hl
  · simpa only [he] using hr.le
  · rw [he, UpperHalfPlane.vadd_im]

theorem SpecialPeriods.Triangle.subgroup_exists_fordRegion_representative (Γ : Subgroup SL(2, ℝ))
    [ProperlyDiscontinuousSMul Γ ℍ] (ha : generatorOneSL ∈ Γ) (hc : cuspSL ∈ Γ) (z : ℍ) :
    ∃ g : Γ, g • z ∈ fordRegion := by
  classical
  by_cases hh : ∃ g : Γ, 1 ≤ (g • z).im
  · obtain ⟨g, hg⟩ := hh
    obtain ⟨k, hkl, hkr, hki⟩ := subgroup_normalize_strip Γ hc (g • z)
    refine ⟨k * g, ?_⟩
    rw [SemigroupAction.mul_smul]
    exact mem_fordRegion_of_one_le_im _ hkl hkr (hki ▸ hg)
  have hbound (g : Γ) : (g • z).im < 1 := lt_of_not_ge (fun hg => hh ⟨g, hg⟩)
  let candidates : Set Γ := {g | g • z ∈ reductionBox z.im 1}
  have hfinite : candidates.Finite := by
    have h :=
      ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (K := { z })
        isCompact_singleton (reductionBox_compact z.im 1 z.im_pos)
    simpa only [Set.image_singleton, Set.singleton_inter_nonempty] using h
  have hnonempty : candidates.Nonempty := by
    obtain ⟨g, hl, hr, hi⟩ := subgroup_normalize_strip Γ hc z
    refine ⟨g, hl, hr, ?_, (hbound g).le⟩
    rw [hi]
  obtain ⟨g, hg, hmax⟩ := Set.exists_max_image candidates (fun g => (g • z).im) hfinite hnonempty
  refine ⟨g, ?_⟩
  by_contra hout
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (g • z).im < (generatorOneSL ^ m • (g • z)).im := by
    rcases outside_fordRegion_increases_height (g • z) hg.1 hg.2.1 hout with h | h
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, h⟩
  let a : Γ := ⟨generatorOneSL, ha⟩
  let u : Γ := a ^ m * g
  have hinc : (g • z).im < (u • z).im := by
    dsimp only [u]
    rw [SemigroupAction.mul_smul]
    exact hm
  obtain ⟨k, hkl, hkr, hki⟩ := subgroup_normalize_strip Γ hc (u • z)
  let v : Γ := k * u
  have hvim : (v • z).im = (u • z).im := by simpa only [v, SemigroupAction.mul_smul] using hki
  have hv : v ∈ candidates := by
    refine ⟨?_, ?_, ?_, (hbound v).le⟩
    · simpa only [v, SemigroupAction.mul_smul] using hkl
    · simpa only [v, SemigroupAction.mul_smul] using hkr
    · have hbase : z.im ≤ (g • z).im := hg.2.2.1
      linarith
  have hle := hmax v hv
  linarith

def SpecialPeriods.Triangle.pingPongOne : Set ℍ :=
  {z | -1 < z.re}

def SpecialPeriods.Triangle.pingPongTwo : Set ℍ :=
  {z | z.re < -1}

theorem SpecialPeriods.Triangle.pingPongOne_nonempty : pingPongOne.Nonempty := by
  exact ⟨UpperHalfPlane.I, by norm_num [pingPongOne]⟩

theorem SpecialPeriods.Triangle.pingPongTwo_nonempty : pingPongTwo.Nonempty := by
  refine ⟨⟨(-2 : ℂ) + Complex.I, by norm_num⟩, ?_⟩
  norm_num [pingPongTwo]

theorem SpecialPeriods.Triangle.pingPong_disjoint : Disjoint pingPongOne pingPongTwo := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  change -1 < z.re at hz₁
  change z.re < -1 at hz₂
  exact lt_asymm hz₁ hz₂

private theorem SpecialPeriods.Triangle.smul_coe_of_matrix_mo1973_15784 (g : SL(2, ℝ))
    (a b c d : ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change
    (((((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) : ℂ) * z +
          (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) : ℂ)) /
        (((((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) : ℂ)) * z +
          (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) : ℂ))) =
      _
  rw [hg]
  rfl

private theorem SpecialPeriods.Triangle.add_real_ne_zero_mo1973_15785 (z : ℍ) (c : ℝ) :
    (z : ℂ) + c ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im,
    UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem SpecialPeriods.Triangle.generatorOneSL_smul_coe (z : ℍ) :
    ((generatorOneSL • z : ℍ) : ℂ) = -((z : ℂ) + 1)⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 generatorOneSL 0 (-1) 1 1 coe_generatorOneSL]
  simp [div_eq_mul_inv]

theorem SpecialPeriods.Triangle.generatorOneSL_sq_smul_coe (z : ℍ) :
    (((generatorOneSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) = -1 - (z : ℂ)⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 (generatorOneSL ^ 2) (-1) (-1) 1 0 coe_generatorOneSL_sq]
  push_cast
  field_simp [z.ne_zero]
  ring

theorem SpecialPeriods.Triangle.generatorTwoSL_smul_coe (z : ℍ) :
    ((generatorTwoSL • z : ℍ) : ℂ) = -1 - ((z : ℂ) + (width : ℂ))⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 generatorTwoSL 1 (width + 1) (-1) (-width)
      coe_generatorTwoSL]
  push_cast
  let u : ℂ := (z : ℂ) + (width : ℂ)
  have hu : u ≠ 0 := add_real_ne_zero_mo1973_15785 z width
  calc
    _ = (u + 1) / (-u) := by dsimp [u]; congr 1 <;> ring
    _ = -(1 + u⁻¹) := by rw [div_neg, add_div, div_self hu, one_div]
    _ = -1 - u⁻¹ := by ring

theorem SpecialPeriods.Triangle.generatorTwoSL_sq_smul_coe (z : ℍ) :
    (((generatorTwoSL ^ 2 : SL(2, ℝ)) • z : ℍ) : ℂ) =
      -1 - ((z : ℂ) + (width : ℂ)) / (((width : ℂ) - 1) * z + (width : ℂ)) := by
  rw [smul_coe_of_matrix_mo1973_15784 (generatorTwoSL ^ 2) (-width) (-2 * width) (width - 1) width
      coe_generatorTwoSL_sq]
  have hd : ((width : ℂ) - 1) * (z : ℂ) + (width : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero, MulZeroClass.zero_mul,
      add_zero, UpperHalfPlane.coe_im] at hi
    exact (mul_pos (sub_pos.mpr one_lt_width) z.im_pos).ne' hi
  push_cast
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hd]
  ring

theorem SpecialPeriods.Triangle.coe_generatorTwoSL_cube :
    ((generatorTwoSL ^ 3 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![width, width + 1; -1, -1] :=
  by
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, coe_generatorTwoSL_sq, coe_generatorTwoSL,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [width_sq]

theorem SpecialPeriods.Triangle.generatorTwoSL_cube_smul_coe (z : ℍ) :
    (((generatorTwoSL ^ 3 : SL(2, ℝ)) • z : ℍ) : ℂ) = -(width : ℂ) - ((z : ℂ) + 1)⁻¹ := by
  rw [smul_coe_of_matrix_mo1973_15784 (generatorTwoSL ^ 3) width (width + 1) (-1) (-1)
      coe_generatorTwoSL_cube]
  have hd : (z : ℂ) + 1 ≠ 0 := by simpa using add_real_ne_zero_mo1973_15785 z 1
  push_cast
  let u : ℂ := (z : ℂ) + 1
  calc
    _ = ((width : ℂ) * u + 1) / (-u) := by dsimp [u]; congr 1 <;> ring
    _ = -((width : ℂ) + u⁻¹) := by rw [div_neg, add_div, mul_div_cancel_right₀ _ hd, one_div]
    _ = -(width : ℂ) - u⁻¹ := by ring

theorem SpecialPeriods.Triangle.generatorOne_pingPong :
    Set.MapsTo (fun z : ℍ => generatorOneSL • z) pingPongTwo pingPongOne := by
  intro z hz
  change -1 < (generatorOneSL • z).re
  change z.re < -1 at hz
  rw [← UpperHalfPlane.coe_re, generatorOneSL_smul_coe]
  simp only [Complex.neg_re, Complex.inv_re, Complex.add_re, Complex.one_re,
    UpperHalfPlane.coe_re]
  have hden : 0 < Complex.normSq ((z : ℂ) + 1) :=
    Complex.normSq_pos.mpr (by simpa using add_real_ne_zero_mo1973_15785 z 1)
  have hn : (z.re + 1) / Complex.normSq ((z : ℂ) + 1) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hden
  linarith

theorem SpecialPeriods.Triangle.generatorOne_sq_pingPong :
    Set.MapsTo (fun z : ℍ => (generatorOneSL ^ 2 : SL(2, ℝ)) • z) pingPongTwo pingPongOne := by
  intro z hz
  change -1 < ((generatorOneSL ^ 2 : SL(2, ℝ)) • z).re
  change z.re < -1 at hz
  rw [← UpperHalfPlane.coe_re, generatorOneSL_sq_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re,
    UpperHalfPlane.coe_re]
  have hn : z.re / Complex.normSq (z : ℂ) < 0 := div_neg_of_neg_of_pos (by linarith) z.normSq_pos
  linarith

theorem SpecialPeriods.Triangle.generatorTwo_pingPong :
    Set.MapsTo (fun z : ℍ => generatorTwoSL • z) pingPongOne pingPongTwo := by
  intro z hz
  change (generatorTwoSL • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.inv_re, Complex.add_re,
    Complex.ofReal_re, UpperHalfPlane.coe_re]
  have hp : 0 < (z.re + width) / Complex.normSq ((z : ℂ) + (width : ℂ)) :=
    div_pos (by linarith [one_lt_width])
      (Complex.normSq_pos.mpr (add_real_ne_zero_mo1973_15785 z width))
  linarith

theorem SpecialPeriods.Triangle.generatorTwo_sq_pingPong :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 2 : SL(2, ℝ)) • z) pingPongOne pingPongTwo := by
  intro z hz
  change ((generatorTwoSL ^ 2 : SL(2, ℝ)) • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_sq_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  suffices hpos : 0 < (((z : ℂ) + (width : ℂ)) / (((width : ℂ) - 1) * z + (width : ℂ))).re by
    linarith
  let u : ℂ := (z : ℂ) + (width : ℂ)
  let v : ℂ := ((width : ℂ) - 1) * z + (width : ℂ)
  have hu : 0 < u.re := by
    change 0 < z.re + width
    linarith [one_lt_width]
  have hv : 0 < v.re := by
    simp only [v, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero,
      MulZeroClass.zero_mul, UpperHalfPlane.coe_re]
    nlinarith [one_lt_width]
  have hvi : 0 < v.im := by
    simp only [v, Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero,
      MulZeroClass.zero_mul, add_zero, UpperHalfPlane.coe_im]
    exact mul_pos (sub_pos.mpr one_lt_width) z.im_pos
  have hui : 0 < u.im := by simpa [u] using z.im_pos
  have hn : 0 < Complex.normSq v := by
    apply Complex.normSq_pos.mpr
    intro h
    exact hv.ne' (by simpa using congrArg Complex.re h)
  change 0 < (u / v).re
  rw [Complex.div_re]
  exact add_pos (div_pos (mul_pos hu hv) hn) (div_pos (mul_pos hui hvi) hn)

theorem SpecialPeriods.Triangle.generatorTwo_cube_pingPong :
    Set.MapsTo (fun z : ℍ => (generatorTwoSL ^ 3 : SL(2, ℝ)) • z) pingPongOne pingPongTwo := by
  intro z hz
  change ((generatorTwoSL ^ 3 : SL(2, ℝ)) • z).re < -1
  change -1 < z.re at hz
  rw [← UpperHalfPlane.coe_re, generatorTwoSL_cube_smul_coe]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.inv_re, Complex.add_re,
    Complex.one_re, UpperHalfPlane.coe_re]
  have hp : 0 < (z.re + 1) / Complex.normSq ((z : ℂ) + 1) :=
    div_pos (by linarith)
      (Complex.normSq_pos.mpr (by simpa using add_real_ne_zero_mo1973_15785 z 1))
  linarith [one_lt_width]

theorem SpecialPeriods.Triangle.generatorOnePerm_pow_apply (n : ℕ) (z : ℍ) :
    (generatorOnePerm ^ n) z = (generatorOneSL ^ n : SL(2, ℝ)) • z := by
  rw [generatorOnePerm, ← map_pow, realSLPermutation_apply]

theorem SpecialPeriods.Triangle.generatorTwoPerm_pow_apply (n : ℕ) (z : ℍ) :
    (generatorTwoPerm ^ n) z = (generatorTwoSL ^ n : SL(2, ℝ)) • z := by
  rw [generatorTwoPerm, ← map_pow, realSLPermutation_apply]

private theorem SpecialPeriods.cyclicPowerHom_natCast'_mo1973_15799 {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) (m : ℕ) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (m : ZMod n)) = a ^ m := by
  simpa only [Int.cast_natCast, zpow_natCast] using cyclicPowerHom_intCast n a ha (m : ℤ)

private theorem SpecialPeriods.cyclicPowerHom_two'_mo1973_15800 {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Nat.cast_ofNat] using cyclicPowerHom_natCast'_mo1973_15799 n a ha 2

private theorem SpecialPeriods.cyclicPowerHom_three'_mo1973_15801 {G : Type*} [Group G] (n : ℕ)
    (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Nat.cast_ofNat] using cyclicPowerHom_natCast'_mo1973_15799 n a ha 3

theorem SpecialPeriods.triangleLift_injective_of_pingPong {G α : Type*} [Group G] [MulAction G α]
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y : Set α) (hXY : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) (ha₁ : Set.MapsTo (fun z => a • z) Y X)
    (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X) (hb₁ : Set.MapsTo (fun z => b • z) X Y)
    (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y) (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) :
    Function.Injective (triangleLift a b ha hb) := by
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
  have htoI : Function.Injective toI := by
    apply Function.LeftInverse.injective (g := fromI)
    intro z
    exact DFunLike.congr_fun hleft z
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  rw [hrepresentation, MonoidHom.coe_comp]
  apply Function.Injective.comp _ htoI
  let U : Bool → Set α := fun i => cond i Y X
  apply Monoid.CoprodI.lift_injective_of_ping_pong f _ U
  · intro i
    cases i
    · exact hX
    · exact hY
  · intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hXY
    · exact hXY.symm
    · exact (hij rfl).elim
  · intro i j hij g hg
    cases i <;> cases j
    · exact (hij rfl).elim
    · change cyclicPowerHom 3 a ha g • Y ⊆ X
      have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 3),
                x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
            g hg
      rcases hc with rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₁ hz)
      · rw [cyclicPowerHom_two'_mo1973_15800 3 a ha]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₂ hz)
    · change cyclicPowerHom 4 b hb g • X ⊆ Y
      have hc :
        g = Multiplicative.ofAdd (1 : ZMod 4) ∨
          g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 4),
                x ≠ 1 →
                  x = Multiplicative.ofAdd 1 ∨
                    x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
            g hg
      rcases hc with rfl | rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₁ hz)
      · rw [cyclicPowerHom_two'_mo1973_15800 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₂ hz)
      · rw [cyclicPowerHom_three'_mo1973_15801 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₃ hz)
    · exact (hij rfl).elim
  · right
    refine ⟨Bool.false, ?_⟩
    change 3 ≤ Cardinal.mk (Multiplicative (ZMod 3))
    simp

theorem SpecialPeriods.triangleGeometricRepresentation_injective :
    Function.Injective triangleGeometricRepresentation := by
  apply
    triangleLift_injective_of_pingPong Triangle.generatorOnePerm Triangle.generatorTwoPerm
      Triangle.generatorOnePerm_cube Triangle.generatorTwoPerm_fourth Triangle.pingPongOne
      Triangle.pingPongTwo Triangle.pingPong_disjoint Triangle.pingPongOne_nonempty
      Triangle.pingPongTwo_nonempty
  · intro z hz
    exact Triangle.generatorOne_pingPong hz
  · intro z hz
    change (Triangle.generatorOnePerm ^ 2) z ∈ Triangle.pingPongOne
    rw [Triangle.generatorOnePerm_pow_apply]
    exact Triangle.generatorOne_sq_pingPong hz
  · intro z hz
    exact Triangle.generatorTwo_pingPong hz
  · intro z hz
    change (Triangle.generatorTwoPerm ^ 2) z ∈ Triangle.pingPongTwo
    rw [Triangle.generatorTwoPerm_pow_apply]
    exact Triangle.generatorTwo_sq_pingPong hz
  · intro z hz
    change (Triangle.generatorTwoPerm ^ 3) z ∈ Triangle.pingPongTwo
    rw [Triangle.generatorTwoPerm_pow_apply]
    exact Triangle.generatorTwo_cube_pingPong hz

private theorem SpecialPeriods.finiteTest_mixed_word_mo1973_15805 {G α : Type*} [Group G]
    [MulAction G α] {H : Bool → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (U : Bool → Set α)
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i)
    (hcard : 3 ≤ Cardinal.mk (H Bool.false)) (xB : α) (hxB : xB ∈ U Bool.true)
    (w : Monoid.CoprodI.NeWord H Bool.false Bool.true) :
    ∃ h : H Bool.false,
      (f Bool.false h * Monoid.CoprodI.lift f w.prod * (f Bool.false h)⁻¹) • xB ∈ U Bool.false := by
  obtain ⟨h, hn1, hnh⟩ := Cardinal.exists_ne_ne_of_three_le hcard 1 w.head⁻¹
  have hnot1 : h * w.head ≠ 1 := by
    rw [← div_inv_eq_mul]
    exact div_ne_one_of_ne hnh
  let w' : Monoid.CoprodI.NeWord H Bool.false Bool.false :=
    Monoid.CoprodI.NeWord.append (w.mulHead h hnot1) (by decide)
      (Monoid.CoprodI.NeWord.singleton h⁻¹ (inv_ne_one.mpr hn1))
  have hw' : Monoid.CoprodI.lift f w'.prod • xB ∈ U Bool.false :=
    Set.smul_set_subset_iff.mp (Monoid.CoprodI.lift_word_ping_pong f U hpp w' (by decide)) hxB
  refine ⟨h, ?_⟩
  simpa [w'] using hw'

private theorem SpecialPeriods.finiteTest_coprodI_mo1973_15806 {G α : Type*} [Group G]
    [MulAction G α] {H : Bool → Type*} [∀ i, Group (H i)] (f : ∀ i, H i →* G) (U : Bool → Set α)
    (hdisj : Disjoint (U Bool.false) (U Bool.true))
    (hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i)
    (hcard : 3 ≤ Cardinal.mk (H Bool.false)) (xA xB : α) (hxA : xA ∈ U Bool.false)
    (hxB : xB ∈ U Bool.true) (w : Monoid.CoprodI H)
    (hA : Monoid.CoprodI.lift f w • xA ∈ U Bool.false)
    (hB :
      ∀ h : H Bool.false,
        (f Bool.false h * Monoid.CoprodI.lift f w * (f Bool.false h)⁻¹) • xB ∈ U Bool.true ∧
          (f Bool.false h * (Monoid.CoprodI.lift f w)⁻¹ * (f Bool.false h)⁻¹) • xB ∈
            U Bool.true) :
    Monoid.CoprodI.lift f w = 1 := by
  classical
  let r := Monoid.CoprodI.Word.equiv (M := H) w
  have hr : r.prod = w := (Monoid.CoprodI.Word.equiv (M := H)).symm_apply_apply w
  by_cases hr0 : r = Monoid.CoprodI.Word.empty
  · have hw1 : w = 1 := by rw [← hr, hr0, Monoid.CoprodI.Word.prod_empty]
    simp [hw1]
  obtain ⟨i, j, v, hv⟩ := Monoid.CoprodI.NeWord.of_word r hr0
  have hvprod : v.prod = w := by
    change v.toWord.prod = w
    rw [hv]
    exact hr
  rw [← hvprod] at hA hB ⊢
  suffices False by contradiction
  cases i <;> cases j
  · have hm : Monoid.CoprodI.lift f v.prod • xB ∈ U Bool.false :=
      Set.smul_set_subset_iff.mp (Monoid.CoprodI.lift_word_ping_pong f U hpp v (by decide)) hxB
    have hn : Monoid.CoprodI.lift f v.prod • xB ∈ U Bool.true := by
      simpa only [map_one, one_mul, inv_one, mul_one] using (hB 1).1
    exact hdisj.le_bot ⟨hm, hn⟩
  · obtain ⟨h, hm⟩ := finiteTest_mixed_word_mo1973_15805 f U hpp hcard xB hxB v
    exact hdisj.le_bot ⟨hm, (hB h).1⟩
  · obtain ⟨h, hm⟩ := finiteTest_mixed_word_mo1973_15805 f U hpp hcard xB hxB v.inv
    have hm' :
      (f Bool.false h * (Monoid.CoprodI.lift f v.prod)⁻¹ * (f Bool.false h)⁻¹) • xB ∈
        U Bool.false := by simpa only [Monoid.CoprodI.NeWord.inv_prod, map_inv] using hm
    exact hdisj.le_bot ⟨hm', (hB h).2⟩
  · have hm : Monoid.CoprodI.lift f v.prod • xA ∈ U Bool.true :=
      Set.smul_set_subset_iff.mp (Monoid.CoprodI.lift_word_ping_pong f U hpp v (by decide)) hxA
    exact hdisj.le_bot ⟨hA, hm⟩

private theorem SpecialPeriods.finiteTest_cyclicPowerHom_two_mo1973_15807 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (2 : ZMod n)) = a ^ 2 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (2 : ℤ)

private theorem SpecialPeriods.finiteTest_cyclicPowerHom_three_mo1973_15808 {G : Type*} [Group G]
    (n : ℕ) (a : G) (ha : a ^ n = 1) :
    cyclicPowerHom n a ha (Multiplicative.ofAdd (3 : ZMod n)) = a ^ 3 := by
  simpa only [Int.cast_ofNat, zpow_ofNat] using cyclicPowerHom_intCast n a ha (3 : ℤ)

theorem SpecialPeriods.triangleLift_eq_one_of_pingPong_finite_tests {G α : Type*} [Group G]
    [MulAction G α] (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 4 = 1) (X Y : Set α) (hXY : Disjoint X Y)
    (ha₁ : Set.MapsTo (fun z => a • z) Y X) (ha₂ : Set.MapsTo (fun z => a ^ 2 • z) Y X)
    (hb₁ : Set.MapsTo (fun z => b • z) X Y) (hb₂ : Set.MapsTo (fun z => b ^ 2 • z) X Y)
    (hb₃ : Set.MapsTo (fun z => b ^ 3 • z) X Y) (xA xB : α) (hxA : xA ∈ X) (hxB : xB ∈ Y)
    (w : TriangleGroup) (hA : triangleLift a b ha hb w • xA ∈ X)
    (hB :
      ∀ h : Multiplicative (ZMod 3),
        (cyclicPowerHom 3 a ha h * triangleLift a b ha hb w * (cyclicPowerHom 3 a ha h)⁻¹) • xB ∈
            Y ∧
          (cyclicPowerHom 3 a ha h * (triangleLift a b ha hb w)⁻¹ * (cyclicPowerHom 3 a ha h)⁻¹) •
              xB ∈
            Y) :
    triangleLift a b ha hb w = 1 := by
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
  have hrepresentation : triangleLift a b ha hb = (Monoid.CoprodI.lift f).comp toI := by
    apply triangle_hom_ext
    · simp only [triangleLift_generator₁, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 3 a ha).symm
    · simp only [triangleLift_generator₂, MonoidHom.coe_comp, Function.comp_apply]
      exact (cyclicPowerHom_one 4 b hb).symm
  let U : Bool → Set α := fun i => cond i Y X
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • U j ⊆ U i := by
    intro i j hij g hg
    cases i <;> cases j
    · exact (hij rfl).elim
    · change cyclicPowerHom 3 a ha g • Y ⊆ X
      have hc : g = Multiplicative.ofAdd (1 : ZMod 3) ∨ g = Multiplicative.ofAdd (2 : ZMod 3) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 3),
                x ≠ 1 → x = Multiplicative.ofAdd 1 ∨ x = Multiplicative.ofAdd 2)
            g hg
      rcases hc with rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₁ hz)
      · rw [finiteTest_cyclicPowerHom_two_mo1973_15807 3 a ha]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => ha₂ hz)
    · change cyclicPowerHom 4 b hb g • X ⊆ Y
      have hc :
        g = Multiplicative.ofAdd (1 : ZMod 4) ∨
          g = Multiplicative.ofAdd (2 : ZMod 4) ∨ g = Multiplicative.ofAdd (3 : ZMod 4) := by
        exact
          (by decide :
              ∀ x : Multiplicative (ZMod 4),
                x ≠ 1 →
                  x = Multiplicative.ofAdd 1 ∨
                    x = Multiplicative.ofAdd 2 ∨ x = Multiplicative.ofAdd 3)
            g hg
      rcases hc with rfl | rfl | rfl
      · rw [cyclicPowerHom_one]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₁ hz)
      · rw [finiteTest_cyclicPowerHom_two_mo1973_15807 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₂ hz)
      · rw [finiteTest_cyclicPowerHom_three_mo1973_15808 4 b hb]
        exact Set.smul_set_subset_iff.mpr (fun _ hz => hb₃ hz)
    · exact (hij rfl).elim
  have hcard : 3 ≤ Cardinal.mk (H Bool.false) := by
    change 3 ≤ Cardinal.mk (Multiplicative (ZMod 3))
    simp
  have heval : triangleLift a b ha hb w = Monoid.CoprodI.lift f (toI w) :=
    DFunLike.congr_fun hrepresentation w
  rw [heval] at hA hB ⊢
  exact finiteTest_coprodI_mo1973_15806 f U hXY hpp hcard xA xB hxA hxB (toI w) hA hB

def SpecialPeriods.Triangle.matrixGroup : Subgroup (SL(2, ℝ)) :=
  Subgroup.closure ({ generatorOneSL, generatorTwoSL } : Set (SL(2, ℝ)))

theorem SpecialPeriods.Triangle.generatorOneSL_mem_matrixGroup : generatorOneSL ∈ matrixGroup :=
  Subgroup.subset_closure (by simp)

theorem SpecialPeriods.Triangle.generatorTwoSL_mem_matrixGroup : generatorTwoSL ∈ matrixGroup :=
  Subgroup.subset_closure (by simp)

theorem SpecialPeriods.Triangle.cuspSL_mem_matrixGroup : cuspSL ∈ matrixGroup := by
  have h :=
    matrixGroup.inv_mem
      (matrixGroup.mul_mem generatorOneSL_mem_matrixGroup generatorTwoSL_mem_matrixGroup)
  simpa only [generatorOneSL_mul_generatorTwoSL, cuspSL] using h

theorem SpecialPeriods.Triangle.neg_one_mem_matrixGroup : (-1 : SL(2, ℝ)) ∈ matrixGroup := by
  have h := matrixGroup.pow_mem generatorOneSL_mem_matrixGroup 3
  simpa only [generatorOneSL_cube] using h

theorem SpecialPeriods.Triangle.matrixGroup_map_realSLPermutation :
    matrixGroup.map realSLPermutation = SpecialPeriods.triangleGeometricRepresentation.range := by
  rw [matrixGroup, MonoidHom.map_closure, Set.image_pair, SpecialPeriods.triangle_range]
  simp only [SpecialPeriods.triangleGeometricRepresentation_generator₁,
    SpecialPeriods.triangleGeometricRepresentation_generator₂, generatorOnePerm, generatorTwoPerm]

theorem SpecialPeriods.Triangle.matrixGroup_permutation_lift (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) :
    ∃ w : SpecialPeriods.TriangleGroup,
      SpecialPeriods.triangleGeometricRepresentation w = realSLPermutation A := by
  have hm : realSLPermutation A ∈ matrixGroup.map realSLPermutation := ⟨A, hA, rfl⟩
  rw [matrixGroup_map_realSLPermutation] at hm
  exact hm

theorem SpecialPeriods.Triangle.triangleGeometricRepresentation_matrixGroup_lift
    (w : SpecialPeriods.TriangleGroup) :
    ∃ A : matrixGroup, realSLPermutation A = SpecialPeriods.triangleGeometricRepresentation w := by
  have hm :
    SpecialPeriods.triangleGeometricRepresentation w ∈
      SpecialPeriods.triangleGeometricRepresentation.range :=
    ⟨w, rfl⟩
  rw [← matrixGroup_map_realSLPermutation] at hm
  obtain ⟨A, hA, hA'⟩ := hm
  exact ⟨⟨A, hA⟩, hA'⟩

theorem SpecialPeriods.Triangle.realSLPermutation_eq_one_iff (A : SL(2, ℝ)) :
    realSLPermutation A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    have hfix : ∀ z : ℍ, Matrix.SpecialLinearGroup.mapGL ℝ A • z = z := by
      intro z
      change realSLPermutation A z = z
      rw [h]
      rfl
    have hc := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp hfix
    obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
    change Matrix.scalar (Fin 2) r = (A : Matrix (Fin 2) (Fin 2) ℝ) at hr
    have hs : r ^ 2 = 1 := by
      simpa [Matrix.scalar_apply, Matrix.det_diagonal] using congrArg Matrix.det hr
    rcases sq_eq_one_iff.mp hs with h₁ | hneg
    · left
      apply Subtype.ext
      simpa [h₁] using hr.symm
    · right
      apply Subtype.ext
      simpa only [hneg, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] using hr.symm
  · rintro (rfl | rfl)
    · exact map_one realSLPermutation
    · exact realSLPermutation_neg_one

def SpecialPeriods.Triangle.testPointOne : ℍ :=
  UpperHalfPlane.I

def SpecialPeriods.Triangle.testPointTwo : ℍ :=
  ⟨(-2 : ℂ) + Complex.I, by norm_num⟩

theorem SpecialPeriods.Triangle.testPointOne_mem : testPointOne ∈ pingPongOne := by
  norm_num [testPointOne, pingPongOne]

theorem SpecialPeriods.Triangle.testPointTwo_mem : testPointTwo ∈ pingPongTwo := by
  norm_num [testPointTwo, pingPongTwo]

theorem SpecialPeriods.Triangle.pingPongOne_isOpen : IsOpen pingPongOne :=
  isOpen_lt continuous_const UpperHalfPlane.continuous_re

theorem SpecialPeriods.Triangle.pingPongTwo_isOpen : IsOpen pingPongTwo :=
  isOpen_lt UpperHalfPlane.continuous_re continuous_const

def SpecialPeriods.Triangle.cyclicConjugator (h : Multiplicative (ZMod 3)) : SL(2, ℝ) :=
  generatorOneSL ^ h.toAdd.val

theorem SpecialPeriods.Triangle.cyclicConjugator_permutation (h : Multiplicative (ZMod 3)) :
    realSLPermutation (cyclicConjugator h) =
      SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h := by
  rw [cyclicConjugator, map_pow]
  change generatorOnePerm ^ h.toAdd.val = _
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd, zpow_natCast] using
    (SpecialPeriods.cyclicPowerHom_intCast 3 generatorOnePerm generatorOnePerm_cube
        (h.toAdd.val : ℤ)).symm

def SpecialPeriods.Triangle.identityTestSet : Set (SL(2, ℝ)) :=
  {A |
    0 < A 0 0 ∧
      A • testPointOne ∈ pingPongOne ∧
        ∀ h : Multiplicative (ZMod 3),
          (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo ∧
            (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo}

theorem SpecialPeriods.Triangle.identityTestSet_isOpen : IsOpen identityTestSet := by
  have he : IsOpen {A : SL(2, ℝ) | 0 < A 0 0} := isOpen_lt continuous_const (by fun_prop)
  have h₁ : IsOpen {A : SL(2, ℝ) | A • testPointOne ∈ pingPongOne} :=
    pingPongOne_isOpen.preimage (by fun_prop)
  have h₂ (h : Multiplicative (ZMod 3)) :
    IsOpen
      {A : SL(2, ℝ) |
        (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo ∧
          (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) • testPointTwo ∈ pingPongTwo} :=
    (pingPongTwo_isOpen.preimage (by fun_prop)).inter (pingPongTwo_isOpen.preimage (by fun_prop))
  simpa only [identityTestSet, Set.ofPred_and, Set.ofPred_forall] using
    he.inter (h₁.inter (isOpen_iInter_of_finite h₂))

theorem SpecialPeriods.Triangle.one_mem_identityTestSet : (1 : SL(2, ℝ)) ∈ identityTestSet := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  · simpa using testPointOne_mem
  · intro h
    simpa using And.intro testPointTwo_mem testPointTwo_mem

theorem SpecialPeriods.Triangle.realSLPermutation_eq_one_of_mem_identityTestSet {A : SL(2, ℝ)}
    (hA : A ∈ matrixGroup) (hT : A ∈ identityTestSet) : realSLPermutation A = 1 := by
  obtain ⟨w, hw⟩ := matrixGroup_permutation_lift A hA
  rw [← hw]
  refine
    SpecialPeriods.triangleLift_eq_one_of_pingPong_finite_tests generatorOnePerm generatorTwoPerm
      generatorOnePerm_cube generatorTwoPerm_fourth pingPongOne pingPongTwo pingPong_disjoint ?_
      ?_ ?_ ?_ ?_ testPointOne testPointTwo testPointOne_mem testPointTwo_mem w ?_ ?_
  · intro z hz
    exact generatorOne_pingPong hz
  · intro z hz
    change (generatorOnePerm ^ 2) z ∈ pingPongOne
    rw [generatorOnePerm_pow_apply]
    exact generatorOne_sq_pingPong hz
  · intro z hz
    exact generatorTwo_pingPong hz
  · intro z hz
    change (generatorTwoPerm ^ 2) z ∈ pingPongTwo
    rw [generatorTwoPerm_pow_apply]
    exact generatorTwo_sq_pingPong hz
  · intro z hz
    change (generatorTwoPerm ^ 3) z ∈ pingPongTwo
    rw [generatorTwoPerm_pow_apply]
    exact generatorTwo_cube_pingPong hz
  · change SpecialPeriods.triangleGeometricRepresentation w testPointOne ∈ pingPongOne
    rw [hw]
    exact hT.2.1
  · intro h
    change
      (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h *
                SpecialPeriods.triangleGeometricRepresentation w *
              (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h)⁻¹)
            testPointTwo ∈
          pingPongTwo ∧
        (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h *
                (SpecialPeriods.triangleGeometricRepresentation w)⁻¹ *
              (SpecialPeriods.cyclicPowerHom 3 generatorOnePerm generatorOnePerm_cube h)⁻¹)
            testPointTwo ∈
          pingPongTwo
    rw [hw, ← cyclicConjugator_permutation]
    have ht := hT.2.2 h
    change
      realSLPermutation (cyclicConjugator h * A * (cyclicConjugator h)⁻¹) testPointTwo ∈
          pingPongTwo ∧
        realSLPermutation (cyclicConjugator h * A⁻¹ * (cyclicConjugator h)⁻¹) testPointTwo ∈
          pingPongTwo at ht
    simpa only [map_mul, map_inv] using ht

theorem SpecialPeriods.Triangle.eq_one_of_mem_identityTestSet {A : SL(2, ℝ)}
    (hA : A ∈ matrixGroup) (hT : A ∈ identityTestSet) : A = 1 := by
  rcases
    (realSLPermutation_eq_one_iff A).mp
      (realSLPermutation_eq_one_of_mem_identityTestSet hA hT) with
    h | h
  · exact h
  · have hp := hT.1
    subst A
    norm_num [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply] at hp

theorem SpecialPeriods.Triangle.identityTestSet_preimage_matrixGroup :
    (fun A : matrixGroup => (A : SL(2, ℝ))) ⁻¹' identityTestSet = { 1 } := by
  ext A
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (Subtype.ext (eq_one_of_mem_identityTestSet A.property h))
  · rintro rfl
    exact one_mem_identityTestSet

instance SpecialPeriods.Triangle.matrixGroup_discrete : DiscreteTopology matrixGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  rw [← identityTestSet_preimage_matrixGroup]
  exact identityTestSet_isOpen.preimage continuous_subtype_val

theorem SpecialPeriods.Triangle.matrixGroup_isClosed : IsClosed (matrixGroup : Set (SL(2, ℝ))) :=
  Subgroup.isClosed_of_discrete

instance SpecialPeriods.Triangle.matrixGroup_properlyDiscontinuous :
    ProperlyDiscontinuousSMul matrixGroup ℍ :=
  inferInstance

instance SpecialPeriods.Triangle.matrixGroup_properSMul : ProperSMul matrixGroup ℍ := by
  have : IsClosed (matrixGroup : Set (SL(2, ℝ))) := matrixGroup_isClosed
  infer_instance

theorem SpecialPeriods.Triangle.matrixGroup_isCompact_transporter {K L : Set ℍ} (hK : IsCompact K)
    (hL : IsCompact L) : IsCompact {g : matrixGroup | (g • K ∩ L).Nonempty} :=
  ProperSMul.isCompact_setOfPred_inter_nonempty hK hL

theorem SpecialPeriods.Triangle.matrixGroup_finite_compact_transporter {K L : Set ℍ}
    (hK : IsCompact K) (hL : IsCompact L) : {g : matrixGroup | (g • K ∩ L).Nonempty}.Finite :=
  isCompact_iff_finite.mp (matrixGroup_isCompact_transporter hK hL)

theorem SpecialPeriods.Triangle.matrixGroup_exists_fordRegion_representative (z : ℍ) :
    ∃ g : matrixGroup, g • z ∈ fordRegion :=
  subgroup_exists_fordRegion_representative matrixGroup generatorOneSL_mem_matrixGroup
    cuspSL_mem_matrixGroup z

theorem SpecialPeriods.triangle_exists_fordRegion_representative (z : ℍ) :
    ∃ g : TriangleGroup, triangleGeometricRepresentation g z ∈ Triangle.fordRegion := by
  obtain ⟨A, hA⟩ := Triangle.matrixGroup_exists_fordRegion_representative z
  obtain ⟨g, hg⟩ := Triangle.matrixGroup_permutation_lift A A.property
  refine ⟨g, ?_⟩
  rw [hg]
  exact hA

theorem SpecialPeriods.triangle_exists_fordRegion_preimage (z : ℍ) :
    ∃ w ∈ Triangle.fordRegion, ∃ g : TriangleGroup, triangleGeometricRepresentation g w = z := by
  obtain ⟨g, hg⟩ := triangle_exists_fordRegion_representative z
  refine ⟨triangleGeometricRepresentation g z, hg, g⁻¹, ?_⟩
  rw [map_inv]
  exact (triangleGeometricRepresentation g).symm_apply_apply z

theorem SpecialPeriods.triangle_translates_fordRegion_cover :
    (⋃ g : TriangleGroup, (triangleGeometricRepresentation g) '' Triangle.fordRegion) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨w, hw, g, hg⟩ := triangle_exists_fordRegion_preimage z
  exact Set.mem_iUnion.mpr ⟨g, w, hw, hg⟩

def SpecialPeriods.Triangle.shimizuTranslation (w : ℝ) : SL(2, ℝ) :=
  ⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
theorem SpecialPeriods.Triangle.coe_shimizuTranslation (w : ℝ) :
    (shimizuTranslation w : Matrix (Fin 2) (Fin 2) ℝ) = !![1, w; 0, 1] :=
  rfl

theorem SpecialPeriods.Triangle.shimizuTranslation_width :
    shimizuTranslation width = cuspInverseSL :=
  rfl

theorem SpecialPeriods.Triangle.shimizu_conjugate_matrix (w : ℝ) (A : SL(2, ℝ)) :
    ((A * shimizuTranslation w * A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - w * A 0 0 * A 1 0, w * (A 0 0) ^ 2; -w * (A 1 0) ^ 2, 1 + w * A 0 0 * A 1 0] := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    (Matrix.det_fin_two A.val).symm.trans A.property
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_shimizuTranslation, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hdet]

def SpecialPeriods.Triangle.shimizuSequence (w : ℝ) (A : SL(2, ℝ)) : ℕ → SL(2, ℝ)
  | 0 => A
  | n + 1 => shimizuSequence w A n * shimizuTranslation w * (shimizuSequence w A n)⁻¹

theorem SpecialPeriods.Triangle.shimizuSequence_mem (Γ : Subgroup (SL(2, ℝ))) (w : ℝ)
    (A : SL(2, ℝ)) (hT : shimizuTranslation w ∈ Γ) (hA : A ∈ Γ) (n : ℕ) :
    shimizuSequence w A n ∈ Γ := by
  induction n with
  | zero => exact hA
  | succ n ih => exact Γ.mul_mem (Γ.mul_mem ih hT) (Γ.inv_mem ih)

theorem SpecialPeriods.Triangle.shimizuSequence_succ_matrix (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    (shimizuSequence w A (n + 1) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 - w * shimizuSequence w A n 0 0 * shimizuSequence w A n 1 0,
          w * (shimizuSequence w A n 0 0) ^ 2;
        -w * (shimizuSequence w A n 1 0) ^ 2,
          1 + w * shimizuSequence w A n 0 0 * shimizuSequence w A n 1 0] :=
  shimizu_conjugate_matrix w (shimizuSequence w A n)

theorem SpecialPeriods.Triangle.shimizuSequence_succ_zero_zero (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 0 0 =
      1 - shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0) := by
  have h :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) (shimizuSequence_succ_matrix w A n)
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, mul_left_comm, mul_assoc] using h

theorem SpecialPeriods.Triangle.shimizuSequence_succ_zero_one (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 0 1 = w * (shimizuSequence w A n 0 0) ^ 2 := by
  simpa using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) (shimizuSequence_succ_matrix w A n)

theorem SpecialPeriods.Triangle.shimizuSequence_succ_one_zero (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 1 0 = -w * (shimizuSequence w A n 1 0) ^ 2 := by
  simpa using
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) (shimizuSequence_succ_matrix w A n)

theorem SpecialPeriods.Triangle.shimizuSequence_succ_one_one (w : ℝ) (A : SL(2, ℝ)) (n : ℕ) :
    shimizuSequence w A (n + 1) 1 1 =
      1 + shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0) := by
  have h :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) (shimizuSequence_succ_matrix w A n)
  simpa only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, mul_left_comm,
    mul_assoc] using h

theorem SpecialPeriods.Triangle.shimizuSequence_succ_scaled_lower_left (w : ℝ) (A : SL(2, ℝ))
    (n : ℕ) : w * shimizuSequence w A (n + 1) 1 0 = -(w * shimizuSequence w A n 1 0) ^ 2 := by
  rw [shimizuSequence_succ_one_zero]
  ring

theorem SpecialPeriods.Triangle.shimizuSequence_lower_left_ne_zero (w : ℝ) (A : SL(2, ℝ))
    (hw : w ≠ 0) (hA : A 1 0 ≠ 0) (n : ℕ) : shimizuSequence w A n 1 0 ≠ 0 := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    rw [shimizuSequence_succ_one_zero]
    exact mul_ne_zero (neg_ne_zero.mpr hw) (pow_ne_zero 2 ih)

theorem SpecialPeriods.Triangle.shimizu_recurrence_abs_le_initial (q : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (hsmall : |q 0| ≤ 1) (n : ℕ) : |q n| ≤ |q 0| := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [hq, abs_neg, abs_pow, pow_two]
    calc
      |q n| * |q n| ≤ |q 0| * |q 0| := mul_le_mul ih ih (abs_nonneg _) (abs_nonneg _)
      _ ≤ |q 0| := by nlinarith [abs_nonneg (q 0)]

theorem SpecialPeriods.Triangle.shimizu_recurrence_geometric_bound (q : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (hsmall : |q 0| ≤ 1) (n : ℕ) : |q n| ≤ |q 0| ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hq, abs_neg, abs_pow, pow_two]
    calc
      |q n| * |q n| ≤ |q 0| * |q 0| ^ (n + 1) :=
        mul_le_mul (shimizu_recurrence_abs_le_initial q hq hsmall n) ih (abs_nonneg _)
          (abs_nonneg _)
      _ = |q 0| ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem SpecialPeriods.Triangle.shimizu_recurrence_a_bound (q a : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (ha : ∀ n, a (n + 1) = 1 - a n * q n) (hsmall : |q 0| < 1)
    (n : ℕ) : |a n| ≤ (1 + |a 0|) / (1 - |q 0|) := by
  let M : ℝ := (1 + |a 0|) / (1 - |q 0|)
  have hd : 0 < 1 - |q 0| := sub_pos.mpr hsmall
  have hM : 0 ≤ M := div_nonneg (by positivity) hd.le
  have hM_eq : M * (1 - |q 0|) = 1 + |a 0| := div_mul_cancel₀ _ hd.ne'
  have hM_step : 1 + M * |q 0| ≤ M := by nlinarith [abs_nonneg (a 0)]
  change |a n| ≤ M
  induction n with
  | zero =>
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (q 0))]
  | succ n ih =>
    rw [ha]
    calc
      |1 - a n * q n| ≤ |(1 : ℝ)| + |a n * q n| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (a n * q n)
      _ = 1 + |a n| * |q n| := by rw [abs_one, abs_mul]
      _ ≤ 1 + M * |q 0| :=
        (add_le_add (le_refl 1)
          (mul_le_mul ih (shimizu_recurrence_abs_le_initial q hq hsmall.le n) (abs_nonneg _) hM))
      _ ≤ M := hM_step

theorem SpecialPeriods.Triangle.shimizu_recurrence_tendsto (q a : ℕ → ℝ)
    (hq : ∀ n, q (n + 1) = -(q n) ^ 2) (ha : ∀ n, a (n + 1) = 1 - a n * q n)
    (hsmall : |q 0| < 1) :
    Filter.Tendsto q Filter.atTop (𝓝 0) ∧ Filter.Tendsto a Filter.atTop (𝓝 1) := by
  have hpow : Filter.Tendsto (fun n : ℕ => |q 0| ^ (n + 1)) Filter.atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hsmall).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hqt : Filter.Tendsto q Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (f := q) (fun n => ?_) hpow
    exact shimizu_recurrence_geometric_bound q hq hsmall.le n
  let M : ℝ := (1 + |a 0|) / (1 - |q 0|)
  have hM : 0 ≤ M := div_nonneg (by positivity) (sub_pos.mpr hsmall).le
  have hprod : Filter.Tendsto (fun n => a n * q n) Filter.atTop (𝓝 0) := by
    refine
      squeeze_zero_norm (f := fun n : ℕ => a n * q n) (a := fun n => M * |q 0| ^ (n + 1)) ?_ ?_
    · intro n
      rw [Real.norm_eq_abs, abs_mul]
      exact
        mul_le_mul (shimizu_recurrence_a_bound q a hq ha hsmall n)
          (shimizu_recurrence_geometric_bound q hq hsmall.le n) (abs_nonneg _) hM
    · simpa only [MulZeroClass.mul_zero] using hpow.const_mul M
  refine ⟨hqt, (Filter.tendsto_add_atTop_iff_nat 1).mp ?_⟩
  simpa only [ha, sub_zero] using hprod.const_sub 1

theorem SpecialPeriods.Triangle.shimizuSequence_tendsto_translation (w : ℝ) (A : SL(2, ℝ))
    (hw : w ≠ 0) (hsmall : |w * A 1 0| < 1) :
    Filter.Tendsto (shimizuSequence w A) Filter.atTop (𝓝 (shimizuTranslation w)) := by
  obtain ⟨hq, ha⟩ :=
    shimizu_recurrence_tendsto (fun n => w * shimizuSequence w A n 1 0)
      (fun n => shimizuSequence w A n 0 0) (shimizuSequence_succ_scaled_lower_left w A)
      (shimizuSequence_succ_zero_zero w A) hsmall
  have hc : Filter.Tendsto (fun n => shimizuSequence w A n 1 0) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [hw] using hq.div_const w
  have hp :
    Filter.Tendsto (fun n => shimizuSequence w A n 0 0 * (w * shimizuSequence w A n 1 0))
      Filter.atTop (𝓝 (0 : ℝ)) := by simpa only [one_mul] using ha.mul hq
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change Filter.Tendsto (fun n => shimizuSequence w A n 0 0) Filter.atTop (𝓝 (1 : ℝ))
    exact ha
  · change Filter.Tendsto (fun n => shimizuSequence w A n 0 1) Filter.atTop (𝓝 w)
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    simpa only [shimizuSequence_succ_zero_one, one_pow, mul_one] using (ha.pow 2).const_mul w
  · change Filter.Tendsto (fun n => shimizuSequence w A n 1 0) Filter.atTop (𝓝 (0 : ℝ))
    exact hc
  · change Filter.Tendsto (fun n => shimizuSequence w A n 1 1) Filter.atTop (𝓝 (1 : ℝ))
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    simpa only [shimizuSequence_succ_one_one, add_zero] using hp.const_add 1

theorem SpecialPeriods.Triangle.shimizu_leutbecher_scaled (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] (w : ℝ) (hw : w ≠ 0) (hT : shimizuTranslation w ∈ Γ) (A : SL(2, ℝ))
    (hA : A ∈ Γ) (hc : A 1 0 ≠ 0) : 1 ≤ |w * A 1 0| := by
  by_contra! hsmall
  let u : ℕ → Γ := fun n => ⟨shimizuSequence w A n, shimizuSequence_mem Γ w A hT hA n⟩
  let t : Γ := ⟨shimizuTranslation w, hT⟩
  have ht : Filter.Tendsto u Filter.atTop (𝓝 t) :=
    tendsto_subtype_rng.mpr (shimizuSequence_tendsto_translation w A hw hsmall)
  have he : ∀ᶠ n in Filter.atTop, u n = t := by
    simpa only [nhds_discrete, Filter.tendsto_pure] using ht
  obtain ⟨n, hn⟩ := he.exists
  have hzero : shimizuSequence w A n 1 0 = 0 := by
    have h := congrArg (fun B : Γ => (B : SL(2, ℝ)) 1 0) hn
    simpa [u, t, shimizuTranslation] using h
  exact shimizuSequence_lower_left_ne_zero w A hw hc n hzero

theorem SpecialPeriods.Triangle.shimizu_leutbecher (Γ : Subgroup (SL(2, ℝ))) [DiscreteTopology Γ]
    (w : ℝ) (hw : 0 < w) (hT : shimizuTranslation w ∈ Γ) (A : SL(2, ℝ)) (hA : A ∈ Γ)
    (hc : A 1 0 ≠ 0) : 1 / w ≤ |A 1 0| := by
  apply (div_le_iff₀ hw).mpr
  simpa only [abs_mul, abs_of_pos hw, mul_comm] using
    shimizu_leutbecher_scaled Γ w hw.ne' hT A hA hc

theorem SpecialPeriods.Triangle.matrixGroup_lower_left_bound (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hc : A 1 0 ≠ 0) : 1 / width ≤ |A 1 0| := by
  apply shimizu_leutbecher matrixGroup width width_pos ?_ A hA hc
  rw [shimizuTranslation_width, ← generatorOneSL_mul_generatorTwoSL]
  exact matrixGroup.mul_mem generatorOneSL_mem_matrixGroup generatorTwoSL_mem_matrixGroup

def SpecialPeriods.modularProjectivization : SL(2, ℤ) →* PSL(2, ℤ) :=
  QuotientGroup.mk' (Subgroup.center (SL(2, ℤ)))

private theorem SpecialPeriods.modular_neg_one_mem_center_mo1973_15869 :
    (-1 : SL(2, ℤ)) ∈ Subgroup.center (SL(2, ℤ)) := by
  apply Subgroup.mem_center_iff.mpr
  intro A
  apply Subtype.ext
  change (A : Matrix (Fin 2) (Fin 2) ℤ) * (-1) = (-1) * A
  simp

@[simp]
theorem SpecialPeriods.modularProjectivization_neg_one : modularProjectivization (-1) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr modular_neg_one_mem_center_mo1973_15869

@[simp]
theorem SpecialPeriods.modularProjectivization_neg (A : SL(2, ℤ)) :
    modularProjectivization (-A) = modularProjectivization A := by
  have hn : (-1 : SL(2, ℤ)) * A = -A := by
    apply Subtype.ext
    change (-1 : Matrix (Fin 2) (Fin 2) ℤ) * A = -(A : Matrix (Fin 2) (Fin 2) ℤ)
    simp
  rw [← hn, map_mul, modularProjectivization_neg_one, one_mul]

def SpecialPeriods.triangleModularA : SL(2, ℤ) :=
  ⟨!![1, -1; 1, 0], by decide⟩

theorem SpecialPeriods.triangleModularA_eq_T_mul_S :
    triangleModularA = ModularGroup.T * ModularGroup.S := by decide

theorem SpecialPeriods.triangleModularA_cube : triangleModularA ^ 3 = -1 := by decide

theorem SpecialPeriods.modularS_square : ModularGroup.S ^ 2 = -1 := by decide

theorem SpecialPeriods.triangleModularA_mul_S :
    triangleModularA * ModularGroup.S = -ModularGroup.T := by decide

def SpecialPeriods.triangleModularGenerator₁ : PSL(2, ℤ) :=
  modularProjectivization triangleModularA

def SpecialPeriods.triangleModularGenerator₂ : PSL(2, ℤ) :=
  modularProjectivization ModularGroup.S

@[simp]
theorem SpecialPeriods.triangleModularGenerator₁_cube : triangleModularGenerator₁ ^ 3 = 1 := by
  rw [triangleModularGenerator₁, ← map_pow, triangleModularA_cube,
    modularProjectivization_neg_one]

@[simp]
theorem SpecialPeriods.triangleModularGenerator₂_square : triangleModularGenerator₂ ^ 2 = 1 := by
  rw [triangleModularGenerator₂, ← map_pow, modularS_square, modularProjectivization_neg_one]

theorem SpecialPeriods.triangleModularGenerator₂_fourth : triangleModularGenerator₂ ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, triangleModularGenerator₂_square, one_pow]

theorem SpecialPeriods.triangleModularGenerator₁_mul_generator₂ :
    triangleModularGenerator₁ * triangleModularGenerator₂ =
      modularProjectivization ModularGroup.T := by
  rw [triangleModularGenerator₁, triangleModularGenerator₂, ← map_mul, triangleModularA_mul_S,
    modularProjectivization_neg]

def SpecialPeriods.triangleModularRepresentation : TriangleGroup →* PSL(2, ℤ) :=
  triangleLift triangleModularGenerator₁ triangleModularGenerator₂ triangleModularGenerator₁_cube
    triangleModularGenerator₂_fourth

@[simp]
theorem SpecialPeriods.triangleModularRepresentation_generator₁ :
    triangleModularRepresentation triangleGenerator₁ = triangleModularGenerator₁ :=
  triangleLift_generator₁ ..

@[simp]
theorem SpecialPeriods.triangleModularRepresentation_generator₂ :
    triangleModularRepresentation triangleGenerator₂ = triangleModularGenerator₂ :=
  triangleLift_generator₂ ..

@[simp]
theorem SpecialPeriods.triangleModularRepresentation_cusp :
    triangleModularRepresentation triangleCuspGenerator =
      modularProjectivization ModularGroup.T⁻¹ := by
  rw [triangleModularRepresentation, triangleLift_cusp, triangleModularGenerator₁_mul_generator₂,
    map_inv]

private theorem SpecialPeriods.modular_center_eq_one_or_neg_one_mo1973_15891 (A : SL(2, ℤ))
    (hA : A ∈ Subgroup.center (SL(2, ℤ))) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr₂ : r ^ 2 = 1 := by simpa using hr
  rcases sq_eq_one_iff.mp hr₂ with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hrA.symm
  · right
    apply Subtype.ext
    simpa using hrA.symm

private theorem SpecialPeriods.modular_center_le_permutation_kernel_mo1973_15892 :
    Subgroup.center (SL(2, ℤ)) ≤ (MulAction.toPermHom (SL(2, ℤ)) ℍ).ker := by
  intro A hA
  rcases modular_center_eq_one_or_neg_one_mo1973_15891 A hA with rfl | rfl
  · exact map_one _
  · apply Equiv.ext
    intro z
    change (-1 : SL(2, ℤ)) • z = z
    simp

def SpecialPeriods.modularPSLPermutation : PSL(2, ℤ) →* Equiv.Perm ℍ :=
  QuotientGroup.lift (Subgroup.center (SL(2, ℤ))) (MulAction.toPermHom (SL(2, ℤ)) ℍ)
    modular_center_le_permutation_kernel_mo1973_15892

@[simp]
theorem SpecialPeriods.modularPSLPermutation_projectivization (A : SL(2, ℤ)) (z : ℍ) :
    modularPSLPermutation (modularProjectivization A) z = A • z :=
  rfl

def SpecialPeriods.triangleModularAction : TriangleGroup →* Equiv.Perm ℍ :=
  modularPSLPermutation.comp triangleModularRepresentation

@[simp]
theorem SpecialPeriods.triangleModularAction_generator₁_apply (z : ℍ) :
    triangleModularAction triangleGenerator₁ z = triangleModularA • z := by
  simp [triangleModularAction, triangleModularGenerator₁]

@[simp]
theorem SpecialPeriods.triangleModularAction_generator₂_apply (z : ℍ) :
    triangleModularAction triangleGenerator₂ z = ModularGroup.S • z := by
  simp [triangleModularAction, triangleModularGenerator₂]

theorem SpecialPeriods.triangleModularAction_generator₁_coe (z : ℍ) :
    (triangleModularAction triangleGenerator₁ z : ℂ) = (z - 1) / z := by
  rw [triangleModularAction_generator₁_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [triangleModularA, sub_eq_add_neg]

theorem SpecialPeriods.triangleModularAction_generator₂_coe (z : ℍ) :
    (triangleModularAction triangleGenerator₂ z : ℂ) = -1 / z := by
  rw [triangleModularAction_generator₂_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [ModularGroup.S]

@[simp]
theorem SpecialPeriods.triangleModularAction_cusp_apply (z : ℍ) :
    triangleModularAction triangleCuspGenerator z = (-1 : ℝ) +ᵥ z := by
  change modularPSLPermutation (triangleModularRepresentation triangleCuspGenerator) z = _
  rw [triangleModularRepresentation_cusp, modularPSLPermutation_projectivization]
  simpa using UpperHalfPlane.modular_T_zpow_smul z (-1)

theorem SpecialPeriods.triangleModularAction_cusp_coe (z : ℍ) :
    (triangleModularAction triangleCuspGenerator z : ℂ) = z - 1 := by
  simp [sub_eq_add_neg, add_comm]

theorem SpecialPeriods.neg_triangleModularA_cube : (-triangleModularA) ^ 3 = 1 := by decide

theorem SpecialPeriods.modularS_fourth : ModularGroup.S ^ 4 = 1 := by decide

theorem SpecialPeriods.neg_triangleModularA_mul_S :
    (-triangleModularA) * ModularGroup.S = ModularGroup.T := by decide

def SpecialPeriods.triangleModularLinearRepresentation : TriangleGroup →* SL(2, ℤ) :=
  triangleLift (-triangleModularA) ModularGroup.S neg_triangleModularA_cube modularS_fourth

@[simp]
theorem SpecialPeriods.triangleModularLinearRepresentation_cusp :
    triangleModularLinearRepresentation triangleCuspGenerator = ModularGroup.T⁻¹ := by
  rw [triangleModularLinearRepresentation, triangleLift_cusp, neg_triangleModularA_mul_S]

private theorem SpecialPeriods.equalDiagonalTriangular_pow_succ_mo1973_15916 {R : Type*}
    [CommSemiring R] (a b : R) (n : ℕ) :
    (!![a, b; 0, a] : Matrix (Fin 2) (Fin 2) R) ^ (n + 1) =
      !![a ^ (n + 1), ((n + 1 : ℕ) : R) * a ^ n * b; 0, a ^ (n + 1)] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Nat.cast_add, Nat.cast_one]
    all_goals ring

private theorem SpecialPeriods.integerTriangular_pow_upper_right_dvd_mo1973_15917 (a b : ℤ)
    (n : ℕ) : (n : ℤ) ∣ ((!![a, b; 0, a] : Matrix (Fin 2) (Fin 2) ℤ) ^ n) 0 1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [equalDiagonalTriangular_pow_succ_mo1973_15916]
    refine ⟨a ^ n * b, ?_⟩
    simp [mul_assoc]

private theorem SpecialPeriods.integerMatrix_commute_translation_entries_mo1973_15918
    (M : Matrix (Fin 2) (Fin 2) ℤ) (h : Commute M !![1, -1; 0, 1]) : M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  have h₀ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 0) h.eq
  have h₁ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 1) h.eq
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h₀ h₁
  constructor <;> linarith

theorem SpecialPeriods.integerMatrix_translationInverse_pow_exponent
    (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) (h : M ^ n = !![1, -1; 0, 1]) : n = 1 := by
  have hc : Commute M !![1, -1; 0, 1] := by
    rw [← h]
    exact Commute.self_pow M n
  obtain ⟨hc₀, hc₁⟩ := integerMatrix_commute_translation_entries_mo1973_15918 M hc
  have hM : M = !![M 0 0, M 0 1; 0, M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc₀, hc₁]
  have hd := integerTriangular_pow_upper_right_dvd_mo1973_15917 (M 0 0) (M 0 1) n
  rw [← hM, h] at hd
  apply Nat.eq_one_of_dvd_one
  simpa [Int.natCast_dvd] using hd

theorem SpecialPeriods.modular_T_inv_pow_exponent (M : SL(2, ℤ)) (n : ℕ)
    (h : M ^ n = ModularGroup.T⁻¹) : n = 1 := by
  apply integerMatrix_translationInverse_pow_exponent (M : Matrix (Fin 2) (Fin 2) ℤ) n
  simpa only [Matrix.SpecialLinearGroup.coe_pow, ModularGroup.coe_T_inv] using
    congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ)) h

theorem SpecialPeriods.triangleCuspGenerator_pow_root_exponent (g : TriangleGroup) (n : ℕ)
    (h : g ^ n = triangleCuspGenerator) : n = 1 := by
  apply modular_T_inv_pow_exponent (triangleModularLinearRepresentation g) n
  rw [← map_pow, h, triangleModularLinearRepresentation_cusp]

theorem SpecialPeriods.triangleCuspGenerator_zpow_root_exponent (g : TriangleGroup) (k : ℤ)
    (h : g ^ k = triangleCuspGenerator) : k.natAbs = 1 := by
  cases k with
  | ofNat n =>
    apply triangleCuspGenerator_pow_root_exponent g n
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h
  | negSucc n =>
    apply triangleCuspGenerator_pow_root_exponent g⁻¹ (n + 1)
    simpa only [zpow_negSucc, inv_pow] using h

@[simp]
theorem SpecialPeriods.Triangle.shimizuTranslation_zero : shimizuTranslation 0 = 1 := by
  apply Subtype.ext
  simp [coe_shimizuTranslation, Matrix.one_fin_two]

theorem SpecialPeriods.Triangle.shimizuTranslation_add (s t : ℝ) :
    shimizuTranslation (s + t) = shimizuTranslation s * shimizuTranslation t := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_shimizuTranslation, add_comm]

@[simp]
theorem SpecialPeriods.Triangle.shimizuTranslation_inv (t : ℝ) :
    (shimizuTranslation t)⁻¹ = shimizuTranslation (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← shimizuTranslation_add, add_neg_cancel, shimizuTranslation_zero]

def SpecialPeriods.Triangle.shimizuTranslationHom : Multiplicative ℝ →* SL(2, ℝ)
    where
  toFun t := shimizuTranslation t.toAdd
  map_one' := shimizuTranslation_zero
  map_mul' s t := shimizuTranslation_add s.toAdd t.toAdd

@[simp]
theorem SpecialPeriods.Triangle.shimizuTranslationHom_apply (t : ℝ) :
    shimizuTranslationHom (Multiplicative.ofAdd t) = shimizuTranslation t :=
  rfl

theorem SpecialPeriods.Triangle.shimizuTranslation_zpow (t : ℝ) (n : ℤ) :
    shimizuTranslation t ^ n = shimizuTranslation ((n : ℝ) * t) := by
  simpa only [← ofAdd_zsmul, shimizuTranslationHom_apply, zsmul_eq_mul] using
    (map_zpow shimizuTranslationHom (Multiplicative.ofAdd t) n).symm

theorem SpecialPeriods.Triangle.shimizuTranslation_injective :
    Function.Injective shimizuTranslation := by
  intro s t h
  have he := congrArg (fun A : SL(2, ℝ) => A 0 1) h
  simpa [shimizuTranslation] using he

theorem SpecialPeriods.Triangle.shimizuTranslation_continuous : Continuous shimizuTranslation := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  change Continuous (fun t : ℝ => (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
    | exact continuous_const
    | exact continuous_id

theorem SpecialPeriods.Triangle.shimizuTranslation_neg_width :
    shimizuTranslation (-width) = cuspSL := by
  rw [← shimizuTranslation_inv, shimizuTranslation_width]
  rfl

def SpecialPeriods.Triangle.translationSubgroup (Γ : Subgroup (SL(2, ℝ))) : AddSubgroup ℝ
    where
  carrier := {t | shimizuTranslation t ∈ Γ}
  zero_mem' := by
    change shimizuTranslation 0 ∈ Γ
    rw [shimizuTranslation_zero]
    exact Γ.one_mem
  add_mem' := by
    intro s t hs ht
    change shimizuTranslation (s + t) ∈ Γ
    rw [shimizuTranslation_add]
    exact Γ.mul_mem hs ht
  neg_mem' := by
    intro t ht
    change shimizuTranslation (-t) ∈ Γ
    rw [← shimizuTranslation_inv]
    exact Γ.inv_mem ht

def SpecialPeriods.Triangle.translationSubgroupMap (Γ : Subgroup (SL(2, ℝ))) :
    translationSubgroup Γ → Γ := fun t => ⟨shimizuTranslation t, t.property⟩

theorem SpecialPeriods.Triangle.translationSubgroupMap_injective (Γ : Subgroup (SL(2, ℝ))) :
    Function.Injective (translationSubgroupMap Γ) := by
  intro s t h
  apply Subtype.ext
  exact shimizuTranslation_injective (congrArg Subtype.val h)

theorem SpecialPeriods.Triangle.translationSubgroupMap_continuous (Γ : Subgroup (SL(2, ℝ))) :
    Continuous (translationSubgroupMap Γ) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  exact shimizuTranslation_continuous.comp continuous_subtype_val

instance SpecialPeriods.Triangle.translationSubgroup_discrete (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] : DiscreteTopology (translationSubgroup Γ) :=
  DiscreteTopology.of_continuous_injective (translationSubgroupMap_continuous Γ)
    (translationSubgroupMap_injective Γ)

theorem SpecialPeriods.Triangle.translationSubgroup_cyclic (Γ : Subgroup (SL(2, ℝ)))
    [DiscreteTopology Γ] : ∃ t : ℝ, translationSubgroup Γ = AddSubgroup.zmultiples t := by
  have hc : IsAddCyclic (translationSubgroup Γ) :=
    AddSubgroup.discrete_iff_addCyclic.mpr inferInstance
  obtain ⟨t, ht⟩ :=
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top (translationSubgroup Γ)).mp hc
  exact ⟨t, ht.symm⟩

theorem SpecialPeriods.Triangle.width_mem_translationSubgroup_matrixGroup :
    width ∈ translationSubgroup matrixGroup := by
  change shimizuTranslation width ∈ matrixGroup
  rw [shimizuTranslation_width, ← cuspSL_inv]
  exact matrixGroup.inv_mem cuspSL_mem_matrixGroup

theorem SpecialPeriods.Triangle.neg_width_mem_translationSubgroup_matrixGroup :
    -width ∈ translationSubgroup matrixGroup := by
  change shimizuTranslation (-width) ∈ matrixGroup
  rw [shimizuTranslation_neg_width]
  exact cuspSL_mem_matrixGroup

theorem SpecialPeriods.Triangle.upperTriangular_det (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 0 0 * A 1 1 = 1 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    (Matrix.det_fin_two A.val).symm.trans A.property
  simpa only [hc, MulZeroClass.mul_zero, sub_zero] using hdet

theorem SpecialPeriods.Triangle.upperTriangular_zero_zero_ne_zero (A : SL(2, ℝ))
    (hc : A 1 0 = 0) : A 0 0 ≠ 0 := by
  intro ha
  have h := upperTriangular_det A hc
  simp [ha] at h

theorem SpecialPeriods.Triangle.upperTriangular_one_one_ne_zero (A : SL(2, ℝ)) (hc : A 1 0 = 0) :
    A 1 1 ≠ 0 := by
  intro hd
  have h := upperTriangular_det A hc
  simp [hd] at h

theorem SpecialPeriods.Triangle.upperTriangular_conjugate_translation (A : SL(2, ℝ))
    (hc : A 1 0 = 0) (t : ℝ) :
    A * shimizuTranslation t * A⁻¹ = shimizuTranslation (t * (A 0 0) ^ 2) := by
  apply Subtype.ext
  rw [shimizu_conjugate_matrix, coe_shimizuTranslation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]

theorem SpecialPeriods.Triangle.upperTriangular_inverse_lower_left (A : SL(2, ℝ))
    (hc : A 1 0 = 0) : (A⁻¹ : SL(2, ℝ)) 1 0 = 0 := by
  change (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = 0
  simp [Matrix.adjugate_fin_two, hc]

theorem SpecialPeriods.Triangle.inverse_upper_left (A : SL(2, ℝ)) :
    (A⁻¹ : SL(2, ℝ)) 0 0 = A 1 1 := by
  change (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = A 1 1
  simp [Matrix.adjugate_fin_two]

private theorem SpecialPeriods.Triangle.neg_one_mul_realSL_mo1973_15956 (A : SL(2, ℝ)) :
    (-1 : SL(2, ℝ)) * A = -A := by
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) ℝ) * A = -(A : Matrix (Fin 2) (Fin 2) ℝ)
  simp

theorem SpecialPeriods.Triangle.realSLPermutation_neg (A : SL(2, ℝ)) :
    realSLPermutation (-A) = realSLPermutation A := by
  rw [← neg_one_mul_realSL_mo1973_15956, map_mul, realSLPermutation_neg_one, one_mul]

theorem SpecialPeriods.Triangle.realSLPermutation_eq_iff (A B : SL(2, ℝ)) :
    realSLPermutation A = realSLPermutation B ↔ A = B ∨ A = -B := by
  constructor
  · intro h
    have hk : realSLPermutation (A * B⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rcases (realSLPermutation_eq_one_iff _).mp hk with hk | hk
    · exact Or.inl (mul_inv_eq_one.mp hk)
    · right
      have he := congrArg (fun C : SL(2, ℝ) => C * B) hk
      simpa only [mul_assoc, inv_mul_cancel, mul_one, neg_one_mul_realSL_mo1973_15956] using he
  · rintro (rfl | rfl)
    · rfl
    · exact realSLPermutation_neg B

theorem SpecialPeriods.Triangle.matrixGroup_of_permutation_mem_range (A : SL(2, ℝ))
    (h : realSLPermutation A ∈ SpecialPeriods.triangleGeometricRepresentation.range) :
    A ∈ matrixGroup := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨B, hB⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  rcases (realSLPermutation_eq_iff A B).mp (hg.symm.trans hB.symm) with he | he
  · rw [he]
    exact B.property
  · rw [he, ← neg_one_mul_realSL_mo1973_15956]
    exact matrixGroup.mul_mem neg_one_mem_matrixGroup B.property

theorem SpecialPeriods.Triangle.same_permutation_lower_left_zero_iff (A B : SL(2, ℝ))
    (h : realSLPermutation A = realSLPermutation B) : A 1 0 = 0 ↔ B 1 0 = 0 := by
  rcases (realSLPermutation_eq_iff A B).mp h with rfl | rfl
  · rfl
  · change -(B 1 0) = 0 ↔ B 1 0 = 0
    exact neg_eq_zero

theorem SpecialPeriods.Triangle.matrixGroup_translationSubgroup_eq :
    translationSubgroup matrixGroup = AddSubgroup.zmultiples width := by
  obtain ⟨t, ht⟩ := translationSubgroup_cyclic matrixGroup
  have ht_mem : shimizuTranslation t ∈ matrixGroup := by
    change t ∈ translationSubgroup matrixGroup
    rw [ht]
    exact AddSubgroup.mem_zmultiples t
  have hw := neg_width_mem_translationSubgroup_matrixGroup
  rw [ht, AddSubgroup.mem_zmultiples_iff] at hw
  obtain ⟨k, hk⟩ := hw
  obtain ⟨g, hg⟩ := matrixGroup_permutation_lift (shimizuTranslation t) ht_mem
  have hroot : g ^ k = SpecialPeriods.triangleCuspGenerator := by
    apply SpecialPeriods.triangleGeometricRepresentation_injective
    rw [map_zpow, hg, ← map_zpow, shimizuTranslation_zpow]
    have hk' : (k : ℝ) * t = -width := by simpa only [zsmul_eq_mul] using hk
    rw [hk', shimizuTranslation_neg_width]
    exact SpecialPeriods.triangleGeometricRepresentation_cusp.symm
  have hk_abs := SpecialPeriods.triangleCuspGenerator_zpow_root_exponent g k hroot
  have hk_cases : k = 1 ∨ k = -1 := by omega
  rcases hk_cases with rfl | rfl
  · have ht' : t = -width := by simpa using hk
    rw [ht, ht', AddSubgroup.zmultiples_neg]
  · have ht' : t = width := by simpa using congrArg Neg.neg hk
    rw [ht, ht']

theorem SpecialPeriods.Triangle.shimizuTranslation_mem_matrixGroup_iff (t : ℝ) :
    shimizuTranslation t ∈ matrixGroup ↔ ∃ n : ℤ, t = (n : ℝ) * width := by
  change t ∈ translationSubgroup matrixGroup ↔ _
  rw [matrixGroup_translationSubgroup_eq, AddSubgroup.mem_zmultiples_iff]
  simp only [zsmul_eq_mul, eq_comm]

private theorem SpecialPeriods.Triangle.upperTriangular_square_is_integer_mo1973_15963
    (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : ∃ n : ℤ, (A 0 0) ^ 2 = (n : ℝ) := by
  have hT : shimizuTranslation width ∈ matrixGroup := width_mem_translationSubgroup_matrixGroup
  have hconj := matrixGroup.mul_mem (matrixGroup.mul_mem hA hT) (matrixGroup.inv_mem hA)
  rw [upperTriangular_conjugate_translation A hc width] at hconj
  obtain ⟨n, hn⟩ := (shimizuTranslation_mem_matrixGroup_iff _).mp hconj
  refine ⟨n, mul_left_cancel₀ width_ne_zero ?_⟩
  simpa only [mul_comm] using hn

theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_square_eq_one (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : (A 0 0) ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := upperTriangular_square_is_integer_mo1973_15963 A hA hc
  obtain ⟨n, hn⟩ :=
    upperTriangular_square_is_integer_mo1973_15963 A⁻¹ (matrixGroup.inv_mem hA)
      (upperTriangular_inverse_lower_left A hc)
  rw [inverse_upper_left] at hn
  have hmpos : (0 : ℤ) < m := by
    have hp : (0 : ℝ) < (m : ℝ) := by
      rw [← hm]
      exact sq_pos_of_ne_zero (upperTriangular_zero_zero_ne_zero A hc)
    exact_mod_cast hp
  have hnpos : (0 : ℤ) < n := by
    have hp : (0 : ℝ) < (n : ℝ) := by
      rw [← hn]
      exact sq_pos_of_ne_zero (upperTriangular_one_one_ne_zero A hc)
    exact_mod_cast hp
  have hmn : m * n = 1 := by
    have he : (m : ℝ) * (n : ℝ) = 1 := by
      rw [← hm, ← hn, ← mul_pow, upperTriangular_det A hc, one_pow]
    exact_mod_cast he
  have hm1 : (1 : ℤ) ≤ m := by omega
  have hn1 : (1 : ℤ) ≤ n := by omega
  have hprod : 0 ≤ m * (n - 1) := mul_nonneg hmpos.le (sub_nonneg.mpr hn1)
  have hm_eq : m = 1 := by nlinarith [hmn]
  rw [hm, hm_eq, Int.cast_one]

private theorem SpecialPeriods.Triangle.upperTriangular_eq_signed_translation_mo1973_15965
    (A : SL(2, ℝ)) (hc : A 1 0 = 0) (ha : (A 0 0) ^ 2 = 1) :
    A = shimizuTranslation (A 0 0 * A 0 1) ∨ A = -shimizuTranslation (A 0 0 * A 0 1) := by
  have hdet := upperTriangular_det A hc
  rcases sq_eq_one_iff.mp ha with ha | ha
  · have hd : A 1 1 = 1 := by simpa [ha] using hdet
    left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_shimizuTranslation, ha, hd, hc]
  · have hd : A 1 1 = -1 := by rw [ha] at hdet; linarith
    right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_shimizuTranslation, ha, hd, hc]

private theorem SpecialPeriods.Triangle.translation_int_width_eq_cusp_zpow_mo1973_15966 (n : ℤ) :
    shimizuTranslation ((n : ℝ) * width) = cuspSL ^ (-n) := by
  rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
  simp

theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_iff (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) : A 1 0 = 0 ↔ ∃ n : ℤ, A = cuspSL ^ n ∨ A = -(cuspSL ^ n) := by
  constructor
  · intro hc
    have hs :=
      upperTriangular_eq_signed_translation_mo1973_15965 A hc
        (matrixGroup_upperTriangular_square_eq_one A hA hc)
    have ht : shimizuTranslation (A 0 0 * A 0 1) ∈ matrixGroup := by
      rcases hs with he | he
      · exact he ▸ hA
      · have hneg : -A ∈ matrixGroup := by
          rw [← neg_one_mul_realSL_mo1973_15956]
          exact matrixGroup.mul_mem neg_one_mem_matrixGroup hA
        have he' := congrArg (fun B : SL(2, ℝ) => -B) he
        rw [neg_neg] at he'
        exact he' ▸ hneg
    obtain ⟨n, hn⟩ := (shimizuTranslation_mem_matrixGroup_iff _).mp ht
    refine ⟨-n, ?_⟩
    simpa only [hn, translation_int_width_eq_cusp_zpow_mo1973_15966] using hs
  · rintro ⟨n, rfl | rfl⟩
    · rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
      rfl
    · change -((cuspSL ^ n) 1 0) = 0
      rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
      simp [shimizuTranslation]

theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_permutation (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) :
    ∃ n : ℤ,
      realSLPermutation A =
        SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.triangleCuspGenerator ^ n) := by
  obtain ⟨n, he | he⟩ := (matrixGroup_upperTriangular_iff A hA).mp hc
  · refine ⟨n, ?_⟩
    rw [he, map_zpow, map_zpow, SpecialPeriods.triangleGeometricRepresentation_cusp]
  · refine ⟨n, ?_⟩
    rw [he, realSLPermutation_neg, map_zpow, map_zpow,
      SpecialPeriods.triangleGeometricRepresentation_cusp]

theorem SpecialPeriods.Triangle.matrixGroup_upperTriangular_smul (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 = 0) : ∃ n : ℤ, ∀ z : ℍ, A • z = (-(n : ℝ) * width) +ᵥ z :=
  by
  obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_permutation A hA hc
  refine ⟨n, fun z => ?_⟩
  change realSLPermutation A z = _
  rw [hn, SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_apply]

theorem SpecialPeriods.Triangle.triangleGeometric_upperTriangular_lift_iff
    (g : SpecialPeriods.TriangleGroup) (A : SL(2, ℝ))
    (hA : realSLPermutation A = SpecialPeriods.triangleGeometricRepresentation g) :
    A 1 0 = 0 ↔ g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator := by
  constructor
  · intro hc
    have hmem : A ∈ matrixGroup := matrixGroup_of_permutation_mem_range A ⟨g, hA.symm⟩
    obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_permutation A hmem hc
    exact
      Subgroup.mem_zpowers_iff.mpr
        ⟨n, SpecialPeriods.triangleGeometricRepresentation_injective (hn.symm.trans hA)⟩
  · intro hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have he : realSLPermutation A = realSLPermutation (cuspSL ^ n) := by
      rw [hA, map_zpow, map_zpow, SpecialPeriods.triangleGeometricRepresentation_cusp]
    apply (same_permutation_lower_left_zero_iff _ _ he).mpr
    rw [← shimizuTranslation_neg_width, shimizuTranslation_zpow]
    rfl

def SpecialPeriods.Triangle.horodisc (Y : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | Y < z.im}, isOpen_lt continuous_const UpperHalfPlane.continuous_im⟩

theorem SpecialPeriods.Triangle.normSq_slDenom_lower_bound (A : SL(2, ℝ)) (z : ℍ) :
    (A 1 0) ^ 2 * z.im ^ 2 ≤ Complex.normSq (slDenom A z) := by
  have he : Complex.normSq (slDenom A z) = (A 1 0 * z.re + A 1 1) ^ 2 + (A 1 0 * z.im) ^ 2 := by
    simp [slDenom, Complex.normSq_apply, pow_two]
  rw [he]
  nlinarith [sq_nonneg (A 1 0 * z.re + A 1 1)]

theorem SpecialPeriods.Triangle.matrixGroup_nonparabolic_im_bound (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) (z : ℍ) : (A • z).im ≤ width ^ 2 / z.im := by
  have hlow := matrixGroup_lower_left_bound A hA hc
  have hmul : 1 ≤ |A 1 0| * width := (div_le_iff₀ width_pos).mp hlow
  have hsq : 1 ≤ (A 1 0) ^ 2 * width ^ 2 := by
    have hs :=
      sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg (abs_nonneg (A 1 0)) width_pos.le) |>.mpr
        hmul
    simpa only [one_pow, mul_pow, sq_abs] using hs
  have hn := normSq_slDenom_lower_bound A z
  have hden := Complex.normSq_pos.mpr (slDenom_ne_zero A z)
  rw [sl_im]
  apply (div_le_iff₀ hden).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ z.im_pos).mpr
  have h₁ := mul_le_mul_of_nonneg_left hn (sq_nonneg width)
  have h₂ := mul_le_mul_of_nonneg_right hsq (sq_nonneg z.im)
  nlinarith

theorem SpecialPeriods.Triangle.matrixGroup_nonparabolic_above_width (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) (z : ℍ) (hz : width < z.im) : (A • z).im < width := by
  apply lt_of_le_of_lt (matrixGroup_nonparabolic_im_bound A hA hc z)
  apply (div_lt_iff₀ z.im_pos).mpr
  nlinarith [width_pos]

theorem SpecialPeriods.Triangle.matrixGroup_nonparabolic_disjoint_horodisc (Y : ℝ)
    (hY : width ≤ Y) (A : SL(2, ℝ)) (hA : A ∈ matrixGroup) (hc : A 1 0 ≠ 0) :
    Disjoint ((fun z : ℍ => A • z) '' (horodisc Y : Set ℍ)) (horodisc Y) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨z, hz, rfl⟩ hw
  have hlow := matrixGroup_nonparabolic_above_width A hA hc z (hY.trans_lt hz)
  exact (not_lt_of_ge (le_trans hlow.le hY)) hw

theorem SpecialPeriods.Triangle.matrixGroup_horodisc_overlap_lower_left_zero (Y : ℝ)
    (hY : width ≤ Y) (A : SL(2, ℝ)) (hA : A ∈ matrixGroup)
    (hinter : ((fun z : ℍ => A • z) '' (horodisc Y : Set ℍ) ∩ horodisc Y).Nonempty) : A 1 0 = 0 :=
  by
  by_contra hc
  exact
    (Set.disjoint_iff_inter_eq_empty.mp
          (matrixGroup_nonparabolic_disjoint_horodisc Y hY A hA hc)) ▸
        hinter |>.ne_empty
      rfl

theorem SpecialPeriods.Triangle.horodisc_nonempty (Y : ℝ) : (horodisc Y : Set ℍ).Nonempty := by
  let z : ℍ :=
    ⟨((Max.max Y 0 + 1 : ℝ) : ℂ) * Complex.I,
      by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
        mul_one, MulZeroClass.mul_zero, add_zero]
      linarith [le_max_right Y 0]⟩
  refine ⟨z, ?_⟩
  change Y < (((Max.max Y 0 + 1 : ℝ) : ℂ) * Complex.I).im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
    mul_one, MulZeroClass.mul_zero, add_zero]
  linarith [le_max_left Y 0]

theorem SpecialPeriods.Triangle.cusp_horodisc_invariant (Y : ℝ)
    (g : Subgroup.zpowers SpecialPeriods.triangleCuspGenerator) :
    Set.MapsTo
      (fun z : ℍ =>
        SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup) z)
      (horodisc Y) (horodisc Y) := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  intro z hz
  change
    Y < (SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup) z).im
  rw [← hn, SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_apply,
    UpperHalfPlane.vadd_im]
  exact hz

theorem SpecialPeriods.Triangle.triangle_horodisc_overlap_mem_cusp (Y : ℝ) (hY : width ≤ Y)
    (g : SpecialPeriods.TriangleGroup)
    (hinter :
      ((SpecialPeriods.triangleGeometricRepresentation g) '' (horodisc Y : Set ℍ) ∩
          horodisc Y).Nonempty) :
    g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  apply (triangleGeometric_upperTriangular_lift_iff g A hA).mp
  apply matrixGroup_horodisc_overlap_lower_left_zero Y hY A A.property
  have he :
    (fun z : ℍ => (A : SL(2, ℝ)) • z) = SpecialPeriods.triangleGeometricRepresentation g := by
    funext z
    change realSLPermutation A z = SpecialPeriods.triangleGeometricRepresentation g z
    rw [hA]
  simpa only [he] using hinter

def SpecialPeriods.Triangle.orbitHeightBound (z : ℍ) : ℝ :=
  Max.max z.im (width ^ 2 / z.im)

theorem SpecialPeriods.Triangle.orbitHeightBound_continuous : Continuous orbitHeightBound :=
  UpperHalfPlane.continuous_im.max
    (continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_ne_zero))

theorem SpecialPeriods.Triangle.matrixGroup_im_le_orbitHeightBound (A : SL(2, ℝ))
    (hA : A ∈ matrixGroup) (z : ℍ) : (A • z).im ≤ orbitHeightBound z := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨n, hn⟩ := matrixGroup_upperTriangular_smul A hA hc
    rw [hn z, UpperHalfPlane.vadd_im]
    exact le_max_left _ _
  · exact (matrixGroup_nonparabolic_im_bound A hA hc z).trans (le_max_right _ _)

theorem SpecialPeriods.Triangle.triangle_im_le_orbitHeightBound (g : SpecialPeriods.TriangleGroup)
    (z : ℍ) : (SpecialPeriods.triangleGeometricRepresentation g z).im ≤ orbitHeightBound z := by
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_matrixGroup_lift g
  rw [← hA]
  exact matrixGroup_im_le_orbitHeightBound A A.property z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.triangleMatrixLift (g : TriangleGroup) : Triangle.matrixGroup :=
  (Triangle.triangleGeometricRepresentation_matrixGroup_lift g).choose

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangleMatrixLift_spec (g : TriangleGroup) :
    Triangle.realSLPermutation (triangleMatrixLift g) = triangleGeometricRepresentation g :=
  (Triangle.triangleGeometricRepresentation_matrixGroup_lift g).choose_spec

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangleMatrixLift_injective : Function.Injective triangleMatrixLift := by
  intro g h hgh
  apply triangleGeometricRepresentation_injective
  rw [← triangleMatrixLift_spec, ← triangleMatrixLift_spec, hgh]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangleMatrixLift_smul (g : TriangleGroup) (z : ℍ) :
    triangleMatrixLift g • z = g • z := by
  exact congrArg (fun f : Equiv.Perm ℍ => f z) (triangleMatrixLift_spec g)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangleGeometricAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul TriangleGroup ℍ where
  finite_disjoint_inter_image {K L} hK
    hL := by
    have hf := Triangle.matrixGroup_finite_compact_transporter hK hL
    apply (hf.preimage triangleMatrixLift_injective.injOn).subset
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact ⟨y, ⟨x, hx, (triangleMatrixLift_smul g x).trans hxy⟩, hy⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangleGeometricAction_continuous : ContinuousConstSMul TriangleGroup ℍ
    where continuous_const_smul g := (triangleGeometricRepresentation_holomorphic g).continuous

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_isOfFinOrder_of_fixed (g : TriangleGroup) (z : ℍ)
    (hg : triangleGeometricRepresentation g z = z) : IsOfFinOrder g :=
  FreeActionLocus.isOfFinOrder_of_smul_eq TriangleGroup ℍ g z hg

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleRegularLocus : Set ℍ :=
  FreeActionLocus.locus TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.mem_triangleRegularLocus_iff (z : ℍ) :
    z ∈ triangleRegularLocus ↔
      ∀ g : TriangleGroup, triangleGeometricRepresentation g z = z → g = 1 :=
  Iff.rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularLocus_invariant (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ triangleRegularLocus ↔ z ∈ triangleRegularLocus :=
  FreeActionLocus.smul_mem_locus_iff TriangleGroup ℍ g z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleRegularDomain : TopologicalSpace.Opens ℍ :=
  FreeActionLocus.opens TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
abbrev SpecialPeriods.TriangleRegularPoint :=
  triangleRegularDomain

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularPoint_locallyCompact :
    LocallyCompactSpace TriangleRegularPoint :=
  triangleRegularDomain.isOpen.locallyCompactSpace

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularAction : MulAction TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.mulAction TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularAction_free :
    IsCancelSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.isCancelSMul TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularAction_continuous :
    ContinuousConstSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.continuousConstSMul TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.properlyDiscontinuousSMul TriangleGroup ℍ

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularAction_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : TriangleRegularPoint => g • z) :=
  FreeActionLocus.smul_contMDiff TriangleGroup ℍ ℂ ω triangleGeometricRepresentation_holomorphic g

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
abbrev SpecialPeriods.TriangleRegularQuotient :=
  Quotient (MulAction.orbitRel TriangleGroup TriangleRegularPoint)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleRegularProject : TriangleRegularPoint → TriangleRegularQuotient :=
  Quotient.mk _

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularProject_surjective :
    Function.Surjective triangleRegularProject :=
  Quotient.mk_surjective

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularProject_covering :
    IsQuotientCoveringMap triangleRegularProject TriangleGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[instance_reducible]
def SpecialPeriods.triangleRegularQuotientChartedSpace : ChartedSpace ℂ TriangleRegularQuotient :=
  CoveringQuotient.chartedSpace (E := ℂ) triangleRegularProject_covering

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularQuotient_isManifold :
    letI := triangleRegularQuotientChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  CoveringQuotient.isManifold triangleRegularProject_covering ω triangleRegularAction_holomorphic

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularProject_isLocalDiffeomorph :
    letI := triangleRegularQuotientChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularProject :=
  CoveringQuotient.project_isLocalDiffeomorph triangleRegularProject_covering
    triangleRegularAction_holomorphic

attribute [local instance] SpecialPeriods.triangleGeometricAction in
attribute [local instance] SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularProject_holomorphic :
    letI := triangleRegularQuotientChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularProject := by
  let := triangleRegularQuotientChartedSpace
  exact triangleRegularProject_isLocalDiffeomorph.contMDiff


attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
abbrev SpecialPeriods.TriangleOrbitSpace :=
  Quotient (MulAction.orbitRel TriangleGroup ℍ)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleOrbitProjection : ℍ → TriangleOrbitSpace :=
  Quotient.mk _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitProjection_surjective :
    Function.Surjective triangleOrbitProjection :=
  Quotient.mk_surjective

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitProjection_continuous : Continuous triangleOrbitProjection :=
  continuous_quot_mk

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitProjection_eq_iff (x y : ℍ) :
    triangleOrbitProjection x = triangleOrbitProjection y ↔
      ∃ g : TriangleGroup, triangleGeometricRepresentation g y = x :=
  Quotient.eq''

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.triangleOrbitProjection_smul (g : TriangleGroup) (z : ℍ) :
    triangleOrbitProjection (triangleGeometricRepresentation g z) = triangleOrbitProjection z :=
  (triangleOrbitProjection_eq_iff _ _).mpr ⟨g, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap triangleOrbitProjection :=
  MulAction.isOpenQuotientMap_quotientMk

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitProjection_isOpenMap : IsOpenMap triangleOrbitProjection :=
  triangleOrbitProjection_isOpenQuotientMap.isOpenMap

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleOrbitSpace_t2 : T2Space TriangleOrbitSpace :=
  inferInstance

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleOrbitSpace_locallyCompact :
    LocallyCompactSpace TriangleOrbitSpace :=
  triangleOrbitProjection_isOpenQuotientMap.locallyCompactSpace

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleOrbitCenterOne : TriangleOrbitSpace :=
  triangleOrbitProjection Triangle.centerOne

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleOrbitCenterTwo : TriangleOrbitSpace :=
  triangleOrbitProjection Triangle.centerTwo

abbrev SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  OnePoint TriangleOrbitSpace

def SpecialPeriods.triangleCuspPoint : TriangleCompactifiedOrbitSpace :=
  (OnePoint.infty)

def SpecialPeriods.triangleOpenInclusion : TriangleOrbitSpace → TriangleCompactifiedOrbitSpace :=
  OnePoint.some

theorem SpecialPeriods.triangleOpenInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding triangleOpenInclusion :=
  OnePoint.isOpenEmbedding_coe

theorem SpecialPeriods.triangleOpenInclusion_ne_cusp (q : TriangleOrbitSpace) :
    triangleOpenInclusion q ≠ triangleCuspPoint :=
  OnePoint.coe_ne_infty q

theorem SpecialPeriods.triangleCompactifiedOrbitSpace_compact :
    CompactSpace TriangleCompactifiedOrbitSpace :=
  inferInstance

def SpecialPeriods.Triangle.cuspImage (Y : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  ⟨SpecialPeriods.triangleOrbitProjection '' (horodisc Y : Set ℍ),
    SpecialPeriods.triangleOrbitProjection_isOpenMap _ (horodisc Y).isOpen⟩

@[simp]
theorem SpecialPeriods.Triangle.mem_cuspImage (Y : ℝ) (q : SpecialPeriods.TriangleOrbitSpace) :
    q ∈ cuspImage Y ↔ ∃ z : ℍ, Y < z.im ∧ SpecialPeriods.triangleOrbitProjection z = q :=
  Iff.rfl

theorem SpecialPeriods.Triangle.cuspImage_antitone :
    Antitone (fun Y : ℝ => (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)) := by
  intro Y Z hYZ q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, hYZ.trans_lt hz, rfl⟩

theorem SpecialPeriods.Triangle.cuspImage_compl_subset_truncated_image (Y : ℝ) :
    (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ ⊆
      SpecialPeriods.triangleOrbitProjection '' truncatedFordRegion Y := by
  intro q hq
  obtain ⟨z, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  obtain ⟨g, hg⟩ := SpecialPeriods.triangle_exists_fordRegion_representative z
  have he :
    SpecialPeriods.triangleOrbitProjection (SpecialPeriods.triangleGeometricRepresentation g z) =
      SpecialPeriods.triangleOrbitProjection z :=
    SpecialPeriods.triangleOrbitProjection_smul g z
  refine ⟨SpecialPeriods.triangleGeometricRepresentation g z, ⟨hg, ?_⟩, he⟩
  apply le_of_not_gt
  intro hi
  exact hq ⟨SpecialPeriods.triangleGeometricRepresentation g z, hi, he⟩

theorem SpecialPeriods.Triangle.cuspImage_compl_compact (Y : ℝ) :
    IsCompact (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ :=
  ((truncatedFordRegion_compact Y).image
        SpecialPeriods.triangleOrbitProjection_continuous).of_isClosed_subset
    (cuspImage Y).isOpen.isClosed_compl (cuspImage_compl_subset_truncated_image Y)

def SpecialPeriods.Triangle.cuspNeighborhood (Y : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  OnePoint.opensOfCompl (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ
    (cuspImage Y).isOpen.isClosed_compl (cuspImage_compl_compact Y)

@[simp]
theorem SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood (Y : ℝ) :
    SpecialPeriods.triangleCuspPoint ∈ cuspNeighborhood Y :=
  OnePoint.infty_mem_opensOfCompl _ _

@[simp]
theorem SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood (Y : ℝ)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ cuspNeighborhood Y ↔ q ∈ cuspImage Y := by
  change
    (q : OnePoint SpecialPeriods.TriangleOrbitSpace) ∉
        ((↑) : SpecialPeriods.TriangleOrbitSpace → OnePoint SpecialPeriods.TriangleOrbitSpace) ''
          (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ ↔
      _
  simp only [OnePoint.coe_injective.mem_set_image, Set.mem_compl_iff, Classical.not_not]
  rfl

theorem SpecialPeriods.Triangle.cuspNeighborhood_preimage (Y : ℝ) :
    SpecialPeriods.triangleOpenInclusion ⁻¹'
        (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      cuspImage Y := by
  ext q
  exact openInclusion_mem_cuspNeighborhood Y q

theorem SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds (Y : ℝ) :
    (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∈
      𝓝 SpecialPeriods.triangleCuspPoint :=
  (cuspNeighborhood Y).isOpen.mem_nhds (cuspPoint_mem_cuspNeighborhood Y)

private theorem SpecialPeriods.Triangle.width_coe_ne_zero_mo1973_16106 : (width : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr width_ne_zero

def SpecialPeriods.Triangle.cuspQ (z : ℍ) : ℂ :=
  Function.Periodic.qParam width z

theorem SpecialPeriods.Triangle.cuspQ_eq_exp (z : ℍ) :
    cuspQ z = Complex.exp (2 * Real.pi * Complex.I * z / width) :=
  rfl

theorem SpecialPeriods.Triangle.cuspQ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspQ :=
  (Function.Periodic.contDiff_qParam (h := width) ω).contMDiff.comp UpperHalfPlane.contMDiff_coe

theorem SpecialPeriods.Triangle.cuspQ_continuous : Continuous cuspQ :=
  cuspQ_holomorphic.continuous

theorem SpecialPeriods.Triangle.cuspQ_ne_zero (z : ℍ) : cuspQ z ≠ 0 :=
  Function.Periodic.qParam_ne_zero z

theorem SpecialPeriods.Triangle.cuspQ_hasStrictDerivAt (z : ℍ) :
    HasStrictDerivAt (cuspQ ∘ UpperHalfPlane.ofComplex)
      (cuspQ z * (2 * Real.pi * Complex.I / width)) (z : ℂ) := by
  have h :
    HasStrictDerivAt (Function.Periodic.qParam width)
      (cuspQ z * (2 * Real.pi * Complex.I / width)) (z : ℂ) := by
    simpa only [id_eq, mul_one] using!
      (((hasStrictDerivAt_id (z : ℂ)).const_mul (2 * Real.pi * Complex.I)).div_const
          (width : ℂ)).cexp
  apply h.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos] with w hw
  change
    Function.Periodic.qParam width w = Function.Periodic.qParam width (UpperHalfPlane.ofComplex w)
  exact congrArg (Function.Periodic.qParam width) hw.symm

theorem SpecialPeriods.Triangle.cuspQ_deriv_ne_zero (z : ℍ) :
    deriv (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  rw [(cuspQ_hasStrictDerivAt z).hasDerivAt.deriv]
  exact
    mul_ne_zero (cuspQ_ne_zero z)
      (div_ne_zero Complex.two_pi_I_ne_zero width_coe_ne_zero_mo1973_16106)

theorem SpecialPeriods.Triangle.cuspQ_norm_lt_one (z : ℍ) : ‖cuspQ z‖ < 1 :=
  Function.Periodic.norm_qParam_lt_one width_pos z.im_pos

theorem SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff (A : ℝ) (z : ℍ) :
    ‖cuspQ z‖ < Real.exp (-2 * Real.pi * A / width) ↔ A < z.im :=
  Function.Periodic.norm_qParam_lt_iff width_pos A z

theorem SpecialPeriods.Triangle.cuspQ_cusp_zpow (n : ℤ) (z : ℍ) :
    cuspQ
        (SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
          z) =
      cuspQ z := by
  rw [cuspQ, SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe, cuspQ]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-n, ?_⟩
  push_cast
  rw [mul_div_assoc, sub_div, mul_div_cancel_right₀ _ width_coe_ne_zero_mo1973_16106]
  ring

theorem SpecialPeriods.Triangle.cuspQ_eq_iff (z w : ℍ) :
    cuspQ z = cuspQ w ↔
      ∃ n : ℤ,
        SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
            w =
          z := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period width_ne_zero (z : ℂ)
    obtain ⟨n, hn⟩ := Function.Periodic.qParam_left_inv_mod_period width_ne_zero (w : ℂ)
    change Function.Periodic.invQParam width (cuspQ z) = (z : ℂ) + m * width at hm
    change Function.Periodic.invQParam width (cuspQ w) = (w : ℂ) + n * width at hn
    rw [h, hn] at hm
    refine ⟨m - n, ?_⟩
    apply UpperHalfPlane.ext
    rw [SpecialPeriods.triangleGeometricRepresentation_cusp_zpow_coe]
    push_cast
    linear_combination hm
  · rintro ⟨n, rfl⟩
    exact cuspQ_cusp_zpow n w

def SpecialPeriods.Triangle.puncturedDisc : TopologicalSpace.Opens ℂ :=
  ⟨{q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
    isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)⟩

abbrev SpecialPeriods.Triangle.PuncturedDisc :=
  puncturedDisc

def SpecialPeriods.Triangle.cuspQMap (z : ℍ) : PuncturedDisc :=
  ⟨cuspQ z, cuspQ_ne_zero z, cuspQ_norm_lt_one z⟩

theorem SpecialPeriods.Triangle.cuspQMap_surjective : Function.Surjective cuspQMap := by
  intro q
  refine
    ⟨⟨Function.Periodic.invQParam width q,
        Function.Periodic.im_invQParam_pos_of_norm_lt_one width_pos q.property.2 q.property.1⟩,
      ?_⟩
  apply Subtype.ext
  exact Function.Periodic.qParam_right_inv width_ne_zero q.property.1

private theorem SpecialPeriods.Triangle.qParam_width_isOpenMap_mo1973_16141 :
    IsOpenMap (Function.Periodic.qParam width) := by
  change IsOpenMap (Complex.exp ∘ (fun z : ℂ => 2 * Real.pi * Complex.I * z / width))
  apply Complex.isOpenMap_exp.comp
  have he :
    (fun z : ℂ => 2 * Real.pi * Complex.I * z / width) =
      (fun z : ℂ => (2 * Real.pi * Complex.I / width) * z) := by
    funext z
    ring
  rw [he]
  exact
    (Homeomorph.mulLeft₀ _
        (div_ne_zero Complex.two_pi_I_ne_zero width_coe_ne_zero_mo1973_16106)).isOpenMap

theorem SpecialPeriods.Triangle.cuspQ_isOpenMap : IsOpenMap cuspQ :=
  qParam_width_isOpenMap_mo1973_16141.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

theorem SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty :
    Filter.Tendsto cuspQ UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) :=
  (Function.Periodic.qParam_tendsto width_pos).comp UpperHalfPlane.tendsto_coe_atImInfty

def SpecialPeriods.Triangle.cuspRadius (Y : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * Y / width)

@[simp]
theorem SpecialPeriods.Triangle.cuspRadius_pos (Y : ℝ) : 0 < cuspRadius Y :=
  Real.exp_pos _

theorem SpecialPeriods.Triangle.cuspRadius_le_one (Y : ℝ) (hY : 0 ≤ Y) : cuspRadius Y ≤ 1 := by
  rw [cuspRadius, Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg _ width_pos.le
  exact
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) Real.pi_pos.le)
      hY

def SpecialPeriods.Triangle.puncturedCuspBall (Y : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{q : ℂ | q ≠ 0 ∧ ‖q‖ < cuspRadius Y},
    isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)⟩

@[simp]
theorem SpecialPeriods.Triangle.mem_puncturedCuspBall (Y : ℝ) (q : ℂ) :
    q ∈ puncturedCuspBall Y ↔ q ≠ 0 ∧ ‖q‖ < cuspRadius Y :=
  Iff.rfl

theorem SpecialPeriods.Triangle.cuspQ_mem_puncturedCuspBall_iff (Y : ℝ) (z : ℍ) :
    cuspQ z ∈ puncturedCuspBall Y ↔ z ∈ horodisc Y := by
  change (cuspQ z ≠ 0 ∧ ‖cuspQ z‖ < Real.exp (-2 * Real.pi * Y / width)) ↔ Y < z.im
  constructor
  · intro h
    exact (cuspQ_norm_lt_exp_iff Y z).mp h.2
  · intro h
    exact ⟨cuspQ_ne_zero z, (cuspQ_norm_lt_exp_iff Y z).mpr h⟩

def SpecialPeriods.Triangle.cuspQHorodisc (Y : ℝ) (z : horodisc Y) : puncturedCuspBall Y :=
  ⟨cuspQ z, (cuspQ_mem_puncturedCuspBall_iff Y z).mpr z.property⟩

theorem SpecialPeriods.Triangle.cuspQHorodisc_eq_iff (Y : ℝ) (z w : horodisc Y) :
    cuspQHorodisc Y z = cuspQHorodisc Y w ↔
      ∃ n : ℤ,
        SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
            (w : ℍ) =
          (z : ℍ) :=
  Subtype.ext_iff.trans (cuspQ_eq_iff z w)

theorem SpecialPeriods.Triangle.cuspQHorodisc_holomorphic (Y : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : horodisc Y => cuspQ (z : ℍ)) :=
    cuspQ_holomorphic.comp contMDiff_subtype_val
  intro z
  have hi :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : horodisc Y => (cuspQHorodisc Y w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (h z)

theorem SpecialPeriods.Triangle.cuspQHorodisc_continuous (Y : ℝ) : Continuous (cuspQHorodisc Y) :=
  (cuspQHorodisc_holomorphic Y).continuous

theorem SpecialPeriods.Triangle.cuspQHorodisc_isOpenMap (Y : ℝ) : IsOpenMap (cuspQHorodisc Y) := by
  apply (puncturedCuspBall Y).isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  exact cuspQ_isOpenMap.comp (horodisc Y).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

theorem SpecialPeriods.Triangle.cuspQHorodisc_surjective (Y : ℝ) (hY : 0 ≤ Y) :
    Function.Surjective (cuspQHorodisc Y) := by
  intro q
  let q' : PuncturedDisc := ⟨q, q.property.1, q.property.2.trans_le (cuspRadius_le_one Y hY)⟩
  obtain ⟨z, hz⟩ := cuspQMap_surjective q'
  have hzq : cuspQ z = (q : ℂ) := congrArg Subtype.val hz
  have hzY : z ∈ horodisc Y := by
    apply (cuspQ_mem_puncturedCuspBall_iff Y z).mp
    rw [hzq]
    exact q.property
  refine ⟨⟨z, hzY⟩, ?_⟩
  exact Subtype.ext hzq

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
abbrev SpecialPeriods.Triangle.CuspHorodiscQuotient (Y : ℝ) :=
  LocalOrbitQuotient.LocalQuotient (Subgroup.zpowers SpecialPeriods.triangleCuspGenerator)
    (horodisc Y) (cusp_horodisc_invariant Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.cuspHorodiscProjection (Y : ℝ) :
    horodisc Y → CuspHorodiscQuotient Y :=
  LocalOrbitQuotient.localProjection _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscProjection_eq_iff (Y : ℝ) (z w : horodisc Y) :
    cuspHorodiscProjection Y z = cuspHorodiscProjection Y w ↔
      ∃ n : ℤ,
        SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n)
            (w : ℍ) =
          (z : ℍ) := by
  rw [cuspHorodiscProjection, LocalOrbitQuotient.localProjection_eq_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    refine ⟨n, ?_⟩
    rw [hn]
    exact hg
  · rintro ⟨n, hn⟩
    exact ⟨⟨SpecialPeriods.triangleCuspGenerator ^ n, Subgroup.zpow_mem_zpowers _ _⟩, hn⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscProjection_surjective (Y : ℝ) :
    Function.Surjective (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_surjective _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscProjection_continuous (Y : ℝ) :
    Continuous (cuspHorodiscProjection Y) :=
  LocalOrbitQuotient.localProjection_continuous _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.cuspImageProjection (Y : ℝ) : horodisc Y → cuspImage Y :=
  LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup) (horodisc Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspImageProjection_surjective (Y : ℝ) :
    Function.Surjective (cuspImageProjection Y) :=
  LocalOrbitQuotient.imageProjection_surjective (horodisc Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.cuspHorodiscImageHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    CuspHorodiscQuotient Y ≃ₜ cuspImage Y :=
  LocalOrbitQuotient.localHomeomorph (Subgroup.zpowers SpecialPeriods.triangleCuspGenerator)
    (horodisc Y) (cusp_horodisc_invariant Y) (triangle_horodisc_overlap_mem_cusp Y hY)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.cuspHorodiscImageHomeomorph_mk (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    cuspHorodiscImageHomeomorph Y hY (cuspHorodiscProjection Y z) = cuspImageProjection Y z :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.cuspHorodiscImageHomeomorph_symm_mk (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    (cuspHorodiscImageHomeomorph Y hY).symm (cuspImageProjection Y z) =
      cuspHorodiscProjection Y z :=
  (cuspHorodiscImageHomeomorph Y hY).symm_apply_apply (cuspHorodiscProjection Y z)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspImageProjection_eq_iff (Y : ℝ) (hY : width ≤ Y)
    (z w : horodisc Y) :
    cuspImageProjection Y z = cuspImageProjection Y w ↔ cuspQ (z : ℍ) = cuspQ (w : ℍ) := by
  rw [← cuspHorodiscImageHomeomorph_mk Y hY z, ← cuspHorodiscImageHomeomorph_mk Y hY w,
    (cuspHorodiscImageHomeomorph Y hY).injective.eq_iff, cuspHorodiscProjection_eq_iff,
    cuspQ_eq_iff]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.cuspHorodiscToBall (Y : ℝ) :
    CuspHorodiscQuotient Y → puncturedCuspBall Y :=
  Quotient.lift (cuspQHorodisc Y) fun z w h =>
    (cuspQHorodisc_eq_iff Y z w).mpr ((cuspHorodiscProjection_eq_iff Y z w).mp (Quotient.sound h))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscToBall_injective (Y : ℝ) :
    Function.Injective (cuspHorodiscToBall Y) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro z w h
  exact (cuspHorodiscProjection_eq_iff Y z w).mpr ((cuspQHorodisc_eq_iff Y z w).mp h)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscToBall_surjective (Y : ℝ) (hY : 0 ≤ Y) :
    Function.Surjective (cuspHorodiscToBall Y) := by
  intro q
  obtain ⟨z, rfl⟩ := cuspQHorodisc_surjective Y hY q
  exact ⟨cuspHorodiscProjection Y z, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscToBall_continuous (Y : ℝ) :
    Continuous (cuspHorodiscToBall Y) :=
  (cuspQHorodisc_continuous Y).quotient_lift _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspHorodiscToBall_isOpenMap (Y : ℝ) :
    IsOpenMap (cuspHorodiscToBall Y) :=
  IsOpenMap.of_comp (cuspHorodiscProjection_continuous Y) (cuspHorodiscProjection_surjective Y)
    (cuspQHorodisc_isOpenMap Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.cuspHorodiscBallHomeomorph (Y : ℝ) (hY : 0 ≤ Y) :
    CuspHorodiscQuotient Y ≃ₜ puncturedCuspBall Y :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (cuspHorodiscToBall Y)
      ⟨cuspHorodiscToBall_injective Y, cuspHorodiscToBall_surjective Y hY⟩)
    (cuspHorodiscToBall_continuous Y) (cuspHorodiscToBall_isOpenMap Y)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.cuspImageHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    cuspImage Y ≃ₜ puncturedCuspBall Y :=
  (cuspHorodiscImageHomeomorph Y hY).symm.trans
    (cuspHorodiscBallHomeomorph Y (width_pos.le.trans hY))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.cuspImageHomeomorph_mk (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspImageHomeomorph Y hY (cuspImageProjection Y z) = cuspQHorodisc Y z := by
  change
    cuspHorodiscToBall Y ((cuspHorodiscImageHomeomorph Y hY).symm (cuspImageProjection Y z)) = _
  rw [cuspHorodiscImageHomeomorph_symm_mk]
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.cuspImageHomeomorph_mk_coe (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) : (cuspImageHomeomorph Y hY (cuspImageProjection Y z) : ℂ) = cuspQ (z : ℍ) :=
  by
  rw [cuspImageHomeomorph_mk]
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.cuspImageHomeomorph_symm_q (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    (cuspImageHomeomorph Y hY).symm (cuspQHorodisc Y z) = cuspImageProjection Y z := by
  rw [← cuspImageHomeomorph_mk Y hY z, Homeomorph.symm_apply_apply]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.cuspImageHomeomorph_norm_lt_iff (Y Z : ℝ) (hY : width ≤ Y)
    (hYZ : Y ≤ Z) (x : cuspImage Y) :
    ‖(cuspImageHomeomorph Y hY x : ℂ)‖ < cuspRadius Z ↔
      (x : SpecialPeriods.TriangleOrbitSpace) ∈ cuspImage Z := by
  obtain ⟨z, rfl⟩ := cuspImageProjection_surjective Y x
  rw [cuspImageHomeomorph_mk_coe]
  change
    ‖cuspQ (z : ℍ)‖ < Real.exp (-2 * Real.pi * Z / width) ↔
      ∃ w : ℍ,
        Z < w.im ∧
          SpecialPeriods.triangleOrbitProjection w =
            SpecialPeriods.triangleOrbitProjection (z : ℍ)
  rw [cuspQ_norm_lt_exp_iff]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, he⟩
    have hwY : w ∈ horodisc Y := hYZ.trans_lt hw
    have he' : cuspImageProjection Y ⟨w, hwY⟩ = cuspImageProjection Y z := Subtype.ext he
    have hq := (cuspImageProjection_eq_iff Y hY ⟨w, hwY⟩ z).mp he'
    have hnorm := (cuspQ_norm_lt_exp_iff Z w).mpr hw
    rw [hq] at hnorm
    exact (cuspQ_norm_lt_exp_iff Z (z : ℍ)).mp hnorm

def SpecialPeriods.Triangle.boundedOrbitImage (R : ℝ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  ⟨SpecialPeriods.triangleOrbitProjection '' {z : ℍ | orbitHeightBound z < R},
    SpecialPeriods.triangleOrbitProjection_isOpenMap _
      (isOpen_lt orbitHeightBound_continuous continuous_const)⟩

theorem SpecialPeriods.Triangle.boundedOrbitImage_mono :
    Monotone (fun R : ℝ => (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace)) := by
  intro R S hRS q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, hz.trans_le hRS, rfl⟩

theorem SpecialPeriods.Triangle.boundedOrbitImage_subset_cuspImage_compl (R : ℝ) :
    (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace) ⊆
      (cuspImage R : Set SpecialPeriods.TriangleOrbitSpace)ᶜ := by
  rintro q ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
  obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp he
  have hb := triangle_im_le_orbitHeightBound g z
  rw [hg] at hb
  exact (not_lt_of_ge (le_trans hb hz.le)) hw

theorem SpecialPeriods.Triangle.boundedOrbitImage_cover :
    (⋃ R : ℝ, (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨z, rfl⟩ := SpecialPeriods.triangleOrbitProjection_surjective q
  refine Set.mem_iUnion.mpr ⟨orbitHeightBound z + 1, z, ?_, rfl⟩
  change orbitHeightBound z < orbitHeightBound z + 1
  linarith

theorem SpecialPeriods.Triangle.compact_subset_cuspImage_compl
    {K : Set SpecialPeriods.TriangleOrbitSpace} (hK : IsCompact K) :
    ∃ Y : ℝ, width ≤ Y ∧ K ⊆ (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace)ᶜ := by
  obtain ⟨R, hR⟩ :=
    hK.elim_directed_cover
      (fun R : ℝ => (boundedOrbitImage R : Set SpecialPeriods.TriangleOrbitSpace))
      (fun R => (boundedOrbitImage R).isOpen)
      (by rw [boundedOrbitImage_cover]; exact Set.subset_univ K)
      (fun R S =>
        ⟨Max.max R S, boundedOrbitImage_mono (le_max_left R S),
          boundedOrbitImage_mono (le_max_right R S)⟩)
  refine ⟨Max.max R width, le_max_right _ _, ?_⟩
  exact
    hR.trans
      ((boundedOrbitImage_mono (le_max_left R width)).trans
        (boundedOrbitImage_subset_cuspImage_compl (Max.max R width)))

theorem SpecialPeriods.Triangle.cuspNeighborhood_basis :
    (𝓝 SpecialPeriods.triangleCuspPoint).HasBasis (fun Y : ℝ => width ≤ Y)
      (fun Y => (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)) := by
  rw [Filter.hasBasis_iff]
  intro U
  constructor
  · intro hU
    obtain ⟨K, ⟨hKclosed, hKcompact⟩, hKU⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
    obtain ⟨Y, hY, hKY⟩ := compact_subset_cuspImage_compl hKcompact
    refine ⟨Y, hY, ?_⟩
    intro x hx
    induction x using OnePoint.rec
    · exact hKU (Or.inr rfl)
    · rename_i q
      have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
      exact hKU (Or.inl ⟨q, fun hqK => hKY hqK hq, rfl⟩)
  · rintro ⟨Y, _, hYU⟩
    exact Filter.mem_of_superset (cuspNeighborhood_mem_nhds Y) hYU

instance SpecialPeriods.triangleOrbitSpace_noncompact : NoncompactSpace TriangleOrbitSpace where
  noncompact_univ := by
    intro hK
    obtain ⟨Y, _, hY⟩ := Triangle.compact_subset_cuspImage_compl hK
    obtain ⟨z, hz⟩ := Triangle.horodisc_nonempty Y
    exact hY (Set.mem_univ (triangleOrbitProjection z)) ⟨z, hz, rfl⟩

theorem SpecialPeriods.triangleCompactifiedOrbitSpace_connected :
    ConnectedSpace TriangleCompactifiedOrbitSpace :=
  inferInstance

theorem SpecialPeriods.Triangle.cuspRadius_tendsto_zero :
    Filter.Tendsto cuspRadius Filter.atTop (𝓝 0) := by
  have hneg : -2 * Real.pi < 0 := by nlinarith [Real.pi_pos]
  exact
    Real.tendsto_exp_atBot.comp
      ((Filter.tendsto_id.const_mul_atTop_of_neg hneg).atBot_div_const width_pos)

theorem SpecialPeriods.Triangle.exists_high_cuspRadius_lt (Y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : ℝ, Y ≤ Z ∧ width ≤ Z ∧ cuspRadius Z < ε := by
  have hsmall : ∀ᶠ Z in Filter.atTop, cuspRadius Z < ε :=
    cuspRadius_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨Max.max Y (Max.max width Z), le_max_left _ _, ?_, hZ _ ?_⟩
  · exact (le_max_left width Z).trans (le_max_right Y _)
  · exact (le_max_right width Z).trans (le_max_right Y _)

def SpecialPeriods.Triangle.cuspFullForward (Y : ℝ) (hY : width ≤ Y) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace → ℂ := by
  classical
    exact
    OnePoint.rec 0
      (fun q : SpecialPeriods.TriangleOrbitSpace =>
        if hq : q ∈ cuspImage Y then (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) else 0)

@[simp]
theorem SpecialPeriods.Triangle.cuspFullForward_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    cuspFullForward Y hY SpecialPeriods.triangleCuspPoint = 0 :=
  rfl

theorem SpecialPeriods.Triangle.cuspFullForward_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : SpecialPeriods.TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q) =
      (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) := by
  classical
  change (if h : q ∈ cuspImage Y then (cuspImageHomeomorph Y hY ⟨q, h⟩ : ℂ) else 0) = _
  rw [dif_pos hq]

def SpecialPeriods.Triangle.cuspFullInverse (Y : ℝ) (hY : width ≤ Y) :
    ℂ → SpecialPeriods.TriangleCompactifiedOrbitSpace := by
  classical
    exact fun z =>
    if hz : z ∈ puncturedCuspBall Y then
      SpecialPeriods.triangleOpenInclusion
        ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩ : SpecialPeriods.TriangleOrbitSpace)
    else SpecialPeriods.triangleCuspPoint

@[simp]
theorem SpecialPeriods.Triangle.cuspFullInverse_zero (Y : ℝ) (hY : width ≤ Y) :
    cuspFullInverse Y hY 0 = SpecialPeriods.triangleCuspPoint := by
  classical simp [cuspFullInverse]

theorem SpecialPeriods.Triangle.cuspFullInverse_of_mem (Y : ℝ) (hY : width ≤ Y) (z : ℂ)
    (hz : z ∈ puncturedCuspBall Y) :
    cuspFullInverse Y hY z =
      SpecialPeriods.triangleOpenInclusion
        ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩ : SpecialPeriods.TriangleOrbitSpace) := by
  classical simp [cuspFullInverse, hz]

theorem SpecialPeriods.Triangle.cuspFullInverse_of_not_mem (Y : ℝ) (hY : width ≤ Y) (z : ℂ)
    (hz : z ∉ puncturedCuspBall Y) : cuspFullInverse Y hY z = SpecialPeriods.triangleCuspPoint := by
  classical simp [cuspFullInverse, hz]

theorem SpecialPeriods.Triangle.cuspFullForward_continuousAt_openInclusion (Y : ℝ)
    (hY : width ≤ Y) (q : SpecialPeriods.TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    ContinuousAt (cuspFullForward Y hY) (SpecialPeriods.triangleOpenInclusion q) := by
  apply OnePoint.continuousAt_coe.mpr
  have hc :
    ContinuousOn
      (fun q : SpecialPeriods.TriangleOrbitSpace =>
        cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q))
      (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change
      Continuous
        (fun q : cuspImage Y => cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q))
    have he :
      (fun q : cuspImage Y => cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q)) =
        (fun q : cuspImage Y => (cuspImageHomeomorph Y hY q : ℂ)) := by
      funext q
      exact cuspFullForward_openInclusion Y hY q q.property
    rw [he]
    exact continuous_subtype_val.comp (cuspImageHomeomorph Y hY).continuous
  exact hc.continuousAt ((cuspImage Y).isOpen.mem_nhds hq)

theorem SpecialPeriods.Triangle.cuspFullForward_continuousAt_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    ContinuousAt (cuspFullForward Y hY) SpecialPeriods.triangleCuspPoint := by
  change Filter.Tendsto (cuspFullForward Y hY) (𝓝 SpecialPeriods.triangleCuspPoint) (𝓝 (0 : ℂ))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Z, hYZ, _, hZε⟩ := exists_high_cuspRadius_lt Y hε
  filter_upwards [cuspNeighborhood_mem_nhds Z] with x hx
  induction x using OnePoint.rec
  · change Dist.dist (0 : ℂ) 0 < ε
    simpa only [dist_self] using hε
  · rename_i q
    have hqZ : q ∈ cuspImage Z := (openInclusion_mem_cuspNeighborhood Z q).mp hx
    have hqY : q ∈ cuspImage Y := cuspImage_antitone hYZ hqZ
    have hn := (cuspImageHomeomorph_norm_lt_iff Y Z hY hYZ ⟨q, hqY⟩).mpr hqZ
    change Dist.dist (cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q)) 0 < ε
    rw [cuspFullForward_openInclusion Y hY q hqY, dist_zero_right]
    exact hn.trans hZε

theorem SpecialPeriods.Triangle.cuspFullForward_continuousOn (Y : ℝ) (hY : width ≤ Y) :
    ContinuousOn (cuspFullForward Y hY)
      (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  intro x hx
  induction x using OnePoint.rec
  · exact (cuspFullForward_continuousAt_cuspPoint Y hY).continuousWithinAt
  · rename_i q
    exact
      (cuspFullForward_continuousAt_openInclusion Y hY q
          ((openInclusion_mem_cuspNeighborhood Y q).mp hx)).continuousWithinAt

theorem SpecialPeriods.Triangle.cuspFullInverse_continuousAt_of_mem (Y : ℝ) (hY : width ≤ Y)
    (z : ℂ) (hz : z ∈ puncturedCuspBall Y) : ContinuousAt (cuspFullInverse Y hY) z := by
  have hc : ContinuousOn (cuspFullInverse Y hY) (puncturedCuspBall Y : Set ℂ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : puncturedCuspBall Y => cuspFullInverse Y hY z)
    have he :
      (fun z : puncturedCuspBall Y => cuspFullInverse Y hY z) =
        (fun z : puncturedCuspBall Y =>
          SpecialPeriods.triangleOpenInclusion
            ((cuspImageHomeomorph Y hY).symm z : SpecialPeriods.TriangleOrbitSpace)) := by
      funext z
      exact cuspFullInverse_of_mem Y hY z z.property
    rw [he]
    exact
      SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.continuous.comp
        (continuous_subtype_val.comp (cuspImageHomeomorph Y hY).symm.continuous)
  exact hc.continuousAt ((puncturedCuspBall Y).isOpen.mem_nhds hz)

theorem SpecialPeriods.Triangle.cuspFullInverse_continuousAt_zero (Y : ℝ) (hY : width ≤ Y) :
    ContinuousAt (cuspFullInverse Y hY) 0 := by
  classical
  change Filter.Tendsto (cuspFullInverse Y hY) (𝓝 (0 : ℂ)) (𝓝 (cuspFullInverse Y hY 0))
  rw [cuspFullInverse_zero, cuspNeighborhood_basis.tendsto_right_iff]
  intro Z _
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (cuspRadius_pos (Max.max Y Z))] with z hz
  by_cases hp : z ∈ puncturedCuspBall Y
  · rw [cuspFullInverse_of_mem Y hY z hp]
    apply (openInclusion_mem_cuspNeighborhood Z _).mpr
    apply cuspImage_antitone (le_max_right Y Z)
    apply
      (cuspImageHomeomorph_norm_lt_iff Y (Max.max Y Z) hY (le_max_left Y Z)
          ((cuspImageHomeomorph Y hY).symm ⟨z, hp⟩)).mp
    simpa using hz
  · rw [cuspFullInverse_of_not_mem Y hY z hp]
    exact cuspPoint_mem_cuspNeighborhood Z

theorem SpecialPeriods.Triangle.cuspFullInverse_continuousOn (Y : ℝ) (hY : width ≤ Y) :
    ContinuousOn (cuspFullInverse Y hY) (Metric.ball (0 : ℂ) (cuspRadius Y)) := by
  classical
  intro z hz
  by_cases h0 : z = 0
  · subst z
    exact (cuspFullInverse_continuousAt_zero Y hY).continuousWithinAt
  · exact (cuspFullInverse_continuousAt_of_mem Y hY z ⟨h0, by simpa using hz⟩).continuousWithinAt

def SpecialPeriods.Triangle.cuspFullChart (Y : ℝ) (hY : width ≤ Y) :
    OpenPartialHomeomorph SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ := by
  classical
    exact
    { toFun := cuspFullForward Y hY
      invFun := cuspFullInverse Y hY
      source := cuspNeighborhood Y
      target := Metric.ball 0 (cuspRadius Y)
      map_source' := by
        intro x hx
        induction x using OnePoint.rec
        · change (0 : ℂ) ∈ Metric.ball 0 (cuspRadius Y)
          simpa only [Metric.mem_ball, dist_self] using cuspRadius_pos Y
        · rename_i q
          have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
          change
            cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q) ∈
              Metric.ball 0 (cuspRadius Y)
          rw [cuspFullForward_openInclusion Y hY q hq]
          simpa using (cuspImageHomeomorph Y hY ⟨q, hq⟩).property.2
      map_target' := by
        intro z _
        by_cases hz : z ∈ puncturedCuspBall Y
        · rw [cuspFullInverse_of_mem Y hY z hz]
          exact
            (openInclusion_mem_cuspNeighborhood Y _).mpr
              ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩).property
        · rw [cuspFullInverse_of_not_mem Y hY z hz]
          exact cuspPoint_mem_cuspNeighborhood Y
      left_inv' := by
        intro x hx
        induction x using OnePoint.rec
        · exact cuspFullInverse_zero Y hY
        · rename_i q
          have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
          change
            cuspFullInverse Y hY (cuspFullForward Y hY (SpecialPeriods.triangleOpenInclusion q)) =
              SpecialPeriods.triangleOpenInclusion q
          rw [cuspFullForward_openInclusion Y hY q hq]
          rw [cuspFullInverse_of_mem Y hY _ (cuspImageHomeomorph Y hY ⟨q, hq⟩).property]
          change
            SpecialPeriods.triangleOpenInclusion
                ((cuspImageHomeomorph Y hY).symm (cuspImageHomeomorph Y hY ⟨q, hq⟩)) =
              _
          rw [Homeomorph.symm_apply_apply]
      right_inv' := by
        intro z hz
        by_cases h0 : z = 0
        · subst z
          rw [cuspFullInverse_zero, cuspFullForward_cuspPoint]
        · have hp : z ∈ puncturedCuspBall Y := ⟨h0, by simpa using hz⟩
          rw [cuspFullInverse_of_mem Y hY z hp]
          rw [cuspFullForward_openInclusion Y hY _
              ((cuspImageHomeomorph Y hY).symm ⟨z, hp⟩).property]
          exact congrArg Subtype.val ((cuspImageHomeomorph Y hY).apply_symm_apply ⟨z, hp⟩)
      open_source := (cuspNeighborhood Y).isOpen
      open_target := Metric.isOpen_ball
      continuousOn_toFun := cuspFullForward_continuousOn Y hY
      continuousOn_invFun := cuspFullInverse_continuousOn Y hY }

@[simp]
theorem SpecialPeriods.Triangle.cuspFullChart_source (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).source =
      (cuspNeighborhood Y : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.cuspFullChart_target (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).target = Metric.ball 0 (cuspRadius Y) :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.cuspFullChart_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    cuspFullChart Y hY SpecialPeriods.triangleCuspPoint = 0 :=
  rfl

@[simp]
theorem SpecialPeriods.Triangle.cuspFullChart_symm_zero (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).symm 0 = SpecialPeriods.triangleCuspPoint :=
  cuspFullInverse_zero Y hY

theorem SpecialPeriods.Triangle.cuspFullChart_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : SpecialPeriods.TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    cuspFullChart Y hY (SpecialPeriods.triangleOpenInclusion q) =
      (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) :=
  cuspFullForward_openInclusion Y hY q hq

theorem SpecialPeriods.Triangle.cuspFullChart_mk (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspFullChart Y hY
        (SpecialPeriods.triangleOpenInclusion
          (SpecialPeriods.triangleOrbitProjection (z : UpperHalfPlane))) =
      cuspQ (z : UpperHalfPlane) := by
  change cuspFullChart Y hY (SpecialPeriods.triangleOpenInclusion (cuspImageProjection Y z)) = _
  rw [cuspFullChart_openInclusion Y hY _ (cuspImageProjection Y z).property]
  exact cuspImageHomeomorph_mk_coe Y hY z

theorem SpecialPeriods.CoprodTorsion.word_prod_injective {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] : Function.Injective (Monoid.CoprodI.Word.prod (M := M)) := by
  classical exact (Monoid.CoprodI.Word.equiv (M := M)).symm.injective

theorem SpecialPeriods.CoprodTorsion.word_prod_eq_one_iff {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M) :
    w.prod = 1 ↔ w = Monoid.CoprodI.Word.empty := by
  constructor
  · intro h
    apply word_prod_injective
    simpa only [Monoid.CoprodI.Word.prod_empty] using h
  · rintro rfl
    exact Monoid.CoprodI.Word.prod_empty

theorem SpecialPeriods.CoprodTorsion.neWord_prod_ne_one {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) : w.prod ≠ 1 := by
  intro h
  have hw : w.toWord = Monoid.CoprodI.Word.empty := (word_prod_eq_one_iff w.toWord).mp h
  exact w.toList_ne_nil (congrArg Monoid.CoprodI.Word.toList hw)

def SpecialPeriods.CoprodTorsion.neWord_pow_succ {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) : ℕ → Monoid.CoprodI.NeWord M i j
  | 0 => w
  | n + 1 => Monoid.CoprodI.NeWord.append (neWord_pow_succ w h n) h.symm w

theorem SpecialPeriods.CoprodTorsion.neWord_pow_succ_prod {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) (n : ℕ) :
    (neWord_pow_succ w h n).prod = w.prod ^ (n + 1) := by
  induction n with
  | zero => simp [neWord_pow_succ]
  | succ n ih => simp only [neWord_pow_succ, Monoid.CoprodI.NeWord.append_prod, ih, pow_succ]

theorem SpecialPeriods.CoprodTorsion.neWord_pow_ne_one {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) (n : ℕ)
    (hn : 0 < n) : w.prod ^ n ≠ 1 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    rw [← neWord_pow_succ_prod w h n]
    exact neWord_prod_ne_one _

theorem SpecialPeriods.CoprodTorsion.neWord_not_isOfFinOrder {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) :
    ¬IsOfFinOrder w.prod := by
  rintro hf
  obtain ⟨n, hn, hpow⟩ := hf.exists_pow_eq_one
  exact neWord_pow_ne_one w h n hn hpow

theorem SpecialPeriods.CoprodTorsion.word_pow_ne_one_of_endpoints_ne {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M)
    (h : w.toList.head?.map Sigma.fst ≠ w.toList.getLast?.map Sigma.fst) (n : ℕ) (hn : 0 < n) :
    w.prod ^ n ≠ 1 := by
  have hw : w ≠ Monoid.CoprodI.Word.empty := by
    rintro rfl
    exact h rfl
  obtain ⟨i, j, v, rfl⟩ := Monoid.CoprodI.NeWord.of_word w hw
  have hij : i ≠ j := by
    simpa only [Monoid.CoprodI.NeWord.toWord, Monoid.CoprodI.NeWord.toList_head?,
      Monoid.CoprodI.NeWord.toList_getLast?, Option.map_some, ne_eq, Option.some.injEq] using h
  exact neWord_pow_ne_one v hij n hn

theorem SpecialPeriods.CoprodTorsion.word_not_isOfFinOrder_of_endpoints_ne {ι : Type*}
    {M : ι → Type*} [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M)
    (h : w.toList.head?.map Sigma.fst ≠ w.toList.getLast?.map Sigma.fst) : ¬IsOfFinOrder w.prod :=
  by
  rintro hf
  obtain ⟨n, hn, hpow⟩ := hf.exists_pow_eq_one
  exact word_pow_ne_one_of_endpoints_ne w h n hn hpow

theorem SpecialPeriods.CoprodTorsion.word_not_isOfFinOrder_of_head_getLast {ι : Type*}
    {M : ι → Type*} [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M) (a b : Σ i, M i)
    (ha : w.toList.head? = Option.some a) (hb : w.toList.getLast? = Option.some b)
    (hab : a.1 ≠ b.1) : ¬IsOfFinOrder w.prod := by
  apply word_not_isOfFinOrder_of_endpoints_ne w
  simpa only [ha, hb, Option.map_some, ne_eq, Option.some.injEq] using hab

theorem SpecialPeriods.CoprodTorsion.exists_shorter_conjugate {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] (w : Monoid.CoprodI.Word G) (a b : Σ i, G i) (l : List (Σ i, G i))
    (hw : w.toList = a :: (l ++ [b])) (hab : a.1 = b.1) :
    ∃ v : Monoid.CoprodI.Word G, v.toList.length < w.toList.length ∧ IsConj v.prod w.prod := by
  classical
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp only at hab
  subst j
  have hchain : (l ++ [Sigma.mk i b]).IsChain (fun x y : Σ i, G i => x.1 ≠ y.1) := by
    have hc := w.chain_ne
    rw [hw] at hc
    exact hc.tail
  have hletters : ∀ x ∈ l, Sigma.snd x ≠ 1 := by
    intro x hx
    apply w.ne_one x
    rw [hw]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  let middle : Monoid.CoprodI.Word G := ⟨l, hletters, hchain.left_of_append⟩
  have hp : w.prod = Monoid.CoprodI.of a * (middle.prod * Monoid.CoprodI.of b) := by
    simp [Monoid.CoprodI.Word.prod, hw, middle]
  by_cases hba : b * a = 1
  · refine ⟨middle, ?_, ?_⟩
    · simp only [middle, hw, List.length_cons, List.length_append]
      omega
    · apply isConj_iff.mpr
      refine ⟨Monoid.CoprodI.of a, ?_⟩
      have hb : Monoid.CoprodI.of b = (Monoid.CoprodI.of a : Monoid.CoprodI G)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, hba, map_one]
      rw [hp, hb, mul_assoc]
  · let v : Monoid.CoprodI.Word G :=
      { toList := l ++ [⟨i, b * a⟩]
        ne_one := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hletters x hx
          · have hx' : x = ⟨i, b * a⟩ := List.mem_singleton.mp hx
            subst x
            exact hba
        chain_ne := by
          apply List.IsChain.append hchain.left_of_append (List.isChain_singleton _)
          intro x hx y hy
          have hy' : y = ⟨i, b * a⟩ := by simpa using hy.symm
          subst y
          exact (List.isChain_append.mp hchain).2.2 x hx ⟨i, b⟩ (by simp) }
    refine ⟨v, ?_, ?_⟩
    · simp only [v, hw, List.length_cons, List.length_append]
      omega
    · apply isConj_iff.mpr
      refine ⟨Monoid.CoprodI.of a, ?_⟩
      have hv : v.prod = middle.prod * Monoid.CoprodI.of (b * a) := by
        simp only [Monoid.CoprodI.Word.prod, v, middle, List.map_append, List.map_singleton,
          List.prod_append, List.prod_singleton]
      rw [hv, hp, map_mul]
      simp only [mul_assoc, mul_inv_cancel, mul_one]

private theorem SpecialPeriods.CoprodTorsion.list_cases_endpoints_mo1973_16238 {α : Type*}
    (l : List α) : l = [] ∨ (∃ a, l = [a]) ∨ ∃ a m b, l = a :: (m ++ [b]) := by
  induction l using List.bidirectionalRec with
  | nil => exact Or.inl rfl
  | singleton a => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | cons_append a l b _ => exact Or.inr (Or.inr ⟨a, l, b, rfl⟩)

theorem SpecialPeriods.CoprodTorsion.coprodI_isOfFinOrder_conjugate_factor {ι : Type*}
    {G : ι → Type*} [∀ i, Group (G i)] (x : Monoid.CoprodI G) (hx : IsOfFinOrder x) :
    x = 1 ∨ ∃ (i : ι) (a : G i), IsConj (Monoid.CoprodI.of a) x := by
  classical
  let P : ℕ → Prop := fun n => ∃ w : Monoid.CoprodI.Word G, w.toList.length = n ∧ IsConj w.prod x
  have hP : ∃ n, P n := by
    refine ⟨(Monoid.CoprodI.Word.equiv x).toList.length, Monoid.CoprodI.Word.equiv x, rfl, ?_⟩
    have hp : (Monoid.CoprodI.Word.equiv x).prod = x :=
      (Monoid.CoprodI.Word.equiv (M := G)).symm_apply_apply x
    rw [hp]
  obtain ⟨w, hwlen, hwconj⟩ := Nat.find_spec hP
  have hmin (v : Monoid.CoprodI.Word G) (hv : IsConj v.prod x) :
    w.toList.length ≤ v.toList.length := by
    rw [hwlen]
    exact Nat.find_min' hP ⟨v, rfl, hv⟩
  have hwfin : IsOfFinOrder w.prod := hwconj.symm.isOfFinOrder hx
  rcases list_cases_endpoints_mo1973_16238 w.toList with hnil | ⟨a, hsingle⟩ | ⟨a, l, b, hw⟩
  · left
    have hp : w.prod = 1 := by simp [Monoid.CoprodI.Word.prod, hnil]
    simpa only [hp, isConj_one_right] using hwconj
  · right
    refine ⟨a.1, a.2, ?_⟩
    have hp : w.prod = Monoid.CoprodI.of a.2 := by simp [Monoid.CoprodI.Word.prod, hsingle]
    simpa only [hp] using hwconj
  · by_cases hab : a.1 = b.1
    · obtain ⟨v, hvlen, hvconj⟩ := exists_shorter_conjugate w a b l hw hab
      exact (Nat.not_lt_of_ge (hmin v (hvconj.trans hwconj)) hvlen).elim
    · exfalso
      apply
        word_not_isOfFinOrder_of_head_getLast w a b (by simp [hw])
          (by rw [hw, ← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; rfl) hab
          hwfin

theorem SpecialPeriods.CoprodTorsion.coprodI_nontrivial_isOfFinOrder_conjugate_factor {ι : Type*}
    {G : ι → Type*} [∀ i, Group (G i)] (x : Monoid.CoprodI G) (hx : IsOfFinOrder x)
    (hne : x ≠ 1) : ∃ (i : ι) (a : G i), a ≠ 1 ∧ IsConj (Monoid.CoprodI.of a) x := by
  obtain hx | ⟨i, a, ha⟩ := coprodI_isOfFinOrder_conjugate_factor x hx
  · exact (hne hx).elim
  · refine ⟨i, a, ?_, ha⟩
    rintro rfl
    exact hne (by simpa using ha.symm)

theorem SpecialPeriods.CoprodTorsion.coprod_nontrivial_isOfFinOrder_conjugate_factor
    {A B : Type u} [Group A] [Group B] (x : Monoid.Coprod A B) (hx : IsOfFinOrder x)
    (hne : x ≠ 1) :
    (∃ a : A, a ≠ 1 ∧ IsConj (Monoid.Coprod.inl a) x) ∨
      ∃ b : B, b ≠ 1 ∧ IsConj (Monoid.Coprod.inr b) x := by
  let H : Bool → Type _ := fun b => cond b B A
  let : ∀ b, Group (H b) := Bool.rec (inferInstance : Group A) (inferInstance : Group B)
  let toI : Monoid.Coprod A B →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* Monoid.Coprod A B :=
    Monoid.CoprodI.lift fun b =>
      match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · ext a
      simp [toI, fromI]
    · ext b
      simp [toI, fromI]
  have hleft_apply (y : Monoid.Coprod A B) : fromI (toI y) = y := DFunLike.congr_fun hleft y
  have hto_ne : toI x ≠ 1 := by
    intro he
    apply hne
    have hh := congrArg fromI he
    simpa only [hleft_apply, map_one] using hh
  obtain ⟨b, a, hane, ha⟩ :=
    coprodI_nontrivial_isOfFinOrder_conjugate_factor (toI x) (toI.isOfFinOrder hx) hto_ne
  have ha' := fromI.map_isConj ha
  rw [hleft_apply] at ha'
  cases b with
  | false => exact Or.inl ⟨a, hane, by simpa [fromI] using ha'⟩
  | true => exact Or.inr ⟨a, hane, by simpa [fromI] using ha'⟩

private theorem SpecialPeriods.cyclic_eq_positive_generator_pow_mo1973_16242 {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) (ha : a ≠ 1) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ a = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  refine ⟨a.toAdd.val, ZMod.val_pos.mpr ?_, ZMod.val_lt _, ?_⟩
  · exact ha
  · change a.toAdd = a.toAdd.val • (1 : ZMod n)
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem SpecialPeriods.triangle_nontrivial_isOfFinOrder_conjugate_generator_power
    (g : TriangleGroup) (hg : IsOfFinOrder g) (hne : g ≠ 1) :
    (∃ n : ℕ, 0 < n ∧ n < 3 ∧ IsConj (triangleGenerator₁ ^ n) g) ∨
      ∃ n : ℕ, 0 < n ∧ n < 4 ∧ IsConj (triangleGenerator₂ ^ n) g := by
  obtain ⟨a, hane, ha⟩ | ⟨a, hane, ha⟩ :=
    CoprodTorsion.coprod_nontrivial_isOfFinOrder_conjugate_factor g hg hne
  · obtain ⟨n, hn0, hn3, rfl⟩ := cyclic_eq_positive_generator_pow_mo1973_16242 a hane
    exact Or.inl ⟨n, hn0, hn3, by simpa only [map_pow, triangleGenerator₁] using ha⟩
  · obtain ⟨n, hn0, hn4, rfl⟩ := cyclic_eq_positive_generator_pow_mo1973_16242 a hane
    exact Or.inr ⟨n, hn0, hn4, by simpa only [map_pow, triangleGenerator₂] using ha⟩

theorem SpecialPeriods.triangle_nontrivial_isOfFinOrder_eq_conjugate_generator_power
    (g : TriangleGroup) (hg : IsOfFinOrder g) (hne : g ≠ 1) :
    (∃ (h : TriangleGroup) (n : ℕ), 0 < n ∧ n < 3 ∧ g = h * triangleGenerator₁ ^ n * h⁻¹) ∨
      (∃ (h : TriangleGroup) (n : ℕ), 0 < n ∧ n < 4 ∧ g = h * triangleGenerator₂ ^ n * h⁻¹) := by
  obtain ⟨n, hn0, hn3, hn⟩ | ⟨n, hn0, hn4, hn⟩ :=
    triangle_nontrivial_isOfFinOrder_conjugate_generator_power g hg hne
  · obtain ⟨h, hh⟩ := isConj_iff.mp hn
    exact Or.inl ⟨h, n, hn0, hn3, hh.symm⟩
  · obtain ⟨h, hh⟩ := isConj_iff.mp hn
    exact Or.inr ⟨h, n, hn0, hn4, hh.symm⟩

def SpecialPeriods.rhoPoint : ℍ :=
  ⟨rho, rho_im_pos⟩

@[simp]
theorem SpecialPeriods.coe_rhoPoint : (rhoPoint : ℂ) = rho :=
  rfl

theorem SpecialPeriods.rho_ne_zero : rho ≠ 0 :=
  rhoPoint.ne_zero

theorem SpecialPeriods.rho_fourth : rho ^ 4 = -rho := by
  calc
    rho ^ 4 = rho ^ 3 * rho := by ring
    _ = -rho := by rw [rho_cube]; ring

theorem SpecialPeriods.rho_fourth_ne_one : rho ^ 4 ≠ 1 := by
  intro h
  have hr : rho = -1 := neg_eq_iff_eq_neg.mp (rho_fourth.symm.trans h)
  have := rho_im_pos
  simp [hr] at this

theorem SpecialPeriods.TS_smul_rhoPoint :
    (ModularGroup.T * ModularGroup.S) • rhoPoint = rhoPoint := by
  rw [SemigroupAction.mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_vadd, Complex.ofReal_one, coe_rhoPoint, inv_neg]
  field_simp [rho_ne_zero]
  linear_combination -rho_sq

theorem SpecialPeriods.S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [UpperHalfPlane.modular_S_smul]
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_I, inv_neg, Complex.inv_I, neg_neg]

theorem SpecialPeriods.levelOne_transform {k : ℤ} (f : ModularForm 𝒮ℒ k) (g : SL(2, ℤ)) (z : ℍ) :
    f (g • z) = (UpperHalfPlane.denom g z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn'' f (show (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨g, rfl⟩) z

theorem SpecialPeriods.E₄_rhoPoint : ModularForm.E₄ rhoPoint = 0 := by
  have h := levelOne_transform ModularForm.E₄ (ModularGroup.T * ModularGroup.S) rhoPoint
  rw [TS_smul_rhoPoint] at h
  have hd : UpperHalfPlane.denom (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) rhoPoint = rho := by
    have h10 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [ModularGroup.denom_apply, h10, h11]
    simp
  rw [hd, zpow_ofNat] at h
  exact
    (mul_eq_zero.mp
          (show (rho ^ 4 - 1) * ModularForm.E₄ rhoPoint = 0 by
            linear_combination -h)).resolve_left
      (sub_ne_zero.mpr rho_fourth_ne_one)

theorem SpecialPeriods.E₆_I : ModularForm.E₆ UpperHalfPlane.I = 0 := by
  have h := levelOne_transform ModularForm.E₆ ModularGroup.S UpperHalfPlane.I
  rw [S_smul_I, ModularGroup.denom_S, UpperHalfPlane.coe_I, zpow_ofNat] at h
  have hi : Complex.I ^ 6 = -1 := by norm_num [Complex.I_sq, pow_succ]
  rw [hi] at h
  linear_combination h / 2

theorem SpecialPeriods.E₄_E₆_not_both_zero (z : ℍ) :
    ModularForm.E₄ z ≠ 0 ∨ ModularForm.E₆ z ≠ 0 := by
  by_contra! h
  have hd := ModularForm.discriminant_ne_zero z
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, h.1, h.2] at hd
  norm_num at hd

theorem SpecialPeriods.E₆_rhoPoint_ne_zero : ModularForm.E₆ rhoPoint ≠ 0 := by
  simpa only [E₄_rhoPoint, ne_self_iff_false, false_or] using E₄_E₆_not_both_zero rhoPoint

theorem SpecialPeriods.E₄_I_ne_zero : ModularForm.E₄ UpperHalfPlane.I ≠ 0 := by
  simpa only [E₆_I, ne_self_iff_false, or_false] using E₄_E₆_not_both_zero UpperHalfPlane.I

theorem SpecialPeriods.levelOne_eq_of_qExpansion_coeff_zero {k : ℤ} (hk : k < 12)
    (f g : ModularForm 𝒮ℒ k)
    (hfg : (UpperHalfPlane.qExpansion 1 f).coeff 0 = (UpperHalfPlane.qExpansion 1 g).coeff 0) :
    f = g := by
  have hq : (UpperHalfPlane.qExpansion 1 (f - g)).coeff 0 = 0 := by
    rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, map_sub, hfg, sub_self]
  have hzero : ModularForm.toCuspForm (f - g) hq = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) _
  ext z
  have hz := congrArg (fun F : CuspForm 𝒮ℒ k => F z) hzero
  exact sub_eq_zero.mp hz

theorem SpecialPeriods.modularForm_analyticAt {k : ℤ} (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet _ z.im_pos

def SpecialPeriods.modularJ (z : ℍ) : ℂ :=
  ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

theorem SpecialPeriods.modularJ_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) modularJ :=
  (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero

theorem SpecialPeriods.modularJ_analyticAt (z : ℍ) :
    AnalyticAt ℂ (modularJ ∘ UpperHalfPlane.ofComplex) z :=
  (UpperHalfPlane.mdifferentiable_iff.mp modularJ_mdifferentiable).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

theorem SpecialPeriods.modularJ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω modularJ := by
  intro z
  exact UpperHalfPlane.contMDiffAt_iff.mpr (modularJ_analyticAt z).contDiffAt

theorem SpecialPeriods.modularJ_continuous : Continuous modularJ :=
  modularJ_holomorphic.continuous

theorem SpecialPeriods.modularJ_invariant (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (z : ℍ) :
    modularJ (γ • z) = modularJ z := by
  have h₄ := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ z
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ z
  change
    ModularForm.discriminant (γ • z) =
      UpperHalfPlane.denom γ z ^ (12 : ℤ) * ModularForm.discriminant z at hΔ
  simp only [modularJ, h₄, hΔ, zpow_ofNat, mul_pow, ← pow_mul]
  norm_num
  exact mul_div_mul_left _ _ (pow_ne_zero 12 (UpperHalfPlane.denom_ne_zero γ z))

theorem SpecialPeriods.modularJ_SL_invariant (γ : SL(2, ℤ)) (z : ℍ) :
    modularJ (γ • z) = modularJ z :=
  modularJ_invariant γ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z

theorem SpecialPeriods.modularJ_sub_1728 (z : ℍ) :
    modularJ z - 1728 = ModularForm.E₆ z ^ 2 / ModularForm.discriminant z := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [eq_div_iff (by norm_num : (1728 : ℂ) ≠ 0)] at h
  unfold modularJ
  field_simp [ModularForm.discriminant_ne_zero z]
  linear_combination -h

theorem SpecialPeriods.modularJ_eq_zero_iff (z : ℍ) : modularJ z = 0 ↔ ModularForm.E₄ z = 0 := by
  simp [modularJ, ModularForm.discriminant_ne_zero]

theorem SpecialPeriods.modularJ_eq_1728_iff (z : ℍ) : modularJ z = 1728 ↔ ModularForm.E₆ z = 0 := by
  rw [← sub_eq_zero, modularJ_sub_1728]
  simp [ModularForm.discriminant_ne_zero]

@[simp]
theorem SpecialPeriods.modularJ_rhoPoint : modularJ rhoPoint = 0 :=
  (modularJ_eq_zero_iff rhoPoint).mpr E₄_rhoPoint

@[simp]
theorem SpecialPeriods.modularJ_I : modularJ UpperHalfPlane.I = 1728 :=
  (modularJ_eq_1728_iff UpperHalfPlane.I).mpr E₆_I

def SpecialPeriods.discriminantUnit (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

@[simp]
theorem SpecialPeriods.discriminantUnit_zero : discriminantUnit 0 = 1 := by
  simp [discriminantUnit]

theorem SpecialPeriods.discriminantUnit_differentiableOn :
    DifferentiableOn ℂ discriminantUnit (Metric.ball 0 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow_pow 24

theorem SpecialPeriods.discriminantUnit_analyticAt_zero : AnalyticAt ℂ discriminantUnit 0 :=
  discriminantUnit_differentiableOn.analyticAt (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

def SpecialPeriods.modularJUnit (q : ℂ) : ℂ :=
  UpperHalfPlane.cuspFunction 1 ModularForm.E₄ q ^ 3 / discriminantUnit q

theorem SpecialPeriods.E₄_cuspFunction_zero :
    UpperHalfPlane.cuspFunction 1 ModularForm.E₄ 0 = 1 := by
  have h :=
    EisensteinSeries.E_qExpansion_coeff_zero (show 3 ≤ 4 by decide) (show Even 4 by decide)
  simpa [UpperHalfPlane.qExpansion_coeff] using h

@[simp]
theorem SpecialPeriods.modularJUnit_zero : modularJUnit 0 = 1 := by
  simp [modularJUnit, E₄_cuspFunction_zero]

theorem SpecialPeriods.modularJUnit_analyticAt_zero : AnalyticAt ℂ modularJUnit 0 :=
  ((ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ zero_lt_one
            one_mem_strictPeriods_SL).pow
        3).div
    discriminantUnit_analyticAt_zero (by simp)

theorem SpecialPeriods.modularJ_eq_unit_div_q (z : ℍ) :
    modularJ z = modularJUnit (Function.Periodic.qParam 1 z) / Function.Periodic.qParam 1 z := by
  have hE :=
    SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ z one_mem_strictPeriods_SL one_ne_zero
  have hΔ := ModularForm.discriminant_eq_q_prod z
  change
    ModularForm.discriminant z =
      Function.Periodic.qParam 1 z * discriminantUnit (Function.Periodic.qParam 1 z) at hΔ
  rw [modularJ, hΔ, modularJUnit, hE]
  rw [div_div, mul_comm]

def SpecialPeriods.modularJInQ (q : ℂ) : ℂ :=
  modularJUnit q / q

theorem SpecialPeriods.modularJInQ_qParam (z : ℍ) :
    modularJInQ (Function.Periodic.qParam 1 z) = modularJ z :=
  (modularJ_eq_unit_div_q z).symm

theorem SpecialPeriods.modularJInQ_order : meromorphicOrderAt modularJInQ 0 = (-1 : ℤ) := by
  have hu : meromorphicOrderAt modularJUnit 0 = 0 := by
    rw [modularJUnit_analyticAt_zero.meromorphicOrderAt_eq,
      (modularJUnit_analyticAt_zero.analyticOrderAt_eq_zero.mpr (by simp))]
    rfl
  change meromorphicOrderAt (modularJUnit / id) 0 = _
  rw [meromorphicOrderAt_div modularJUnit_analyticAt_zero.meromorphicAt
      analyticAt_id.meromorphicAt,
    hu, meromorphicOrderAt_id]
  norm_num

theorem SpecialPeriods.q_mul_modularJ_tendsto :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z * modularJ z)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h :=
    modularJUnit_analyticAt_zero.continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)
  simp only [modularJUnit_zero, Function.comp_def] at h
  apply h.congr
  intro z
  rw [modularJ_eq_unit_div_q]
  exact (mul_div_cancel₀ _ (Function.Periodic.qParam_ne_zero z)).symm

theorem SpecialPeriods.norm_modularJ_tendsto :
    Filter.Tendsto (fun z : ℍ => ‖modularJ z‖) UpperHalfPlane.atImInfty Filter.atTop := by
  have hq :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z) UpperHalfPlane.atImInfty
      (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one, ?_⟩
    exact Filter.Eventually.of_forall (fun z => Function.Periodic.qParam_ne_zero z)
  have hj : Filter.Tendsto modularJInQ (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg
      (by
        rw [modularJInQ_order]
        exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))
  have h := (tendsto_norm_atTop_iff_cobounded.mpr hj).comp hq
  simpa only [Function.comp_def, modularJInQ_qParam] using h

theorem SpecialPeriods.modularJ_not_constant : ¬∃ c : ℂ, ∀ z : ℍ, modularJ z = c := by
  rintro ⟨c, hc⟩
  have h :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z * c) UpperHalfPlane.atImInfty
      (𝓝 0) := by simpa using (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one).mul_const c
  have h' :
    Filter.Tendsto (fun z : ℍ => Function.Periodic.qParam 1 z * c) UpperHalfPlane.atImInfty
      (𝓝 1) := by simpa only [hc] using q_mul_modularJ_tendsto
  exact zero_ne_one (tendsto_nhds_unique h h')

theorem SpecialPeriods.inv_modularJ_sub_tendsto (c : ℂ) :
    Filter.Tendsto (fun z : ℍ => (modularJ z - c)⁻¹) UpperHalfPlane.atImInfty (𝓝 0) := by
  exact
    Filter.tendsto_inv₀_cobounded.comp
      ((tendsto_sub_const_cobounded c).comp
        (tendsto_norm_atTop_iff_cobounded.mp norm_modularJ_tendsto))

private theorem SpecialPeriods.inv_modularJ_sub_slash_mo1973_16294 (c : ℂ) (γ : SL(2, ℤ)) :
    (fun z : ℍ => (modularJ z - c)⁻¹) ∣[(0 : ℤ)] γ = fun z : ℍ => (modularJ z - c)⁻¹ := by
  funext z
  simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact congrArg (fun w : ℂ => (w - c)⁻¹) (modularJ_SL_invariant γ z)

private def SpecialPeriods.omittedValueModularForm_mo1973_16295 (c : ℂ)
    (hc : ∀ z : ℍ, modularJ z ≠ c) : ModularForm 𝒮ℒ 0
    where
  toFun z := (modularJ z - c)⁻¹
  slash_action_eq' := by
    rintro γ ⟨γ', rfl⟩
    exact inv_modularJ_sub_slash_mo1973_16294 c γ'
  holo' :=
    (modularJ_mdifferentiable.sub mdifferentiable_const).inv (fun z => sub_ne_zero.mpr (hc z))
  bdd_at_cusps' {s}
    hs := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hs]
    intro γ _
    rw [inv_modularJ_sub_slash_mo1973_16294]
    exact Filter.ZeroAtFilter.boundedAtFilter (inv_modularJ_sub_tendsto c)

theorem SpecialPeriods.modularJ_surjective : Function.Surjective modularJ := by
  intro c
  by_contra h
  have hc : ∀ z : ℍ, modularJ z ≠ c := fun z hz => h ⟨z, hz⟩
  let f := omittedValueModularForm_mo1973_16295 c hc
  obtain ⟨a, ha⟩ := ModularFormClass.levelOne_weight_zero_const f
  have hlim : Filter.Tendsto (fun _ : ℍ => a) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ)) := by
    change Filter.Tendsto (Function.const ℍ a) UpperHalfPlane.atImInfty (𝓝 (0 : ℂ))
    rw [← ha]
    exact inv_modularJ_sub_tendsto c
  have ha₀ : a = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hz : (modularJ UpperHalfPlane.I - c)⁻¹ = 0 := by
    have he := congr_fun ha UpperHalfPlane.I
    change (modularJ UpperHalfPlane.I - c)⁻¹ = a at he
    exact he.trans ha₀
  exact inv_ne_zero (sub_ne_zero.mpr (hc UpperHalfPlane.I)) hz

theorem SpecialPeriods.modularJ_eventually_ne (c : ℂ) (z : ℍ) : ∀ᶠ w in 𝓝[≠] z, modularJ w ≠ c := by
  by_contra h
  have hfreq : ∃ᶠ w in 𝓝[≠] z, modularJ w = c := by
    simpa only [Classical.not_not] using (Filter.not_eventually.mp h)
  have hzero : (fun w : ℍ => modularJ w - c) = 0 :=
    UpperHalfPlane.eq_zero_of_frequently (modularJ_mdifferentiable.sub mdifferentiable_const)
      (hfreq.mono fun w hw => sub_eq_zero.mpr hw)
  apply modularJ_not_constant
  exact ⟨c, fun w => sub_eq_zero.mp (congr_fun hzero w)⟩

theorem SpecialPeriods.modularJ_preimage_finite_closed_discrete {s : Set ℂ} (hs : s.Finite) :
    IsClosed (modularJ ⁻¹' s) ∧ IsDiscrete (modularJ ⁻¹' s) := by
  rw [isClosed_and_discrete_iff]
  intro z
  rw [Filter.disjoint_principal_right]
  have h : ∀ᶠ w in 𝓝[≠] z, ∀ c ∈ s, modularJ w ≠ c :=
    hs.eventually_all.mpr (fun c _ => modularJ_eventually_ne c z)
  exact h.mono fun w hw hmem => hw (modularJ w) hmem rfl

theorem SpecialPeriods.modularJ_fibre_isClosed (c : ℂ) : IsClosed {z : ℍ | modularJ z = c} :=
  (modularJ_preimage_finite_closed_discrete (Set.finite_singleton c)).1

theorem SpecialPeriods.modularJ_fibre_isDiscrete (c : ℂ) : IsDiscrete {z : ℍ | modularJ z = c} :=
  (modularJ_preimage_finite_closed_discrete (Set.finite_singleton c)).2

theorem SpecialPeriods.modularJ_isOpenMap : IsOpenMap modularJ := by
  have hA : AnalyticOnNhd ℂ (modularJ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact modularJ_analyticAt ⟨z, hz⟩
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hO :=
    (hA.is_constant_or_isOpen hU).resolve_left
      (by
        rintro ⟨c, hc⟩
        apply modularJ_not_constant
        refine ⟨c, fun z => ?_⟩
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hc z z.im_pos)
  intro s hs
  have ho :=
    hO (((↑) : ℍ → ℂ) '' s)
      (by
        rintro _ ⟨z, _, rfl⟩
        exact z.im_pos)
      (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap s hs)
  simpa only [Set.image_image, Function.comp_def, UpperHalfPlane.ofComplex_apply] using ho

private def SpecialPeriods.upperHalfPlaneEuclideanHomeomorph_mo1973_16307 : ℂ ≃ₜ ℍ
    where
  toFun z := ⟨⟨z.re, Real.exp z.im⟩, Real.exp_pos z.im⟩
  invFun z := ⟨z.re, Real.log z.im⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv
    z := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [Real.exp_log z.im_pos]
  continuous_toFun :=
    Continuous.upperHalfPlaneMk
      (Complex.equivRealProdCLM.symm.continuous.comp
        (Complex.continuous_re.prodMk (Real.continuous_exp.comp Complex.continuous_im)))
      (fun z => Real.exp_pos z.im)
  continuous_invFun :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (UpperHalfPlane.continuous_re.prodMk
        (UpperHalfPlane.continuous_im.log (fun z => ne_of_gt z.im_pos)))

theorem SpecialPeriods.upperHalfPlane_compl_isPathConnected_of_countable {s : Set ℍ}
    (hs : s.Countable) : IsPathConnected sᶜ := by
  let e := upperHalfPlaneEuclideanHomeomorph_mo1973_16307
  have h : IsPathConnected (e ⁻¹' s)ᶜ :=
    (hs.preimage e.injective).isPathConnected_compl_of_one_lt_rank (by simp)
  exact e.isPathConnected_preimage.mp h

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleGenerator₁_ne_one : triangleGenerator₁ ≠ 1 := by
  intro h
  have ho := triangleGenerator₁_order
  simp [h] at ho

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleGenerator₂_ne_one : triangleGenerator₂ ≠ 1 := by
  intro h
  have ho := triangleGenerator₂_order
  simp [h] at ho

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_generator₁_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₁ ^ n) z =
      Triangle.generatorOneSL ^ n • z := by
  rw [map_pow, triangleGeometricRepresentation_generator₁]
  exact Triangle.generatorOnePerm_pow_apply n z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_generator₂_pow_apply (n : ℕ) (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₂ ^ n) z =
      Triangle.generatorTwoSL ^ n • z := by
  rw [map_pow, triangleGeometricRepresentation_generator₂]
  exact Triangle.generatorTwoPerm_pow_apply n z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_generator₁_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 3)
    (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₁ ^ n) z = z ↔ z = Triangle.centerOne := by
  rw [triangle_generator₁_pow_apply]
  exact Triangle.generatorOne_pow_fixed_iff n hn hn' z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_generator₂_pow_fixed_iff (n : ℕ) (hn : 0 < n) (hn' : n < 4)
    (z : ℍ) :
    triangleGeometricRepresentation (triangleGenerator₂ ^ n) z = z ↔ z = Triangle.centerTwo := by
  rw [triangle_generator₂_pow_apply]
  exact Triangle.generatorTwo_pow_fixed_iff n hn hn' z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
private theorem SpecialPeriods.triangle_conjugate_fixed_iff_mo1973_16318 (g h : TriangleGroup)
    (z : ℍ) :
    triangleGeometricRepresentation (h * g * h⁻¹) z = z ↔
      triangleGeometricRepresentation g (triangleGeometricRepresentation h⁻¹ z) =
        triangleGeometricRepresentation h⁻¹ z := by
  change (h * g * h⁻¹) • z = z ↔ g • (h⁻¹ • z) = h⁻¹ • z
  constructor
  · intro hz
    simpa only [SemigroupAction.mul_smul, inv_smul_smul] using congrArg (fun x : ℍ => h⁻¹ • x) hz
  · intro hz
    simpa only [SemigroupAction.mul_smul, smul_inv_smul] using congrArg (fun x : ℍ => h • x) hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_conjugate_generator₁_fixed_iff (h : TriangleGroup) (n : ℕ)
    (hn : 0 < n) (hn' : n < 3) (z : ℍ) :
    triangleGeometricRepresentation (h * triangleGenerator₁ ^ n * h⁻¹) z = z ↔
      z = triangleGeometricRepresentation h Triangle.centerOne := by
  rw [triangle_conjugate_fixed_iff_mo1973_16318, triangle_generator₁_pow_fixed_iff n hn hn']
  change h⁻¹ • z = Triangle.centerOne ↔ z = h • Triangle.centerOne
  exact inv_smul_eq_iff

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_conjugate_generator₂_fixed_iff (h : TriangleGroup) (n : ℕ)
    (hn : 0 < n) (hn' : n < 4) (z : ℍ) :
    triangleGeometricRepresentation (h * triangleGenerator₂ ^ n * h⁻¹) z = z ↔
      z = triangleGeometricRepresentation h Triangle.centerTwo := by
  rw [triangle_conjugate_fixed_iff_mo1973_16318, triangle_generator₂_pow_fixed_iff n hn hn']
  change h⁻¹ • z = Triangle.centerTwo ↔ z = h • Triangle.centerTwo
  exact inv_smul_eq_iff

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_centerOne_not_regular :
    Triangle.centerOne ∉ triangleRegularLocus := by
  intro h
  rw [mem_triangleRegularLocus_iff] at h
  exact
    triangleGenerator₁_ne_one
      (h triangleGenerator₁
        ((triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_centerTwo_not_regular :
    Triangle.centerTwo ∉ triangleRegularLocus := by
  intro h
  rw [mem_triangleRegularLocus_iff] at h
  exact
    triangleGenerator₂_ne_one
      (h triangleGenerator₂
        ((triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleEllipticSet : Set ℍ :=
  Set.range (fun g : TriangleGroup => triangleGeometricRepresentation g Triangle.centerOne) ∪
    Set.range (fun g : TriangleGroup => triangleGeometricRepresentation g Triangle.centerTwo)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularLocus_eq_compl_ellipticSet :
    triangleRegularLocus = triangleEllipticSetᶜ := by
  ext z
  constructor
  · intro hz hze
    rcases hze with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact
        triangle_centerOne_not_regular
          ((triangleRegularLocus_invariant g Triangle.centerOne).mp hz)
    · exact
        triangle_centerTwo_not_regular
          ((triangleRegularLocus_invariant g Triangle.centerTwo).mp hz)
  · intro hz g hg
    by_contra hgne
    obtain ⟨h, n, hn, hn', hgh⟩ | ⟨h, n, hn, hn', hgh⟩ :=
      triangle_nontrivial_isOfFinOrder_eq_conjugate_generator_power g
        (triangle_isOfFinOrder_of_fixed g z hg) hgne
    · rw [hgh] at hg
      exact hz (Or.inl ⟨h, ((triangle_conjugate_generator₁_fixed_iff h n hn hn' z).mp hg).symm⟩)
    · rw [hgh] at hg
      exact hz (Or.inr ⟨h, ((triangle_conjugate_generator₂_fixed_iff h n hn hn' z).mp hg).symm⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangle_orbit_inter_compact_finite (a : ℍ) {K : Set ℍ}
    (hK : IsCompact K) :
    (Set.range (fun g : TriangleGroup => triangleGeometricRepresentation g a) ∩ K).Finite := by
  have hf : {g : TriangleGroup | triangleGeometricRepresentation g a ∈ K}.Finite := by
    simpa only [Set.image_singleton, Set.singleton_inter_nonempty,
      triangleGeometricAction_smul] using
      (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := TriangleGroup)
        (isCompact_singleton (x := a)) hK)
  convert hf.image (fun g : TriangleGroup => triangleGeometricRepresentation g a) using 1
  ext z
  constructor
  · rintro ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleEllipticSet_inter_compact_finite {K : Set ℍ} (hK : IsCompact K) :
    (triangleEllipticSet ∩ K).Finite := by
  rw [triangleEllipticSet, Set.union_inter_distrib_right]
  exact
    (triangle_orbit_inter_compact_finite Triangle.centerOne hK).union
      (triangle_orbit_inter_compact_finite Triangle.centerTwo hK)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleEllipticSet_closed_discrete :
    IsClosed triangleEllipticSet ∧ IsDiscrete triangleEllipticSet := by
  rw [isClosed_and_discrete_iff]
  intro z
  obtain ⟨K, hK, hKz⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds z
  have hf := triangleEllipticSet_inter_compact_finite hK
  have hf' : ((triangleEllipticSet ∩ K) ∩ ({ z } : Set ℍ)ᶜ).Finite :=
    hf.subset Set.inter_subset_left
  have hU : ((triangleEllipticSet ∩ K) ∩ ({ z } : Set ℍ)ᶜ)ᶜ ∈ 𝓝 z :=
    hf'.isClosed.isOpen_compl.mem_nhds (by simp)
  rw [Filter.disjoint_principal_right]
  filter_upwards [nhdsWithin_le_nhds hKz, nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hyK
    hyU hyz
  intro hyE
  exact hyU ⟨⟨hyE, hyK⟩, hyz⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleEllipticSet_isDiscrete : IsDiscrete triangleEllipticSet :=
  triangleEllipticSet_closed_discrete.2

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleEllipticSet_countable : triangleEllipticSet.Countable :=
  (HereditarilyLindelofSpace.isLindelof triangleEllipticSet).countable_of_isDiscrete
    triangleEllipticSet_isDiscrete

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularLocus_isPathConnected :
    IsPathConnected triangleRegularLocus := by
  rw [triangleRegularLocus_eq_compl_ellipticSet]
  exact upperHalfPlane_compl_isPathConnected_of_countable triangleEllipticSet_countable

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularPoint_pathConnected :
    PathConnectedSpace TriangleRegularPoint :=
  isPathConnected_iff_pathConnectedSpace.mp triangleRegularLocus_isPathConnected

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
instance SpecialPeriods.triangleRegularQuotient_pathConnected :
    PathConnectedSpace TriangleRegularQuotient :=
  triangleRegularProject_surjective.pathConnectedSpace triangleRegularProject_covering.continuous

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleRegularToOrbit : TriangleRegularQuotient → TriangleOrbitSpace :=
  Quotient.lift (fun z : TriangleRegularPoint => triangleOrbitProjection z.val) fun x y h =>
    by
    obtain ⟨g, hg⟩ := h
    apply (triangleOrbitProjection_eq_iff _ _).mpr
    exact ⟨g, congrArg Subtype.val hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.triangleRegularToOrbit_project (z : TriangleRegularPoint) :
    triangleRegularToOrbit (triangleRegularProject z) = triangleOrbitProjection z.val :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularToOrbit_continuous : Continuous triangleRegularToOrbit :=
  (triangleOrbitProjection_continuous.comp continuous_subtype_val).quotient_lift _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularToOrbit_injective :
    Function.Injective triangleRegularToOrbit := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp hab
  apply Quotient.sound
  exact ⟨g, Subtype.ext hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularToOrbit_isOpenMap : IsOpenMap triangleRegularToOrbit :=
  IsOpenMap.of_comp triangleRegularProject_covering.continuous triangleRegularProject_surjective
    (triangleOrbitProjection_isOpenMap.comp triangleRegularDomain.isOpen.isOpenMap_subtype_val)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularToOrbit_isOpenEmbedding :
    Topology.IsOpenEmbedding triangleRegularToOrbit :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap triangleRegularToOrbit_continuous
    triangleRegularToOrbit_injective triangleRegularToOrbit_isOpenMap

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleRegularToOrbit_range :
    Set.range triangleRegularToOrbit = triangleOrbitProjection '' triangleRegularLocus := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := triangleRegularProject_surjective y
    exact ⟨z.val, z.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨triangleRegularProject ⟨z, hz⟩, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleOrbitRegularDomain : TopologicalSpace.Opens TriangleOrbitSpace :=
  ⟨Set.range triangleRegularToOrbit, triangleRegularToOrbit_isOpenEmbedding.isOpen_range⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff (z : ℍ) :
    triangleOrbitProjection z ∈ triangleOrbitRegularDomain ↔ z ∈ triangleRegularLocus := by
  change triangleOrbitProjection z ∈ Set.range triangleRegularToOrbit ↔ _
  rw [triangleRegularToOrbit_range]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp he
    exact (triangleRegularLocus_invariant g z).mp (hg ▸ hw)
  · intro hz
    exact ⟨z, hz, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.triangleOrbitRegularDomain_mem_iff (x : TriangleOrbitSpace) :
    x ∈ triangleOrbitRegularDomain ↔ x ≠ triangleOrbitCenterOne ∧ x ≠ triangleOrbitCenterTwo := by
  obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective x
  rw [triangleOrbitProjection_mem_regularDomain_iff, triangleRegularLocus_eq_compl_ellipticSet]
  simp only [triangleEllipticSet, Set.mem_compl_iff, Set.mem_union, Set.mem_range, not_or, ne_eq,
    triangleOrbitCenterOne, triangleOrbitCenterTwo, triangleOrbitProjection_eq_iff]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleRegularOrbitHomeomorph :
    TriangleRegularQuotient ≃ₜ triangleOrbitRegularDomain :=
  triangleRegularToOrbit_isOpenEmbedding.toIsEmbedding.toHomeomorph

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.triangleRegularOrbitParametrization :
    OpenPartialHomeomorph TriangleRegularQuotient TriangleOrbitSpace :=
  triangleRegularToOrbit_isOpenEmbedding.toOpenPartialHomeomorph triangleRegularToOrbit

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.triangleRegularOrbitParametrization_target :
    triangleRegularOrbitParametrization.target =
      (triangleOrbitRegularDomain : Set TriangleOrbitSpace) := by
  simp [triangleRegularOrbitParametrization, triangleOrbitRegularDomain]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.triangleRegularOrbitParametrization_symm_apply
    (x : TriangleRegularQuotient) :
    triangleRegularOrbitParametrization.symm (triangleRegularToOrbit x) = x :=
  triangleRegularOrbitParametrization.left_inv (Set.mem_univ x)

theorem SpecialPeriods.Triangle.horodisc_subset_triangleRegularLocus (Y : ℝ) (hY : width ≤ Y) :
    (horodisc Y : Set ℍ) ⊆ SpecialPeriods.triangleRegularLocus := by
  intro z hz
  apply (SpecialPeriods.mem_triangleRegularLocus_iff z).mpr
  intro g hg
  have hgC := triangle_horodisc_overlap_mem_cusp Y hY g ⟨z, ⟨z, hz, hg⟩, hz⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgC
  have hfixed :
    SpecialPeriods.triangleGeometricRepresentation (SpecialPeriods.triangleCuspGenerator ^ n) z =
      z := by
    rw [hn]
    exact hg
  have hzero :
    SpecialPeriods.triangleGeometricRepresentation
        (SpecialPeriods.triangleCuspGenerator ^ (0 : ℤ)) z =
      z := by simp
  have hn0 :=
    SpecialPeriods.triangleGeometricRepresentation_cusp_orbit_injective z
      (hfixed.trans hzero.symm)
  rw [← hn, hn0, zpow_zero]

theorem SpecialPeriods.Triangle.cuspImage_subset_regularDomain (Y : ℝ) (hY : width ≤ Y) :
    (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) ⊆
      SpecialPeriods.triangleOrbitRegularDomain := by
  rintro q ⟨z, hz, rfl⟩
  exact
    (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mpr
      (horodisc_subset_triangleRegularLocus Y hY hz)

theorem SpecialPeriods.exists_analytic_openPartialHomeomorph {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hderiv : deriv f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      x ∈ e.source ∧
        (∀ z, e z = f z) ∧ AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target := by
  let e₀ : OpenPartialHomeomorph ℂ ℂ :=
    (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph f
  have hx : x ∈ e₀.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hi : AnalyticAt ℂ e₀.symm (f x) := hf.analyticAt_localInverse hderiv
  let e₁ := e₀.restrOpen {z | AnalyticAt ℂ f z} (isOpen_analyticAt ℂ f)
  let e := (e₁.symm.restrOpen {z | AnalyticAt ℂ e₀.symm z} (isOpen_analyticAt ℂ e₀.symm)).symm
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (x ∈ e₀.source ∧ AnalyticAt ℂ f x) ∧ AnalyticAt ℂ e₀.symm (f x)
    exact ⟨⟨hx, hf⟩, hi⟩
  · intro z
    rfl
  · intro z hz
    change AnalyticAt ℂ f z
    exact hz.1.2
  · intro z hz
    change AnalyticAt ℂ e₀.symm z
    exact hz.2

private theorem SpecialPeriods.Triangle.upperHalfPlaneCoe_isLocalDiffeomorph_mo1973_16358 :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (UpperHalfPlane.coe : ℍ → ℂ) := by
  let Φ : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℂ ω :=
    { toPartialEquiv := UpperHalfPlane.ofComplex.symm.toPartialEquiv
      open_source := UpperHalfPlane.ofComplex.symm.open_source
      open_target := UpperHalfPlane.ofComplex.symm.open_target
      contMDiffOn_toFun := UpperHalfPlane.contMDiff_coe.contMDiffOn
      contMDiffOn_invFun := by
        intro w hw
        have he : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w :=
          UpperHalfPlane.ofComplex.left_inv hw
        have hwim : 0 < w.im := by
          rw [← he]
          exact (UpperHalfPlane.ofComplex w).im_pos
        exact (UpperHalfPlane.contMDiffAt_ofComplex hwim).contMDiffWithinAt }
  intro z
  refine ⟨Φ, ?_, fun _ _ => rfl⟩
  exact Set.mem_univ z

private theorem SpecialPeriods.Triangle.cuspQ_coordinate_isLocalDiffeomorphAt_mo1973_16359
    (z : ℍ) : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) := by
  have ha : AnalyticAt ℂ (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
    (UpperHalfPlane.contMDiffAt_iff.mp (cuspQ_holomorphic z)).analyticAt
  obtain ⟨e, hz, he, hforward, hinverse⟩ :=
    SpecialPeriods.exists_analytic_openPartialHomeomorph ha (cuspQ_deriv_ne_zero z)
  refine
    ⟨{  toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := (hforward.contDiffOn e.open_source.uniqueDiffOn).contMDiffOn
        contMDiffOn_invFun := (hinverse.contDiffOn e.open_target.uniqueDiffOn).contMDiffOn }, hz,
      ?_⟩
  intro w _
  exact (he w).symm

theorem SpecialPeriods.Triangle.cuspQ_isLocalDiffeomorph : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω cuspQ :=
  by
  intro z
  have h :=
    (upperHalfPlaneCoe_isLocalDiffeomorph_mo1973_16358 z).comp (K := 𝓘(ℂ)) (P := ℂ)
      (cuspQ_coordinate_isLocalDiffeomorphAt_mo1973_16359 z)
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using h

theorem SpecialPeriods.Triangle.cuspQHorodisc_isLocalDiffeomorph (Y : ℝ) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ) (cuspQ_isLocalDiffeomorph (z : ℍ)) (horodisc Y)
      (puncturedCuspBall Y) (fun w hw => (cuspQ_mem_puncturedCuspBall_iff Y w).mpr hw) z.property

theorem isLocalDiffeomorphAt_of_comp_opensSubtypeVal {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
    (U : TopologicalSpace.Opens M) {f : M → N} (x : U)
    (hf : IsLocalDiffeomorphAt I J ω (f ∘ (Subtype.val : U → M)) x) :
    IsLocalDiffeomorphAt I J ω f (x : M) := by
  obtain ⟨φ, hx, he⟩ := hf
  let e := opensInclusionPartialDiffeomorph I U ⟨x⟩
  have hxU : (x : M) ∈ e.target := by
    change (x : M) ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    change (x : M) ∈ U
    exact x.property
  have hinv : e.symm (x : M) = x := e.left_inv (Set.mem_univ x)
  refine ⟨e.symm.trans φ, ⟨hxU, ?_⟩, ?_⟩
  · change e.symm (x : M) ∈ φ.source
    rw [hinv]
    exact hx
  intro y hy
  have hval : ((e.symm y : U) : M) = y := e.right_inv hy.1
  change f y = φ (e.symm y)
  exact (congrArg f hval.symm).trans (he hy.2)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
theorem SpecialPeriods.instIsManifold1 : IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  triangleRegularQuotient_isManifold

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
def SpecialPeriods.regularFullChart (x : TriangleRegularQuotient) :
    OpenPartialHomeomorph TriangleOrbitSpace ℂ :=
  triangleRegularOrbitParametrization.symm.trans (chartAt ℂ x)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
theorem SpecialPeriods.regularFullChart_mem_source_iff (x : TriangleRegularQuotient)
    (y : TriangleOrbitSpace) :
    y ∈ (regularFullChart x).source ↔
      y ∈ triangleOrbitRegularDomain ∧
        triangleRegularOrbitParametrization.symm y ∈ (chartAt ℂ x).source := by
  change
    (y ∈ triangleRegularOrbitParametrization.target ∧
        triangleRegularOrbitParametrization.symm y ∈ (chartAt ℂ x).source) ↔
      _
  rw [triangleRegularOrbitParametrization_target]
  rfl

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
theorem SpecialPeriods.regularFullChart_source_subset (x : TriangleRegularQuotient) :
    (regularFullChart x).source ⊆ triangleOrbitRegularDomain := fun _ hy =>
  ((regularFullChart_mem_source_iff x _).mp hy).1

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
@[simp]
theorem SpecialPeriods.regularFullChart_apply_inclusion (x y : TriangleRegularQuotient) :
    regularFullChart x (triangleRegularToOrbit y) = chartAt ℂ x y := by
  change chartAt ℂ x (triangleRegularOrbitParametrization.symm (triangleRegularToOrbit y)) = _
  rw [triangleRegularOrbitParametrization_symm_apply]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
@[simp]
theorem SpecialPeriods.regularFullChart_mem_source_inclusion_iff (x y : TriangleRegularQuotient) :
    triangleRegularToOrbit y ∈ (regularFullChart x).source ↔ y ∈ (chartAt ℂ x).source := by
  rw [regularFullChart_mem_source_iff, triangleRegularOrbitParametrization_symm_apply]
  exact and_iff_right ⟨y, rfl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
theorem SpecialPeriods.regularFullChart_mem_source (x : TriangleRegularQuotient) :
    triangleRegularToOrbit x ∈ (regularFullChart x).source :=
  (regularFullChart_mem_source_inclusion_iff x x).mpr (mem_chart_source ℂ x)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
theorem SpecialPeriods.exists_regularFullChart (y : TriangleOrbitSpace)
    (hy : y ∈ triangleOrbitRegularDomain) :
    ∃ x : TriangleRegularQuotient, y ∈ (regularFullChart x).source := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, regularFullChart_mem_source x⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
@[simp]
theorem SpecialPeriods.regularFullChart_projection (x : TriangleRegularQuotient)
    (z : TriangleRegularPoint) :
    regularFullChart x (triangleOrbitProjection z.val) = chartAt ℂ x (triangleRegularProject z) :=
  by rw [← triangleRegularToOrbit_project z, regularFullChart_apply_inclusion]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
def SpecialPeriods.triangleRegularCoordinatePartial (x : TriangleRegularQuotient) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient ℂ ω
    where
  toPartialEquiv := (chartAt ℂ x).toPartialEquiv
  open_source := (chartAt ℂ x).open_source
  open_target := (chartAt ℂ x).open_target
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
theorem SpecialPeriods.regularFullChart_pullback_isLocalDiffeomorphAt
    (x : TriangleRegularQuotient) {z : ℍ}
    (hz : triangleOrbitProjection z ∈ (regularFullChart x).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart x ∘ triangleOrbitProjection) z := by
  have hzreg : z ∈ triangleRegularLocus :=
    (triangleOrbitProjection_mem_regularDomain_iff z).mp (regularFullChart_source_subset x hz)
  let a : TriangleRegularPoint := ⟨z, hzreg⟩
  have hsource : triangleRegularProject a ∈ (chartAt ℂ x).source := by
    apply (regularFullChart_mem_source_inclusion_iff x (triangleRegularProject a)).mp
    simpa only [triangleRegularToOrbit_project] using hz
  have hchart : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x) (triangleRegularProject a) :=
    (triangleRegularCoordinatePartial x).isLocalDiffeomorphAt _ _ _ hsource
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x ∘ triangleRegularProject) a :=
    (triangleRegularProject_isLocalDiffeomorph a).comp (K := 𝓘(ℂ)) (P := ℂ) hchart
  have heq :
    (regularFullChart x ∘ triangleOrbitProjection) ∘ (Subtype.val : TriangleRegularPoint → ℍ) =
      chartAt ℂ x ∘ triangleRegularProject := by
    funext w
    exact regularFullChart_projection x w
  have hrestricted :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      ((regularFullChart x ∘ triangleOrbitProjection) ∘ (Subtype.val : TriangleRegularPoint → ℍ))
      a := by
    rw [heq]
    exact hreg
  exact isLocalDiffeomorphAt_of_comp_opensSubtypeVal 𝓘(ℂ) 𝓘(ℂ) triangleRegularDomain a hrestricted

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold1 in
theorem SpecialPeriods.regularFullChart_pullback_holomorphic (x : TriangleRegularQuotient) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart x ∘ triangleOrbitProjection)
      (triangleOrbitProjection ⁻¹' (regularFullChart x).source) :=
  fun _ hz => (regularFullChart_pullback_isLocalDiffeomorphAt x hz).contMDiffAt.contMDiffWithinAt

theorem SpecialPeriods.CoprodTorsion.coprodI_conjugate_factor {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] {i : ι} (a b : G i) (ha : a ≠ 1) (g : Monoid.CoprodI G)
    (h : g⁻¹ * Monoid.CoprodI.of a * g = Monoid.CoprodI.of b) :
    ∃ c : G i, g = Monoid.CoprodI.of c := by
  classical
  have hb : b ≠ 1 := by
    intro hb
    have he : (Monoid.CoprodI.of a : Monoid.CoprodI G) = 1 := by
      have hh := congrArg (fun x : Monoid.CoprodI G => g * x * g⁻¹) h
      simpa only [hb, map_one, mul_one, one_mul, mul_assoc, mul_inv_cancel, inv_mul_cancel,
        mul_inv_cancel_left] using hh
    apply ha
    apply Monoid.CoprodI.of_injective i
    simpa only [map_one] using he
  let p : Monoid.CoprodI.Word.Pair G i :=
    Monoid.CoprodI.Word.equivPair i (Monoid.CoprodI.Word.equiv g)
  have he : Monoid.CoprodI.Word.rcons p = Monoid.CoprodI.Word.equiv g :=
    (Monoid.CoprodI.Word.equivPair i).symm_apply_apply (Monoid.CoprodI.Word.equiv g)
  have hg : g = Monoid.CoprodI.of p.head * p.tail.prod := by
    calc
      g = (Monoid.CoprodI.Word.equiv g).prod :=
        ((Monoid.CoprodI.Word.equiv (M := G)).symm_apply_apply g).symm
      _ = (Monoid.CoprodI.Word.rcons p).prod := (congrArg Monoid.CoprodI.Word.prod he.symm)
      _ = Monoid.CoprodI.of p.head * p.tail.prod := Monoid.CoprodI.Word.prod_rcons p
  by_cases ht : p.tail = Monoid.CoprodI.Word.empty
  · exact ⟨p.head, by simpa only [ht, Monoid.CoprodI.Word.prod_empty, mul_one] using hg⟩
  · obtain ⟨j, k, w, hw⟩ := Monoid.CoprodI.NeWord.of_word p.tail ht
    have hji : j ≠ i := by
      have hh := p.fstIdx_ne
      rw [← hw] at hh
      simpa only [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.NeWord.toWord,
        Monoid.CoprodI.NeWord.toList_head?, Option.map_some, ne_eq, Option.some.injEq] using hh
    let d : G i := p.head⁻¹ * a * p.head
    have hd : d ≠ 1 := by
      intro hd
      apply ha
      have hh := congrArg (fun x : G i => p.head * x * p.head⁻¹) hd
      simpa only [d, mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one, one_mul,
        mul_inv_cancel_left] using hh
    let v : Monoid.CoprodI.NeWord G k k :=
      Monoid.CoprodI.NeWord.append
        (Monoid.CoprodI.NeWord.append w.inv hji (Monoid.CoprodI.NeWord.singleton d hd)) hji.symm w
    have hgp : g = Monoid.CoprodI.of p.head * w.prod := by
      simpa only [Monoid.CoprodI.NeWord.prod, hw] using hg
    have hv : v.prod = Monoid.CoprodI.of b := by
      rw [hgp] at h
      simpa only [v, Monoid.CoprodI.NeWord.append_prod, Monoid.CoprodI.NeWord.inv_prod,
        Monoid.CoprodI.NeWord.prod_singleton, d, map_mul, map_inv, mul_inv_rev, mul_assoc] using h
    have hvw : v.toWord = (Monoid.CoprodI.NeWord.singleton b hb).toWord := by
      apply word_prod_injective
      exact hv.trans (Monoid.CoprodI.NeWord.prod_singleton b hb).symm
    have hlen := congrArg (fun t : Monoid.CoprodI.Word G => t.toList.length) hvw
    simp only [v, Monoid.CoprodI.NeWord.toWord, Monoid.CoprodI.NeWord.toList, List.length_append,
      List.length_singleton] at hlen
    have hpos : 0 < w.toList.length := List.length_pos_iff.mpr w.toList_ne_nil
    omega

theorem SpecialPeriods.CoprodTorsion.coprodI_commute_of {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] {i : ι} (a : G i) (ha : a ≠ 1) (g : Monoid.CoprodI G)
    (h : Commute (Monoid.CoprodI.of a) g) : ∃ b : G i, g = Monoid.CoprodI.of b := by
  apply coprodI_conjugate_factor a a ha g
  have hh := congrArg (fun x : Monoid.CoprodI G => g⁻¹ * x) h.eq
  simpa only [mul_assoc, inv_mul_cancel_left] using hh

theorem SpecialPeriods.CoprodTorsion.coprod_commute_inl {A B : Type u} [Group A] [Group B] (a : A)
    (ha : a ≠ 1) (g : Monoid.Coprod A B) (h : Commute (Monoid.Coprod.inl a) g) :
    ∃ b : A, g = Monoid.Coprod.inl b := by
  let H : Bool → Type u := fun b => cond b B A
  let : ∀ b, Group (H b) := Bool.rec (inferInstance : Group A) (inferInstance : Group B)
  let toI : Monoid.Coprod A B →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* Monoid.Coprod A B :=
    Monoid.CoprodI.lift fun b =>
      match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · ext b
      simp [toI, fromI]
    · ext b
      simp [toI, fromI]
  have hleft_apply (x : Monoid.Coprod A B) : fromI (toI x) = x := DFunLike.congr_fun hleft x
  have hc : Commute (Monoid.CoprodI.of (i := Bool.false) a) (toI g) := by
    have hh := congrArg toI h.eq
    simpa only [commute_iff_eq, map_mul, toI, Monoid.Coprod.lift_apply_inl] using hh
  obtain ⟨b, hb⟩ := coprodI_commute_of (G := H) (i := Bool.false) a ha (toI g) hc
  refine ⟨b, ?_⟩
  have hh := congrArg fromI hb
  simpa only [hleft_apply, fromI, Monoid.CoprodI.lift_of] using hh

theorem SpecialPeriods.CoprodTorsion.coprod_commute_inr {A B : Type u} [Group A] [Group B] (a : B)
    (ha : a ≠ 1) (g : Monoid.Coprod A B) (h : Commute (Monoid.Coprod.inr a) g) :
    ∃ b : B, g = Monoid.Coprod.inr b := by
  have hc : Commute (Monoid.Coprod.inl a) (Monoid.Coprod.swap A B g) := by
    have hh := congrArg (Monoid.Coprod.swap A B) h.eq
    simpa only [commute_iff_eq, map_mul, Monoid.Coprod.swap_inr] using hh
  obtain ⟨b, hb⟩ := coprod_commute_inl a ha (Monoid.Coprod.swap A B g) hc
  refine ⟨b, ?_⟩
  have hh := congrArg (Monoid.Coprod.swap B A) hb
  simpa only [Monoid.Coprod.swap_swap, Monoid.Coprod.swap_inl] using hh

private theorem SpecialPeriods.cyclic_eq_bounded_generator_pow_mo1973_16380 {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) : ∃ k : ℕ, k < n ∧ a = Multiplicative.ofAdd (1 : ZMod n) ^ k := by
  refine ⟨a.toAdd.val, ZMod.val_lt _, ?_⟩
  change a.toAdd = a.toAdd.val • (1 : ZMod n)
  simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem SpecialPeriods.triangleGenerator₁_commute_eq_pow (g : TriangleGroup)
    (h : Commute triangleGenerator₁ g) : ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  obtain ⟨a, ha⟩ :=
    CoprodTorsion.coprod_commute_inl (Multiplicative.ofAdd (1 : ZMod 3)) (by decide) g h
  obtain ⟨n, hn, rfl⟩ := cyclic_eq_bounded_generator_pow_mo1973_16380 a
  exact ⟨n, hn, by simpa only [map_pow, triangleGenerator₁] using ha⟩

theorem SpecialPeriods.triangleGenerator₂_commute_eq_pow (g : TriangleGroup)
    (h : Commute triangleGenerator₂ g) : ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  obtain ⟨a, ha⟩ :=
    CoprodTorsion.coprod_commute_inr (Multiplicative.ofAdd (1 : ZMod 4)) (by decide) g h
  obtain ⟨n, hn, rfl⟩ := cyclic_eq_bounded_generator_pow_mo1973_16380 a
  exact ⟨n, hn, by simpa only [map_pow, triangleGenerator₂] using ha⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.Triangle.realSLPermutation_commute_of_fixed (A B : SL(2, ℝ)) (a : ℍ)
    (hA : A • a = a) (hB : B • a = a) : Commute (realSLPermutation A) (realSLPermutation B) := by
  apply Equiv.ext
  intro z
  apply (cayleyBiholomorph a).injective
  apply Subtype.ext
  change cayleyCoordinate a (A • (B • z)) = cayleyCoordinate a (B • (A • z))
  rw [cayleyCoordinate_smul A a _ hA, cayleyCoordinate_smul B a _ hB,
    cayleyCoordinate_smul B a _ hB, cayleyCoordinate_smul A a _ hA]
  ring

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangle_commute_of_common_fixed (g h : TriangleGroup) (z : ℍ)
    (hg : triangleGeometricRepresentation g z = z)
    (hh : triangleGeometricRepresentation h z = z) : Commute g h := by
  apply triangleGeometricRepresentation_injective
  rw [map_mul, map_mul]
  obtain ⟨A, hA⟩ := triangleGeometricRepresentation_has_SL_lift g
  obtain ⟨B, hB⟩ := triangleGeometricRepresentation_has_SL_lift h
  have ha : A • z = z := (congrArg (fun f : Equiv.Perm ℍ => f z) hA).trans hg
  have hb : B • z = z := (congrArg (fun f : Equiv.Perm ℍ => f z) hB).trans hh
  simpa only [hA, hB] using (Triangle.realSLPermutation_commute_of_fixed A B z ha hb).eq

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangle_fixed_centerOne_iff (g : TriangleGroup) :
    triangleGeometricRepresentation g Triangle.centerOne = Triangle.centerOne ↔
      ∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n := by
  constructor
  · intro hg
    apply triangleGenerator₁_commute_eq_pow g
    exact
      triangle_commute_of_common_fixed _ _ Triangle.centerOne
        ((triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix) hg
  · rintro ⟨n, hn, rfl⟩
    clear hn
    rw [triangle_generator₁_pow_apply]
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', SemigroupAction.mul_smul, ih, Triangle.generatorOne_fix]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangle_fixed_centerTwo_iff (g : TriangleGroup) :
    triangleGeometricRepresentation g Triangle.centerTwo = Triangle.centerTwo ↔
      ∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n := by
  constructor
  · intro hg
    apply triangleGenerator₂_commute_eq_pow g
    exact
      triangle_commute_of_common_fixed _ _ Triangle.centerTwo
        ((triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix) hg
  · rintro ⟨n, hn, rfl⟩
    clear hn
    rw [triangle_generator₂_pow_apply]
    induction n with
    | zero => simp
    | succ n ih => simp only [pow_succ', SemigroupAction.mul_smul, ih, Triangle.generatorTwo_fix]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangle_stabilizer_centerOne :
    MulAction.stabilizer TriangleGroup Triangle.centerOne = Subgroup.zpowers triangleGenerator₁ :=
  by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, _, rfl⟩ := (triangle_fixed_centerOne_iff g).mp hg
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (triangleGeometricRepresentation_generator₁_apply _).trans Triangle.generatorOne_fix

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangle_stabilizer_centerTwo :
    MulAction.stabilizer TriangleGroup Triangle.centerTwo = Subgroup.zpowers triangleGenerator₂ :=
  by
  apply le_antisymm
  · intro g hg
    obtain ⟨n, _, rfl⟩ := (triangle_fixed_centerTwo_iff g).mp hg
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · apply Subgroup.zpowers_le.mpr
    exact (triangleGeometricRepresentation_generator₂_apply _).trans Triangle.generatorTwo_fix

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo :
    triangleOrbitCenterOne ≠ triangleOrbitCenterTwo := by
  intro he
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff _ _).mp he.symm
  have hfix :
    triangleGeometricRepresentation (g * triangleGenerator₁ * g⁻¹) Triangle.centerTwo =
      Triangle.centerTwo := by
    simpa only [pow_one] using
      (triangle_conjugate_generator₁_fixed_iff g 1 (by norm_num) (by norm_num)
            Triangle.centerTwo).mpr
        hg.symm
  obtain ⟨n, _, hn⟩ := (triangle_fixed_centerTwo_iff _).mp hfix
  have ho : orderOf (g * triangleGenerator₁ * g⁻¹) = 3 := by
    change orderOf ((MulAut.conj g) triangleGenerator₁) = 3
    exact
      (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
            triangleGenerator₁).trans
        triangleGenerator₁_order
  have hd := orderOf_pow_dvd (x := triangleGenerator₂) n
  rw [← hn, ho, triangleGenerator₂_order] at hd
  norm_num at hd

def SpecialPeriods.Triangle.cayleyBall (a : ℍ) (r : ℝ) : TopologicalSpace.Opens ℍ :=
  ⟨{z | ‖cayleyCoordinate a z‖ < r},
    isOpen_lt (cayleyCoordinate_holomorphic a).continuous.norm continuous_const⟩

@[simp]
theorem SpecialPeriods.Triangle.mem_cayleyBall (a z : ℍ) (r : ℝ) :
    z ∈ cayleyBall a r ↔ ‖cayleyCoordinate a z‖ < r :=
  Iff.rfl

@[simp]
theorem SpecialPeriods.Triangle.center_mem_cayleyBall (a : ℍ) (r : ℝ) :
    a ∈ cayleyBall a r ↔ 0 < r := by simp [cayleyBall, cayleyCoordinate]

def SpecialPeriods.Triangle.cayleyBallToDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (z : cayleyBall a r) :
    SpecialPeriods.Disc :=
  ⟨cayleyCoordinate a z / (r : ℂ),
    by
    have hn : ‖cayleyCoordinate a z / (r : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (div_lt_one hr).mpr z.property
    simpa [SpecialPeriods.unitDisc] using hn⟩

@[simp]
theorem SpecialPeriods.Triangle.cayleyBallToDisc_val (a : ℍ) (r : ℝ) (hr : 0 < r)
    (z : cayleyBall a r) : (cayleyBallToDisc a r hr z : ℂ) = cayleyCoordinate a z / (r : ℂ) :=
  rfl

def SpecialPeriods.Triangle.cayleyBallDiscScale (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : SpecialPeriods.Disc :=
  ⟨(r : ℂ) * z,
    by
    have hn : ‖(r : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_lt_of_lt_one_right hr (SpecialPeriods.disc_norm_lt_one z)).trans_le hr1
    simpa [SpecialPeriods.unitDisc] using hn⟩

@[simp]
theorem SpecialPeriods.Triangle.cayleyBallDiscScale_val (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : (cayleyBallDiscScale r hr hr1 z : ℂ) = (r : ℂ) * z :=
  rfl

theorem SpecialPeriods.Triangle.cayleyBallDiscScale_norm (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : ‖(cayleyBallDiscScale r hr hr1 z : ℂ)‖ < r := by
  rw [cayleyBallDiscScale_val, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr (SpecialPeriods.disc_norm_lt_one z)

def SpecialPeriods.Triangle.cayleyBallFromDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : SpecialPeriods.Disc) : cayleyBall a r :=
  ⟨fromDisc a (cayleyBallDiscScale r hr hr1 z),
    by
    change ‖(toDisc a (fromDisc a (cayleyBallDiscScale r hr hr1 z)) : ℂ)‖ < r
    rw [toDisc_fromDisc]
    exact cayleyBallDiscScale_norm r hr hr1 z⟩

theorem SpecialPeriods.Triangle.cayleyBallFromDisc_toDisc (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : cayleyBall a r) :
    cayleyBallFromDisc a r hr hr1 (cayleyBallToDisc a r hr z) = z := by
  apply Subtype.ext
  change fromDisc a (cayleyBallDiscScale r hr hr1 (cayleyBallToDisc a r hr z)) = z
  have he : cayleyBallDiscScale r hr hr1 (cayleyBallToDisc a r hr z) = toDisc a z := by
    apply Subtype.ext
    simp only [cayleyBallDiscScale_val, cayleyBallToDisc_val, toDisc_val]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')
  rw [he, fromDisc_toDisc]

theorem SpecialPeriods.Triangle.cayleyBallToDisc_fromDisc (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : SpecialPeriods.Disc) :
    cayleyBallToDisc a r hr (cayleyBallFromDisc a r hr hr1 z) = z := by
  apply Subtype.ext
  change (toDisc a (fromDisc a (cayleyBallDiscScale r hr hr1 z)) : ℂ) / (r : ℂ) = z
  rw [toDisc_fromDisc, cayleyBallDiscScale_val]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')

theorem SpecialPeriods.Triangle.cayleyBallToDisc_holomorphic (a : ℍ) (r : ℝ) (hr : 0 < r) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallToDisc a r hr) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : cayleyBall a r => cayleyCoordinate a z / (r : ℂ)) :=
    ((cayleyCoordinate_holomorphic a).comp contMDiff_subtype_val).div₀ contMDiff_const
      (fun _ => Complex.ofReal_ne_zero.mpr hr.ne')
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

theorem SpecialPeriods.Triangle.cayleyBallDiscScale_holomorphic (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallDiscScale r hr hr1) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : SpecialPeriods.Disc => (r : ℂ) * z) :=
    contMDiff_const.mul contMDiff_subtype_val
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

theorem SpecialPeriods.Triangle.cayleyBallFromDisc_holomorphic (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallFromDisc a r hr hr1) := by
  have hc := (fromDisc_holomorphic a).comp (cayleyBallDiscScale_holomorphic r hr hr1)
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

def SpecialPeriods.Triangle.cayleyBallBiholomorph (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (cayleyBall a r) SpecialPeriods.Disc ω
    where
  toFun := cayleyBallToDisc a r hr
  invFun := cayleyBallFromDisc a r hr hr1
  left_inv := cayleyBallFromDisc_toDisc a r hr hr1
  right_inv := cayleyBallToDisc_fromDisc a r hr hr1
  contMDiff_toFun := cayleyBallToDisc_holomorphic a r hr
  contMDiff_invFun := cayleyBallFromDisc_holomorphic a r hr hr1

@[simp]
theorem SpecialPeriods.Triangle.cayleyBallToDisc_center (a : ℍ) (r : ℝ) (hr : 0 < r) :
    cayleyBallToDisc a r hr ⟨a, (center_mem_cayleyBall a r).mpr hr⟩ = SpecialPeriods.discZero := by
  apply Subtype.ext
  simp [cayleyBallToDisc_val, cayleyCoordinate]

@[simp]
theorem SpecialPeriods.Triangle.cayleyBallBiholomorph_center (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    cayleyBallBiholomorph a r hr hr1 ⟨a, (center_mem_cayleyBall a r).mpr hr⟩ =
      SpecialPeriods.discZero :=
  cayleyBallToDisc_center a r hr

theorem SpecialPeriods.Triangle.exists_cayleyBall_subset (a : ℍ) {U : Set ℍ} (hU : U ∈ 𝓝 a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (cayleyBall a r : Set ℍ) ⊆ U := by
  have hc : fromDisc a SpecialPeriods.discZero = a := by
    apply UpperHalfPlane.ext
    simp [fromDisc_val]
  have hpre : fromDisc a ⁻¹' U ∈ 𝓝 SpecialPeriods.discZero :=
    (fromDisc_holomorphic a).continuous.continuousAt.preimage_mem_nhds (by simpa [hc] using hU)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨Min.min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hm : toDisc a z ∈ Metric.ball SpecialPeriods.discZero r := by
    change Dist.dist (toDisc a z : ℂ) (SpecialPeriods.discZero : ℂ) < r
    rw [toDisc_val, SpecialPeriods.discZero_val, dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  simpa only [Set.mem_preimage, fromDisc_toDisc] using hsub hm

theorem SpecialPeriods.Triangle.smul_mem_cayleyBall_iff (g : SL(2, ℝ)) (a z : ℍ) (r : ℝ)
    (hfix : g • a = a) : g • z ∈ cayleyBall a r ↔ z ∈ cayleyBall a r := by
  simp only [mem_cayleyBall, cayleyCoordinate_smul g a z hfix, norm_mul,
    slMultiplier_norm g a hfix, one_mul]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticOtherKind : Elliptic.Kind → Elliptic.Kind
  | .three => .four
  | .four => .three

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticCenter : Elliptic.Kind → ℍ
  | .three => centerOne
  | .four => centerTwo

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticGenerator : Elliptic.Kind → SpecialPeriods.TriangleGroup
  | .three => SpecialPeriods.triangleGenerator₁
  | .four => SpecialPeriods.triangleGenerator₂

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticGeneratorSL : Elliptic.Kind → SL(2, ℝ)
  | .three => generatorOneSL
  | .four => generatorTwoSL

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticGenerator_smul (j : Elliptic.Kind) (z : ℍ) :
    ellipticGenerator j • z = ellipticGeneratorSL j • z := by
  cases j
  · exact SpecialPeriods.triangleGeometricRepresentation_generator₁_apply z
  · exact SpecialPeriods.triangleGeometricRepresentation_generator₂_apply z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticGeneratorSL_fixed (j : Elliptic.Kind) :
    ellipticGeneratorSL j • ellipticCenter j = ellipticCenter j := by
  cases j
  · exact generatorOne_fix
  · exact generatorTwo_fix

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticOrbitCenter (j : Elliptic.Kind) :
    SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbitProjection (ellipticCenter j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticOrbitCenter_three :
    ellipticOrbitCenter .three = SpecialPeriods.triangleOrbitCenterOne :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticOrbitCenter_four :
    ellipticOrbitCenter .four = SpecialPeriods.triangleOrbitCenterTwo :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticOrbitCenter_ne_other (j : Elliptic.Kind) :
    ellipticOrbitCenter j ≠ ellipticOrbitCenter (ellipticOtherKind j) := by
  cases j
  · exact SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo
  · exact SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo.symm

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticStabilizer (j : Elliptic.Kind) :
    Subgroup SpecialPeriods.TriangleGroup :=
  MulAction.stabilizer SpecialPeriods.TriangleGroup (ellipticCenter j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.mem_ellipticStabilizer_iff (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup) :
    g ∈ ellipticStabilizer j ↔ ∃ n : ℕ, n < j.order ∧ g = ellipticGenerator j ^ n := by
  cases j
  · exact SpecialPeriods.triangle_fixed_centerOne_iff g
  · exact SpecialPeriods.triangle_fixed_centerTwo_iff g

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticStabilizer_eq_zpowers (j : Elliptic.Kind) :
    ellipticStabilizer j = Subgroup.zpowers (ellipticGenerator j) := by
  cases j
  · exact SpecialPeriods.triangle_stabilizer_centerOne
  · exact SpecialPeriods.triangle_stabilizer_centerTwo

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticGenerator_mem_stabilizer (j : Elliptic.Kind) :
    ellipticGenerator j ∈ ellipticStabilizer j := by
  change ellipticGenerator j • ellipticCenter j = ellipticCenter j
  rw [ellipticGenerator_smul, ellipticGeneratorSL_fixed]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticStabilizerGenerator (j : Elliptic.Kind) :
    ellipticStabilizer j :=
  ⟨ellipticGenerator j, ellipticGenerator_mem_stabilizer j⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticStabilizerGenerator_val (j : Elliptic.Kind) :
    (ellipticStabilizerGenerator j : SpecialPeriods.TriangleGroup) = ellipticGenerator j :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticStabilizer_eq_generator_pow (j : Elliptic.Kind)
    (g : ellipticStabilizer j) : ∃ n : ℕ, n < j.order ∧ g = ellipticStabilizerGenerator j ^ n := by
  obtain ⟨n, hn, hg⟩ := (mem_ellipticStabilizer_iff j g).mp g.property
  exact ⟨n, hn, Subtype.ext hg⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticOtherOrbitComplement (j : Elliptic.Kind) :
    TopologicalSpace.Opens ℍ :=
  ⟨{z | SpecialPeriods.triangleOrbitProjection z ≠ ellipticOrbitCenter (ellipticOtherKind j)},
    isOpen_ne_fun SpecialPeriods.triangleOrbitProjection_continuous continuous_const⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticCenter_mem_otherOrbitComplement (j : Elliptic.Kind) :
    ellipticCenter j ∈ ellipticOtherOrbitComplement j :=
  ellipticOrbitCenter_ne_other j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.exists_ellipticNeighborhoodRadius (j : Elliptic.Kind) :
    ∃ r : ℝ,
      0 < r ∧
        r ≤ 1 ∧
          (∀ g : SpecialPeriods.TriangleGroup,
              (((g • ·) '' (cayleyBall (ellipticCenter j) r : Set ℍ)) ∩
                    cayleyBall (ellipticCenter j) r).Nonempty →
                g ∈ ellipticStabilizer j) ∧
            (cayleyBall (ellipticCenter j) r : Set ℍ) ⊆ ellipticOtherOrbitComplement j := by
  obtain ⟨U, hU, hret⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self SpecialPeriods.TriangleGroup
      (ellipticCenter j)
  have hV :=
    (ellipticOtherOrbitComplement j).isOpen.mem_nhds (ellipticCenter_mem_otherOrbitComplement j)
  obtain ⟨r, hr, hr1, hball⟩ :=
    exists_cayleyBall_subset (ellipticCenter j) (Filter.inter_mem hU hV)
  refine ⟨r, hr, hr1, ?_, fun z hz => (hball hz).2⟩
  intro g hg
  obtain ⟨z, ⟨w, hw, hgw⟩, hz⟩ := hg
  exact hret g ⟨z, ⟨w, (hball hw).1, hgw⟩, (hball hz).1⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticNeighborhoodRadius (j : Elliptic.Kind) : ℝ :=
  (exists_ellipticNeighborhoodRadius j).choose

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhoodRadius_pos (j : Elliptic.Kind) :
    0 < ellipticNeighborhoodRadius j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.1

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhoodRadius_le_one (j : Elliptic.Kind) :
    ellipticNeighborhoodRadius j ≤ 1 :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.1

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticNeighborhood (j : Elliptic.Kind) : TopologicalSpace.Opens ℍ :=
  cayleyBall (ellipticCenter j) (ellipticNeighborhoodRadius j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticCenter_mem_neighborhood (j : Elliptic.Kind) :
    ellipticCenter j ∈ ellipticNeighborhood j :=
  (center_mem_cayleyBall _ _).mpr (ellipticNeighborhoodRadius_pos j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_mem_nhds (j : Elliptic.Kind) :
    (ellipticNeighborhood j : Set ℍ) ∈ 𝓝 (ellipticCenter j) :=
  (ellipticNeighborhood j).isOpen.mem_nhds (ellipticCenter_mem_neighborhood j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_return (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup)
    (hret : (((g • ·) '' (ellipticNeighborhood j : Set ℍ)) ∩ ellipticNeighborhood j).Nonempty) :
    g ∈ ellipticStabilizer j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.2.1 g hret

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_subset_otherOrbitComplement
    (j : Elliptic.Kind) : (ellipticNeighborhood j : Set ℍ) ⊆ ellipticOtherOrbitComplement j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.2.2

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_avoids_other (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ ellipticNeighborhood j) :
    SpecialPeriods.triangleOrbitProjection z ≠ ellipticOrbitCenter (ellipticOtherKind j) :=
  ellipticNeighborhood_subset_otherOrbitComplement j hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticStabilizer_cayleyBall_invariant (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (r : ℝ) (z : ℍ) :
    (g : SpecialPeriods.TriangleGroup) • z ∈ cayleyBall (ellipticCenter j) r ↔
      z ∈ cayleyBall (ellipticCenter j) r := by
  have hfix :
    (SpecialPeriods.triangleMatrixLift g : SL(2, ℝ)) • ellipticCenter j = ellipticCenter j :=
    (SpecialPeriods.triangleMatrixLift_smul g _).trans g.property
  rw [← SpecialPeriods.triangleMatrixLift_smul]
  exact smul_mem_cayleyBall_iff (SpecialPeriods.triangleMatrixLift g) (ellipticCenter j) z r hfix

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_invariant (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (z : ℍ) :
    (g : SpecialPeriods.TriangleGroup) • z ∈ ellipticNeighborhood j ↔
      z ∈ ellipticNeighborhood j :=
  ellipticStabilizer_cayleyBall_invariant j g _ z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_mapsTo (j : Elliptic.Kind)
    (g : ellipticStabilizer j) :
    Set.MapsTo (fun z : ℍ => (g : SpecialPeriods.TriangleGroup) • z) (ellipticNeighborhood j)
      (ellipticNeighborhood j) :=
  fun z hz => (ellipticNeighborhood_invariant j g z).mpr hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[instance_reducible]
def SpecialPeriods.Triangle.ellipticNeighborhoodAction (j : Elliptic.Kind) :
    MulAction (ellipticStabilizer j) (ellipticNeighborhood j) :=
  LocalOrbitQuotient.restrictedAction (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticNeighborhood_smul_val (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ((g • z : ellipticNeighborhood j) : ℍ) = (g : SpecialPeriods.TriangleGroup) • (z : ℍ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticNeighborhoodCenter (j : Elliptic.Kind) :
    ellipticNeighborhood j :=
  ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticNeighborhoodChart (j : Elliptic.Kind) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (ellipticNeighborhood j) SpecialPeriods.Disc ω :=
  cayleyBallBiholomorph (ellipticCenter j) (ellipticNeighborhoodRadius j)
    (ellipticNeighborhoodRadius_pos j) (ellipticNeighborhoodRadius_le_one j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticNeighborhoodChart_val (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    (ellipticNeighborhoodChart j z : ℂ) =
      cayleyCoordinate (ellipticCenter j) z / (ellipticNeighborhoodRadius j : ℂ) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticNeighborhoodChart_center (j : Elliptic.Kind) :
    ellipticNeighborhoodChart j (ellipticNeighborhoodCenter j) = SpecialPeriods.discZero :=
  cayleyBallBiholomorph_center _ _ _ _

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhoodChart_generator (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) =
      Elliptic.familyRotation j (ellipticNeighborhoodChart j z) := by
  let := ellipticNeighborhoodAction j
  apply Subtype.ext
  change
    cayleyCoordinate (ellipticCenter j) (ellipticGenerator j • (z : ℍ)) /
        (ellipticNeighborhoodRadius j : ℂ) =
      _
  rw [ellipticGenerator_smul]
  cases j
  · change
      cayleyCoordinate centerOne (generatorOneSL • (z : ℍ)) /
          (ellipticNeighborhoodRadius .three : ℂ) =
        -SpecialPeriods.rho *
          (cayleyCoordinate centerOne z / (ellipticNeighborhoodRadius .three : ℂ))
    rw [generatorOne_cayley, mul_div_assoc]
  · change
      cayleyCoordinate centerTwo (generatorTwoSL • (z : ℍ)) /
          (ellipticNeighborhoodRadius .four : ℂ) =
        -Complex.I * (cayleyCoordinate centerTwo z / (ellipticNeighborhoodRadius .four : ℂ))
    rw [generatorTwo_cayley, mul_div_assoc]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticNeighborhood_projection_eq_center_iff (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    SpecialPeriods.triangleOrbitProjection z = ellipticOrbitCenter j ↔
      z = ellipticNeighborhoodCenter j := by
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff z (ellipticCenter j)).mp hz
    have hgH : g ∈ ellipticStabilizer j :=
      ellipticNeighborhood_return j g
        ⟨z, ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, hg⟩, z.property⟩
    apply Subtype.ext
    exact hg.symm.trans hgH
  · rintro rfl
    rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
abbrev SpecialPeriods.Triangle.EllipticNeighborhoodQuotient (j : Elliptic.Kind) :=
  LocalOrbitQuotient.LocalQuotient (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticNeighborhoodImage (j : Elliptic.Kind) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  LocalOrbitQuotient.imageOpen (G := SpecialPeriods.TriangleGroup) (ellipticNeighborhood j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticNeighborhoodQuotientHomeomorph (j : Elliptic.Kind) :
    EllipticNeighborhoodQuotient j ≃ₜ ellipticNeighborhoodImage j :=
  LocalOrbitQuotient.localHomeomorph (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j) (ellipticNeighborhood_return j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ ellipticNeighborhoodImage j :=
  ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticOtherOrbitCenter_not_mem_neighborhoodImage
    (j : Elliptic.Kind) :
    ellipticOrbitCenter (ellipticOtherKind j) ∉ ellipticNeighborhoodImage j := by
  rintro ⟨z, hz, he⟩
  exact ellipticNeighborhood_avoids_other j z hz he

theorem Elliptic.discPower_eq_iff_scalar_iterate (m : ℕ) (hm : 0 < m) (c : ℂ) (hc : ‖c‖ = 1)
    (hroot : IsPrimitiveRoot c m) (z w : SpecialPeriods.Disc) :
    discPower m hm z = discPower m hm w ↔ ∃ r < m, (SpecialPeriods.discScalar c hc)^[r] w = z := by
  let : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro he
    have hp : (z : ℂ) ^ m = (w : ℂ) ^ m := congrArg Subtype.val he
    by_cases hw : (w : ℂ) = 0
    · have hz : (z : ℂ) = 0 :=
        (pow_eq_zero_iff hm.ne').mp (by simpa only [hw, zero_pow hm.ne'] using hp)
      exact ⟨0, hm, Subtype.ext (hw.trans hz.symm)⟩
    · have hr : ((z : ℂ) / (w : ℂ)) ^ m = 1 := by rw [div_pow, hp, div_self (pow_ne_zero m hw)]
      obtain ⟨r, hrm, hr⟩ := hroot.eq_pow_of_pow_eq_one hr
      refine ⟨r, hrm, Subtype.ext ?_⟩
      rw [SpecialPeriods.discScalar_iterate_val, hr, div_mul_cancel₀ _ hw]
  · rintro ⟨r, _, rfl⟩
    apply Subtype.ext
    change ((SpecialPeriods.discScalar c hc)^[r] w : ℂ) ^ m = (w : ℂ) ^ m
    rw [SpecialPeriods.discScalar_iterate_val, mul_pow, ← pow_mul, Nat.mul_comm r m, pow_mul,
      hroot.pow_eq_one, one_pow, one_mul]

theorem Elliptic.neg_rho_isPrimitiveRoot : IsPrimitiveRoot (-SpecialPeriods.rho) 3 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide)
  · calc
      (-SpecialPeriods.rho) ^ 3 = -(SpecialPeriods.rho ^ 3) := by ring
      _ = 1 := by rw [SpecialPeriods.rho_cube]; norm_num
  · exact fun r hr hrm => SpecialPeriods.neg_rho_pow_ne_one hr hrm

theorem Elliptic.discPower_three_eq_iff (z w : SpecialPeriods.Disc) :
    discPower 3 (by decide) z = discPower 3 (by decide) w ↔
      ∃ r < 3, SpecialPeriods.discRotateThree^[r] w = z :=
  discPower_eq_iff_scalar_iterate 3 (by decide) (-SpecialPeriods.rho)
    (by simpa using SpecialPeriods.norm_rho) neg_rho_isPrimitiveRoot z w

theorem Elliptic.discPower_four_eq_iff (z w : SpecialPeriods.Disc) :
    discPower 4 (by decide) z = discPower 4 (by decide) w ↔
      ∃ r < 4, SpecialPeriods.discRotateFour^[r] w = z :=
  discPower_eq_iff_scalar_iterate 4 (by decide) (-Complex.I) (by simp)
    Complex.isPrimitiveRoot_neg_I z w

theorem Elliptic.discPower_eq_iff_familyRotation (j : Kind) (z w : SpecialPeriods.Disc) :
    discPower j.order j.order_pos z = discPower j.order j.order_pos w ↔
      ∃ r < j.order, (familyRotation j)^[r] w = z := by
  cases j
  · exact discPower_three_eq_iff z w
  · exact discPower_four_eq_iff z w

theorem Elliptic.complexPower_hasDerivAt (m : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ m) ((m : ℂ) * z ^ (m - 1)) z :=
  hasDerivAt_pow m z

theorem SpecialPeriods.TriangleQuotientPower.discPower_isOpenMap (m : ℕ) (hm : 0 < m) :
    IsOpenMap (Elliptic.discPower m hm) := by
  let : NeZero m := ⟨hm.ne'⟩
  have h : IsOpenMap (fun z : SpecialPeriods.Disc => (z : ℂ) ^ m) :=
    (Complex.isOpenQuotientMap_pow m).isOpenMap.comp
      SpecialPeriods.unitDisc.isOpen.isOpenMap_subtype_val
  exact h.subtype_mk _

theorem SpecialPeriods.TriangleQuotientPower.map_pow_smul {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) (n : ℕ) (y : Y) :
    e ((a ^ n) • y) = (Elliptic.familyRotation j)^[n] (e y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', SemigroupAction.mul_smul, heq, ih, Function.iterate_succ_apply']

theorem SpecialPeriods.TriangleQuotientPower.powerCoordinate_eq_iff_mem_orbit {H Y : Type*}
    [Group H] [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind)
    (e : Y ≃ₜ SpecialPeriods.Disc) (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) (x y : Y) :
    Elliptic.discPower j.order j.order_pos (e x) = Elliptic.discPower j.order j.order_pos (e y) ↔
      x ∈ MulAction.orbit H y := by
  rw [Elliptic.discPower_eq_iff_familyRotation]
  constructor
  · rintro ⟨n, hn, hxy⟩
    refine ⟨a ^ n, ?_⟩
    apply e.injective
    exact (map_pow_smul j e a heq n y).trans hxy
  · rintro ⟨h, hh⟩
    obtain ⟨n, hn, rfl⟩ := hgen h
    exact ⟨n, hn, (map_pow_smul j e a heq n y).symm.trans (congrArg e hh)⟩

def SpecialPeriods.TriangleQuotientPower.orbitDiscMap {H Y : Type*} [Group H] [TopologicalSpace Y]
    [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc) (a : H)
    (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Quotient (MulAction.orbitRel H Y) → SpecialPeriods.Disc :=
  Quotient.lift (fun y => Elliptic.discPower j.order j.order_pos (e y)) fun x y hxy =>
    (powerCoordinate_eq_iff_mem_orbit j e a hgen heq x y).mpr hxy

@[simp]
theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_mk {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) (y : Y) :
    orbitDiscMap j e a hgen heq (Quotient.mk (MulAction.orbitRel H Y) y) =
      Elliptic.discPower j.order j.order_pos (e y) :=
  rfl

theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_continuous {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Continuous (orbitDiscMap j e a hgen heq) :=
  ((Elliptic.discPower_continuous j.order j.order_pos).comp e.continuous).quotient_lift _

theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_surjective {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Function.Surjective (orbitDiscMap j e a hgen heq) := by
  intro z
  obtain ⟨w, hw⟩ := Elliptic.discPower_surjective j.order j.order_pos z
  refine ⟨Quotient.mk (MulAction.orbitRel H Y) (e.symm w), ?_⟩
  simpa only [orbitDiscMap_mk, e.apply_symm_apply] using hw

theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_injective {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Function.Injective (orbitDiscMap j e a hgen heq) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y hxy
  apply Quotient.sound
  exact (powerCoordinate_eq_iff_mem_orbit j e a hgen heq x y).mp hxy

theorem SpecialPeriods.TriangleQuotientPower.orbitDiscMap_isOpenMap {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    IsOpenMap (orbitDiscMap j e a hgen heq) := by
  apply
    IsOpenMap.of_comp
      (show Continuous (Quotient.mk (MulAction.orbitRel H Y)) from continuous_quotient_mk')
      Quotient.mk_surjective
  exact (discPower_isOpenMap j.order j.order_pos).comp e.isOpenMap

def SpecialPeriods.TriangleQuotientPower.orbitDiscHomeomorph {H Y : Type*} [Group H]
    [TopologicalSpace Y] [MulAction H Y] (j : Elliptic.Kind) (e : Y ≃ₜ SpecialPeriods.Disc)
    (a : H) (hgen : ∀ h : H, ∃ n : ℕ, n < j.order ∧ h = a ^ n)
    (heq : ∀ y : Y, e (a • y) = Elliptic.familyRotation j (e y)) :
    Quotient (MulAction.orbitRel H Y) ≃ₜ SpecialPeriods.Disc :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (orbitDiscMap j e a hgen heq)
      ⟨orbitDiscMap_injective j e a hgen heq, orbitDiscMap_surjective j e a hgen heq⟩)
    (orbitDiscMap_continuous j e a hgen heq) (orbitDiscMap_isOpenMap j e a hgen heq)

theorem SpecialPeriods.Triangle.cayleyCoordinate_eq_zero_iff (a z : ℍ) :
    cayleyCoordinate a z = 0 ↔ z = a := by
  simp [cayleyCoordinate, div_eq_zero_iff, sub_conj_ne_zero a z, sub_eq_zero]

theorem SpecialPeriods.Triangle.cayleyCoordinate_analyticAt (a z : ℍ) :
    AnalyticAt ℂ (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp
        ((cayleyCoordinate_holomorphic a).mdifferentiable (by simp))).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

theorem SpecialPeriods.Triangle.cayleyCoordinate_hasStrictDerivAt_center (a : ℍ) :
    HasStrictDerivAt (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex)
      (1 / ((a : ℂ) - starRingEnd ℂ (a : ℂ))) (a : ℂ) := by
  have hd := sub_conj_ne_zero a a
  have h :
    HasStrictDerivAt (fun z : ℂ => (z - (a : ℂ)) / (z - starRingEnd ℂ (a : ℂ)))
      (1 / ((a : ℂ) - starRingEnd ℂ (a : ℂ))) (a : ℂ) := by
    have hn : HasStrictDerivAt (fun z : ℂ => z - (a : ℂ)) 1 (a : ℂ) :=
      (hasStrictDerivAt_id (a : ℂ)).sub_const (a : ℂ)
    have hd' : HasStrictDerivAt (fun z : ℂ => z - starRingEnd ℂ (a : ℂ)) 1 (a : ℂ) :=
      (hasStrictDerivAt_id (a : ℂ)).sub_const (starRingEnd ℂ (a : ℂ))
    convert hn.div hd' hd using 1
    all_goals
      first
      | rfl
      | (field_simp; ring)
  apply h.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex a.im_pos] with z hz
  change (UpperHalfPlane.ofComplex z : ℂ) = z at hz
  simp only [Function.comp_apply, cayleyCoordinate, hz]

theorem SpecialPeriods.Triangle.cayleyCoordinate_order_center (a : ℍ) :
    analyticOrderAt (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex) (a : ℂ) = 1 := by
  apply (cayleyCoordinate_analyticAt a a).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp [cayleyCoordinate]
  · rw [(cayleyCoordinate_hasStrictDerivAt_center a).hasDerivAt.deriv]
    exact one_div_ne_zero (sub_conj_ne_zero a a)

theorem Elliptic.complexPower_holomorphic (m : ℕ) : ContDiff ℂ ω (fun z : ℂ => z ^ m) :=
  contDiff_id.pow m

theorem Elliptic.complexPower_coefficient_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    (m : ℂ) * z ^ (m - 1) ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hz)

def Elliptic.complexPowerChart (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ :=
  ((complexPower_holomorphic m).contDiffAt.toOpenPartialHomeomorph (fun w : ℂ => w ^ m)
        ((complexPower_hasDerivAt m z).hasFDerivAt_equiv
          (complexPower_coefficient_ne_zero m hm z hz))
        (by simp)).restr
    {w | w ≠ 0}

theorem Elliptic.mem_complexPowerChart_source (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    z ∈ (complexPowerChart m hm z hz).source := by
  have ho : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  rw [complexPowerChart, OpenPartialHomeomorph.restr_source' _ _ ho]
  exact
    ⟨(complexPower_holomorphic m).contDiffAt.mem_toOpenPartialHomeomorph_source
        ((complexPower_hasDerivAt m z).hasFDerivAt_equiv
          (complexPower_coefficient_ne_zero m hm z hz))
        (by simp),
      hz⟩

theorem Elliptic.complexPowerChart_source_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0)
    {w : ℂ} (hw : w ∈ (complexPowerChart m hm z hz).source) : w ≠ 0 := by
  have ho : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  rw [complexPowerChart, OpenPartialHomeomorph.restr_source' _ _ ho] at hw
  exact hw.2

theorem Elliptic.complexPowerChart_holomorphic (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerChart m hm z hz) (complexPowerChart m hm z hz).source :=
  (complexPower_holomorphic m).contDiffOn

theorem Elliptic.complexPowerChart_symm_holomorphic (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerChart m hm z hz).symm (complexPowerChart m hm z hz).target := by
  intro w hw
  have hne :=
    complexPowerChart_source_ne_zero m hm z hz ((complexPowerChart m hm z hz).map_target hw)
  exact
    ((complexPowerChart m hm z hz).contDiffAt_symm hw
        ((complexPower_hasDerivAt m _).hasFDerivAt_equiv
          (complexPower_coefficient_ne_zero m hm _ hne))
        (complexPower_holomorphic m).contDiffAt).contDiffWithinAt

theorem Elliptic.complexPower_isLocalDiffeomorphAt (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun w : ℂ => w ^ m) z := by
  refine
    ⟨{  toPartialEquiv := (complexPowerChart m hm z hz).toPartialEquiv
        open_source := (complexPowerChart m hm z hz).open_source
        open_target := (complexPowerChart m hm z hz).open_target
        contMDiffOn_toFun := (complexPowerChart_holomorphic m hm z hz).contMDiffOn
        contMDiffOn_invFun := (complexPowerChart_symm_holomorphic m hm z hz).contMDiffOn },
      mem_complexPowerChart_source m hm z hz, fun _ _ => rfl⟩

theorem isLocalDiffeomorphAt_congr_of_eventuallyEq {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ F K} {n : ℕ∞ω}
    {f g : M → N} {x : M} (hf : IsLocalDiffeomorphAt I J n f x) (hgf : g =ᶠ[𝓝 x] f) :
    IsLocalDiffeomorphAt I J n g x := by
  obtain ⟨U, hUf, hU, hxU⟩ := mem_nhds_iff.mp hgf
  obtain ⟨Φ, hx, hΦ⟩ := hf
  let Ψ : PartialDiffeomorph I J M N n :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen U hU).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen U hU).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left }
  refine ⟨Ψ, ⟨hx, hxU⟩, ?_⟩
  intro y hy
  exact (hUf hy.2).trans (hΦ hy.1)

def SpecialPeriods.Triangle.complexDivideBiholomorph (c : ℂ) (hc : c ≠ 0) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω where
  toFun z := z / c
  invFun z := z * c
  left_inv z := div_mul_cancel₀ z hc
  right_inv z := mul_div_cancel_right₀ z hc
  contMDiff_toFun := contMDiff_id.div₀ contMDiff_const (fun _ => hc)
  contMDiff_invFun := contMDiff_id.mul contMDiff_const

def SpecialPeriods.Triangle.normalizedCayley (a : ℍ) (r : ℝ) (z : ℍ) : ℂ :=
  cayleyCoordinate a z / (r : ℂ)

theorem SpecialPeriods.Triangle.normalizedCayley_holomorphic (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayley a r) :=
  (cayleyCoordinate_holomorphic a).div₀ contMDiff_const (fun _ => Complex.ofReal_ne_zero.mpr hr)

theorem SpecialPeriods.Triangle.normalizedCayley_isLocalDiffeomorph (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayley a r) := by
  intro z
  have hc :=
    ((cayleyBiholomorph a).isLocalDiffeomorph z).comp (K := 𝓘(ℂ)) (P := ℂ)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) SpecialPeriods.unitDisc (toDisc a z))
  exact
    hc.comp (K := 𝓘(ℂ)) (P := ℂ)
      ((complexDivideBiholomorph (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)).isLocalDiffeomorph
        (cayleyCoordinate a z))

def SpecialPeriods.Triangle.normalizedCayleyBranch (a : ℍ) (r : ℝ) (m : ℕ) (z : ℍ) : ℂ :=
  normalizedCayley a r z ^ m

theorem SpecialPeriods.Triangle.normalizedCayleyBranch_holomorphic (a : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayleyBranch a r m) :=
  (normalizedCayley_holomorphic a r hr).pow m

theorem SpecialPeriods.Triangle.normalizedCayleyBranch_isLocalDiffeomorphAt (a z : ℍ) (r : ℝ)
    (hr : r ≠ 0) (m : ℕ) (hm : 0 < m) (hz : z ≠ a) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (normalizedCayleyBranch a r m) z := by
  have hc : normalizedCayley a r z ≠ 0 :=
    div_ne_zero ((cayleyCoordinate_eq_zero_iff a z).not.mpr hz) (Complex.ofReal_ne_zero.mpr hr)
  exact
    (normalizedCayley_isLocalDiffeomorph a r hr z).comp (K := 𝓘(ℂ)) (P := ℂ)
      (Elliptic.complexPower_isLocalDiffeomorphAt m hm (normalizedCayley a r z) hc)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticLocalDiscHomeomorph (j : Elliptic.Kind) :
    EllipticNeighborhoodQuotient j ≃ₜ SpecialPeriods.Disc := by
  letI := ellipticNeighborhoodAction j
  exact
    SpecialPeriods.TriangleQuotientPower.orbitDiscHomeomorph j
      (ellipticNeighborhoodChart j).toHomeomorph (ellipticStabilizerGenerator j)
      (ellipticStabilizer_eq_generator_pow j) (ellipticNeighborhoodChart_generator j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticLocalDiscHomeomorph_mk (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticLocalDiscHomeomorph j
        (LocalOrbitQuotient.localProjection (ellipticStabilizer j) (ellipticNeighborhood j)
          (ellipticNeighborhood_mapsTo j) z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) :=
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticImageDiscHomeomorph (j : Elliptic.Kind) :
    ellipticNeighborhoodImage j ≃ₜ SpecialPeriods.Disc :=
  (ellipticNeighborhoodQuotientHomeomorph j).symm.trans (ellipticLocalDiscHomeomorph j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticImageDiscHomeomorph_projection (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticImageDiscHomeomorph j
        (LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup)
          (ellipticNeighborhood j) z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := by
  let q :=
    LocalOrbitQuotient.localProjection (ellipticStabilizer j) (ellipticNeighborhood j)
      (ellipticNeighborhood_mapsTo j) z
  have he :
    ellipticNeighborhoodQuotientHomeomorph j q =
      LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup)
        (ellipticNeighborhood j) z :=
    rfl
  change ellipticLocalDiscHomeomorph j ((ellipticNeighborhoodQuotientHomeomorph j).symm _) = _
  rw [← he, Homeomorph.symm_apply_apply]
  exact ellipticLocalDiscHomeomorph_mk j z

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticOrbitParametrization (j : Elliptic.Kind) :
    OpenPartialHomeomorph SpecialPeriods.Disc SpecialPeriods.TriangleOrbitSpace :=
  (ellipticImageDiscHomeomorph j).symm.toOpenPartialHomeomorph.trans
    ((ellipticNeighborhoodImage j).openPartialHomeomorphSubtypeCoe
      ⟨⟨ellipticOrbitCenter j, ellipticOrbitCenter_mem_neighborhoodImage j⟩⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticOrbitParametrization_source (j : Elliptic.Kind) :
    (ellipticOrbitParametrization j).source = Set.univ := by simp [ellipticOrbitParametrization]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticOrbitParametrization_target (j : Elliptic.Kind) :
    (ellipticOrbitParametrization j).target = ellipticNeighborhoodImage j := by
  simp [ellipticOrbitParametrization]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticOrbitParametrization_power (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticOrbitParametrization j
        (Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z)) =
      SpecialPeriods.triangleOrbitProjection z := by
  change
    ((ellipticImageDiscHomeomorph j).symm
          (Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z)) :
        SpecialPeriods.TriangleOrbitSpace) =
      SpecialPeriods.triangleOrbitProjection z
  rw [← ellipticImageDiscHomeomorph_projection j z]
  exact
    congrArg (fun q : ellipticNeighborhoodImage j => (q : SpecialPeriods.TriangleOrbitSpace))
      ((ellipticImageDiscHomeomorph j).symm_apply_apply
        (show ellipticNeighborhoodImage j from
          LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup)
            (ellipticNeighborhood j) z))

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
def SpecialPeriods.Triangle.ellipticFullChart (j : Elliptic.Kind) :
    OpenPartialHomeomorph SpecialPeriods.TriangleOrbitSpace ℂ :=
  (ellipticOrbitParametrization j).symm.trans
    (SpecialPeriods.unitDisc.openPartialHomeomorphSubtypeCoe ⟨SpecialPeriods.discZero⟩)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticFullChart_source (j : Elliptic.Kind) :
    (ellipticFullChart j).source = ellipticNeighborhoodImage j := by simp [ellipticFullChart]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticFullChart_target (j : Elliptic.Kind) :
    (ellipticFullChart j).target = SpecialPeriods.unitDisc := by simp [ellipticFullChart]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_projection (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    ellipticFullChart j (SpecialPeriods.triangleOrbitProjection z) =
      normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order z := by
  have he :
    (ellipticOrbitParametrization j).symm (SpecialPeriods.triangleOrbitProjection z) =
      Elliptic.discPower j.order j.order_pos (ellipticNeighborhoodChart j z) := by
    rw [← ellipticOrbitParametrization_power j z]
    exact (ellipticOrbitParametrization j).left_inv (by simp)
  change
    ((ellipticOrbitParametrization j).symm (SpecialPeriods.triangleOrbitProjection z) : ℂ) = _
  rw [he, Elliptic.discPower_coe, ellipticNeighborhoodChart_val]
  rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_center_mem_source (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ellipticOrbitCenter_mem_neighborhoodImage j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
@[simp]
theorem SpecialPeriods.Triangle.ellipticFullChart_center (j : Elliptic.Kind) :
    ellipticFullChart j (ellipticOrbitCenter j) = 0 := by
  have he := ellipticFullChart_projection j (ellipticNeighborhoodCenter j)
  simpa only [ellipticOrbitCenter, ellipticNeighborhoodCenter, normalizedCayleyBranch,
    normalizedCayley, cayleyCoordinate, sub_self, zero_div, zero_pow j.order_pos.ne'] using he

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_other_not_mem_source (j : Elliptic.Kind) :
    ellipticOrbitCenter (ellipticOtherKind j) ∉ (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ellipticOtherOrbitCenter_not_mem_neighborhoodImage j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_pullback_eventuallyEq (j : Elliptic.Kind)
    (g : SpecialPeriods.TriangleGroup) {z : ℍ}
    (hz : SpecialPeriods.triangleGeometricRepresentation g z ∈ ellipticNeighborhood j) :
    (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection) =ᶠ[𝓝 z]
      (normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order ∘
        SpecialPeriods.triangleGeometricRepresentation g) := by
  have hU :
    ∀ᶠ w in 𝓝 z, SpecialPeriods.triangleGeometricRepresentation g w ∈ ellipticNeighborhood j :=
    (SpecialPeriods.triangleGeometricRepresentation_holomorphic g).continuous.continuousAt
      ((ellipticNeighborhood j).isOpen.mem_nhds hz)
  filter_upwards [hU] with w hw
  change ellipticFullChart j (SpecialPeriods.triangleOrbitProjection w) = _
  rw [← SpecialPeriods.triangleOrbitProjection_smul g w]
  exact ellipticFullChart_projection j ⟨SpecialPeriods.triangleGeometricRepresentation g w, hw⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_exists_lift (j : Elliptic.Kind) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z ∈ (ellipticFullChart j).source) :
    ∃ g : SpecialPeriods.TriangleGroup,
      SpecialPeriods.triangleGeometricRepresentation g z ∈ ellipticNeighborhood j := by
  rw [ellipticFullChart_source] at hz
  obtain ⟨w, hw, he⟩ := hz
  obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp he
  exact ⟨g, hg ▸ hw⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_pullback_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection)
      (SpecialPeriods.triangleOrbitProjection ⁻¹' (ellipticFullChart j).source) := by
  intro z hz
  obtain ⟨g, hg⟩ := ellipticFullChart_exists_lift j hz
  have hf :=
    (normalizedCayleyBranch_holomorphic (ellipticCenter j) (ellipticNeighborhoodRadius j)
          (ellipticNeighborhoodRadius_pos j).ne' j.order).comp
      (SpecialPeriods.triangleGeometricRepresentation_holomorphic g)
  exact
    (hf.contMDiffAt.congr_of_eventuallyEq
        (ellipticFullChart_pullback_eventuallyEq j g hg)).contMDiffWithinAt

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_properlyDiscontinuous
    SpecialPeriods.triangleGeometricAction_continuous in
theorem SpecialPeriods.Triangle.ellipticFullChart_pullback_isLocalDiffeomorphAt
    (j : Elliptic.Kind) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z ∈ (ellipticFullChart j).source)
    (hcenter : SpecialPeriods.triangleOrbitProjection z ≠ ellipticOrbitCenter j) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection) z := by
  obtain ⟨g, hg⟩ := ellipticFullChart_exists_lift j hz
  have hgc : SpecialPeriods.triangleGeometricRepresentation g z ≠ ellipticCenter j := by
    intro h
    apply hcenter
    rw [← SpecialPeriods.triangleOrbitProjection_smul g z, h]
    rfl
  have hf :=
    ((SpecialPeriods.triangleGeometricBiholomorph g).isLocalDiffeomorph z).comp (K := 𝓘(ℂ)) (P :=
      ℂ)
      (normalizedCayleyBranch_isLocalDiffeomorphAt (ellipticCenter j)
        (SpecialPeriods.triangleGeometricRepresentation g z) (ellipticNeighborhoodRadius j)
        (ellipticNeighborhoodRadius_pos j).ne' j.order j.order_pos hgc)
  exact
    isLocalDiffeomorphAt_congr_of_eventuallyEq hf (ellipticFullChart_pullback_eventuallyEq j g hg)

abbrev SpecialPeriods.TriangleOrbitChartIndex :=
  TriangleRegularQuotient ⊕ Elliptic.Kind

def SpecialPeriods.triangleOrbitChart :
    TriangleOrbitChartIndex → OpenPartialHomeomorph TriangleOrbitSpace ℂ
  | .inl x => regularFullChart x
  | .inr j => Triangle.ellipticFullChart j

theorem SpecialPeriods.triangleOrbitChart_cover (x : TriangleOrbitSpace) :
    ∃ i, x ∈ (triangleOrbitChart i).source := by
  by_cases h₁ : x = triangleOrbitCenterOne
  · subst x
    exact ⟨.inr .three, Triangle.ellipticFullChart_center_mem_source .three⟩
  by_cases h₂ : x = triangleOrbitCenterTwo
  · subst x
    exact ⟨.inr .four, Triangle.ellipticFullChart_center_mem_source .four⟩
  obtain ⟨r, hr⟩ :=
    exists_regularFullChart x ((triangleOrbitRegularDomain_mem_iff x).mpr ⟨h₁, h₂⟩)
  exact ⟨.inl r, hr⟩

theorem SpecialPeriods.triangleOrbitChart_center_unique (j : Elliptic.Kind)
    (i : TriangleOrbitChartIndex)
    (hi : Triangle.ellipticOrbitCenter j ∈ (triangleOrbitChart i).source) : i = .inr j := by
  cases i with
  | inl
    x =>
    have h := (triangleOrbitRegularDomain_mem_iff _).mp (regularFullChart_source_subset x hi)
    cases j
    · exact (h.1 rfl).elim
    · exact (h.2 rfl).elim
  | inr k =>
    cases j <;> cases k
    · rfl
    · exact (Triangle.ellipticFullChart_other_not_mem_source .four hi).elim
    · exact (Triangle.ellipticFullChart_other_not_mem_source .three hi).elim
    · rfl

def SpecialPeriods.triangleOrbitAtlasData :
    BranchedQuotientAtlas.Data (E := ℂ) triangleOrbitProjection TriangleOrbitChartIndex
    where
  chart := triangleOrbitChart
  cover := triangleOrbitChart_cover
  continuous_project := triangleOrbitProjection_continuous
  pullback_contMDiff
    i := by
    cases i with
    | inl x => exact regularFullChart_pullback_holomorphic x
    | inr j => exact Triangle.ellipticFullChart_pullback_holomorphic j
  overlap_lift i j hij z
    hz := by
    obtain ⟨a, ha⟩ := triangleOrbitProjection_surjective ((triangleOrbitChart i).symm z)
    have hsource : triangleOrbitProjection a ∈ (triangleOrbitChart i).source := by
      rw [ha]
      exact (triangleOrbitChart i).map_target hz.1
    refine ⟨a, ha, ?_⟩
    cases i with
    | inl r => exact regularFullChart_pullback_isLocalDiffeomorphAt r hsource
    | inr k =>
      apply Triangle.ellipticFullChart_pullback_isLocalDiffeomorphAt k hsource
      intro h
      have hcritical : Triangle.ellipticOrbitCenter k ∈ (triangleOrbitChart j).source := by
        rw [← h, ha]
        exact hz.2
      exact hij (triangleOrbitChart_center_unique k j hcritical).symm

@[instance_reducible]
def SpecialPeriods.triangleOrbitChartedSpace : ChartedSpace ℂ TriangleOrbitSpace :=
  triangleOrbitAtlasData.chartedSpace

theorem SpecialPeriods.triangleOrbit_isManifold :
    letI := triangleOrbitChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbitAtlasData.isManifold

theorem SpecialPeriods.triangleOrbitChart_mem_atlas (i : TriangleOrbitChartIndex) :
    letI := triangleOrbitChartedSpace
    triangleOrbitChart i ∈ atlas ℂ TriangleOrbitSpace :=
  triangleOrbitAtlasData.chart_mem_atlas i

theorem SpecialPeriods.triangleOrbitProjection_holomorphic :
    letI := triangleOrbitChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection :=
  triangleOrbitAtlasData.contMDiff_project

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
theorem SpecialPeriods.instIsManifold2 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
def SpecialPeriods.triangleOrbitCoordinatePartial (i : TriangleOrbitChartIndex) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace ℂ ω
    where
  toPartialEquiv := (triangleOrbitChart i).toPartialEquiv
  open_source := (triangleOrbitChart i).open_source
  open_target := (triangleOrbitChart i).open_target
  contMDiffOn_toFun :=
    contMDiffOn_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ (triangleOrbitChart_mem_atlas i))
  contMDiffOn_invFun :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ (triangleOrbitChart_mem_atlas i))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_regular {z : ℍ}
    (hz : z ∈ triangleRegularLocus) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z := by
  obtain ⟨r, hr⟩ :=
    exists_regularFullChart (triangleOrbitProjection z)
      ((triangleOrbitProjection_mem_regularDomain_iff z).mpr hz)
  have hf := regularFullChart_pullback_isLocalDiffeomorphAt r hr
  have hinv :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (regularFullChart r).symm
      (regularFullChart r (triangleOrbitProjection z)) :=
    (triangleOrbitCoordinatePartial (.inl r)).symm.isLocalDiffeomorphAt _ _ _
      ((regularFullChart r).map_source hr)
  have hcomp := hf.comp (K := 𝓘(ℂ)) (P := TriangleOrbitSpace) hinv
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  have hU : ∀ᶠ w in 𝓝 z, triangleOrbitProjection w ∈ (regularFullChart r).source :=
    triangleOrbitProjection_continuous.continuousAt ((regularFullChart r).open_source.mem_nhds hr)
  exact hU.mono fun w hw => ((regularFullChart r).left_inv hw).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic {z : ℍ}
    (h₁ : triangleOrbitProjection z ≠ triangleOrbitCenterOne)
    (h₂ : triangleOrbitProjection z ≠ triangleOrbitCenterTwo) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection z :=
  triangleOrbitProjection_isLocalDiffeomorphAt_of_regular
    ((triangleOrbitProjection_mem_regularDomain_iff z).mp
      ((triangleOrbitRegularDomain_mem_iff _).mpr ⟨h₁, h₂⟩))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleRegularToOrbit_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularToOrbit := by
  apply CoveringQuotient.contMDiff_of_comp triangleRegularProject_covering 𝓘(ℂ) ω
  have hf :=
    triangleOrbitProjection_holomorphic.comp
      (contMDiff_subtype_val (U := triangleRegularDomain) (I := 𝓘(ℂ)) (n := ω))
  convert hf using 1
  funext z
  exact triangleRegularToOrbit_project z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleRegularOrbitHomeomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph := by
  intro x
  have he :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun y : TriangleRegularQuotient =>
          (triangleRegularOrbitHomeomorph y : TriangleOrbitSpace))
        x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (triangleRegularToOrbit_holomorphic x)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
def SpecialPeriods.triangleRegularFullProjection :
    TriangleRegularPoint → triangleOrbitRegularDomain := fun z =>
  ⟨triangleOrbitProjection z, (triangleOrbitProjection_mem_regularDomain_iff z).mpr z.property⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleRegularFullProjection_eq :
    triangleRegularFullProjection = triangleRegularOrbitHomeomorph ∘ triangleRegularProject := by
  funext z
  apply Subtype.ext
  exact (triangleRegularToOrbit_project z).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleRegularFullProjection_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularFullProjection := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
      (triangleOrbitProjection_isLocalDiffeomorphAt_of_regular z.property) triangleRegularDomain
      triangleOrbitRegularDomain
      (fun w hw => (triangleOrbitProjection_mem_regularDomain_iff w).mpr hw) z.property

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleRegularFullProjection_surjective :
    Function.Surjective triangleRegularFullProjection := by
  rw [triangleRegularFullProjection_eq]
  exact triangleRegularOrbitHomeomorph.surjective.comp triangleRegularProject_surjective

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
theorem SpecialPeriods.triangleRegularOrbitHomeomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularOrbitHomeomorph.symm := by
  apply
    contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
      triangleRegularFullProjection_isLocalDiffeomorph triangleRegularFullProjection_surjective
  have he :
    triangleRegularOrbitHomeomorph.symm ∘ triangleRegularFullProjection =
      triangleRegularProject := by
    rw [triangleRegularFullProjection_eq]
    funext z
    exact triangleRegularOrbitHomeomorph.symm_apply_apply (triangleRegularProject z)
  rw [he]
  exact triangleRegularProject_holomorphic

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleRegularQuotientChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold2 in
def SpecialPeriods.triangleRegularOrbitBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleRegularQuotient triangleOrbitRegularDomain ω
    where
  toEquiv := triangleRegularOrbitHomeomorph.toEquiv
  contMDiff_toFun := triangleRegularOrbitHomeomorph_holomorphic
  contMDiff_invFun := triangleRegularOrbitHomeomorph_symm_holomorphic

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.Triangle.cuspImageProjection_isLocalDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageProjection Y) := by
  intro z
  exact
    isLocalDiffeomorphAt_restrictOpens 𝓘(ℂ) 𝓘(ℂ)
      (SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_regular
        (horodisc_subset_triangleRegularLocus Y hY z.property))
      (horodisc Y) (cuspImage Y) (fun w hw => ⟨w, hw, rfl⟩) z.property

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.Triangle.cuspImageHomeomorph_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageHomeomorph Y hY) := by
  apply
    contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ)
      (cuspImageProjection_isLocalDiffeomorph Y hY) (cuspImageProjection_surjective Y)
  have he : (cuspImageHomeomorph Y hY) ∘ cuspImageProjection Y = cuspQHorodisc Y := by
    funext z
    exact cuspImageHomeomorph_mk Y hY z
  rw [he]
  exact cuspQHorodisc_holomorphic Y

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.Triangle.cuspImageHomeomorph_symm_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspImageHomeomorph Y hY).symm := by
  apply
    contMDiff_of_comp_localDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 𝓘(ℂ) (cuspQHorodisc_isLocalDiffeomorph Y)
      (cuspQHorodisc_surjective Y (width_pos.le.trans hY))
  have he : (cuspImageHomeomorph Y hY).symm ∘ cuspQHorodisc Y = cuspImageProjection Y := by
    funext z
    exact cuspImageHomeomorph_symm_q Y hY z
  rw [he]
  exact (cuspImageProjection_isLocalDiffeomorph Y hY).contMDiff

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
def SpecialPeriods.Triangle.cuspImageBiholomorph (Y : ℝ) (hY : width ≤ Y) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (cuspImage Y) (puncturedCuspBall Y) ω
    where
  toEquiv := (cuspImageHomeomorph Y hY).toEquiv
  contMDiff_toFun := cuspImageHomeomorph_holomorphic Y hY
  contMDiff_invFun := cuspImageHomeomorph_symm_holomorphic Y hY

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.cuspImageBiholomorph_toHomeomorph (Y : ℝ) (hY : width ≤ Y) :
    (cuspImageBiholomorph Y hY).toHomeomorph = cuspImageHomeomorph Y hY := by
  ext x
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.Triangle.cuspImageNonemptyForChart_mo1973_16605 (Y : ℝ) :
    Nonempty (cuspImage Y) := by
  obtain ⟨z, hz⟩ := horodisc_nonempty Y
  exact ⟨cuspImageProjection Y ⟨z, hz⟩⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
def SpecialPeriods.Triangle.cuspImagePartialDiffeomorph (Y : ℝ) (hY : width ≤ Y) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω :=
  (opensInclusionPartialDiffeomorph 𝓘(ℂ) (cuspImage Y)
        (cuspImageNonemptyForChart_mo1973_16605 Y)).symm.trans
    ((cuspImageBiholomorph Y hY).toPartialDiffeomorph.trans
      (opensInclusionPartialDiffeomorph 𝓘(ℂ) (puncturedCuspBall Y)
        ((cuspImageNonemptyForChart_mo1973_16605 Y).map (cuspImageHomeomorph Y hY))))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
@[simp]
theorem SpecialPeriods.Triangle.cuspImagePartialDiffeomorph_source (Y : ℝ) (hY : width ≤ Y) :
    (cuspImagePartialDiffeomorph Y hY).source =
      (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
  simp [cuspImagePartialDiffeomorph, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.Triangle.cuspImagePartialDiffeomorph_apply (Y : ℝ) (hY : width ≤ Y)
    (x : SpecialPeriods.TriangleOrbitSpace) (hx : x ∈ cuspImage Y) :
    cuspImagePartialDiffeomorph Y hY x = (cuspImageHomeomorph Y hY ⟨x, hx⟩ : ℂ) := by
  let e :=
    (cuspImage Y).openPartialHomeomorphSubtypeCoe (cuspImageNonemptyForChart_mo1973_16605 Y)
  have he : e.symm x = ⟨x, hx⟩ := e.left_inv (Set.mem_univ (⟨x, hx⟩ : cuspImage Y))
  change (cuspImageBiholomorph Y hY (e.symm x) : ℂ) = _
  rw [he]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.Triangle.cuspImagePartialDiffeomorph_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspImagePartialDiffeomorph Y hY)
      (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
  simpa only [cuspImagePartialDiffeomorph_source] using
    (cuspImagePartialDiffeomorph Y hY).contMDiffOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.instIsManifold3 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.Triangle.cuspFullChart_pullback_eqOn (Y : ℝ) (hY : width ≤ Y) :
    Set.EqOn (cuspFullChart Y hY ∘ SpecialPeriods.triangleOpenInclusion)
      (cuspImagePartialDiffeomorph Y hY) (cuspImage Y : Set SpecialPeriods.TriangleOrbitSpace) := by
  intro q hq
  simp only [Function.comp_apply, cuspFullChart_openInclusion Y hY q hq,
    cuspImagePartialDiffeomorph_apply Y hY q hq]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.Triangle.cuspFullChart_pullback_holomorphic (Y : ℝ) (hY : width ≤ Y) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart Y hY ∘ SpecialPeriods.triangleOpenInclusion)
      (SpecialPeriods.triangleOpenInclusion ⁻¹' (cuspFullChart Y hY).source) := by
  rw [cuspFullChart_source, cuspNeighborhood_preimage]
  exact (cuspImagePartialDiffeomorph_holomorphic Y hY).congr (cuspFullChart_pullback_eqOn Y hY)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.Triangle.cuspFullChart_pullback_isLocalDiffeomorphAt (Y : ℝ)
    (hY : width ≤ Y) (q : SpecialPeriods.TriangleOrbitSpace)
    (hq : SpecialPeriods.triangleOpenInclusion q ∈ (cuspFullChart Y hY).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspFullChart Y hY ∘ SpecialPeriods.triangleOpenInclusion)
      q := by
  have hmem : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hq
  refine ⟨cuspImagePartialDiffeomorph Y hY, ?_, ?_⟩
  · rw [cuspImagePartialDiffeomorph_source]
    exact hmem
  · rw [cuspImagePartialDiffeomorph_source]
    exact cuspFullChart_pullback_eqOn Y hY

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
def SpecialPeriods.triangleCompactifiedAtlasData :
    BranchedQuotientAtlas.Data (E := ℂ) triangleOpenInclusion (Option TriangleOrbitSpace) :=
  OnePointAtlas.data (Triangle.cuspFullChart Triangle.width le_rfl)
    (Triangle.cuspPoint_mem_cuspNeighborhood Triangle.width)
    (Triangle.cuspFullChart_pullback_holomorphic Triangle.width le_rfl)
    (Triangle.cuspFullChart_pullback_isLocalDiffeomorphAt Triangle.width le_rfl)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
@[instance_reducible]
def SpecialPeriods.triangleCompactifiedChartedSpace :
    ChartedSpace ℂ TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.chartedSpace

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.triangleCompactified_isManifold :
    letI := triangleCompactifiedChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.triangleCompactified_cuspChart_mem_atlas :
    letI := triangleCompactifiedChartedSpace
    Triangle.cuspFullChart Triangle.width le_rfl ∈ atlas ℂ TriangleCompactifiedOrbitSpace :=
  triangleCompactifiedAtlasData.chart_mem_atlas Option.none

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.triangleOpenInclusion_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusion :=
  triangleCompactifiedAtlasData.contMDiff_project

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
def SpecialPeriods.triangleCompactifiedProjection : ℍ → TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion ∘ triangleOrbitProjection

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.triangleCompactified_cuspChart_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (Triangle.cuspFullChart Triangle.width le_rfl)
      (Triangle.cuspNeighborhood Triangle.width : Set TriangleCompactifiedOrbitSpace) := by
  let := triangleCompactifiedChartedSpace
  let := triangleCompactified_isManifold
  exact
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas triangleCompactified_cuspChart_mem_atlas)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold3 in
theorem SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic :
    letI := triangleCompactifiedChartedSpace
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (Triangle.cuspFullChart Triangle.width le_rfl).symm
      (Metric.ball 0 (Triangle.cuspRadius Triangle.width)) := by
  let := triangleCompactifiedChartedSpace
  let := triangleCompactified_isManifold
  exact
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas triangleCompactified_cuspChart_mem_atlas)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.instIsManifold4 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 in
theorem SpecialPeriods.instIsManifold5 : IsManifold 𝓘(ℂ) ω TriangleCompactifiedOrbitSpace :=
  triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
def SpecialPeriods.triangleCompactifiedOldCoordinatePartial (q : TriangleOrbitSpace) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleCompactifiedOrbitSpace ℂ ω
    where
  toPartialEquiv := (OnePointAtlas.oldChart q).toPartialEquiv
  open_source := (OnePointAtlas.oldChart q).open_source
  open_target := (OnePointAtlas.oldChart q).open_target
  contMDiffOn_toFun :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas
        (triangleCompactifiedAtlasData.chart_mem_atlas (Option.some q)))
  contMDiffOn_invFun :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas
        (triangleCompactifiedAtlasData.chart_mem_atlas (Option.some q)))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
theorem SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusion := by
  intro q
  have hq : triangleOpenInclusion q ∈ (OnePointAtlas.oldChart q).source :=
    (OnePointAtlas.coe_mem_oldChart_source q q).mpr (mem_chart_source ℂ q)
  have hpull := OnePointAtlas.oldChart_pullback_localDiffeomorph q q hq
  have hinv :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (OnePointAtlas.oldChart q).symm
      (OnePointAtlas.oldChart q (triangleOpenInclusion q)) :=
    (triangleCompactifiedOldCoordinatePartial q).symm.isLocalDiffeomorphAt _ _ _
      ((OnePointAtlas.oldChart q).map_source hq)
  have hcomp := hpull.comp (K := 𝓘(ℂ)) (P := TriangleCompactifiedOrbitSpace) hinv
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp
  have hU : ∀ᶠ x in 𝓝 q, triangleOpenInclusion x ∈ (OnePointAtlas.oldChart q).source :=
    OnePoint.continuous_coe.continuousAt ((OnePointAtlas.oldChart q).open_source.mem_nhds hq)
  exact hU.mono fun x hx => ((OnePointAtlas.oldChart q).left_inv hx).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
def SpecialPeriods.triangleCuspComplement :
    TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  ⟨{ triangleCuspPoint }ᶜ, isClosed_singleton.isOpen_compl⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
def SpecialPeriods.triangleOpenInclusionToComplement (q : TriangleOrbitSpace) :
    triangleCuspComplement :=
  ⟨triangleOpenInclusion q, triangleOpenInclusion_ne_cusp q⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
theorem SpecialPeriods.triangleOpenInclusionToComplement_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleOpenInclusionToComplement :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) triangleOpenInclusion_isLocalDiffeomorph
    triangleCuspComplement triangleOpenInclusion_ne_cusp

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
theorem SpecialPeriods.triangleOpenInclusionToComplement_bijective :
    Function.Bijective triangleOpenInclusionToComplement := by
  constructor
  · intro x y h
    exact OnePoint.coe_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp x.property
    exact ⟨q, Subtype.ext hq⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
def SpecialPeriods.triangleOpenComplementBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace triangleCuspComplement ω :=
  triangleOpenInclusionToComplement_isLocalDiffeomorph.diffeomorphOfBijective
    triangleOpenInclusionToComplement_bijective

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold4 SpecialPeriods.instIsManifold5 in
@[simp]
theorem SpecialPeriods.triangleOpenComplementBiholomorph_symm_apply (q : triangleCuspComplement) :
    triangleOpenInclusion (triangleOpenComplementBiholomorph.symm q) = q :=
  congrArg Subtype.val (triangleOpenComplementBiholomorph.apply_symm_apply q)

def SpecialPeriods.triangleCompactifiedCenterOne : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion triangleOrbitCenterOne

def SpecialPeriods.triangleCompactifiedCenterTwo : TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion triangleOrbitCenterTwo

theorem SpecialPeriods.triangleCompactifiedCenterOne_ne_centerTwo :
    triangleCompactifiedCenterOne ≠ triangleCompactifiedCenterTwo := by
  intro h
  exact triangleOrbitCenterOne_ne_centerTwo (OnePoint.coe_injective h)

def SpecialPeriods.Triangle.ellipticCompactifiedCenter (j : Elliptic.Kind) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleOpenInclusion (ellipticOrbitCenter j)

@[simp]
theorem SpecialPeriods.Triangle.ellipticCompactifiedCenter_ne_cusp (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ≠ SpecialPeriods.triangleCuspPoint :=
  SpecialPeriods.triangleOpenInclusion_ne_cusp (ellipticOrbitCenter j)

theorem SpecialPeriods.Triangle.normalizedCayley_analyticAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0) :
    AnalyticAt ℂ (normalizedCayley a r ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (cayleyCoordinate_analyticAt a z).div analyticAt_const (Complex.ofReal_ne_zero.mpr hr)

theorem SpecialPeriods.Triangle.normalizedCayley_order_center (a : ℍ) (r : ℝ) (hr : r ≠ 0) :
    analyticOrderAt (normalizedCayley a r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = 1 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (r : ℂ)⁻¹) (a : ℂ) := analyticAt_const
  have hcorder : analyticOrderAt (fun _ : ℂ => (r : ℂ)⁻¹) (a : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Complex.ofReal_ne_zero.mpr hr))
  have he :
    normalizedCayley a r ∘ UpperHalfPlane.ofComplex =
      (cayleyCoordinate a ∘ UpperHalfPlane.ofComplex) * (fun _ : ℂ => (r : ℂ)⁻¹) := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul (cayleyCoordinate_analyticAt a a) hc, cayleyCoordinate_order_center,
    hcorder, add_zero]

theorem SpecialPeriods.Triangle.normalizedCayleyBranch_analyticAt (a z : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) : AnalyticAt ℂ (normalizedCayleyBranch a r m ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  (normalizedCayley_analyticAt a z r hr).pow m

theorem SpecialPeriods.Triangle.normalizedCayleyBranch_order_center (a : ℍ) (r : ℝ) (hr : r ≠ 0)
    (m : ℕ) :
    analyticOrderAt (normalizedCayleyBranch a r m ∘ UpperHalfPlane.ofComplex) (a : ℂ) =
      (m : ℕ∞) := by
  change analyticOrderAt ((normalizedCayley a r ∘ UpperHalfPlane.ofComplex) ^ m) (a : ℂ) = _
  rw [analyticOrderAt_pow (normalizedCayley_analyticAt a a r hr),
    normalizedCayley_order_center a r hr]
  simp

theorem SpecialPeriods.Triangle.ellipticFullChart_complexGerm_eventuallyEq (j : Elliptic.Kind) :
    (ellipticFullChart j ∘
        SpecialPeriods.triangleOrbitProjection ∘
          UpperHalfPlane.ofComplex) =ᶠ[𝓝 (ellipticCenter j : ℂ)]
      (normalizedCayleyBranch (ellipticCenter j) (ellipticNeighborhoodRadius j) j.order ∘
        UpperHalfPlane.ofComplex) := by
  have hU : IsOpen (UpperHalfPlane.coe '' (ellipticNeighborhood j : Set ℍ)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ (ellipticNeighborhood j).isOpen
  have hcenter :
    (ellipticCenter j : ℂ) ∈ UpperHalfPlane.coe '' (ellipticNeighborhood j : Set ℍ) :=
    ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, rfl⟩
  filter_upwards [hU.mem_nhds hcenter] with z hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  exact ellipticFullChart_projection j ⟨w, hw⟩

theorem SpecialPeriods.Triangle.ellipticFullChart_complexGerm_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ
      (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex)
      (ellipticCenter j : ℂ) :=
  (normalizedCayleyBranch_analyticAt (ellipticCenter j) (ellipticCenter j)
        (ellipticNeighborhoodRadius j) (ellipticNeighborhoodRadius_pos j).ne' j.order).congr
    (ellipticFullChart_complexGerm_eventuallyEq j).symm

theorem SpecialPeriods.Triangle.ellipticFullChart_order_center (j : Elliptic.Kind) :
    analyticOrderAt
        (ellipticFullChart j ∘ SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex)
        (ellipticCenter j : ℂ) =
      (j.order : ℕ∞) := by
  rw [analyticOrderAt_congr (ellipticFullChart_complexGerm_eventuallyEq j)]
  exact
    normalizedCayleyBranch_order_center (ellipticCenter j) (ellipticNeighborhoodRadius j)
      (ellipticNeighborhoodRadius_pos j).ne' j.order

theorem SpecialPeriods.Triangle.sl_analyticAt_smul (g : SL(2, ℝ)) (z : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (z : ℂ) := by
  have h := UpperHalfPlane.analyticAt_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) z
  simpa only [MulAction.compHom_smul_def] using h

theorem SpecialPeriods.Triangle.sl_analyticOrderAt_comp_smul (f : ℍ → ℂ) (g : SL(2, ℝ)) (z : ℍ) :
    analyticOrderAt (fun w : ℂ => f (g • UpperHalfPlane.ofComplex w)) (z : ℂ) =
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) ((g • z : ℍ) : ℂ) := by
  let G : ℂ → ℂ := fun w => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ)
  have he :
    (fun w : ℂ => f (g • UpperHalfPlane.ofComplex w)) = (f ∘ UpperHalfPlane.ofComplex) ∘ G := by
    funext w
    simp only [Function.comp_apply, G, UpperHalfPlane.ofComplex_apply]
  rw [he, analyticOrderAt_comp_of_deriv_ne_zero]
  · simp only [G, UpperHalfPlane.ofComplex_apply]
  · exact sl_analyticAt_smul g z
  · rw [sl_deriv_smul]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 (slDenom_ne_zero g z))

theorem SpecialPeriods.Triangle.triangle_analyticOrderAt_comp_action (f : ℍ → ℂ)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    analyticOrderAt
        (fun w : ℂ =>
          f (SpecialPeriods.triangleGeometricRepresentation g (UpperHalfPlane.ofComplex w)))
        (z : ℂ) =
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.triangleGeometricRepresentation g z : ℂ) := by
  have hl (w : ℍ) :
    (SpecialPeriods.triangleMatrixLift g).val • w =
      SpecialPeriods.triangleGeometricRepresentation g w :=
    SpecialPeriods.triangleMatrixLift_smul g w
  simpa only [hl] using sl_analyticOrderAt_comp_smul f (SpecialPeriods.triangleMatrixLift g).val z

theorem SpecialPeriods.Triangle.triangle_invariant_analyticOrderAt (f : ℍ → ℂ)
    (hf :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    analyticOrderAt (f ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.triangleGeometricRepresentation g z : ℂ) =
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) := by
  have he :
    (fun w : ℂ =>
        f (SpecialPeriods.triangleGeometricRepresentation g (UpperHalfPlane.ofComplex w))) =
      f ∘ UpperHalfPlane.ofComplex := by
    funext w
    exact hf g (UpperHalfPlane.ofComplex w)
  have h := triangle_analyticOrderAt_comp_action f g z
  rw [he] at h
  exact h.symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.instIsManifold6 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.instIsManifold7 : IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
private theorem SpecialPeriods.triangleCuspComplement_nonempty_for_coordinates_mo1973_16685 :
    Nonempty triangleCuspComplement :=
  ⟨triangleOpenInclusionToComplement triangleOrbitCenterOne⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
def SpecialPeriods.triangleOpenInclusionPartial :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) TriangleOrbitSpace TriangleCompactifiedOrbitSpace ω :=
  triangleOpenComplementBiholomorph.toPartialDiffeomorph.trans
    (opensInclusionPartialDiffeomorph 𝓘(ℂ) triangleCuspComplement
      triangleCuspComplement_nonempty_for_coordinates_mo1973_16685)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.triangleOpenInclusionPartial_source :
    triangleOpenInclusionPartial.source = Set.univ := by
  simp [triangleOpenInclusionPartial, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.triangleOpenInclusionPartial_target :
    triangleOpenInclusionPartial.target =
      (triangleCuspComplement : Set TriangleCompactifiedOrbitSpace) := by
  simp [triangleOpenInclusionPartial, PartialDiffeomorph.trans, Diffeomorph.toPartialDiffeomorph,
    opensInclusionPartialDiffeomorph]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.triangleOpenInclusionPartial_symm_apply (q : TriangleOrbitSpace) :
    triangleOpenInclusionPartial.symm (triangleOpenInclusion q) = q := by
  change
    triangleOpenInclusionPartial.toPartialEquiv.invFun
        (triangleOpenInclusionPartial.toPartialEquiv.toFun q) =
      q
  exact triangleOpenInclusionPartial.toPartialEquiv.left_inv (by simp)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
def SpecialPeriods.Triangle.ellipticCompactifiedPartial (j : Elliptic.Kind) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ ω :=
  SpecialPeriods.triangleOpenInclusionPartial.symm.trans
    (SpecialPeriods.triangleOrbitCoordinatePartial (.inr j))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
def SpecialPeriods.Triangle.ellipticCompactifiedChart (j : Elliptic.Kind) :
    OpenPartialHomeomorph SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ :=
  (ellipticCompactifiedPartial j).toOpenPartialHomeomorph

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_openInclusion (j : Elliptic.Kind)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    ellipticCompactifiedChart j (SpecialPeriods.triangleOpenInclusion q) =
      ellipticFullChart j q := by
  change
    ellipticFullChart j
        (SpecialPeriods.triangleOpenInclusionPartial.symm
          (SpecialPeriods.triangleOpenInclusion q)) =
      _
  rw [SpecialPeriods.triangleOpenInclusionPartial_symm_apply]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.Triangle.openInclusion_mem_ellipticCompactifiedChart_source
    (j : Elliptic.Kind) (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ (ellipticCompactifiedChart j).source ↔
      q ∈ (ellipticFullChart j).source := by
  change
    (SpecialPeriods.triangleOpenInclusion q ∈ SpecialPeriods.triangleOpenInclusionPartial.target ∧
        SpecialPeriods.triangleOpenInclusionPartial.symm
            (SpecialPeriods.triangleOpenInclusion q) ∈
          (ellipticFullChart j).source) ↔
      _
  rw [SpecialPeriods.triangleOpenInclusionPartial_target,
    SpecialPeriods.triangleOpenInclusionPartial_symm_apply]
  exact and_iff_right (SpecialPeriods.triangleOpenInclusion_ne_cusp q)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_target (j : Elliptic.Kind) :
    (ellipticCompactifiedChart j).target = (SpecialPeriods.unitDisc : Set ℂ) := by
  change
    (ellipticFullChart j).target ∩
        (ellipticFullChart j).symm ⁻¹' SpecialPeriods.triangleOpenInclusionPartial.source =
      _
  rw [SpecialPeriods.triangleOpenInclusionPartial_source, Set.preimage_univ, Set.inter_univ,
    ellipticFullChart_target]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_center_mem_source (j : Elliptic.Kind) :
    ellipticCompactifiedCenter j ∈ (ellipticCompactifiedChart j).source :=
  (openInclusion_mem_ellipticCompactifiedChart_source j (ellipticOrbitCenter j)).mpr
    (ellipticFullChart_center_mem_source j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
@[simp]
theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_center (j : Elliptic.Kind) :
    ellipticCompactifiedChart j (ellipticCompactifiedCenter j) = 0 := by
  change
    ellipticCompactifiedChart j (SpecialPeriods.triangleOpenInclusion (ellipticOrbitCenter j)) = 0
  rw [ellipticCompactifiedChart_openInclusion, ellipticFullChart_center]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j) (ellipticCompactifiedChart j).source :=
  (ellipticCompactifiedPartial j).contMDiffOn

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.instIsManifold7 in
theorem SpecialPeriods.Triangle.ellipticCompactifiedChart_symm_holomorphic (j : Elliptic.Kind) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (ellipticCompactifiedChart j).symm
      (ellipticCompactifiedChart j).target :=
  (ellipticCompactifiedPartial j).symm.contMDiffOn

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.Threefold.Puncture :=
  Option Elliptic.Kind

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.puncturePoint :
    Puncture → SpecialPeriods.TriangleCompactifiedOrbitSpace
  | none => SpecialPeriods.triangleCuspPoint
  | some j => SpecialPeriods.Triangle.ellipticCompactifiedCenter j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.puncturePoint_injective : Function.Injective puncturePoint := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact (SpecialPeriods.Triangle.ellipticCompactifiedCenter_ne_cusp j h.symm).elim
  | some i =>
    cases j with
    | none => exact (SpecialPeriods.Triangle.ellipticCompactifiedCenter_ne_cusp i h).elim
    | some j =>
      congr 1
      cases i <;> cases j
      · rfl
      · exact (SpecialPeriods.triangleCompactifiedCenterOne_ne_centerTwo h).elim
      · exact (SpecialPeriods.triangleCompactifiedCenterOne_ne_centerTwo h.symm).elim
      · rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.punctureChart :
    Puncture → OpenPartialHomeomorph SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ
  | none => SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
  | some j => SpecialPeriods.Triangle.ellipticCompactifiedChart j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.punctureChartRadius : Puncture → ℝ
  | none => SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width
  | some _ => 1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.punctureChartRadius_pos (i : Puncture) :
    0 < punctureChartRadius i := by
  cases i with
  | none => exact SpecialPeriods.Triangle.cuspRadius_pos SpecialPeriods.Triangle.width
  | some j => norm_num [punctureChartRadius]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.punctureChart_target (i : Puncture) :
    (punctureChart i).target = Metric.ball 0 (punctureChartRadius i) := by
  cases i with
  | none =>
    exact SpecialPeriods.Triangle.cuspFullChart_target SpecialPeriods.Triangle.width le_rfl
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_target j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.puncturePoint_mem_source (i : Puncture) :
    puncturePoint i ∈ (punctureChart i).source := by
  cases i with
  | none =>
    exact SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood SpecialPeriods.Triangle.width
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_center_mem_source j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.punctureChart_point (i : Puncture) :
    punctureChart i (puncturePoint i) = 0 := by
  cases i with
  | none =>
    exact SpecialPeriods.Triangle.cuspFullChart_cuspPoint SpecialPeriods.Triangle.width le_rfl
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_center j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.Threefold.punctureChart_symm_zero (i : Puncture) :
    (punctureChart i).symm 0 = puncturePoint i := by
  rw [← punctureChart_point i]
  exact (punctureChart i).left_inv (puncturePoint_mem_source i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.punctureChart_eq_zero_iff (i : Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ (punctureChart i).source) :
    punctureChart i x = 0 ↔ x = puncturePoint i := by
  constructor
  · intro h
    apply (punctureChart i).injOn hx (puncturePoint_mem_source i)
    exact h.trans (punctureChart_point i).symm
  · rintro rfl
    exact punctureChart_point i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.punctureChart_holomorphic (i : Puncture) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (punctureChart i) (punctureChart i).source := by
  cases i with
  | none => exact SpecialPeriods.triangleCompactified_cuspChart_holomorphic
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_holomorphic j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Threefold.punctureChart_symm_holomorphic (i : Puncture) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (punctureChart i).symm (punctureChart i).target := by
  cases i with
  | none => exact SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_symm_holomorphic j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Threefold.puncturePartial (i : Puncture) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ ω
    where
  toPartialEquiv := (punctureChart i).toPartialEquiv
  open_source := (punctureChart i).open_source
  open_target := (punctureChart i).open_target
  contMDiffOn_toFun := punctureChart_holomorphic i
  contMDiffOn_invFun := punctureChart_symm_holomorphic i

theorem SpecialPeriods.Threefold.exists_pairwise_disjoint_opens {I X : Type*} [TopologicalSpace X]
    [Finite I] [T2Space X] (p : I → X) (hp : Function.Injective p)
    (U : I → TopologicalSpace.Opens X) (hU : ∀ i, p i ∈ U i) :
    ∃ V : I → TopologicalSpace.Opens X,
      (∀ i, p i ∈ V i) ∧
        (∀ i, V i ≤ U i) ∧ Pairwise (fun i j => Disjoint (V i : Set X) (V j : Set X)) := by
  obtain ⟨W, hW, hdisj⟩ := (Set.finite_range p).t2_separation
  refine
    ⟨fun i => ⟨W (p i) ∩ U i, (hW (p i)).2.inter (U i).isOpen⟩, fun i => ⟨(hW (p i)).1, hU i⟩,
      fun _ => Set.inter_subset_right, ?_⟩
  intro i j hij
  exact
    (hdisj (Set.mem_range_self i) (Set.mem_range_self j) (fun h => hij (hp h))).mono
      Set.inter_subset_left Set.inter_subset_left

def SpecialPeriods.Threefold.coordinateDisc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (r : ℝ) : TopologicalSpace.Opens X :=
  ⟨e.source ∩ e ⁻¹' Metric.ball 0 r, e.isOpen_inter_preimage Metric.isOpen_ball⟩

@[simp]
theorem SpecialPeriods.Threefold.mem_coordinateDisc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (r : ℝ) (x : X) :
    x ∈ coordinateDisc e r ↔ x ∈ e.source ∧ e x ∈ Metric.ball 0 r :=
  Iff.rfl

theorem SpecialPeriods.Threefold.center_mem_coordinateDisc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {p : X} (hp : p ∈ e.source) (h0 : e p = 0) {r : ℝ}
    (hr : 0 < r) : p ∈ coordinateDisc e r := by exact ⟨hp, h0 ▸ Metric.mem_ball_self hr⟩

theorem SpecialPeriods.Threefold.coordinateDisc_eq_symm_image {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {r : ℝ} (hr : Metric.ball 0 r ⊆ e.target) :
    (coordinateDisc e r : Set X) = e.symm '' Metric.ball 0 r :=
  (e.symm_image_eq_source_inter_preimage hr).symm

theorem SpecialPeriods.Threefold.exists_coordinateDisc_subset {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {p : X} (hp : p ∈ e.source) (h0 : e p = 0)
    (U : TopologicalSpace.Opens X) (hU : p ∈ U) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ Metric.ball 0 r ⊆ e.target ∧ coordinateDisc e r ≤ U := by
  have hnhds : e.target ∩ e.symm ⁻¹' (U : Set X) ∈ 𝓝 (e p) :=
    Filter.inter_mem (e.open_target.mem_nhds (e.map_source hp))
      ((e.tendsto_symm hp).eventually (U.isOpen.mem_nhds hU))
  rw [h0] at hnhds
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let ρ := Min.min r (R / 2)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρball : Metric.ball (0 : ℂ) ρ ⊆ e.target ∩ e.symm ⁻¹' (U : Set X) :=
    (Metric.ball_subset_ball hρr).trans hball
  refine
    ⟨ρ, lt_min hr (half_pos hR), (min_le_right _ _).trans_lt (half_lt_self hR),
      hρball.trans Set.inter_subset_left, ?_⟩
  intro x hx
  have hmem := (hρball hx.2).2
  change e.symm (e x) ∈ (U : Set X) at hmem
  rw [e.left_inv hx.1] at hmem
  exact hmem

theorem SpecialPeriods.Threefold.exists_pairwise_disjoint_coordinateDiscs {I X : Type*}
    [TopologicalSpace X] [Finite I] [T2Space X] (p : I → X) (hp : Function.Injective p)
    (e : I → OpenPartialHomeomorph X ℂ) (hsource : ∀ i, p i ∈ (e i).source)
    (hzero : ∀ i, e i (p i) = 0) (U : I → TopologicalSpace.Opens X) (hU : ∀ i, p i ∈ U i)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ r : I → ℝ,
      (∀ i, 0 < r i ∧ r i < R i) ∧
        (∀ i, Metric.ball 0 (r i) ⊆ (e i).target) ∧
          (∀ i, coordinateDisc (e i) (r i) ≤ U i) ∧
            Pairwise
              (fun i j =>
                Disjoint (coordinateDisc (e i) (r i) : Set X)
                  (coordinateDisc (e j) (r j) : Set X)) := by
  obtain ⟨V, hpV, hVU, hVdisj⟩ := exists_pairwise_disjoint_opens p hp U hU
  have hdisc (i : I) :=
    exists_coordinateDisc_subset (e i) (hsource i) (hzero i) (V i) (hpV i) (hR i)
  choose r hr hrR htarget hsubset using hdisc
  refine ⟨r, fun i => ⟨hr i, hrR i⟩, htarget, fun i => (hsubset i).trans (hVU i), ?_⟩
  intro i j hij
  exact (hVdisj hij).mono (hsubset i) (hsubset j)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.finiteInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℂ) : SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  π.symm (z : RiemannSphere)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.apply_finiteInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℂ) : π (finiteInverse π z) = (z : RiemannSphere) :=
  π.apply_symm_apply _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_continuous
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω) :
    Continuous (finiteInverse π) :=
  π.symm.continuous.comp OnePoint.continuous_coe

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteInverse π) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => (z : RiemannSphere)) :=
    RiemannSphere.standardCharts.affineMap_holomorphic Bool.false
  exact π.symm.contMDiff.comp hc

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.finitePullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    TopologicalSpace.Opens ℂ :=
  ⟨finiteInverse π ⁻¹' (V : Set SpecialPeriods.TriangleCompactifiedOrbitSpace),
    V.isOpen.preimage (finiteInverse_continuous π)⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.mem_finitePullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace) (z : ℂ) :
    z ∈ finitePullback π V ↔ finiteInverse π z ∈ V :=
  Iff.rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.symm_infty
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    π.symm ((OnePoint.infty) : RiemannSphere) = SpecialPeriods.triangleCuspPoint := by
  exact π.injective ((π.apply_symm_apply _).trans hπ.symm)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_ne_cusp
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    finiteInverse π z ≠ SpecialPeriods.triangleCuspPoint := by
  intro h
  exact OnePoint.coe_ne_infty z ((apply_finiteInverse π z).symm.trans ((congrArg π h).trans hπ))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.finiteInverse_tendsto_cusp
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (finiteInverse π) (Bornology.cobounded ℂ)
      (𝓝 SpecialPeriods.triangleCuspPoint) := by
  have hc :
    Filter.Tendsto (fun z : ℂ => (z : RiemannSphere)) (Bornology.cobounded ℂ)
      (𝓝 ((OnePoint.infty) : RiemannSphere)) := by
    simpa only [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  have h := π.symm.continuous.continuousAt.tendsto.comp hc
  change
    Filter.Tendsto (finiteInverse π) (Bornology.cobounded ℂ)
      (𝓝 (π.symm ((OnePoint.infty) : RiemannSphere))) at h
  simpa only [symm_infty π hπ] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.finitePullback_contains_exterior
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace)
    (hV : SpecialPeriods.triangleCuspPoint ∈ V) :
    ∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ finitePullback π V := by
  have hmem : (finitePullback π V : Set ℂ) ∈ Bornology.cobounded ℂ :=
    (finiteInverse_tendsto_cusp π hπ) (V.isOpen.mem_nhds hV)
  obtain ⟨r, _, hr⟩ := (Metric.hasBasis_cobounded_compl_ball (0 : ℂ)).mem_iff.mp hmem
  refine ⟨Max.max r 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  exact (Set.compl_subset_compl.mpr (Metric.ball_subset_ball (le_max_left r 1))).trans hr

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate : RiemannSphere → ℂ :=
  (RiemannSphere.standardCharts.parametrization Bool.true).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_mem_source
    {p : RiemannSphere} (hp : p ≠ ((0 : ℂ) : RiemannSphere)) :
    p ∈ (RiemannSphere.standardCharts.parametrization Bool.true).target := by
  rw [TwoAffineCharts.parametrization_target]
  change p ∈ Set.range RiemannSphere.standardCharts.right
  rw [RiemannSphere.standardCharts.range_right]
  exact hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_infty :
    sphereReciprocalCoordinate ((OnePoint.infty) : RiemannSphere) = 0 := by
  have h := RiemannSphere.standardCharts.parametrization_symm_apply Bool.true (0 : ℂ)
  change sphereReciprocalCoordinate (RiemannSphere.infinityParametrization 0) = 0 at h
  simpa only [RiemannSphere.infinityParametrization_zero] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_coe {z : ℂ}
    (hz : z ≠ 0) : sphereReciprocalCoordinate (z : RiemannSphere) = z⁻¹ := by
  have he : RiemannSphere.infinityParametrization z⁻¹ = (z : RiemannSphere) := by
    rw [RiemannSphere.infinityParametrization_of_ne (inv_ne_zero hz), inv_inv]
  have h := RiemannSphere.standardCharts.parametrization_symm_apply Bool.true z⁻¹
  change sphereReciprocalCoordinate (RiemannSphere.infinityParametrization z⁻¹) = z⁻¹ at h
  simpa only [he] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_holomorphicAt
    {p : RiemannSphere} (hp : p ≠ ((0 : ℂ) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate p := by
  apply
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.true))
  exact sphereReciprocalCoordinate_mem_source hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.CuspCoordinates.t
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (q : ℂ) : ℂ :=
  sphereReciprocalCoordinate
    (π ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm q))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.CuspCoordinates.tDivQ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω) :
    ℂ → ℂ :=
  dslope (t π) 0

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) : t π 0 = 0 := by
  rw [t, SpecialPeriods.Triangle.cuspFullChart_symm_zero, hπ, sphereReciprocalCoordinate_infty]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_holomorphicAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (t π) 0 := by
  have hC :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm (0 : ℂ) :=
    SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic.contMDiffAt
      (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self
          (SpecialPeriods.Triangle.cuspRadius_pos SpecialPeriods.Triangle.width)))
  have hR :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereReciprocalCoordinate
      (π ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0)) :=
    by
    rw [SpecialPeriods.Triangle.cuspFullChart_symm_zero, hπ]
    exact sphereReciprocalCoordinate_holomorphicAt (OnePoint.infty_ne_coe (0 : ℂ))
  exact hR.comp 0 (π.contMDiffAt.comp 0 hC)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    AnalyticAt ℂ (t π) 0 :=
  (t_holomorphicAt_zero π hπ).contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.tDivQ_analyticAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    AnalyticAt ℂ (tDivQ π) 0 :=
  (t_analyticAt_zero π hπ).hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_eq_mul_tDivQ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (q : ℂ) :
    t π q = q * tDivQ π q := by
  simpa only [tDivQ, sub_zero, t_zero π hπ, smul_eq_mul] using (sub_smul_dslope (t π) 0 q).symm

theorem SpecialPeriods.MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph {f : ℂ → ℂ}
    {z : ℂ} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) : deriv f z ≠ 0 := by
  let e : ℂ ≃L[ℂ] ℂ := hf.mfderivToContinuousLinearEquiv (by simp)
  have he : e 1 = deriv f z := by
    change (show ℂ →L[ℂ] ℂ from mfderiv 𝓘(ℂ) 𝓘(ℂ) f z) 1 = deriv f z
    rw [mfderiv_eq_fderiv]
    rfl
  intro h
  have h10 : e 1 = e 0 := by rw [he, h, map_zero]
  exact one_ne_zero (e.injective h10)

theorem SpecialPeriods.MuTorsor.SourceOrders.centered_order_eq_one_of_isLocalDiffeomorph
    {f : ℂ → ℂ} {z : ℂ} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) :
    analyticOrderAt (fun w => f w - f z) z = 1 :=
  hf.contMDiffAt.contDiffAt.analyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero
    (deriv_ne_zero_of_isLocalDiffeomorph hf)

theorem SpecialPeriods.MuTorsor.SourceOrders.order_eq_one_of_isLocalDiffeomorph {f : ℂ → ℂ}
    {z : ℂ} (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f z) (hz : f z = 0) :
    analyticOrderAt f z = 1 := by
  simpa only [hz, sub_zero] using centered_order_eq_one_of_isLocalDiffeomorph hf

theorem SpecialPeriods.MuTorsor.SourceOrders.centered_order_comp {F f : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (hf : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f (F a)) :
    analyticOrderAt (fun w => f (F w) - f (F a)) a = analyticOrderAt (fun w => F w - F a) a := by
  have houter : AnalyticAt ℂ (fun w => f w - f (F a)) (F a) :=
    hf.contMDiffAt.contDiffAt.analyticAt.sub analyticAt_const
  simpa only [Function.comp_def, centered_order_eq_one_of_isLocalDiffeomorph hf, one_mul] using
    houter.analyticOrderAt_comp hF

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.TriangleSource.cuspPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ ω
    where
  toPartialEquiv :=
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).toPartialEquiv
  open_source :=
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).open_source
  open_target :=
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).open_target
  contMDiffOn_toFun := SpecialPeriods.triangleCompactified_cuspChart_holomorphic
  contMDiffOn_invFun := SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.TriangleSource.sphereReciprocalPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) RiemannSphere ℂ ω
    where
  toPartialEquiv := (RiemannSphere.standardCharts.parametrization Bool.true).symm.toPartialEquiv
  open_source := (RiemannSphere.standardCharts.parametrization Bool.true).open_target
  open_target := (RiemannSphere.standardCharts.parametrization Bool.true).open_source
  contMDiffOn_toFun :=
    contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.true))
  contMDiffOn_invFun :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.true))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.TriangleSource.meromorphicCuspJ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (q : ℂ) : ℂ :=
  1728 / SpecialPeriods.MuTorsor.CuspCoordinates.t π q

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.reciprocalCusp_isLocalDiffeomorphAt
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (SpecialPeriods.MuTorsor.CuspCoordinates.t π) 0 := by
  have hc :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0 :=
    cuspPartialDiffeomorph.symm.isLocalDiffeomorphAt _ _ _
      (Metric.mem_ball_self
        (SpecialPeriods.Triangle.cuspRadius_pos SpecialPeriods.Triangle.width))
  have hr :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω
      SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate
      (π ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0)) :=
    by
    rw [SpecialPeriods.Triangle.cuspFullChart_symm_zero, hπ]
    exact
      sphereReciprocalPartialDiffeomorph.isLocalDiffeomorphAt _ _ _
        (SpecialPeriods.MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_mem_source
          (OnePoint.infty_ne_coe (0 : ℂ)))
  have hp :=
    hc.comp (K := 𝓘(ℂ)) (P := RiemannSphere)
      (π.isLocalDiffeomorph
        ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm 0))
  exact hp.comp (K := 𝓘(ℂ)) (P := ℂ) hr

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.reciprocalCusp_deriv_ne_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    deriv (SpecialPeriods.MuTorsor.CuspCoordinates.t π) 0 ≠ 0 :=
  SpecialPeriods.MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (reciprocalCusp_isLocalDiffeomorphAt π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.reciprocalCusp_analyticOrder
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    analyticOrderAt (SpecialPeriods.MuTorsor.CuspCoordinates.t π) 0 = 1 :=
  SpecialPeriods.MuTorsor.SourceOrders.order_eq_one_of_isLocalDiffeomorph
    (reciprocalCusp_isLocalDiffeomorphAt π hπ)
    (SpecialPeriods.MuTorsor.CuspCoordinates.t_zero π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.meromorphicCuspJ_meromorphicAt
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    MeromorphicAt (meromorphicCuspJ π) 0 :=
  analyticAt_const.meromorphicAt.div
    (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).meromorphicAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.meromorphicCuspJ_order
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    meromorphicOrderAt (meromorphicCuspJ π) 0 = (-1 : ℤ) := by
  change
    meromorphicOrderAt ((fun _ : ℂ => (1728 : ℂ)) / SpecialPeriods.MuTorsor.CuspCoordinates.t π)
        0 =
      _
  rw [meromorphicOrderAt_div analyticAt_const.meromorphicAt
      (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).meromorphicAt,
    (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ).meromorphicOrderAt_eq,
    reciprocalCusp_analyticOrder π hπ]
  norm_num [meromorphicOrderAt_const]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.sphereFiniteCoordinate : RiemannSphere → ℂ :=
  (RiemannSphere.standardCharts.parametrization Bool.false).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_coe (z : ℂ) :
    sphereFiniteCoordinate (z : RiemannSphere) = z :=
  RiemannSphere.standardCharts.parametrization_symm_apply Bool.false z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_mem_source {q : RiemannSphere}
    (hq : q ≠ ((OnePoint.infty) : RiemannSphere)) :
    q ∈ (RiemannSphere.standardCharts.parametrization Bool.false).target := by
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hq
  exact ⟨z, Set.mem_univ z, rfl⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_coe_apply {q : RiemannSphere}
    (hq : q ≠ ((OnePoint.infty) : RiemannSphere)) :
    (sphereFiniteCoordinate q : RiemannSphere) = q :=
  (RiemannSphere.standardCharts.parametrization Bool.false).right_inv
    (sphereFiniteCoordinate_mem_source hq)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.sphereFiniteCoordinate_holomorphicAt {q : RiemannSphere}
    (hq : q ≠ ((OnePoint.infty) : RiemannSphere)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereFiniteCoordinate q := by
  apply
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (Set.mem_range_self Bool.false))
  exact sphereFiniteCoordinate_mem_source hq

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.finiteOrbitCoordinate
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (q : SpecialPeriods.TriangleOrbitSpace) : ℂ :=
  sphereFiniteCoordinate (π (SpecialPeriods.triangleOpenInclusion q))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : ℂ :=
  finiteOrbitCoordinate π (SpecialPeriods.triangleOrbitProjection z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_target_ne_infty
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    π (SpecialPeriods.triangleOpenInclusion q) ≠ ((OnePoint.infty) : RiemannSphere) := by
  intro h
  exact SpecialPeriods.triangleOpenInclusion_ne_cusp q (π.injective (h.trans hπ.symm))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    (finiteOrbitCoordinate π q : RiemannSphere) = π (SpecialPeriods.triangleOpenInclusion q) :=
  sphereFiniteCoordinate_coe_apply (finiteOrbitCoordinate_target_ne_infty π hπ q)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteOrbitCoordinate π) := by
  intro q
  exact
    (sphereFiniteCoordinate_holomorphicAt (finiteOrbitCoordinate_target_ne_infty π hπ q)).comp q
      ((π.contMDiff.comp SpecialPeriods.triangleOpenInclusion_holomorphic) q)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_injective
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Function.Injective (finiteOrbitCoordinate π) := by
  intro q r h
  apply OnePoint.coe_injective
  apply π.injective
  exact
    (finiteOrbitCoordinate_coe π hπ q).symm.trans
      ((congrArg (fun z : ℂ => (z : RiemannSphere)) h).trans (finiteOrbitCoordinate_coe π hπ r))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.finiteOrbitInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOpenComplementBiholomorph.symm
    ⟨SpecialPeriods.MuTorsor.Cover.finiteInverse π z,
      SpecialPeriods.MuTorsor.Cover.finiteInverse_ne_cusp π hπ z⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.openInclusion_finiteOrbitInverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    SpecialPeriods.triangleOpenInclusion (finiteOrbitInverse π hπ z) =
      SpecialPeriods.MuTorsor.Cover.finiteInverse π z :=
  SpecialPeriods.triangleOpenComplementBiholomorph_symm_apply _

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteOrbitInverse_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteOrbitInverse π hπ) := by
  have hcod :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ =>
        (⟨SpecialPeriods.MuTorsor.Cover.finiteInverse π z,
            SpecialPeriods.MuTorsor.Cover.finiteInverse_ne_cusp π hπ z⟩ :
          SpecialPeriods.triangleCuspComplement)) := by
    intro z
    exact
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
        (SpecialPeriods.MuTorsor.Cover.finiteInverse_holomorphic π z)
  exact SpecialPeriods.triangleOpenComplementBiholomorph.symm.contMDiff.comp hcod

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_inverse
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℂ) :
    finiteOrbitCoordinate π (finiteOrbitInverse π hπ z) = z := by
  apply OnePoint.coe_injective
  rw [finiteOrbitCoordinate_coe π hπ, openInclusion_finiteOrbitInverse,
    SpecialPeriods.MuTorsor.Cover.apply_finiteInverse]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.BetaTorsor.finiteOrbitInverse_coordinate
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (q : SpecialPeriods.TriangleOrbitSpace) :
    finiteOrbitInverse π hπ (finiteOrbitCoordinate π q) = q :=
  finiteOrbitCoordinate_injective π hπ (finiteOrbitCoordinate_inverse π hπ _)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.finiteOrbitBiholomorph
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleOrbitSpace ℂ ω
    where
  toEquiv :=
    { toFun := finiteOrbitCoordinate π
      invFun := finiteOrbitInverse π hπ
      left_inv := finiteOrbitInverse_coordinate π hπ
      right_inv := finiteOrbitCoordinate_inverse π hπ }
  contMDiff_toFun := finiteOrbitCoordinate_holomorphic π hπ
  contMDiff_invFun := finiteOrbitInverse_holomorphic π hπ

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteProjection_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteProjection π) :=
  (finiteOrbitCoordinate_holomorphic π hπ).comp SpecialPeriods.triangleOrbitProjection_holomorphic

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteProjection_surjective
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Function.Surjective (finiteProjection π) := by
  intro z
  obtain ⟨a, ha⟩ := SpecialPeriods.triangleOrbitProjection_surjective (finiteOrbitInverse π hπ z)
  exact ⟨a, by simp only [finiteProjection, ha, finiteOrbitCoordinate_inverse]⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteProjection_invariant
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    finiteProjection π (SpecialPeriods.triangleGeometricRepresentation g z) =
      finiteProjection π z := by
  simp only [finiteProjection, SpecialPeriods.triangleOrbitProjection_smul]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteInverse_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ) :
    SpecialPeriods.MuTorsor.Cover.finiteInverse π (finiteProjection π z) =
      SpecialPeriods.triangleCompactifiedProjection z := by
  apply π.injective
  change
    π (SpecialPeriods.MuTorsor.Cover.finiteInverse π (finiteProjection π z)) =
      π (SpecialPeriods.triangleCompactifiedProjection z)
  rw [SpecialPeriods.MuTorsor.Cover.apply_finiteInverse]
  exact finiteOrbitCoordinate_coe π hπ (SpecialPeriods.triangleOrbitProjection z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteProjection_mem_pullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace) (z : ℍ) :
    finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePullback π V ↔
      SpecialPeriods.triangleCompactifiedProjection z ∈ V := by
  rw [SpecialPeriods.MuTorsor.Cover.mem_finitePullback, finiteInverse_finiteProjection π hπ]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.analyticOnNhd_finite_pullback
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (U : TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace)
    {f : SpecialPeriods.TriangleOrbitSpace → ℂ} (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f U) :
    AnalyticOnNhd ℂ (f ∘ finiteOrbitInverse π hπ)
      (finiteOrbitInverse π hπ ⁻¹' (U : Set SpecialPeriods.TriangleOrbitSpace)) := by
  intro z hz
  have hh := hf.contMDiffAt (U.isOpen.mem_nhds hz)
  exact (hh.comp z (finiteOrbitInverse_holomorphic π hπ z)).contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.eventually_mem_horodisc (Y : ℝ) :
    ∀ᶠ z in UpperHalfPlane.atImInfty, z ∈ SpecialPeriods.Triangle.horodisc Y := by
  apply (UpperHalfPlane.atImInfty_mem _).mpr
  exact ⟨Y + 1, fun _ hz => lt_of_lt_of_le (lt_add_one Y) hz⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.compactifiedProjection_tendsto_cusp :
    Filter.Tendsto SpecialPeriods.triangleCompactifiedProjection UpperHalfPlane.atImInfty
      (𝓝 SpecialPeriods.triangleCuspPoint) := by
  rw [SpecialPeriods.Triangle.cuspNeighborhood_basis.tendsto_right_iff]
  intro Y _
  filter_upwards [eventually_mem_horodisc Y] with z hz
  change
    SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z) ∈
      SpecialPeriods.Triangle.cuspNeighborhood Y
  apply (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood Y _).mpr
  exact ⟨z, hz, rfl⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.sphereProjection_tendsto_infty
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (π ∘ SpecialPeriods.triangleCompactifiedProjection) UpperHalfPlane.atImInfty
      (𝓝 ((OnePoint.infty) : RiemannSphere)) := by
  have h := π.continuous.continuousAt.tendsto.comp compactifiedProjection_tendsto_cusp
  simpa only [hπ] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_coe
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ) :
    (SpecialPeriods.BetaTorsor.finiteProjection π z : RiemannSphere) =
      π (SpecialPeriods.triangleCompactifiedProjection z) :=
  SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe π hπ
    (SpecialPeriods.triangleOrbitProjection z)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_tendsto_cobounded
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (SpecialPeriods.BetaTorsor.finiteProjection π) UpperHalfPlane.atImInfty
      (Bornology.cobounded ℂ) := by
  have hc :
    Filter.comap (fun z : ℂ => (z : RiemannSphere)) (𝓝 ((OnePoint.infty) : RiemannSphere)) =
      Bornology.cobounded ℂ := by
    simpa only [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
      (OnePoint.comap_coe_nhds_infty (X := ℂ))
  rw [← hc, Filter.tendsto_comap_iff]
  simpa only [Function.comp_def, finiteProjection_coe π hπ] using
    sphereProjection_tendsto_infty π hπ

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_norm_tendsto_atTop
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (fun z : ℍ => ‖SpecialPeriods.BetaTorsor.finiteProjection π z‖)
      UpperHalfPlane.atImInfty Filter.atTop :=
  tendsto_norm_cobounded_atTop.comp (finiteProjection_tendsto_cobounded π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.eventually_lt_norm_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (R : ℝ) :
    ∀ᶠ z in UpperHalfPlane.atImInfty, R < ‖SpecialPeriods.BetaTorsor.finiteProjection π z‖ :=
  (finiteProjection_norm_tendsto_atTop π hπ).eventually_gt_atTop R

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_eventually_ne_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∀ᶠ z in UpperHalfPlane.atImInfty, SpecialPeriods.BetaTorsor.finiteProjection π z ≠ 0 := by
  filter_upwards [eventually_lt_norm_finiteProjection π hπ 0] with z hz
  exact norm_pos_iff.mp hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_inv_tendsto_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    Filter.Tendsto (fun z : ℍ => (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹)
      UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) :=
  Filter.tendsto_inv₀_cobounded'.comp (finiteProjection_tendsto_cobounded π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.cuspChart_symm_cuspQ_of_mem (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) :
    (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
        (SpecialPeriods.Triangle.cuspQ z) =
      SpecialPeriods.triangleCompactifiedProjection z := by
  have hs :
    SpecialPeriods.triangleCompactifiedProjection z ∈
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).source := by
    rw [SpecialPeriods.Triangle.cuspFullChart_source]
    exact
      (SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood SpecialPeriods.Triangle.width
            _).mpr
        ⟨z, hz, rfl⟩
  have he := SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl ⟨z, hz⟩
  exact
    (congrArg (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).symm
          he).symm.trans
      ((SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl).left_inv hs)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection_of_mem
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width)
    (hp : SpecialPeriods.BetaTorsor.finiteProjection π z ≠ 0) :
    t π (SpecialPeriods.Triangle.cuspQ z) = (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ := by
  rw [t, cuspChart_symm_cuspQ_of_mem z hz, ← finiteProjection_coe π hπ z]
  exact sphereReciprocalCoordinate_coe hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      t π (SpecialPeriods.Triangle.cuspQ z) =
        (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ := by
  filter_upwards [eventually_mem_horodisc SpecialPeriods.Triangle.width,
    finiteProjection_eventually_ne_zero π hπ] with z hz hp
  exact t_cuspQ_eq_inv_finiteProjection_of_mem π hπ z hz hp

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.CuspCoordinates.analyticAt_correction
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {v S : ℂ → ℂ}
    (hv : AnalyticAt ℂ v 0) (hS : AnalyticAt ℂ S 0) :
    AnalyticAt ℂ (fun q => -v q * tDivQ π q * S (t π q)) 0 := by
  have hS' : AnalyticAt ℂ S (t π 0) := by simpa only [t_zero π hπ] using hS
  exact (hv.neg.mul (tDivQ_analyticAt_zero π hπ)).mul (hS'.comp (t_analyticAt_zero π hπ))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.exists_cusp_formula_radius
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ r₀ : ℝ,
      0 < r₀ ∧
        ∀ z : ℍ,
          ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r₀ →
            1728 * SpecialPeriods.BetaTorsor.finiteProjection π z =
              1728 /
                SpecialPeriods.MuTorsor.CuspCoordinates.t π
                  (Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)) := by
  obtain ⟨Y, hY⟩ :=
    (UpperHalfPlane.atImInfty_mem _).mp
      (SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ)
  refine ⟨SpecialPeriods.Triangle.cuspRadius Y, SpecialPeriods.Triangle.cuspRadius_pos Y, ?_⟩
  intro z hz
  have hheight : Y < z.im := (SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff Y z).mp hz
  have he := hY z hheight.le
  change
    SpecialPeriods.MuTorsor.CuspCoordinates.t π
        (Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)) =
      (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ at he
  rw [he, div_inv_eq_mul]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.SourceOrders.chartToFinite
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (j : Elliptic.Kind) : ℂ → ℂ :=
  SpecialPeriods.BetaTorsor.finiteOrbitCoordinate π ∘
    (SpecialPeriods.Triangle.ellipticFullChart j).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.ellipticFullChart_symm_zero (j : Elliptic.Kind) :
    (SpecialPeriods.Triangle.ellipticFullChart j).symm 0 =
      SpecialPeriods.Triangle.ellipticOrbitCenter j := by
  simpa only [SpecialPeriods.Triangle.ellipticFullChart_center] using
    (SpecialPeriods.Triangle.ellipticFullChart j).left_inv
      (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.SourceOrders.chartToFinite_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (j : Elliptic.Kind) :
    chartToFinite π j 0 =
      SpecialPeriods.BetaTorsor.finiteProjection π (SpecialPeriods.Triangle.ellipticCenter j) := by
  rw [chartToFinite, Function.comp_apply, ellipticFullChart_symm_zero]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_germ_eventuallyEq_chartToFinite
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (j : Elliptic.Kind) (z : ℍ)
    (hz :
      SpecialPeriods.triangleOrbitProjection z ∈
        (SpecialPeriods.Triangle.ellipticFullChart j).source) :
    (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (z : ℂ)]
      chartToFinite π j ∘
        (SpecialPeriods.Triangle.ellipticFullChart j ∘
          SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex) := by
  have hc :
    ContinuousAt (SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
    SpecialPeriods.triangleOrbitProjection_continuous.continuousAt.comp
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) z.im_pos).continuousAt
  have hz' :
    (SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex) (z : ℂ) ∈
      (SpecialPeriods.Triangle.ellipticFullChart j).source := by
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  have hU :
    ∀ᶠ w in 𝓝 (z : ℂ),
      SpecialPeriods.triangleOrbitProjection (UpperHalfPlane.ofComplex w) ∈
        (SpecialPeriods.Triangle.ellipticFullChart j).source :=
    hc ((SpecialPeriods.Triangle.ellipticFullChart j).open_source.mem_nhds hz')
  filter_upwards [hU] with w hw
  exact
    congrArg (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate π)
      ((SpecialPeriods.Triangle.ellipticFullChart j).left_inv hw).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.chartToFinite_isLocalDiffeomorphAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartToFinite π j) 0 := by
  have hzero : (0 : ℂ) ∈ (SpecialPeriods.Triangle.ellipticFullChart j).target := by
    simpa only [SpecialPeriods.Triangle.ellipticFullChart_center] using
      (SpecialPeriods.Triangle.ellipticFullChart j).map_source
        (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)
  have hinv :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (SpecialPeriods.Triangle.ellipticFullChart j).symm 0 :=
    (SpecialPeriods.triangleOrbitCoordinatePartial (.inr j)).symm.isLocalDiffeomorphAt _ _ _ hzero
  exact
    hinv.comp (K := 𝓘(ℂ)) (P := ℂ)
      ((SpecialPeriods.BetaTorsor.finiteOrbitBiholomorph π hπ).isLocalDiffeomorph _)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_analyticAt
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (z : ℍ) :
    AnalyticAt ℂ (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex)
      (z : ℂ) :=
  ((SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ).contMDiffAt.comp (z : ℂ)
      (UpperHalfPlane.contMDiffAt_ofComplex z.im_pos)).contDiffAt.analyticAt

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_eq_center_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z =
        SpecialPeriods.BetaTorsor.finiteProjection π (SpecialPeriods.Triangle.ellipticCenter j) ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.Triangle.ellipticOrbitCenter j :=
  (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_injective π hπ).eq_iff

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centered_order_center
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) :
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π
              (SpecialPeriods.Triangle.ellipticCenter j))
        (SpecialPeriods.Triangle.ellipticCenter j : ℂ) =
      (j.order : ℕ∞) := by
  let F : ℂ → ℂ :=
    SpecialPeriods.Triangle.ellipticFullChart j ∘
      SpecialPeriods.triangleOrbitProjection ∘ UpperHalfPlane.ofComplex
  have hF : AnalyticAt ℂ F (SpecialPeriods.Triangle.ellipticCenter j : ℂ) :=
    SpecialPeriods.Triangle.ellipticFullChart_complexGerm_analyticAt j
  have hF0 : F (SpecialPeriods.Triangle.ellipticCenter j : ℂ) = 0 := by
    simp only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact SpecialPeriods.Triangle.ellipticFullChart_center j
  have hlocal :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (chartToFinite π j)
      (F (SpecialPeriods.Triangle.ellipticCenter j : ℂ)) := by
    rw [hF0]
    exact chartToFinite_isLocalDiffeomorphAt_zero π hπ j
  have horder := centered_order_comp hF hlocal
  have he :
    (fun w : ℂ =>
        SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
          SpecialPeriods.BetaTorsor.finiteProjection π
            (SpecialPeriods.Triangle.ellipticCenter
              j)) =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j : ℂ)]
      (fun w =>
        chartToFinite π j (F w) -
          SpecialPeriods.BetaTorsor.finiteProjection π
            (SpecialPeriods.Triangle.ellipticCenter j)) := by
    filter_upwards [finiteProjection_germ_eventuallyEq_chartToFinite π j
        (SpecialPeriods.Triangle.ellipticCenter j)
        (SpecialPeriods.Triangle.ellipticFullChart_center_mem_source j)] with
      w hw
    exact
      congrArg
        (fun a : ℂ =>
          a -
            SpecialPeriods.BetaTorsor.finiteProjection π
              (SpecialPeriods.Triangle.ellipticCenter j))
        hw
  calc
    analyticOrderAt
          (fun w : ℂ =>
            SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
              SpecialPeriods.BetaTorsor.finiteProjection π
                (SpecialPeriods.Triangle.ellipticCenter j))
          (SpecialPeriods.Triangle.ellipticCenter j : ℂ) =
        analyticOrderAt
          (fun w =>
            chartToFinite π j (F w) -
              SpecialPeriods.BetaTorsor.finiteProjection π
                (SpecialPeriods.Triangle.ellipticCenter j))
          (SpecialPeriods.Triangle.ellipticCenter j : ℂ) :=
      analyticOrderAt_congr he
    _ = analyticOrderAt F (SpecialPeriods.Triangle.ellipticCenter j : ℂ) := by
      simpa only [hF0, chartToFinite_zero, sub_zero] using horder
    _ = (j.order : ℕ∞) := SpecialPeriods.Triangle.ellipticFullChart_order_center j

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centered_order_of_fibre
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (j : Elliptic.Kind) (z : ℍ)
    (hz :
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.Triangle.ellipticOrbitCenter j) :
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π
              (SpecialPeriods.Triangle.ellipticCenter j))
        (z : ℂ) =
      (j.order : ℕ∞) := by
  obtain ⟨g, rfl⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff z
          (SpecialPeriods.Triangle.ellipticCenter j)).mp
      hz
  have ht :=
    SpecialPeriods.Triangle.triangle_invariant_analyticOrderAt
      (fun a : ℍ =>
        SpecialPeriods.BetaTorsor.finiteProjection π a -
          SpecialPeriods.BetaTorsor.finiteProjection π (SpecialPeriods.Triangle.ellipticCenter j))
      (fun g a => by rw [SpecialPeriods.BetaTorsor.finiteProjection_invariant]) g
      (SpecialPeriods.Triangle.ellipticCenter j)
  exact ht.trans (finiteProjection_centered_order_center π hπ j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centerOne
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere)) :
    SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerOne = 0 := by
  apply OnePoint.coe_injective
  exact
    (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe π hπ
          SpecialPeriods.triangleOrbitCenterOne).trans
      h₀

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_centerTwo
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerTwo = 1 := by
  apply OnePoint.coe_injective
  exact
    (SpecialPeriods.BetaTorsor.finiteOrbitCoordinate_coe π hπ
          SpecialPeriods.triangleOrbitCenterTwo).trans
      h₁

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_eq_zero_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z = 0 ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne := by
  rw [← finiteProjection_centerOne π hπ h₀]
  exact finiteProjection_eq_center_iff π hπ .three z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_eq_one_iff
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z = 1 ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo := by
  rw [← finiteProjection_centerTwo π hπ h₁]
  exact finiteProjection_eq_center_iff π hπ .four z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.SourceOrders.sourceJ
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : ℂ :=
  1728 * SpecialPeriods.BetaTorsor.finiteProjection π z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_invariant
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    sourceJ π (SpecialPeriods.triangleGeometricRepresentation g z) = sourceJ π z := by
  simp only [sourceJ, SpecialPeriods.BetaTorsor.finiteProjection_invariant]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_eq_zero_iff_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : sourceJ π z = 0 ↔ SpecialPeriods.BetaTorsor.finiteProjection π z = 0 := by
  simp only [sourceJ, mul_eq_zero, show (1728 : ℂ) ≠ 0 by norm_num, false_or]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_eq_1728_iff_finiteProjection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℍ) : sourceJ π z = 1728 ↔ SpecialPeriods.BetaTorsor.finiteProjection π z = 1 := by
  constructor
  · intro h
    exact mul_left_cancel₀ (by norm_num : (1728 : ℂ) ≠ 0) (h.trans (mul_one (1728 : ℂ)).symm)
  · intro h
    simp only [sourceJ, h, mul_one]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (sourceJ π) :=
  contMDiff_const.mul (SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_order_of_eq_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : SpecialPeriods.BetaTorsor.finiteProjection π z = 0) :
    analyticOrderAt (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex)
        (z : ℂ) =
      3 := by
  have h :=
    finiteProjection_centered_order_of_fibre π hπ .three z
      ((finiteProjection_eq_zero_iff π hπ h₀ z).mp hz)
  change
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerOne)
        (z : ℂ) =
      3 at h
  simpa only [finiteProjection_centerOne π hπ h₀, sub_zero, Function.comp_def] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.finiteProjection_sub_one_order_of_eq_one
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : SpecialPeriods.BetaTorsor.finiteProjection π z = 1) :
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) - 1)
        (z : ℂ) =
      4 := by
  have h :=
    finiteProjection_centered_order_of_fibre π hπ .four z
      ((finiteProjection_eq_one_iff π hπ h₁ z).mp hz)
  change
    analyticOrderAt
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) -
            SpecialPeriods.BetaTorsor.finiteProjection π SpecialPeriods.Triangle.centerTwo)
        (z : ℂ) =
      4 at h
  simpa only [finiteProjection_centerTwo π hπ h₁] using h

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_centerOne
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere)) :
    sourceJ π SpecialPeriods.Triangle.centerOne = 0 := by
  simp only [sourceJ, finiteProjection_centerOne π hπ h₀, MulZeroClass.mul_zero]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_centerTwo
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    sourceJ π SpecialPeriods.Triangle.centerTwo = 1728 := by
  simp only [sourceJ, finiteProjection_centerTwo π hπ h₁, mul_one]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_of_eq_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : sourceJ π z = 0) :
    analyticOrderAt (sourceJ π ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 3 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) := analyticAt_const
  have hco : analyticOrderAt (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (by norm_num)
  change
    analyticOrderAt
        ((fun _ : ℂ => (1728 : ℂ)) *
          (SpecialPeriods.BetaTorsor.finiteProjection π ∘ UpperHalfPlane.ofComplex))
        (z : ℂ) =
      3
  rw [analyticOrderAt_mul hc (finiteProjection_analyticAt π hπ z), hco, zero_add]
  exact
    finiteProjection_order_of_eq_zero π hπ h₀ z ((sourceJ_eq_zero_iff_finiteProjection π z).mp hz)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_of_eq
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : sourceJ π z = 1728) :
    analyticOrderAt (fun w : ℂ => sourceJ π (UpperHalfPlane.ofComplex w) - 1728) (z : ℂ) = 4 := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) := analyticAt_const
  have hco : analyticOrderAt (fun _ : ℂ => (1728 : ℂ)) (z : ℂ) = 0 :=
    hc.analyticOrderAt_eq_zero.mpr (by norm_num)
  have hp :
    AnalyticAt ℂ
      (fun w : ℂ => SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) - 1)
      (z : ℂ) :=
    (finiteProjection_analyticAt π hπ z).sub analyticAt_const
  have he :
    (fun w : ℂ => sourceJ π (UpperHalfPlane.ofComplex w) - 1728) =
      (fun _ : ℂ => (1728 : ℂ)) *
        (fun w : ℂ =>
          SpecialPeriods.BetaTorsor.finiteProjection π (UpperHalfPlane.ofComplex w) - 1) := by
    funext w
    simp only [sourceJ, Pi.mul_apply]
    ring
  rw [he, analyticOrderAt_mul hc hp, hco, zero_add]
  exact
    finiteProjection_sub_one_order_of_eq_one π hπ h₁ z
      ((sourceJ_eq_1728_iff_finiteProjection π z).mp hz)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_centerOne
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere)) :
    analyticOrderAt (sourceJ π ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.Triangle.centerOne : ℂ) =
      3 :=
  sourceJ_order_of_eq_zero π hπ h₀ SpecialPeriods.Triangle.centerOne (sourceJ_centerOne π hπ h₀)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_centerTwo
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    analyticOrderAt (fun w : ℂ => sourceJ π (UpperHalfPlane.ofComplex w) - 1728)
        (SpecialPeriods.Triangle.centerTwo : ℂ) =
      4 :=
  sourceJ_sub_1728_order_of_eq π hπ h₁ SpecialPeriods.Triangle.centerTwo
    (sourceJ_centerTwo π hπ h₁)

abbrev SpecialPeriods.ModularOrbitSpace :=
  Quotient (MulAction.orbitRel SL(2, ℤ) ℍ)

def SpecialPeriods.modularOrbitProjection : ℍ → ModularOrbitSpace :=
  Quotient.mk _

theorem SpecialPeriods.modularOrbitProjection_continuous : Continuous modularOrbitProjection :=
  continuous_quotient_mk'

theorem SpecialPeriods.modularOrbitProjection_surjective :
    Function.Surjective modularOrbitProjection :=
  Quotient.mk_surjective

@[simp]
theorem SpecialPeriods.modularOrbitProjection_smul (γ : SL(2, ℤ)) (z : ℍ) :
    modularOrbitProjection (γ • z) = modularOrbitProjection z :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

def SpecialPeriods.modularQuotientJ : ModularOrbitSpace → ℂ :=
  Quotient.lift modularJ
    (by
      intro z w h
      change z ∈ MulAction.orbit SL(2, ℤ) w at h
      obtain ⟨γ, rfl⟩ := h
      exact modularJ_SL_invariant γ w)

@[simp]
theorem SpecialPeriods.modularQuotientJ_projection (z : ℍ) :
    modularQuotientJ (modularOrbitProjection z) = modularJ z :=
  rfl

theorem SpecialPeriods.modularQuotientJ_continuous : Continuous modularQuotientJ :=
  modularJ_continuous.quotient_lift _

theorem SpecialPeriods.modularJ_bounded_im (R : ℝ) :
    ∃ A : ℝ, ∀ z : ℍ, ‖modularJ z‖ ≤ R → z.im ≤ A := by
  have h := norm_modularJ_tendsto.eventually (Filter.eventually_gt_atTop R)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem {z : ℍ | R < ‖modularJ z‖}).mp h
  refine ⟨A, fun z hz => ?_⟩
  by_contra hzA
  exact (not_lt_of_ge hz) (hA z (le_of_lt (lt_of_not_ge hzA)))

theorem SpecialPeriods.modularQuotientJ_bounded_representatives (R : ℝ) :
    ∃ A : ℝ,
      ∀ x : ModularOrbitSpace,
        ‖modularQuotientJ x‖ ≤ R →
          x ∈ modularOrbitProjection '' ModularGroup.truncatedFundamentalDomain A := by
  obtain ⟨A, hA⟩ := modularJ_bounded_im R
  refine ⟨A, ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨γ • z, ⟨hγ, hA (γ • z) ?_⟩, modularOrbitProjection_smul γ z⟩
  simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hx

theorem SpecialPeriods.modularQuotientJ_isCompact_preimage {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (modularQuotientJ ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨A, hA⟩ := modularQuotientJ_bounded_representatives R
  have hcompact :
    IsCompact (modularOrbitProjection '' ModularGroup.truncatedFundamentalDomain A) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain A).image modularOrbitProjection_continuous
  exact
    hcompact.of_isClosed_subset (hK.isClosed.preimage modularQuotientJ_continuous)
      (fun x hx => hA x (hR _ hx))

theorem SpecialPeriods.modularQuotientJ_proper : IsProperMap modularQuotientJ :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨modularQuotientJ_continuous, fun _ hK => modularQuotientJ_isCompact_preimage hK⟩

theorem SpecialPeriods.modularQuotientJ_isClosedMap : IsClosedMap modularQuotientJ :=
  modularQuotientJ_proper.isClosedMap

theorem SpecialPeriods.modularJ_compact_fibre_finite {K : Set ℍ} (hK : IsCompact K) (c : ℂ) :
    (K ∩ modularJ ⁻¹' { c }).Finite := by
  have hd : IsDiscrete (K ∩ {z : ℍ | modularJ z = c}) :=
    (modularJ_fibre_isDiscrete c).mono Set.inter_subset_right
  have h := (hK.inter_right (modularJ_fibre_isClosed c)).finite hd
  simpa only [Set.preimage, Set.mem_singleton_iff] using h

theorem SpecialPeriods.modularQuotientJ_fibre_finite (c : ℂ) :
    (modularQuotientJ ⁻¹' { c }).Finite := by
  obtain ⟨A, hA⟩ := modularQuotientJ_bounded_representatives ‖c‖
  have hfinite :=
    modularJ_compact_fibre_finite (ModularGroup.isCompact_truncatedFundamentalDomain A) c
  apply (hfinite.image modularOrbitProjection).subset
  intro x hx
  have hxc : modularQuotientJ x = c := hx
  obtain ⟨z, hz, hzx⟩ := hA x (by rw [hxc])
  refine ⟨z, ⟨hz, ?_⟩, hzx⟩
  change modularJ z = c
  rw [← modularQuotientJ_projection, hzx, hxc]

theorem SpecialPeriods.modularQuotientJ_surjective : Function.Surjective modularQuotientJ := by
  intro c
  obtain ⟨z, hz⟩ := modularJ_surjective c
  exact ⟨modularOrbitProjection z, hz⟩

theorem SpecialPeriods.modularQuotientJ_isOpenMap : IsOpenMap modularQuotientJ :=
  IsOpenMap.of_comp modularOrbitProjection_continuous modularOrbitProjection_surjective
    modularJ_isOpenMap

instance SpecialPeriods.modularGroup_continuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul
    γ := ContinuousConstSMul.continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ)

instance SpecialPeriods.modularGroup_properlyDiscontinuous :
    ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  constructor
  intro K L hK hL
  have hfinite : {g : GL (Fin 2) ℝ | g ∈ 𝒮ℒ ∧ (g • K ∩ L).Nonempty}.Finite :=
    (Subgroup.properlyDiscontinuousSMul_iff 𝒮ℒ).mp inferInstance hK hL
  have hpre :=
    hfinite.preimage
      (Matrix.SpecialLinearGroup.mapGL_injective (R := ℤ) (n := Fin 2) (S := ℝ)).injOn
  exact hpre.subset fun γ hγ => ⟨⟨γ, rfl⟩, hγ⟩

theorem SpecialPeriods.modularOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap modularOrbitProjection :=
  MulAction.isOpenQuotientMap_quotientMk

theorem SpecialPeriods.modularOrbitProjection_isOpenMap : IsOpenMap modularOrbitProjection :=
  modularOrbitProjection_isOpenQuotientMap.isOpenMap

instance SpecialPeriods.modularOrbitSpace_t2 : T2Space ModularOrbitSpace :=
  t2Space_of_properlyDiscontinuousSMul_of_t2Space

private theorem SpecialPeriods.hasDerivAt_qParam_one_mo1973_16934 (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam 1)
      ((2 * Real.pi * Complex.I) * Function.Periodic.qParam 1 z) z := by
  change
    HasDerivAt (fun w : ℂ => Complex.exp ((2 * Real.pi * Complex.I) * w / 1))
      ((2 * Real.pi * Complex.I) * Complex.exp ((2 * Real.pi * Complex.I) * z / 1)) z
  simpa [Function.Periodic.qParam, mul_comm] using
    ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp

theorem SpecialPeriods.normalizedDerivOfComplex_eq_q_mul_deriv {k : ℤ} (f : ModularForm 𝒮ℒ k)
    (z : ℍ) :
    Derivative.normalizedDerivOfComplex f z =
      Function.Periodic.qParam 1 z *
        deriv (UpperHalfPlane.cuspFunction 1 f) (Function.Periodic.qParam 1 z) := by
  have hdiff :=
    ModularFormClass.differentiableAt_cuspFunction f zero_lt_one one_mem_strictPeriods_SL
      (Function.Periodic.norm_qParam_lt_one zero_lt_one z.im_pos)
  have hcomp := hdiff.hasDerivAt.comp (z : ℂ) (hasDerivAt_qParam_one_mo1973_16934 z)
  have heq :
    (f ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (z : ℂ)]
      (fun w => UpperHalfPlane.cuspFunction 1 f (Function.Periodic.qParam 1 w)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    have h :=
      SlashInvariantFormClass.eq_cuspFunction f (⟨w, hw⟩ : ℍ) one_mem_strictPeriods_SL one_ne_zero
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using h.symm
  have hd := (hcomp.congr_of_eventuallyEq heq).deriv
  rw [Derivative.normalizedDerivOfComplex, hd]
  field_simp [Complex.two_pi_I_ne_zero]

theorem SpecialPeriods.normalizedDerivOfComplex_tendsto_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto (Derivative.normalizedDerivOfComplex f) UpperHalfPlane.atImInfty (𝓝 0) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one one_mem_strictPeriods_SL
  have ht :=
    (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one).mul
      (ha.deriv.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one))
  simpa only [MulZeroClass.zero_mul, Function.comp_def,
    ← normalizedDerivOfComplex_eq_q_mul_deriv] using ht

theorem SpecialPeriods.E2_periodic_comp_ofComplex :
    Function.Periodic (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
  have hT (z : ℍ) : EisensteinSeries.E2 ((1 : ℝ) +ᵥ z) = EisensteinSeries.E2 z := by
    have h := congrFun (EisensteinSeries.E2_slash_action ModularGroup.T) z
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul] at h
    have hd : UpperHalfPlane.denom (ModularGroup.T : SL(2, ℤ)) z = 1 := by
      rw [ModularGroup.denom_apply]
      rw [ModularGroup.coe_T]
      norm_num
    simpa only [hd, one_zpow, mul_one, EisensteinSeries.D2_T, smul_zero, sub_zero] using h
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    have hz : UpperHalfPlane.ofComplex (w + 1) = (1 : ℝ) +ᵥ (⟨w, hw⟩ : ℍ) := by
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hw', add_comm]
    simpa [Function.comp_apply, hz, UpperHalfPlane.ofComplex_apply_of_im_pos hw] using hT ⟨w, hw⟩
  · have hw' : (w + 1).im ≤ 0 := by simpa using le_of_not_gt hw
    simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (le_of_not_gt hw)]

theorem SpecialPeriods.E2_cuspFunction_analyticAt_zero :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero zero_lt_one E2_periodic_comp_ofComplex
    E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2

theorem SpecialPeriods.E2_hasSum_qParam (z : ℍ) :
    HasSum
      (fun m : ℕ =>
        (if m = 0 then (1 : ℂ) else -24 * (ArithmeticFunction.sigma 1 m : ℂ)) •
          Function.Periodic.qParam 1 z ^ m)
      (EisensteinSeries.E2 z) := by
  simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one] using
    EisensteinSeries.hasSum_qExpansion_E2 (z := z)

private theorem SpecialPeriods.cuspFunction_zero_of_hasSum_mo1973_16940 (f : ℍ → ℂ) (c : ℕ → ℂ)
    (ha : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0)
    (hs : ∀ z : ℍ, HasSum (fun m => c m • Function.Periodic.qParam 1 z ^ m) (f z)) :
    UpperHalfPlane.cuspFunction 1 f 0 = c 0 := by
  have h :=
    (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (h := 1) (f := f) (c := c) zero_lt_one ha
          hs).coeff_zero
      (fun i => Fin.elim0 i)
  simpa using h.symm

theorem SpecialPeriods.E2_cuspFunction_zero :
    UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 0 = 1 := by
  exact
    cuspFunction_zero_of_hasSum_mo1973_16940 EisensteinSeries.E2
      (fun m => if m = 0 then (1 : ℂ) else -24 * (ArithmeticFunction.sigma 1 m : ℂ))
      E2_cuspFunction_analyticAt_zero E2_hasSum_qParam

theorem SpecialPeriods.E2_tendsto_one :
    Filter.Tendsto EisensteinSeries.E2 UpperHalfPlane.atImInfty (𝓝 1) := by
  have h :=
    E2_cuspFunction_analyticAt_zero.continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one)
  simpa only [Function.comp_def, E2_cuspFunction_zero,
    UpperHalfPlane.eq_cuspFunction _ one_ne_zero E2_periodic_comp_ofComplex] using h

theorem SpecialPeriods.modularForm_tendsto_qExpansion_coeff_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto f UpperHalfPlane.atImInfty (𝓝 ((UpperHalfPlane.qExpansion 1 f).coeff 0)) := by
  have h :=
    (ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one
          one_mem_strictPeriods_SL).continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) zero_lt_one)
  simpa [Function.comp_def, UpperHalfPlane.qExpansion_coeff,
    SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero] using h

theorem SpecialPeriods.serreDerivative_tendsto {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Filter.Tendsto (Derivative.serreDerivative k f) UpperHalfPlane.atImInfty
      (𝓝 (-(k : ℂ) / 12 * (UpperHalfPlane.qExpansion 1 f).coeff 0)) := by
  have h :=
    (normalizedDerivOfComplex_tendsto_zero f).sub
      (((tendsto_const_nhds (x := (k : ℂ) * 12⁻¹)).mul E2_tendsto_one).mul
        (modularForm_tendsto_qExpansion_coeff_zero f))
  convert h using 1
  · ext z
    rfl
  · congr 1
    ring

theorem SpecialPeriods.serreDerivative_boundedAtImInfty {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.serreDerivative k f) :=
  (serreDerivative_tendsto f).isBigO_one ℝ

def SpecialPeriods.serreDerivativeModularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ (k + 2)
    where
  toFun := Derivative.serreDerivative k f
  slash_action_eq' γ
    hγ := by
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hγ
    apply Derivative.serreDerivative_slash_invariant (ModularFormClass.holo f)
    exact SlashInvariantFormClass.slash_action_eq f g (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  holo' := Derivative.serreDerivative_mdifferentiable k (ModularFormClass.holo f)
  bdd_at_cusps'
    hc := by
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr
    intro γ hγ
    rw [Derivative.serreDerivative_slash_invariant (ModularFormClass.holo f)
        (SlashInvariantFormClass.slash_action_eq f γ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩))]
    exact serreDerivative_boundedAtImInfty f

theorem SpecialPeriods.serreDerivativeModularForm_qExpansion_coeff_zero {k : ℤ}
    (f : ModularForm 𝒮ℒ k) :
    (UpperHalfPlane.qExpansion 1 (serreDerivativeModularForm f)).coeff 0 =
      -(k : ℂ) / 12 * (UpperHalfPlane.qExpansion 1 f).coeff 0 := by
  apply
    tendsto_nhds_unique (modularForm_tendsto_qExpansion_coeff_zero (serreDerivativeModularForm f))
  exact serreDerivative_tendsto f

theorem SpecialPeriods.serreDerivative_E₄ (z : ℍ) :
    Derivative.serreDerivative 4 ModularForm.E₄ z = -(ModularForm.E₆ z) / 3 := by
  have heq : serreDerivativeModularForm ModularForm.E₄ = (-1 / 3 : ℂ) • ModularForm.E₆ := by
    apply levelOne_eq_of_qExpansion_coeff_zero (by norm_num)
    rw [serreDerivativeModularForm_qExpansion_coeff_zero, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
    norm_num
  have hz := congrArg (fun f : ModularForm 𝒮ℒ 6 => f z) heq
  change Derivative.serreDerivative 4 ModularForm.E₄ z = (-1 / 3 : ℂ) * ModularForm.E₆ z at hz
  rw [hz]
  ring

theorem SpecialPeriods.serreDerivative_E₆ (z : ℍ) :
    Derivative.serreDerivative 6 ModularForm.E₆ z = -(ModularForm.E₄ z ^ 2) / 2 := by
  have heq :
    serreDerivativeModularForm ModularForm.E₆ =
      (-1 / 2 : ℂ) • ModularForm.E₄.mul ModularForm.E₄ := by
    apply levelOne_eq_of_qExpansion_coeff_zero (by norm_num)
    rw [serreDerivativeModularForm_qExpansion_coeff_zero, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_mul]
    norm_num [EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩]
  have hz := congrArg (fun f : ModularForm 𝒮ℒ 8 => f z) heq
  change
    Derivative.serreDerivative 6 ModularForm.E₆ z =
      (-1 / 2 : ℂ) * (ModularForm.E₄ z * ModularForm.E₄ z) at hz
  rw [hz]
  ring

theorem SpecialPeriods.normalizedDeriv_E₄ (z : ℍ) :
    Derivative.normalizedDerivOfComplex ModularForm.E₄ z =
      (EisensteinSeries.E2 z * ModularForm.E₄ z - ModularForm.E₆ z) / 3 := by
  have h := serreDerivative_E₄ z
  unfold Derivative.serreDerivative at h
  linear_combination h

theorem SpecialPeriods.normalizedDeriv_E₆ (z : ℍ) :
    Derivative.normalizedDerivOfComplex ModularForm.E₆ z =
      (EisensteinSeries.E2 z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2) / 2 := by
  have h := serreDerivative_E₆ z
  unfold Derivative.serreDerivative at h
  linear_combination h

theorem SpecialPeriods.normalizedDeriv_discriminant (z : ℍ) :
    Derivative.normalizedDerivOfComplex ModularForm.discriminant z =
      EisensteinSeries.E2 z * ModularForm.discriminant z := by
  have hf :
    ModularForm.discriminant =
      (1 / 1728 : ℂ) • ((ModularForm.E₄ : ℍ → ℂ) ^ 3 - (ModularForm.E₆ : ℍ → ℂ) ^ 2) := by
    funext w
    change
      ModularForm.discriminant w = (1 / 1728 : ℂ) * (ModularForm.E₄ w ^ 3 - ModularForm.E₆ w ^ 2)
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have h4 : MDiff (ModularForm.E₄ : ℍ → ℂ) := ModularFormClass.holo ModularForm.E₄
  have h6 : MDiff (ModularForm.E₆ : ℍ → ℂ) := ModularFormClass.holo ModularForm.E₆
  rw [hf, Derivative.normalizedDerivOfComplex_smul _ _ ((h4.pow 3).sub (h6.pow 2)),
    Derivative.normalizedDerivOfComplex_sub _ _ (h4.pow 3) (h6.pow 2),
    Derivative.normalizedDerivOfComplex_pow _ 3 h4,
    Derivative.normalizedDerivOfComplex_pow _ 2 h6]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply,
    smul_eq_mul]
  rw [normalizedDeriv_E₄, normalizedDeriv_E₆]
  ring

theorem SpecialPeriods.deriv_eq_two_pi_I_mul_normalizedDeriv (f : ℍ → ℂ) (z : ℍ) :
    deriv (f ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) * Derivative.normalizedDerivOfComplex f z := by
  rw [Derivative.normalizedDerivOfComplex, ← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero,
    one_mul]

theorem SpecialPeriods.deriv_E₄ (z : ℍ) :
    deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) / 3 *
        (EisensteinSeries.E2 z * ModularForm.E₄ z - ModularForm.E₆ z) := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_E₄]
  ring

theorem SpecialPeriods.deriv_E₆ (z : ℍ) :
    deriv (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) / 2 *
        (EisensteinSeries.E2 z * ModularForm.E₆ z - ModularForm.E₄ z ^ 2) := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_E₆]
  ring

theorem SpecialPeriods.deriv_discriminant (z : ℍ) :
    deriv (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) * EisensteinSeries.E2 z * ModularForm.discriminant z := by
  rw [deriv_eq_two_pi_I_mul_normalizedDeriv, normalizedDeriv_discriminant]
  ring

theorem SpecialPeriods.deriv_E₄_ne_zero_of_eq_zero (z : ℍ) (hz : ModularForm.E₄ z = 0) :
    deriv (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  have h6 : ModularForm.E₆ z ≠ 0 := (E₄_E₆_not_both_zero z).resolve_left (by simp [hz])
  rw [deriv_E₄, hz, MulZeroClass.mul_zero, zero_sub]
  exact mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (by norm_num)) (neg_ne_zero.mpr h6)

theorem SpecialPeriods.deriv_E₆_ne_zero_of_eq_zero (z : ℍ) (hz : ModularForm.E₆ z = 0) :
    deriv (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  have h4 : ModularForm.E₄ z ≠ 0 := (E₄_E₆_not_both_zero z).resolve_right (by simp [hz])
  rw [deriv_E₆, hz, MulZeroClass.mul_zero, zero_sub]
  exact
    mul_ne_zero (div_ne_zero Complex.two_pi_I_ne_zero (by norm_num))
      (neg_ne_zero.mpr (pow_ne_zero 2 h4))

theorem SpecialPeriods.analyticOrderAt_E₄_of_eq_zero (z : ℍ) (hz : ModularForm.E₄ z = 0) :
    analyticOrderAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 1 := by
  apply (modularForm_analyticAt ModularForm.E₄ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  · exact deriv_E₄_ne_zero_of_eq_zero z hz

theorem SpecialPeriods.analyticOrderAt_E₆_of_eq_zero (z : ℍ) (hz : ModularForm.E₆ z = 0) :
    analyticOrderAt (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 1 := by
  apply (modularForm_analyticAt ModularForm.E₆ z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hz
  · exact deriv_E₆_ne_zero_of_eq_zero z hz

theorem SpecialPeriods.discriminant_analyticAt (z : ℍ) :
    AnalyticAt ℂ (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex) (z : ℂ) :=
  modularForm_analyticAt (CuspForm.discriminant : ModularForm 𝒮ℒ 12) z

theorem SpecialPeriods.deriv_modularJ (z : ℍ) :
    deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I) * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) /
        ModularForm.discriminant z := by
  have h₄ := (modularForm_analyticAt ModularForm.E₄ z).differentiableAt.hasDerivAt
  have hΔ := (discriminant_analyticAt z).differentiableAt.hasDerivAt
  have hd :=
    (h₄.pow 3).div hΔ
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  have he := hd.deriv
  change deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = _ at he
  rw [he]
  simp only [Pi.pow_apply, Function.comp_apply, UpperHalfPlane.ofComplex_apply, Nat.cast_ofNat,
    Nat.reduceSub]
  rw [deriv_E₄, deriv_discriminant]
  field_simp [ModularForm.discriminant_ne_zero z]
  ring

theorem SpecialPeriods.deriv_modularJ_eq_zero_iff (z : ℍ) :
    deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 0 ↔
      modularJ z = 0 ∨ modularJ z = 1728 := by
  rw [deriv_modularJ, modularJ_eq_zero_iff, modularJ_eq_1728_iff]
  simp [ModularForm.discriminant_ne_zero z]

theorem SpecialPeriods.deriv_modularJ_ne_zero (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  exact fun he => ((deriv_modularJ_eq_zero_iff z).mp he).elim h₀ h₁

theorem SpecialPeriods.discriminant_inv_order_zero (z : ℍ) :
    analyticOrderAt (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)⁻¹ (z : ℂ) = 0 := by
  have hΔ :=
    (discriminant_analyticAt z).inv
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  apply hΔ.analyticOrderAt_eq_zero.mpr
  simpa only [Pi.inv_apply, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    inv_ne_zero (ModularForm.discriminant_ne_zero z)

theorem SpecialPeriods.analyticOrderAt_modularJ_of_eq_zero (z : ℍ) (hz : modularJ z = 0) :
    analyticOrderAt (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ) = 3 := by
  have h₄ := modularForm_analyticAt ModularForm.E₄ z
  have hΔ :=
    (discriminant_analyticAt z).inv
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  change
    analyticOrderAt
        (((ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) ^ 3) *
          (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)⁻¹)
        (z : ℂ) =
      3
  rw [analyticOrderAt_mul (h₄.pow 3) hΔ, analyticOrderAt_pow h₄, discriminant_inv_order_zero,
    analyticOrderAt_E₄_of_eq_zero z ((modularJ_eq_zero_iff z).mp hz)]
  norm_num

theorem SpecialPeriods.analyticOrderAt_modularJ_sub_1728_of_eq (z : ℍ) (hz : modularJ z = 1728) :
    analyticOrderAt (fun w : ℂ => modularJ (UpperHalfPlane.ofComplex w) - 1728) (z : ℂ) = 2 := by
  have h₆ := modularForm_analyticAt ModularForm.E₆ z
  have hΔ :=
    (discriminant_analyticAt z).inv
      (by
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ModularForm.discriminant_ne_zero z)
  simp_rw [modularJ_sub_1728, div_eq_mul_inv]
  change
    analyticOrderAt
        (((ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) ^ 2) *
          (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)⁻¹)
        (z : ℂ) =
      2
  rw [analyticOrderAt_mul (h₆.pow 2) hΔ, analyticOrderAt_pow h₆, discriminant_inv_order_zero,
    analyticOrderAt_E₆_of_eq_zero z ((modularJ_eq_1728_iff z).mp hz)]
  norm_num

def SpecialPeriods.modularLocalInverse (z : ℍ) (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) :
    ℂ → ℂ :=
  (modularJ_analyticAt z).hasStrictDerivAt.localInverse (modularJ ∘ UpperHalfPlane.ofComplex)
    (deriv (modularJ ∘ UpperHalfPlane.ofComplex) (z : ℂ)) (z : ℂ) (deriv_modularJ_ne_zero z h₀ h₁)

theorem SpecialPeriods.modularLocalInverse_analyticAt (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : AnalyticAt ℂ (modularLocalInverse z h₀ h₁) (modularJ z) := by
  simpa only [modularLocalInverse, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    (modularJ_analyticAt z).analyticAt_localInverse (deriv_modularJ_ne_zero z h₀ h₁)

theorem SpecialPeriods.modularLocalInverse_eventually_left_inverse (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) :
    ∀ᶠ w in 𝓝 (z : ℂ), modularLocalInverse z h₀ h₁ (modularJ (UpperHalfPlane.ofComplex w)) = w :=
  (modularJ_analyticAt z).hasStrictDerivAt.eventually_left_inverse
    (deriv_modularJ_ne_zero z h₀ h₁)

theorem SpecialPeriods.modularLocalInverse_eventually_right_inverse (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) :
    ∀ᶠ w in 𝓝 (modularJ z),
      modularJ (UpperHalfPlane.ofComplex (modularLocalInverse z h₀ h₁ w)) = w := by
  simpa only [modularLocalInverse, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    (modularJ_analyticAt z).hasStrictDerivAt.eventually_right_inverse
      (deriv_modularJ_ne_zero z h₀ h₁)

def SpecialPeriods.modularRegularValues : Set ℂ :=
  ({0, 1728} : Set ℂ)ᶜ

@[simp]
theorem SpecialPeriods.mem_modularRegularValues (c : ℂ) :
    c ∈ modularRegularValues ↔ c ≠ 0 ∧ c ≠ 1728 := by simp [modularRegularValues]

theorem SpecialPeriods.modularJ_regular_injOn_neighbourhood (z : ℍ) (h₀ : modularJ z ≠ 0)
    (h₁ : modularJ z ≠ 1728) : ∃ U : Set ℍ, IsOpen U ∧ z ∈ U ∧ Set.InjOn modularJ U := by
  have hleft : ∀ᶠ w in 𝓝 z, modularLocalInverse z h₀ h₁ (modularJ w) = (w : ℂ) := by
    have h :=
      UpperHalfPlane.continuous_coe.continuousAt.tendsto.eventually
        (modularLocalInverse_eventually_left_inverse z h₀ h₁)
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h
  obtain ⟨U, hU, hUo, hz⟩ := mem_nhds_iff.mp hleft
  refine ⟨U, hUo, hz, ?_⟩
  intro w hw v hv heq
  apply UpperHalfPlane.ext
  rw [← hU hw, ← hU hv, heq]

theorem SpecialPeriods.modularQuotientJ_regular_injOn_neighbourhood (x : ModularOrbitSpace)
    (hx : modularQuotientJ x ∈ modularRegularValues) :
    ∃ V : Set ModularOrbitSpace, IsOpen V ∧ x ∈ V ∧ Set.InjOn modularQuotientJ V := by
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨h₀, h₁⟩ := (mem_modularRegularValues _).mp hx
  obtain ⟨U, hUo, hz, hinj⟩ := modularJ_regular_injOn_neighbourhood z h₀ h₁
  refine ⟨modularOrbitProjection '' U, modularOrbitProjection_isOpenMap U hUo, ⟨z, hz, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩ _ ⟨v, hv, rfl⟩ h
  exact congrArg modularOrbitProjection (hinj hw hv h)

theorem SpecialPeriods.modularQuotientJ_regular_isLocalHomeomorphOn :
    IsLocalHomeomorphOn modularQuotientJ (modularQuotientJ ⁻¹' modularRegularValues) := by
  intro x hx
  obtain ⟨V, hVo, hxV, hinj⟩ := modularQuotientJ_regular_injOn_neighbourhood x hx
  let e :=
    OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv modularQuotientJ V)
      modularQuotientJ_continuous.continuousOn modularQuotientJ_isOpenMap hVo
  exact ⟨e, hxV, rfl⟩

theorem SpecialPeriods.modularQuotientJ_regular_isCoveringMapOn :
    IsCoveringMapOn modularQuotientJ modularRegularValues :=
  modularQuotientJ_isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun c _ => modularQuotientJ_fibre_finite c) modularQuotientJ_regular_isLocalHomeomorphOn

abbrev SpecialPeriods.ModularRegularBase :=
  ↥modularRegularValues

abbrev SpecialPeriods.ModularRegularOrbitSpace :=
  ↥(modularQuotientJ ⁻¹' modularRegularValues)

def SpecialPeriods.modularRegularQuotientJ : ModularRegularOrbitSpace → ModularRegularBase :=
  modularRegularValues.restrictPreimage modularQuotientJ

theorem SpecialPeriods.modularRegularQuotientJ_isCoveringMap :
    IsCoveringMap modularRegularQuotientJ :=
  modularQuotientJ_regular_isCoveringMapOn.isCoveringMap_restrictPreimage

def SpecialPeriods.modularCuspBase (q : ℂ) : ℂ :=
  1728 * q / modularJUnit q

@[simp]
theorem SpecialPeriods.modularCuspBase_zero : modularCuspBase 0 = 0 := by simp [modularCuspBase]

theorem SpecialPeriods.modularCuspBase_analyticAt_zero : AnalyticAt ℂ modularCuspBase 0 :=
  (analyticAt_const.mul analyticAt_id).div modularJUnit_analyticAt_zero (by simp)

theorem SpecialPeriods.modularCuspBase_hasDerivAt : HasDerivAt modularCuspBase 1728 0 := by
  have hn : HasDerivAt (fun q : ℂ => 1728 * q) 1728 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℂ)).const_mul (1728 : ℂ)
  have hu : HasDerivAt modularJUnit (deriv modularJUnit 0) 0 :=
    modularJUnit_analyticAt_zero.differentiableAt.hasDerivAt
  have hd := hn.div hu (by simp : modularJUnit 0 ≠ 0)
  change
    HasDerivAt modularCuspBase
      ((1728 * modularJUnit 0 - (1728 * (0 : ℂ)) * deriv modularJUnit 0) / modularJUnit 0 ^ 2)
      0 at hd
  simpa only [modularJUnit_zero, mul_one, MulZeroClass.mul_zero, MulZeroClass.zero_mul, sub_zero,
    one_pow, div_one] using hd

theorem SpecialPeriods.modularCuspBase_deriv : deriv modularCuspBase 0 = 1728 :=
  modularCuspBase_hasDerivAt.deriv

theorem SpecialPeriods.modularCuspBase_deriv_ne_zero : deriv modularCuspBase 0 ≠ 0 := by
  rw [modularCuspBase_deriv]
  norm_num

def SpecialPeriods.modularCuspQ : ℂ → ℂ :=
  modularCuspBase_analyticAt_zero.hasStrictDerivAt.localInverse modularCuspBase
    (deriv modularCuspBase 0) 0 modularCuspBase_deriv_ne_zero

theorem SpecialPeriods.modularCuspQ_analyticAt_zero : AnalyticAt ℂ modularCuspQ 0 := by
  simpa only [modularCuspQ, modularCuspBase_zero] using
    modularCuspBase_analyticAt_zero.analyticAt_localInverse modularCuspBase_deriv_ne_zero

theorem SpecialPeriods.modularCuspQ_eventually_left_inverse :
    ∀ᶠ q in 𝓝 (0 : ℂ), modularCuspQ (modularCuspBase q) = q :=
  modularCuspBase_analyticAt_zero.hasStrictDerivAt.eventually_left_inverse
    modularCuspBase_deriv_ne_zero

theorem SpecialPeriods.modularCuspQ_eventually_right_inverse :
    ∀ᶠ t in 𝓝 (0 : ℂ), modularCuspBase (modularCuspQ t) = t := by
  simpa only [modularCuspQ, modularCuspBase_zero] using
    modularCuspBase_analyticAt_zero.hasStrictDerivAt.eventually_right_inverse
      modularCuspBase_deriv_ne_zero

@[simp]
theorem SpecialPeriods.modularCuspQ_zero : modularCuspQ 0 = 0 := by
  simpa only [modularCuspBase_zero] using modularCuspQ_eventually_left_inverse.self_of_nhds

theorem SpecialPeriods.modularCuspQ_hasDerivAt : HasDerivAt modularCuspQ (1 / 1728) 0 := by
  simpa only [modularCuspQ, modularCuspBase_zero, modularCuspBase_deriv, one_div] using
    (modularCuspBase_analyticAt_zero.hasStrictDerivAt.to_localInverse
        modularCuspBase_deriv_ne_zero).hasDerivAt

theorem SpecialPeriods.modularCuspQ_deriv : deriv modularCuspQ 0 = 1 / 1728 :=
  modularCuspQ_hasDerivAt.deriv

def SpecialPeriods.modularCuspUnit : ℂ → ℂ :=
  dslope modularCuspQ 0

theorem SpecialPeriods.modularCuspUnit_analyticAt_zero : AnalyticAt ℂ modularCuspUnit 0 :=
  modularCuspQ_analyticAt_zero.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

@[simp]
theorem SpecialPeriods.modularCuspUnit_zero : modularCuspUnit 0 = 1 / 1728 := by
  rw [modularCuspUnit, dslope_same, modularCuspQ_deriv]

theorem SpecialPeriods.modularCuspQ_eq_mul_unit (t : ℂ) :
    modularCuspQ t = t * modularCuspUnit t := by
  simpa only [modularCuspUnit, sub_zero, modularCuspQ_zero, smul_eq_mul] using
    (sub_smul_dslope modularCuspQ 0 t).symm

theorem SpecialPeriods.modularCuspUnit_eventually_ne_zero :
    ∀ᶠ t in 𝓝 (0 : ℂ), modularCuspUnit t ≠ 0 :=
  modularCuspUnit_analyticAt_zero.continuousAt.eventually_ne (by simp)

theorem SpecialPeriods.modularCuspQ_eventually_j_eq :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), modularJInQ (modularCuspQ t) = 1728 / t := by
  filter_upwards [modularCuspQ_eventually_right_inverse.filter_mono nhdsWithin_le_nhds,
    modularCuspUnit_eventually_ne_zero.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t
    ht hu ht₀
  have ht₀' : t ≠ 0 := ht₀
  have hq : modularCuspQ t ≠ 0 := by rw [modularCuspQ_eq_mul_unit]; exact mul_ne_zero ht₀' hu
  have hj : modularJUnit (modularCuspQ t) ≠ 0 := by
    intro h
    simp [modularCuspBase, h] at ht
    exact ht₀' ht.symm
  unfold modularCuspBase at ht
  unfold modularJInQ
  rw [eq_div_iff ht₀']
  calc
    modularJUnit (modularCuspQ t) / modularCuspQ t * t =
        modularJUnit (modularCuspQ t) / modularCuspQ t *
          (1728 * modularCuspQ t / modularJUnit (modularCuspQ t)) :=
      congrArg (fun v => modularJUnit (modularCuspQ t) / modularCuspQ t * v) ht.symm
    _ = 1728 := by field_simp

theorem SpecialPeriods.modularCuspBase_eq_div_j (q : ℂ) :
    modularCuspBase q = 1728 / modularJInQ q := by
  rw [modularCuspBase, modularJInQ, div_div_eq_mul_div]

theorem SpecialPeriods.modularJInQ_injOn_small_disc :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn modularJInQ (Metric.ball 0 r) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp modularCuspQ_eventually_left_inverse
  refine ⟨r, hr, ?_⟩
  intro q hq w hw he
  calc
    q = modularCuspQ (modularCuspBase q) := (hball hq).symm
    _ = modularCuspQ (modularCuspBase w) := by
      rw [modularCuspBase_eq_div_j, he, ← modularCuspBase_eq_div_j]
    _ = w := hball hw

theorem SpecialPeriods.modularOrbitProjection_eq_of_qParam_eq {z w : ℍ}
    (hq : Function.Periodic.qParam 1 (z : ℂ) = Function.Periodic.qParam 1 (w : ℂ)) :
    modularOrbitProjection z = modularOrbitProjection w := by
  obtain ⟨m, hm⟩ :=
    Function.Periodic.qParam_left_inv_mod_period (h := (1 : ℝ)) one_ne_zero (z : ℂ)
  obtain ⟨n, hn⟩ :=
    Function.Periodic.qParam_left_inv_mod_period (h := (1 : ℝ)) one_ne_zero (w : ℂ)
  have he : (z : ℂ) + (m : ℂ) = (w : ℂ) + (n : ℂ) := by
    simpa only [Complex.ofReal_one, mul_one] using
      hm.symm.trans ((congrArg (Function.Periodic.invQParam 1) hq).trans hn)
  have htw : ModularGroup.T ^ (m - n) • z = w := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq, Int.cast_sub]
    linear_combination he
  rw [← htw, modularOrbitProjection_smul]

theorem SpecialPeriods.modularJ_high_im_orbit_separation :
    ∃ A : ℝ,
      ∀ z w : ℍ,
        A ≤ z.im →
          A ≤ w.im →
            modularJ z = modularJ w → modularOrbitProjection z = modularOrbitProjection w := by
  obtain ⟨r, hr, hinj⟩ := modularJInQ_injOn_small_disc
  have hevent :
    {z : ℍ | Function.Periodic.qParam 1 (z : ℂ) ∈ Metric.ball 0 r} ∈ UpperHalfPlane.atImInfty :=
    (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one).eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨A, hA⟩ := UpperHalfPlane.atImInfty_mem _ |>.mp hevent
  refine ⟨A, fun z w hz hw hj => modularOrbitProjection_eq_of_qParam_eq ?_⟩
  apply hinj (hA z hz) (hA w hw)
  simpa only [modularJInQ_qParam] using hj

theorem SpecialPeriods.modularQuotientJ_large_norm_injective :
    ∃ R : ℝ,
      ∀ x y : ModularOrbitSpace,
        R < ‖modularQuotientJ x‖ → modularQuotientJ x = modularQuotientJ y → x = y := by
  obtain ⟨A, hA⟩ := modularJ_high_im_orbit_separation
  have hcompact := ModularGroup.isCompact_truncatedFundamentalDomain A
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn modularJ_continuous.continuousOn
  refine ⟨R, ?_⟩
  intro x y hx hxy
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨w, rfl⟩ := modularOrbitProjection_surjective y
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨δ, hδ⟩ := ModularGroup.exists_smul_mem_fd w
  have hzlarge : R < ‖modularJ (γ • z)‖ := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hx
  have hwlarge : R < ‖modularJ (δ • w)‖ := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection, hxy] using hx
  have hzheight : A ≤ (γ • z).im := by
    by_contra h
    exact (not_lt_of_ge (hR (γ • z) ⟨hγ, (lt_of_not_ge h).le⟩)) hzlarge
  have hwheight : A ≤ (δ • w).im := by
    by_contra h
    exact (not_lt_of_ge (hR (δ • w) ⟨hδ, (lt_of_not_ge h).le⟩)) hwlarge
  have heq : modularJ (γ • z) = modularJ (δ • w) := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hxy
  simpa only [modularOrbitProjection_smul] using hA _ _ hzheight hwheight heq

theorem SpecialPeriods.modularQuotientJ_unique_fibre_at_large_values :
    ∃ R : ℝ, 0 < R ∧ ∀ c : ℂ, R < ‖c‖ → ∃! x : ModularOrbitSpace, modularQuotientJ x = c := by
  obtain ⟨R, hR⟩ := modularQuotientJ_large_norm_injective
  refine ⟨Max.max R 0 + 1, by positivity, ?_⟩
  intro c hc
  obtain ⟨x, hx⟩ := modularQuotientJ_surjective c
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply hR y x
  · rw [hy]
    exact
      (lt_of_le_of_lt (le_max_left R 0) (lt_add_of_pos_right (Max.max R 0) zero_lt_one)).trans hc
  · exact hy.trans hx.symm

theorem SpecialPeriods.ModularCoverTools.injective_of_covering_singleton_fibre {X B : Type*}
    [TopologicalSpace X] [TopologicalSpace B] [PathConnectedSpace B] {f : X → B}
    (hf : IsCoveringMap f) (b₀ : B) (h₀ : Subsingleton (f ⁻¹' { b₀ })) : Function.Injective f := by
  intro x y hxy
  let γ : Path.Homotopic.Quotient (f x) b₀ := .mk (PathConnectedSpace.somePath (f x) b₀)
  have he : (⟨x, rfl⟩ : f ⁻¹' {f x}) = ⟨y, hxy.symm⟩ := (hf.monodromy_bijective γ).1 (h₀.elim _ _)
  exact congrArg Subtype.val he

theorem SpecialPeriods.ModularCoverTools.injective_of_open_dense {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {f : X → Y} {D : Set Y}
    (hf : IsOpenMap f) (hD : Dense D) (hi : Set.InjOn f (f ⁻¹' D)) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hne
  have hnonempty : (f '' U ∩ f '' V).Nonempty := ⟨f x, ⟨x, hx, rfl⟩, y, hy, hxy.symm⟩
  obtain ⟨z, hzD, ⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ :=
    hD.exists_mem_open ((hf U hU).inter (hf V hV)) hnonempty
  have huv : u = v :=
    hi (by simpa only [Set.mem_preimage, huz] using hzD)
      (by simpa only [Set.mem_preimage, hvz] using hzD) (huz.trans hvz.symm)
  subst v
  exact hUV.le_bot ⟨hu, hv⟩

theorem SpecialPeriods.ModularCoverTools.complex_compl_countable_pathConnected {S : Set ℂ}
    (hS : S.Countable) : PathConnectedSpace ↥(Sᶜ) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (hS.isPathConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex]))

theorem SpecialPeriods.ModularCoverTools.complex_compl_pair_pathConnected (a b : ℂ) :
    PathConnectedSpace ↥(({ a, b } : Set ℂ)ᶜ) :=
  complex_compl_countable_pathConnected (Set.toFinite _).countable

theorem SpecialPeriods.ModularCoverTools.complex_compl_countable_dense {S : Set ℂ}
    (hS : S.Countable) : Dense Sᶜ :=
  hS.dense_compl ℝ

theorem SpecialPeriods.ModularCoverTools.complex_compl_pair_dense (a b : ℂ) :
    Dense (({ a, b } : Set ℂ)ᶜ) :=
  complex_compl_countable_dense (Set.toFinite _).countable

instance SpecialPeriods.modularRegularBase_pathConnected :
    PathConnectedSpace ModularRegularBase :=
  ModularCoverTools.complex_compl_pair_pathConnected 0 1728

theorem SpecialPeriods.modularRegularValues_dense : Dense modularRegularValues :=
  ModularCoverTools.complex_compl_pair_dense 0 1728

theorem SpecialPeriods.modularRegularQuotientJ_exists_subsingleton_fibre :
    ∃ c : ModularRegularBase, Subsingleton (modularRegularQuotientJ ⁻¹' { c }) := by
  obtain ⟨R, hR, hlarge⟩ := modularQuotientJ_unique_fibre_at_large_values
  let r : ℝ := Max.max R 1728 + 1
  have hrpos : 0 < r := by dsimp [r]; linarith [le_max_right R (1728 : ℝ)]
  have hrbig : 1728 < r := by dsimp [r]; linarith [le_max_right R (1728 : ℝ)]
  have hrR : R < r := by dsimp [r]; linarith [le_max_left R (1728 : ℝ)]
  let c : ModularRegularBase :=
    ⟨(r : ℂ),
      (mem_modularRegularValues _).mpr ⟨by exact_mod_cast hrpos.ne', by exact_mod_cast hrbig.ne'⟩⟩
  have hRc : R < ‖(c : ℂ)‖ := by
    change R < ‖(r : ℂ)‖
    simpa only [Complex.norm_real, Real.norm_of_nonneg hrpos.le] using hrR
  obtain ⟨x, hx, hunique⟩ := hlarge c hRc
  refine ⟨c, ⟨?_⟩⟩
  intro u v
  apply Subtype.ext
  apply Subtype.ext
  have hu : modularQuotientJ (u.1 : ModularOrbitSpace) = (c : ℂ) :=
    congrArg Subtype.val (show modularRegularQuotientJ u.1 = c from u.2)
  have hv : modularQuotientJ (v.1 : ModularOrbitSpace) = (c : ℂ) :=
    congrArg Subtype.val (show modularRegularQuotientJ v.1 = c from v.2)
  exact (hunique _ hu).trans (hunique _ hv).symm

theorem SpecialPeriods.modularRegularQuotientJ_injective :
    Function.Injective modularRegularQuotientJ := by
  obtain ⟨c, hc⟩ := modularRegularQuotientJ_exists_subsingleton_fibre
  exact
    ModularCoverTools.injective_of_covering_singleton_fibre modularRegularQuotientJ_isCoveringMap
      c hc

theorem SpecialPeriods.modularQuotientJ_injOn_regular :
    Set.InjOn modularQuotientJ (modularQuotientJ ⁻¹' modularRegularValues) := by
  intro x hx y hy hxy
  have h : (⟨x, hx⟩ : ModularRegularOrbitSpace) = ⟨y, hy⟩ :=
    modularRegularQuotientJ_injective (Subtype.ext hxy)
  exact congrArg Subtype.val h

theorem SpecialPeriods.modularQuotientJ_injective : Function.Injective modularQuotientJ :=
  ModularCoverTools.injective_of_open_dense modularQuotientJ_isOpenMap modularRegularValues_dense
    modularQuotientJ_injOn_regular

theorem SpecialPeriods.modularJ_eq_iff_mem_orbit (z w : ℍ) :
    modularJ z = modularJ w ↔ z ∈ MulAction.orbit SL(2, ℤ) w := by
  constructor
  · intro h
    exact Quotient.exact (modularQuotientJ_injective h)
  · intro h
    exact congrArg modularQuotientJ (Quotient.sound h)

theorem SpecialPeriods.modularJ_eq_iff_exists_smul (z w : ℍ) :
    modularJ z = modularJ w ↔ ∃ γ : SL(2, ℤ), γ • w = z :=
  modularJ_eq_iff_mem_orbit z w

theorem SpecialPeriods.exists_analytic_power_coordinate {F : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ h a = 0 ∧ deriv h a ≠ 0 ∧ ∀ᶠ w in 𝓝 a, F w = h w ^ m := by
  obtain ⟨g, hg, hga, hFg⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  obtain ⟨r, hr, hra, hrpow⟩ := AnalyticRootCover.exists_analytic_unit_root hg hga hm
  let h : ℂ → ℂ := fun w => (w - a) * r w
  have hh : AnalyticAt ℂ h a := (analyticAt_id.sub analyticAt_const).mul hr
  have hderiv : deriv h a = r a := by
    simpa only [h, id_eq, sub_self, MulZeroClass.zero_mul, one_mul, add_zero] using
      (((hasDerivAt_id a).sub_const a).fun_mul hr.differentiableAt.hasDerivAt).deriv
  refine ⟨h, hh, by simp [h], hderiv ▸ hra, ?_⟩
  filter_upwards [hFg, hrpow] with w hw hwr
  rw [hw, smul_eq_mul, ← hwr, ← mul_pow]

theorem SpecialPeriods.exists_analytic_power_chart_in {F : ℂ → ℂ} {a : ℂ} {m : ℕ} {U : Set ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) (hU : U ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧
        e a = 0 ∧
          e.source ⊆ U ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧ ∀ w ∈ e.source, F w = e w ^ m := by
  obtain ⟨h, hh, hha, hdh, hpower⟩ := exists_analytic_power_coordinate hF horder hm
  obtain ⟨e₀, hae₀, he₀, hea, hei⟩ := exists_analytic_openPartialHomeomorph hh hdh
  have hboth : ∀ᶠ w in 𝓝 a, F w = h w ^ m ∧ w ∈ U := hpower.and hU
  obtain ⟨V, hV, hVo, haV⟩ := eventually_nhds_iff.mp hboth
  let e : OpenPartialHomeomorph ℂ ℂ := e₀.restrOpen V hVo
  refine ⟨e, ⟨hae₀, haV⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (he₀ a).trans hha
  · intro w hw
    exact (hV w hw.2).2
  · intro w hw
    exact hea w hw.1
  · intro w hw
    exact hei w hw.1
  · intro w hw
    exact (hV w hw.2).1.trans (congrArg (· ^ m) (he₀ w).symm)

theorem SpecialPeriods.exists_analytic_power_chart {F : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = m) (hm : 0 < m) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧
        e a = 0 ∧
          AnalyticOnNhd ℂ e e.source ∧
            AnalyticOnNhd ℂ e.symm e.target ∧ ∀ w ∈ e.source, F w = e w ^ m := by
  obtain ⟨e, ha, he, _, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in hF horder hm (Filter.univ_mem : Set.univ ∈ 𝓝 a)
  exact ⟨e, ha, he, hf, hi, hp⟩

theorem SpecialPeriods.power_chart_inverse_identity (e : OpenPartialHomeomorph ℂ ℂ) {F : ℂ → ℂ}
    {m : ℕ} (hp : ∀ w ∈ e.source, F w = e w ^ m) : ∀ w ∈ e.target, F (e.symm w) = w ^ m := by
  intro w hw
  rw [hp _ (e.map_target hw), e.right_inv hw]

theorem SpecialPeriods.modularJ_cubic_chart (z : ℍ) (hz : modularJ z = 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧
        e z = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) = e w ^ 3) ∧
                  (∀ w ∈ e.target, modularJ (UpperHalfPlane.ofComplex (e.symm w)) = w ^ 3) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in (modularJ_analyticAt z)
      (analyticOrderAt_modularJ_of_eq_zero z hz) (by decide : 0 < 3)
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  exact ⟨e, ha, he, hU, hf, hi, hp, power_chart_inverse_identity e hp⟩

theorem SpecialPeriods.modularJ_quadratic_chart (z : ℍ) (hz : modularJ z = 1728) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (z : ℂ) ∈ e.source ∧
        e z = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) - 1728 = e w ^ 2) ∧
                  (∀ w ∈ e.target,
                    modularJ (UpperHalfPlane.ofComplex (e.symm w)) - 1728 = w ^ 2) := by
  obtain ⟨e, ha, he, hU, hf, hi, hp⟩ :=
    exists_analytic_power_chart_in ((modularJ_analyticAt z).sub analyticAt_const)
      (analyticOrderAt_modularJ_sub_1728_of_eq z hz) (by decide : 0 < 2)
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  exact ⟨e, ha, he, hU, hf, hi, hp, power_chart_inverse_identity e hp⟩

theorem SpecialPeriods.modularJ_rhoPoint_cubic_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      rho ∈ e.source ∧
        e rho = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) = e w ^ 3) ∧
                  (∀ w ∈ e.target, modularJ (UpperHalfPlane.ofComplex (e.symm w)) = w ^ 3) :=
  modularJ_cubic_chart rhoPoint modularJ_rhoPoint

theorem SpecialPeriods.modularJ_I_quadratic_chart :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      Complex.I ∈ e.source ∧
        e Complex.I = 0 ∧
          e.source ⊆ UpperHalfPlane.upperHalfPlaneSet ∧
            AnalyticOnNhd ℂ e e.source ∧
              AnalyticOnNhd ℂ e.symm e.target ∧
                (∀ w ∈ e.source, modularJ (UpperHalfPlane.ofComplex w) - 1728 = e w ^ 2) ∧
                  (∀ w ∈ e.target,
                    modularJ (UpperHalfPlane.ofComplex (e.symm w)) - 1728 = w ^ 2) :=
  modularJ_quadratic_chart UpperHalfPlane.I modularJ_I

theorem SpecialPeriods.analytic_chart_inverse_order_one (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : e a = 0) (hf : AnalyticOnNhd ℂ e e.source)
    (hi : AnalyticOnNhd ℂ e.symm e.target) : analyticOrderAt (fun z : ℂ => e.symm z - a) 0 = 1 := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hia : e.symm 0 = a := by rw [← he, e.left_inv ha]
  have hfi : AnalyticAt ℂ e (e.symm 0) := hia ▸ hf a ha
  have hii := hi 0 ht
  have hc := hfi.differentiableAt.hasDerivAt.comp 0 hii.differentiableAt.hasDerivAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 0, z ∈ e.target := e.open_target.mem_nhds ht
  have heq : (fun z : ℂ => e (e.symm z)) =ᶠ[𝓝 0] id := hnear.mono fun z hz => e.right_inv hz
  have hm : deriv e (e.symm 0) * deriv e.symm 0 = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id 0)
  have hne : deriv e.symm 0 ≠ 0 := by
    intro h
    rw [h, MulZeroClass.mul_zero] at hm
    exact zero_ne_one hm
  simpa only [hia] using hii.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hne

theorem SpecialPeriods.analytic_chart_inverse_power_order (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (he : e a = 0) (hf : AnalyticOnNhd ℂ e e.source)
    (hi : AnalyticOnNhd ℂ e.symm e.target) (c : ℂ) (hc : c ≠ 0) (k : ℕ) (hk : 0 < k) :
    analyticOrderAt (fun z : ℂ => e.symm (c * z ^ k) - a) 0 = (k : ℕ∞) := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hg : AnalyticAt ℂ (fun z : ℂ => c * z ^ k) 0 := by fun_prop
  have hg0 : c * (0 : ℂ) ^ k = 0 := by simp [hk.ne']
  have hi0 : AnalyticAt ℂ (fun z : ℂ => e.symm z - a) (c * (0 : ℂ) ^ k) := by
    rw [hg0]
    exact (hi 0 ht).sub analyticAt_const
  have horder : analyticOrderAt (fun z : ℂ => c * z ^ k) 0 = (k : ℕ∞) := by
    rw [hg.analyticOrderAt_eq_natCast]
    refine ⟨fun _ => c, analyticAt_const, hc, ?_⟩
    exact Filter.Eventually.of_forall fun z => by simp [mul_comm]
  have hcomp := hi0.analyticOrderAt_comp (g := fun z : ℂ => c * z ^ k) (z₀ := 0) hg
  simpa only [Function.comp_def, hg0, sub_zero, analytic_chart_inverse_order_one e ha he hf hi,
    horder, one_mul] using hcomp

theorem SpecialPeriods.analytic_chart_deriv_ne_zero (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ}
    (ha : a ∈ e.source) (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target) :
    deriv e a ≠ 0 := by
  have hii := hi (e a) (e.map_source ha)
  have hc := hii.differentiableAt.hasDerivAt.comp a (hf a ha).differentiableAt.hasDerivAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, z ∈ e.source := e.open_source.mem_nhds ha
  have heq : (fun z : ℂ => e.symm (e z)) =ᶠ[𝓝 a] id := hnear.mono fun z hz => e.left_inv hz
  have hm : deriv e.symm (e a) * deriv e a = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id a)
  intro h
  rw [h, MulZeroClass.mul_zero] at hm
  exact zero_ne_one hm

def SpecialPeriods.modularRhoAction (w : ℂ) : ℂ :=
  (w - 1) / w

def SpecialPeriods.modularIAction (w : ℂ) : ℂ :=
  -1 / w

theorem SpecialPeriods.modularRhoAction_coe (z : ℍ) :
    modularRhoAction z = (((ModularGroup.T * ModularGroup.S) • z : ℍ) : ℂ) := by
  rw [SemigroupAction.mul_smul, UpperHalfPlane.modular_T_smul, UpperHalfPlane.modular_S_smul]
  simp only [modularRhoAction, UpperHalfPlane.coe_vadd, Complex.ofReal_one, inv_neg]
  field_simp [z.ne_zero]
  ring

theorem SpecialPeriods.modularIAction_coe (z : ℍ) :
    modularIAction z = ((ModularGroup.S • z : ℍ) : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [modularIAction, inv_neg, div_eq_mul_inv]

theorem SpecialPeriods.modularRhoAction_deriv_rho : deriv modularRhoAction rho = -rho := by
  have h := ((hasDerivAt_id rho).sub_const 1).div (hasDerivAt_id rho) rho_ne_zero
  change HasDerivAt modularRhoAction _ rho at h
  rw [h.deriv]
  simp only [id_eq, one_mul, mul_one]
  field_simp [rho_ne_zero]
  linear_combination rho_cube

theorem SpecialPeriods.modularSL_holomorphic (g : SL(2, ℤ)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => g • z) :=
  UpperHalfPlane.contMDiff_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp)

theorem SpecialPeriods.upperHalfPlane_holomorphic_eq_of_eventuallyEq {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) {a : ℍ} (he : f =ᶠ[𝓝 a] g) :
    f = g := by
  have hfc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (f z : ℂ)) :=
    (UpperHalfPlane.contMDiff_coe.comp hf).mdifferentiable (by simp)
  have hgc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (g z : ℂ)) :=
    (UpperHalfPlane.contMDiff_coe.comp hg).mdifferentiable (by simp)
  have hz : ∀ᶠ z in 𝓝[≠] a, (f z : ℂ) - (g z : ℂ) = 0 :=
    (he.mono fun z hz => by rw [hz, sub_self]).filter_mono nhdsWithin_le_nhds
  have hzero := UpperHalfPlane.eq_zero_of_frequently (hfc.sub hgc) hz.frequently
  funext z
  apply UpperHalfPlane.ext
  exact sub_eq_zero.mp (congrFun hzero z)

theorem SpecialPeriods.realSL_action_identity_of_two_fixed (g : SL(2, ℝ)) {a b : ℍ}
    (ha : g • a = a) (hb : g • b = b) (hab : a ≠ b) : ∀ z : ℍ, g • z = z := by
  have hc : Triangle.cayleyCoordinate a b ≠ 0 := by
    apply div_ne_zero _ (Triangle.sub_conj_ne_zero a b)
    apply sub_ne_zero.mpr
    intro h
    exact hab (UpperHalfPlane.ext h).symm
  have hm : Triangle.slMultiplier g a = 1 := by
    have h := Triangle.cayleyCoordinate_smul g a b ha
    rw [hb] at h
    exact mul_right_cancel₀ hc (by simpa only [one_mul] using h.symm)
  intro z
  apply (Triangle.cayleyBiholomorph a).injective
  apply Subtype.ext
  change Triangle.cayleyCoordinate a (g • z) = Triangle.cayleyCoordinate a z
  rw [Triangle.cayleyCoordinate_smul g a z ha, hm, one_mul]

theorem SpecialPeriods.integerSL_real_action (g : SL(2, ℤ)) (z : ℍ) :
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • z = g • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

theorem SpecialPeriods.modularSL_action_identity_of_two_fixed (g : SL(2, ℤ)) {a b : ℍ}
    (ha : g • a = a) (hb : g • b = b) (hab : a ≠ b) : ∀ z : ℍ, g • z = z := by
  have h :=
    realSL_action_identity_of_two_fixed (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)
      (by simpa only [integerSL_real_action] using ha)
      (by simpa only [integerSL_real_action] using hb) hab
  simpa only [integerSL_real_action] using h

theorem SpecialPeriods.modularJ_equal_lifts_differ_by_SL {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hJ : ∀ z, modularJ (f z) = modularJ (g z)) (a : ℍ)
    (ha : modularJ (f a) ∈ modularRegularValues) : ∃ γ : SL(2, ℤ), ∀ z, γ • f z = g z := by
  obtain ⟨γ, hγ⟩ := (modularJ_eq_iff_exists_smul (g a) (f a)).mp (hJ a).symm
  have hga : modularJ (g a) ∈ modularRegularValues := (hJ a) ▸ ha
  obtain ⟨U, hUo, hgaU, hUi⟩ :=
    modularJ_regular_injOn_neighbourhood (g a) ((mem_modularRegularValues _).mp hga).1
      ((mem_modularRegularValues _).mp hga).2
  have hγf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => γ • f z) := (modularSL_holomorphic γ).comp hf
  have hnear₁ : ∀ᶠ z in 𝓝 a, γ • f z ∈ U := by
    apply hγf.continuous.continuousAt.preimage_mem_nhds
    simpa only [hγ] using hUo.mem_nhds hgaU
  have hnear₂ : ∀ᶠ z in 𝓝 a, g z ∈ U :=
    hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgaU)
  have he : (fun z => γ • f z) =ᶠ[𝓝 a] g := by
    filter_upwards [hnear₁, hnear₂] with z h₁ h₂
    exact hUi h₁ h₂ ((modularJ_SL_invariant γ (f z)).trans (hJ z))
  refine ⟨γ, ?_⟩
  exact congrFun (upperHalfPlane_holomorphic_eq_of_eventuallyEq hγf hg he)

theorem SpecialPeriods.modular_T_has_no_fixed_point (z : ℍ) : ModularGroup.T • z ≠ z := by
  intro h
  have hc := congrArg (fun w : ℍ => (w : ℂ)) h
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.ofReal_one, Complex.one_re] at hr
  linarith

theorem SpecialPeriods.modularRho_fixed_iff (z : ℍ) :
    (ModularGroup.T * ModularGroup.S) • z = z ↔ z = rhoPoint := by
  constructor
  · intro hz
    by_contra hzr
    have hid :=
      modularSL_action_identity_of_two_fixed (ModularGroup.T * ModularGroup.S) TS_smul_rhoPoint hz
        (Ne.symm hzr)
    have hI := hid UpperHalfPlane.I
    rw [SemigroupAction.mul_smul, S_smul_I] at hI
    exact modular_T_has_no_fixed_point UpperHalfPlane.I hI
  · rintro rfl
    exact TS_smul_rhoPoint

theorem SpecialPeriods.modularI_fixed_iff (z : ℍ) :
    ModularGroup.S • z = z ↔ z = UpperHalfPlane.I := by
  constructor
  · intro hz
    by_contra hzi
    have hid := modularSL_action_identity_of_two_fixed ModularGroup.S S_smul_I hz (Ne.symm hzi)
    have hρ : ModularGroup.T • rhoPoint = rhoPoint := by
      simpa only [SemigroupAction.mul_smul, hid rhoPoint] using TS_smul_rhoPoint
    exact modular_T_has_no_fixed_point rhoPoint hρ
  · rintro rfl
    exact S_smul_I

def SpecialPeriods.TauCovariant (τ : ℍ → ℍ) : Prop :=
  (∀ z : ℍ, (τ (Triangle.generatorOneSL • z) : ℂ) = ((τ z : ℂ) - 1) / (τ z : ℂ)) ∧
    (∀ z : ℍ, (τ (Triangle.generatorTwoSL • z) : ℂ) = -1 / (τ z : ℂ))

theorem SpecialPeriods.tau_covariant_values {τ : ℍ → ℍ} (hτ : TauCovariant τ) :
    τ Triangle.centerOne = rhoPoint ∧ τ Triangle.centerTwo = UpperHalfPlane.I := by
  constructor
  · apply (modularRho_fixed_iff _).mp
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    have h := hτ.1 Triangle.centerOne
    rw [Triangle.generatorOne_fix] at h
    exact h.symm
  · apply (modularI_fixed_iff _).mp
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    have h := hτ.2 Triangle.centerTwo
    rw [Triangle.generatorTwo_fix] at h
    exact h.symm

private theorem SpecialPeriods.ModularGermLift.enat_eq_nat_of_mul_eq_mo1973_17094 {x : ℕ∞}
    {m n : ℕ} (hm : 0 < m) (h : (m : ℕ∞) * x = (m * n : ℕ)) : x = n := by
  have hm0 : (m : ℕ∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hfin : x ≠ ⊤ := by
    intro hx
    rw [hx, ENat.mul_top hm0] at h
    exact ENat.top_ne_natCast _ h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at h
  have hkn : k = n := by
    have hmul : m * k = m * n := by exact_mod_cast h
    exact Nat.eq_of_mul_eq_mul_left hm hmul
  rw [← hk, hkn]

theorem SpecialPeriods.ModularGermLift.modularJ_lift_order_mul {F τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F) :
    analyticOrderAt F a =
      analyticOrderAt (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) *
        analyticOrderAt (fun z => τ z - τ a) a := by
  have hj : AnalyticAt ℂ (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularJ_analyticAt (UpperHalfPlane.ofComplex (τ a))
  exact (analyticOrderAt_congr hJ).symm.trans (hj.analyticOrderAt_comp hτ)

theorem SpecialPeriods.ModularGermLift.modularJ_lift_sub_1728_order_mul {F τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F) :
    analyticOrderAt (fun z => F z - 1728) a =
      analyticOrderAt (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) - 1728)
          (τ a) *
        analyticOrderAt (fun z => τ z - τ a) a := by
  have hjbase : AnalyticAt ℂ (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularJ_analyticAt (UpperHalfPlane.ofComplex (τ a))
  have hj :
    AnalyticAt ℂ (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) - 1728) (τ a) :=
    hjbase.sub analyticAt_const
  have he :
    (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) - 1728) =ᶠ[𝓝 a]
      (fun z => F z - 1728) :=
    hJ.sub (Filter.EventuallyEq.rfl)
  exact (analyticOrderAt_congr he).symm.trans (hj.analyticOrderAt_comp hτ)

theorem SpecialPeriods.ModularGermLift.modularJ_lift_order_of_zero {F τ : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F)
    (ha : F a = 0) (horder : analyticOrderAt F a = (3 * n : ℕ)) :
    analyticOrderAt (fun z => τ z - τ a) a = n := by
  have hj0 : SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ a)) = 0 :=
    hJ.self_of_nhds.trans ha
  have hjord : analyticOrderAt (SpecialPeriods.modularJ ∘ UpperHalfPlane.ofComplex) (τ a) = 3 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_modularJ_of_eq_zero (UpperHalfPlane.ofComplex (τ a)) hj0
  have hmul := modularJ_lift_order_mul hτ hpos hJ
  rw [horder, hjord] at hmul
  exact enat_eq_nat_of_mul_eq_mo1973_17094 (by decide : 0 < 3) hmul.symm

theorem SpecialPeriods.ModularGermLift.modularJ_lift_order_of_1728 {F τ : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (hJ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a] F)
    (ha : F a = 1728) (horder : analyticOrderAt (fun z => F z - 1728) a = (2 * n : ℕ)) :
    analyticOrderAt (fun z => τ z - τ a) a = n := by
  have hj1728 : SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ a)) = 1728 :=
    hJ.self_of_nhds.trans ha
  have hjord :
    analyticOrderAt (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) - 1728) (τ a) =
      2 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_modularJ_sub_1728_of_eq (UpperHalfPlane.ofComplex (τ a))
        hj1728
  have hmul := modularJ_lift_sub_1728_order_mul hτ hpos hJ
  rw [horder, hjord] at hmul
  exact enat_eq_nat_of_mul_eq_mo1973_17094 (by decide : 0 < 2) hmul.symm

theorem SpecialPeriods.ModularGermLift.E₄_lift_order_of_zero {τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (ha : ModularForm.E₄ (UpperHalfPlane.ofComplex (τ a)) = 0) :
    analyticOrderAt (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex (τ z))) a =
      analyticOrderAt (fun z => τ z - τ a) a := by
  have hE : AnalyticAt ℂ (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularForm_analyticAt ModularForm.E₄ (UpperHalfPlane.ofComplex (τ a))
  have ho : analyticOrderAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ a) = 1 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_E₄_of_eq_zero (UpperHalfPlane.ofComplex (τ a)) ha
  calc
    analyticOrderAt (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex (τ z))) a =
        analyticOrderAt (ModularForm.E₄ ∘ UpperHalfPlane.ofComplex) (τ a) *
          analyticOrderAt (fun z => τ z - τ a) a :=
      hE.analyticOrderAt_comp hτ
    _ = analyticOrderAt (fun z => τ z - τ a) a := by rw [ho, one_mul]

theorem SpecialPeriods.ModularGermLift.E₆_lift_order_of_zero {τ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hpos : 0 < (τ a).im)
    (ha : ModularForm.E₆ (UpperHalfPlane.ofComplex (τ a)) = 0) :
    analyticOrderAt (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex (τ z))) a =
      analyticOrderAt (fun z => τ z - τ a) a := by
  have hE : AnalyticAt ℂ (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (τ a) := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.modularForm_analyticAt ModularForm.E₆ (UpperHalfPlane.ofComplex (τ a))
  have ho : analyticOrderAt (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (τ a) = 1 := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hpos] using
      SpecialPeriods.analyticOrderAt_E₆_of_eq_zero (UpperHalfPlane.ofComplex (τ a)) ha
  calc
    analyticOrderAt (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex (τ z))) a =
        analyticOrderAt (ModularForm.E₆ ∘ UpperHalfPlane.ofComplex) (τ a) *
          analyticOrderAt (fun z => τ z - τ a) a :=
      hE.analyticOrderAt_comp hτ
    _ = analyticOrderAt (fun z => τ z - τ a) a := by rw [ho, one_mul]

theorem SpecialPeriods.ModularGermLift.analyticAt_upperHalfPlane_lift {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (a : ℍ) :
    AnalyticAt ℂ (fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)) (a : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp (UpperHalfPlane.mdifferentiable_coe.comp hτ)).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos)

theorem SpecialPeriods.ModularGermLift.native_modular_equation_eventually {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) (a : ℍ) :
    (fun z : ℂ =>
        SpecialPeriods.modularJ
          (UpperHalfPlane.ofComplex (τ (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (a : ℂ)]
      (F ∘ UpperHalfPlane.ofComplex) := by
  filter_upwards with z
  simpa only [UpperHalfPlane.ofComplex_apply, Function.comp_apply] using
    hJ (UpperHalfPlane.ofComplex z)

theorem SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_zero {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ}
    {n : ℕ} (ha : F a = 0)
    (horder : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) = n :=
  by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    modularJ_lift_order_of_zero (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (native_modular_equation_eventually hJ a)
      (by simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using ha) horder

theorem SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_1728 {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ}
    {n : ℕ} (ha : F a = 1728)
    (horder :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) = n :=
  by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    modularJ_lift_order_of_1728 (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (native_modular_equation_eventually hJ a)
      (by simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using ha) horder

theorem SpecialPeriods.ModularGermLift.native_E₄_lift_order_of_zero {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) {a : ℍ} (ha : ModularForm.E₄ (τ a) = 0) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) := by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    E₄_lift_order_of_zero (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (by simpa only [UpperHalfPlane.ofComplex_apply] using ha)

theorem SpecialPeriods.ModularGermLift.native_E₆_lift_order_of_zero {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) {a : ℍ} (ha : ModularForm.E₆ (τ a) = 0) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) := by
  simpa only [UpperHalfPlane.ofComplex_apply] using
    E₆_lift_order_of_zero (analyticAt_upperHalfPlane_lift hτ a)
      (by simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im] using (τ a).im_pos)
      (by simpa only [UpperHalfPlane.ofComplex_apply] using ha)

theorem SpecialPeriods.ModularGermLift.native_E₆_order_of_source_order {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ}
    {n : ℕ} (ha : F a = 1728)
    (horder :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) = n := by
  have hE : ModularForm.E₆ (τ a) = 0 :=
    (SpecialPeriods.modularJ_eq_1728_iff (τ a)).mp ((hJ a).trans ha)
  exact
    (native_E₆_lift_order_of_zero hτ hE).trans
      (native_modularJ_lift_order_of_1728 hτ hJ ha horder)

theorem SpecialPeriods.ModularGermLift.native_E₆_order_of_source_four_order {τ : ℍ → ℍ}
    {F : ℍ → ℂ} (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a) {a : ℍ} {k : ℕ} (ha : F a = 1728)
    (horder :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
        (4 * k : ℕ)) :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
      (2 * k : ℕ) := by
  apply native_E₆_order_of_source_order hτ hJ ha
  simpa only [← Nat.mul_assoc] using horder

theorem SpecialPeriods.ModularGermLift.native_E₆_finite_even_zeros {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = F a)
    (hsource :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (4 * k : ℕ)) :
    ∀ a : ℍ,
      ModularForm.E₆ (τ a) = 0 →
        ∃ n : ℕ,
          analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
            (2 * n : ℕ) := by
  intro a ha
  have hFa : F a = 1728 := (hJ a).symm.trans ((SpecialPeriods.modularJ_eq_1728_iff (τ a)).mpr ha)
  obtain ⟨k, hk⟩ := hsource a hFa
  exact ⟨k, native_E₆_order_of_source_four_order hτ hJ hFa hk⟩

theorem SpecialPeriods.realSL_actions_eq_of_fixed_deriv (g h : SL(2, ℝ)) (a : ℍ) (hg : g • a = a)
    (hh : h • a = a)
    (hd :
      deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) =
        deriv (fun z : ℂ => ((h • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ)) :
    ∀ z : ℍ, g • z = h • z := by
  have hm : Triangle.slMultiplier g a = Triangle.slMultiplier h a := by
    simpa only [Triangle.sl_deriv_smul] using hd
  intro z
  apply (Triangle.cayleyBiholomorph a).injective
  apply Subtype.ext
  change Triangle.cayleyCoordinate a (g • z) = Triangle.cayleyCoordinate a (h • z)
  rw [Triangle.cayleyCoordinate_smul g a z hg, Triangle.cayleyCoordinate_smul h a z hh, hm]

theorem SpecialPeriods.modularSL_actions_eq_of_fixed_deriv (g h : SL(2, ℤ)) (a : ℍ)
    (hg : g • a = a) (hh : h • a = a)
    (hd :
      deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) =
        deriv (fun z : ℂ => ((h • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ)) :
    ∀ z : ℍ, g • z = h • z := by
  simpa only [integerSL_real_action] using
    realSL_actions_eq_of_fixed_deriv (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g)
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) h) a
      (by simpa only [integerSL_real_action] using hg)
      (by simpa only [integerSL_real_action] using hh)
      (by simpa only [integerSL_real_action] using hd)

theorem SpecialPeriods.modularSL_ambient_deriv_eq (g : SL(2, ℤ)) (f : ℂ → ℂ)
    (hf : ∀ z : ℍ, f z = ((g • z : ℍ) : ℂ)) (a : ℍ) :
    deriv (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (a : ℂ) = deriv f (a : ℂ) := by
  apply Filter.EventuallyEq.deriv_eq
  have hpos : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), 0 < z.im :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos
  filter_upwards [hpos] with z hz
  simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    (hf (UpperHalfPlane.ofComplex z)).symm

theorem SpecialPeriods.modularRho_ambient_deriv :
    deriv
        (fun z : ℂ => (((ModularGroup.T * ModularGroup.S) • UpperHalfPlane.ofComplex z : ℍ) : ℂ))
        (rhoPoint : ℂ) =
      -rho :=
  (modularSL_ambient_deriv_eq (ModularGroup.T * ModularGroup.S) modularRhoAction
        modularRhoAction_coe rhoPoint).trans
    modularRhoAction_deriv_rho

theorem SpecialPeriods.modularJ_invariant_lift_action {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (A : SL(2, ℝ)) (hJ : ∀ z : ℍ, modularJ (τ (A • z)) = modularJ (τ z)) (x : ℍ)
    (hx : modularJ (τ x) ∈ modularRegularValues) : ∃ γ : SL(2, ℤ), ∀ z : ℍ, γ • τ z = τ (A • z) :=
  by
  exact
    modularJ_equal_lifts_differ_by_SL hτ (hτ.comp (Triangle.specialLinear_holomorphic A))
      (fun z => (hJ z).symm) x hx

theorem SpecialPeriods.analytic_semiconjugacy_multiplier (τ A B : ℂ → ℂ) (a b ξ η : ℂ) (k : ℕ)
    (hτ : AnalyticAt ℂ τ a) (hτa : τ a = b)
    (horder : analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞)) (hA : HasDerivAt A ξ a)
    (hAa : A a = a) (hB : HasDerivAt B η b) (hBb : B b = b) (hsem : τ ∘ A =ᶠ[𝓝 a] B ∘ τ) :
    η = ξ ^ k := by
  obtain ⟨u, hu, hu0, hfactor⟩ := (hτ.sub analyticAt_const).analyticOrderAt_eq_natCast.mp horder
  have hf : ∀ᶠ z in 𝓝 a, τ z - b = (z - a) ^ k * u z := by
    simpa only [Pi.sub_apply, smul_eq_mul] using hfactor
  have hAt : Filter.Tendsto A (𝓝 a) (𝓝 a) := by
    simpa only [ContinuousAt, hAa] using hA.continuousAt
  have hfA : ∀ᶠ z in 𝓝 a, τ (A z) - b = (A z - a) ^ k * u (A z) := hAt.eventually hf
  have he : (fun z => dslope A a z ^ k * u (A z)) =ᶠ[𝓝[≠] a] (fun z => u z * dslope B b (τ z)) := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds, hfA.filter_mono nhdsWithin_le_nhds,
      hsem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hfz hfAz hsemz hza
    have hAz : A z - a = (z - a) * dslope A a z := by
      simpa only [smul_eq_mul, hAa] using (sub_smul_dslope A a z).symm
    have hBz : B (τ z) - b = (τ z - b) * dslope B b (τ z) := by
      simpa only [smul_eq_mul, hBb] using (sub_smul_dslope B b (τ z)).symm
    apply mul_left_cancel₀ (pow_ne_zero k (sub_ne_zero.mpr hza))
    calc
      (z - a) ^ k * (dslope A a z ^ k * u (A z)) = ((z - a) * dslope A a z) ^ k * u (A z) := by
        rw [mul_pow, mul_assoc]
      _ = (A z - a) ^ k * u (A z) := by rw [← hAz]
      _ = τ (A z) - b := hfAz.symm
      _ = B (τ z) - b := (congrArg (fun w => w - b) hsemz)
      _ = (τ z - b) * dslope B b (τ z) := hBz
      _ = (z - a) ^ k * (u z * dslope B b (τ z)) := by rw [hfz, mul_assoc]
  have hcL : ContinuousAt (fun z => dslope A a z ^ k * u (A z)) a :=
    ((continuousAt_dslope_same.mpr hA.differentiableAt).pow k).mul
      (hu.continuousAt.comp_of_eq hA.continuousAt hAa)
  have hcR : ContinuousAt (fun z => u z * dslope B b (τ z)) a :=
    hu.continuousAt.mul
      ((continuousAt_dslope_same.mpr hB.differentiableAt).comp_of_eq hτ.continuousAt hτa)
  have hcenter :=
    tendsto_nhds_unique_of_eventuallyEq hcL.continuousWithinAt hcR.continuousWithinAt he
  have hcoeff : ξ ^ k * u a = u a * η := by
    simpa only [hAa, hτa, dslope_same, hA.deriv, hB.deriv] using hcenter
  apply mul_right_cancel₀ hu0
  rw [mul_comm η (u a)]
  exact hcoeff.symm

theorem SpecialPeriods.analytic_semiconjugacy_deriv_pow (τ A B : ℂ → ℂ) (a b : ℂ) (k : ℕ)
    (hτ : AnalyticAt ℂ τ a) (hτa : τ a = b)
    (horder : analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞)) (hA : AnalyticAt ℂ A a)
    (hAa : A a = a) (hB : AnalyticAt ℂ B b) (hBb : B b = b) (hsem : τ ∘ A =ᶠ[𝓝 a] B ∘ τ) :
    deriv B b = deriv A a ^ k :=
  analytic_semiconjugacy_multiplier τ A B a b (deriv A a) (deriv B b) k hτ hτa horder
    hA.differentiableAt.hasDerivAt hAa hB.differentiableAt.hasDerivAt hBb hsem

def SpecialPeriods.TauEquivariance.intertwiningSubgroup {G X Y : Type*} [Group G]
    (α : G →* Equiv.Perm X) (β : G →* Equiv.Perm Y) (f : X → Y) : Subgroup G
    where
  carrier := {g | ∀ x, f (α g x) = β g (f x)}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    simpa only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply] using
      (hg (α h x)).trans (congrArg (β g) (hh x))
  inv_mem' := by
    intro g hg x
    apply (β g).injective
    have h := hg (α g⁻¹ x)
    simpa using h.symm

theorem SpecialPeriods.tau_covariant_triangle_action {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (g : TriangleGroup) (z : ℍ) :
    τ (triangleGeometricRepresentation g z) = triangleModularAction g (τ z) := by
  let H :=
    TauEquivariance.intertwiningSubgroup triangleGeometricRepresentation triangleModularAction τ
  have hgen : ({ triangleGenerator₁, triangleGenerator₂ } : Set TriangleGroup) ⊆ H := by
    intro h hh
    rcases Set.mem_insert_iff.mp hh with rfl | hh
    · intro x
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_generator₁_apply, triangleModularAction_generator₁_coe]
      exact hτ.1 x
    · have he : h = triangleGenerator₂ := Set.mem_singleton_iff.mp hh
      subst h
      intro x
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_generator₂_apply, triangleModularAction_generator₂_coe]
      exact hτ.2 x
  have htop : (⊤ : Subgroup TriangleGroup) ≤ H := by
    rw [← triangle_generators_generate]
    exact (Subgroup.closure_le _).mpr hgen
  exact htop (Subgroup.mem_top g) z

theorem SpecialPeriods.tau_covariant_cusp {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    τ (triangleGeometricRepresentation triangleCuspGenerator z) = (-1 : ℝ) +ᵥ τ z := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_apply]

theorem SpecialPeriods.tau_covariant_cusp_coe {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    (τ (triangleGeometricRepresentation triangleCuspGenerator z) : ℂ) = (τ z : ℂ) - 1 := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_coe]

theorem SpecialPeriods.modular_lift_action_of_order {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (A : SL(2, ℝ)) (a : ℍ) (hAa : A • a = a) (k : ℕ)
    (horder :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) =
        (k : ℕ∞))
    (B : SL(2, ℤ)) (hBb : B • τ a = τ a)
    (hBderiv :
      deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (τ a : ℂ) =
        Triangle.slMultiplier A a ^ k)
    (hJ : ∀ z : ℍ, modularJ (τ (A • z)) = modularJ (τ z)) (x : ℍ)
    (hx : modularJ (τ x) ∈ modularRegularValues) : ∀ z : ℍ, τ (A • z) = B • τ z := by
  obtain ⟨γ, hγ⟩ := modularJ_invariant_lift_action hτ A hJ x hx
  have hγfix : γ • τ a = τ a := by simpa only [hAa] using hγ a
  let t : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let α : ℂ → ℂ := fun z => ((A • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  let β : ℂ → ℂ := fun z => ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  have ht : AnalyticAt ℂ t (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift (hτ.mdifferentiable (by simp)) a
  have hα : AnalyticAt ℂ α (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((Triangle.specialLinear_holomorphic A).mdifferentiable (by simp)) a
  have hβ : AnalyticAt ℂ β (τ a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((modularSL_holomorphic γ).mdifferentiable (by simp)) (τ a)
  have ht₀ : t (a : ℂ) = (τ a : ℂ) := by simp only [t, UpperHalfPlane.ofComplex_apply]
  have hα₀ : α (a : ℂ) = (a : ℂ) := by simp only [α, UpperHalfPlane.ofComplex_apply, hAa]
  have hβ₀ : β (τ a : ℂ) = (τ a : ℂ) := by simp only [β, UpperHalfPlane.ofComplex_apply, hγfix]
  have hsem : t ∘ α =ᶠ[𝓝 (a : ℂ)] β ∘ t := by
    filter_upwards with w
    simpa only [t, α, β, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      (congrArg (fun z : ℍ => (z : ℂ)) (hγ (UpperHalfPlane.ofComplex w))).symm
  have hm :=
    analytic_semiconjugacy_deriv_pow t α β (a : ℂ) (τ a : ℂ) k ht ht₀ horder hα hα₀ hβ hβ₀ hsem
  have hderiv :
    deriv (fun z : ℂ => ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k := by simpa only [α, β, Triangle.sl_deriv_smul] using hm
  have he := modularSL_actions_eq_of_fixed_deriv γ B (τ a) hγfix hBb (hderiv.trans hBderiv.symm)
  intro z
  exact (hγ z).symm.trans (he (τ z))

theorem SpecialPeriods.exists_regular_modular_value_of_j_values {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {τ : X → ℍ} (hτ : Continuous τ) (a b : X) (ha : modularJ (τ a) = 0)
    (hb : modularJ (τ b) = 1728) : ∃ x, modularJ (τ x) ∈ modularRegularValues := by
  let F : X → ℝ := fun x => (modularJ (τ x)).re
  have hF : Continuous F := Complex.continuous_re.comp (modularJ_continuous.comp hτ)
  have hmid : (864 : ℝ) ∈ Set.Icc (F a) (F b) := by norm_num [F, ha, hb]
  obtain ⟨x, hx⟩ := intermediate_value_univ a b hF hmid
  refine ⟨x, (mem_modularRegularValues _).mpr ⟨?_, ?_⟩⟩
  · intro hz
    have hh : F x = 0 := by simp [F, hz]
    linarith
  · intro hz
    have hh : F x = 1728 := by norm_num [F, hz]
    linarith

theorem SpecialPeriods.modular_lift_first_generator_of_rho_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (ha : τ Triangle.centerOne = rhoPoint)
    (horder :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - rho)
          (Triangle.centerOne : ℂ) =
        1)
    (hJ : ∀ z : ℍ, modularJ (τ (Triangle.generatorOneSL • z)) = modularJ (τ z)) (x : ℍ)
    (hx : modularJ (τ x) ∈ modularRegularValues) :
    ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z := by
  rw [triangleModularA_eq_T_mul_S]
  exact
    modular_lift_action_of_order hτ Triangle.generatorOneSL Triangle.centerOne
      Triangle.generatorOne_fix 1 (by simpa [ha] using horder) (ModularGroup.T * ModularGroup.S)
      (by rw [ha]; exact TS_smul_rhoPoint)
      (by rw [ha, modularRho_ambient_deriv, Triangle.generatorOne_multiplier, pow_one]) hJ x hx

theorem SpecialPeriods.modularSL_actions_eq_of_two_values (B C : SL(2, ℤ)) (a b : ℍ) (hab : a ≠ b)
    (ha : B • a = C • a) (hb : B • b = C • b) : ∀ z : ℍ, B • z = C • z := by
  have ha' : (C⁻¹ * B) • a = a := by rw [SemigroupAction.mul_smul, ha, inv_smul_smul]
  have hb' : (C⁻¹ * B) • b = b := by rw [SemigroupAction.mul_smul, hb, inv_smul_smul]
  have h := modularSL_action_identity_of_two_fixed (C⁻¹ * B) ha' hb' hab
  intro z
  simpa only [SemigroupAction.mul_smul, smul_inv_smul] using congrArg (fun w : ℍ => C • w) (h z)

theorem SpecialPeriods.modular_lift_product_cusp_action {τ : ℍ → ℍ} (B : SL(2, ℤ))
    (hA : ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z)
    (hB : ∀ z : ℍ, B • τ z = τ (Triangle.generatorTwoSL • z)) :
    ∀ z : ℍ, (triangleModularA * B)⁻¹ • τ z = τ (Triangle.cuspSL • z) := by
  intro z
  rw [inv_smul_eq_iff, SemigroupAction.mul_smul, hB, ← hA, ← SemigroupAction.mul_smul, ←
    SemigroupAction.mul_smul, Triangle.generatorOneSL_mul_generatorTwoSL_mul_cuspSL, one_smul]

theorem SpecialPeriods.modular_lift_cusp_monodromy_comparison {τ : ℍ → ℍ} (B C : SL(2, ℤ))
    (hA : ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z)
    (hB : ∀ z : ℍ, B • τ z = τ (Triangle.generatorTwoSL • z))
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) (a b : ℍ) (hab : τ a ≠ τ b) :
    ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = C • z := by
  have hp := modular_lift_product_cusp_action B hA hB
  exact
    modularSL_actions_eq_of_two_values _ _ (τ a) (τ b) hab ((hp a).trans (hC a))
      ((hp b).trans (hC b))

theorem SpecialPeriods.modular_lift_cusp_monodromy_conjugate {τ : ℍ → ℍ} (γ C : SL(2, ℤ))
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∀ z : ℍ, γ • τ (Triangle.cuspSL • z) = (γ * C * γ⁻¹) • (γ • τ z) := by
  intro z
  rw [hC, SemigroupAction.mul_smul, SemigroupAction.mul_smul, inv_smul_smul]

theorem SpecialPeriods.modular_lift_monodromy_fixes_image {τ : ℍ → ℍ} (A : SL(2, ℝ)) (a : ℍ)
    (hAa : A • a = a) (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (A • z)) : γ • τ a = τ a := by
  simpa only [hAa] using hγ a

theorem SpecialPeriods.modular_lift_monodromy_deriv_of_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (A : SL(2, ℝ)) (a : ℍ) (hAa : A • a = a) (k : ℕ)
    (horder :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) =
        (k : ℕ∞))
    (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (A • z)) :
    deriv (fun w : ℂ => ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k := by
  have hγfix := modular_lift_monodromy_fixes_image A a hAa γ hγ
  let t : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let α : ℂ → ℂ := fun z => ((A • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  let β : ℂ → ℂ := fun z => ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  have ht : AnalyticAt ℂ t (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift (hτ.mdifferentiable (by simp)) a
  have hα : AnalyticAt ℂ α (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((Triangle.specialLinear_holomorphic A).mdifferentiable (by simp)) a
  have hβ : AnalyticAt ℂ β (τ a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((modularSL_holomorphic γ).mdifferentiable (by simp)) (τ a)
  have ht₀ : t (a : ℂ) = (τ a : ℂ) := by simp only [t, UpperHalfPlane.ofComplex_apply]
  have hα₀ : α (a : ℂ) = (a : ℂ) := by simp only [α, UpperHalfPlane.ofComplex_apply, hAa]
  have hβ₀ : β (τ a : ℂ) = (τ a : ℂ) := by simp only [β, UpperHalfPlane.ofComplex_apply, hγfix]
  have hsem : t ∘ α =ᶠ[𝓝 (a : ℂ)] β ∘ t := by
    filter_upwards with w
    simpa only [t, α, β, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      (congrArg (fun z : ℍ => (z : ℂ)) (hγ (UpperHalfPlane.ofComplex w))).symm
  have hm :=
    analytic_semiconjugacy_deriv_pow t α β (a : ℂ) (τ a : ℂ) k ht ht₀ horder hα hα₀ hβ hβ₀ hsem
  simpa only [α, β, Triangle.sl_deriv_smul] using hm

theorem SpecialPeriods.modular_lift_generatorTwo_monodromy_deriv {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (horder :
      analyticOrderAt
          (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - (τ Triangle.centerTwo : ℂ))
          (Triangle.centerTwo : ℂ) =
        2)
    (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (Triangle.generatorTwoSL • z)) :
    deriv (fun w : ℂ => ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) (τ Triangle.centerTwo : ℂ) =
      -1 := by
  simpa only [Triangle.generatorTwo_multiplier, neg_sq, Complex.I_sq] using
    modular_lift_monodromy_deriv_of_order hτ Triangle.generatorTwoSL Triangle.centerTwo
      Triangle.generatorTwo_fix 2 horder γ hγ

theorem SpecialPeriods.GlobalTauNormalization.trace_neg_two_triples (p q r : ℤ)
    (hdet : -p ^ 2 - q * r = 1) (htr : p + q - r = -2) :
    (p = 0 ∧ q = -1 ∧ r = 1) ∨ (p = 1 ∧ q = -2 ∧ r = 1) ∨ (p = 1 ∧ q = -1 ∧ r = 2) := by
  have hq : q = r - p - 2 := by omega
  rw [hq] at hdet
  have hquad : p ^ 2 - p * r + r ^ 2 - 2 * r + 1 = 0 := by nlinarith only [hdet]
  have hp₀ : 0 ≤ p := by nlinarith only [hquad, sq_nonneg (2 * r - p - 2), sq_nonneg p]
  have hp_upper : 2 * p ≤ 3 := by
    nlinarith only [hquad, sq_nonneg (2 * r - p - 2), sq_nonneg (p - 1)]
  have hp₁ : p ≤ 1 := by omega
  have hr_lower : 4 ≤ 8 * r := by nlinarith only [hquad, sq_nonneg (2 * p - r), sq_nonneg r]
  have hr_upper : 10 * r ≤ 23 := by
    nlinarith only [hquad, sq_nonneg (2 * p - r), sq_nonneg (r - 3)]
  have hr₁ : 1 ≤ r := by omega
  have hr₂ : r ≤ 2 := by omega
  have hp_cases : p = 0 ∨ p = 1 := by omega
  have hr_cases : r = 1 ∨ r = 2 := by omega
  rcases hp_cases with rfl | rfl
  · rcases hr_cases with rfl | rfl
    · left
      omega
    · norm_num at hquad
  · rcases hr_cases with rfl | rfl
    · right
      left
      omega
    · right
      right
      omega

def SpecialPeriods.modularSCyclicConjugate (k : Fin 3) : SL(2, ℤ) :=
  triangleModularA ^ (k : ℕ) * ModularGroup.S * (triangleModularA ^ (k : ℕ))⁻¹

theorem SpecialPeriods.modularSCyclicConjugate_zero_matrix :
    (modularSCyclicConjugate 0 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 0] := by decide

theorem SpecialPeriods.modularSCyclicConjugate_one_matrix :
    (modularSCyclicConjugate 1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -2; 1, -1] := by decide

theorem SpecialPeriods.modularSCyclicConjugate_two_matrix :
    (modularSCyclicConjugate 2 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 2, -1] := by decide

theorem SpecialPeriods.triangleModularA_product_trace (B : SL(2, ℤ)) :
    Matrix.trace (triangleModularA * B).val = B 0 0 + B 0 1 - B 1 0 := by
  change Matrix.trace ((triangleModularA : Matrix (Fin 2) (Fin 2) ℤ) * B.val) = _
  rw [Matrix.trace_fin_two]
  simp [triangleModularA, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem SpecialPeriods.trace_zero_entry_one_one_mo1973_17146 (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0) : B 1 1 = -(B 0 0) := by
  rw [Matrix.trace_fin_two] at htr
  omega

theorem SpecialPeriods.modular_trace_zero_trace_neg_two_classification (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0) (hprod : Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3, B = modularSCyclicConjugate k := by
  have h11 := trace_zero_entry_one_one_mo1973_17146 B htr
  have hdet : -(B 0 0) ^ 2 - B 0 1 * B 1 0 = 1 := by
    have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 :=
      (Matrix.det_fin_two B.val).symm.trans B.property
    rw [h11] at hd
    nlinarith [hd]
  rw [triangleModularA_product_trace] at hprod
  rcases GlobalTauNormalization.trace_neg_two_triples (B 0 0) (B 0 1) (B 1 0) hdet hprod with
    ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩ | ⟨hp, hq, hr⟩
  · refine ⟨0, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_zero_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
  · refine ⟨1, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_one_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]
  · refine ⟨2, Subtype.ext ?_⟩
    rw [modularSCyclicConjugate_two_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, h11]

theorem SpecialPeriods.modular_trace_zero_parabolic_pair_classification (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3, B = modularSCyclicConjugate k ∨ B = -modularSCyclicConjugate k := by
  rcases hprod with hprod | hprod
  · have htr' : Matrix.trace (-B).val = 0 := by
      change Matrix.trace (-B.val) = 0
      rw [Matrix.trace_neg, htr, neg_zero]
    have hprod' : Matrix.trace (triangleModularA * (-B)).val = -2 := by
      rw [mul_neg]
      change Matrix.trace (-(triangleModularA * B).val) = -2
      rw [Matrix.trace_neg, hprod]
    obtain ⟨k, hk⟩ := modular_trace_zero_trace_neg_two_classification (-B) htr' hprod'
    refine ⟨k, Or.inr ?_⟩
    simpa only [neg_neg] using congrArg (fun C : SL(2, ℤ) => -C) hk
  · obtain ⟨k, hk⟩ := modular_trace_zero_trace_neg_two_classification B htr hprod
    exact ⟨k, Or.inl hk⟩

def SpecialPeriods.modularCyclicNormalizer (k : Fin 3) : SL(2, ℤ) :=
  (triangleModularA ^ (k : ℕ))⁻¹

theorem SpecialPeriods.modularCyclicNormalizer_conjugate_A (k : Fin 3) :
    modularCyclicNormalizer k * triangleModularA * (modularCyclicNormalizer k)⁻¹ =
      triangleModularA := by fin_cases k <;> decide

theorem SpecialPeriods.modularCyclicNormalizer_conjugate_S (k : Fin 3) :
    modularCyclicNormalizer k * modularSCyclicConjugate k * (modularCyclicNormalizer k)⁻¹ =
      ModularGroup.S := by simp [modularCyclicNormalizer, modularSCyclicConjugate, mul_assoc]

theorem SpecialPeriods.modular_pair_signed_conjugation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹ = ModularGroup.S ∨
        modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹ = -ModularGroup.S := by
  obtain ⟨k, hk | hk⟩ := modular_trace_zero_parabolic_pair_classification B htr hprod
  · refine ⟨k, Or.inl ?_⟩
    rw [hk]
    exact modularCyclicNormalizer_conjugate_S k
  · refine ⟨k, Or.inr ?_⟩
    rw [hk, mul_neg, neg_mul, modularCyclicNormalizer_conjugate_S]

theorem SpecialPeriods.modular_pair_projective_conjugation_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S := by
  obtain ⟨k, hk | hk⟩ := modular_pair_signed_conjugation_normalization B htr hprod
  · exact ⟨k, congrArg modularProjectivization hk⟩
  · exact
      ⟨k,
        (congrArg modularProjectivization hk).trans (modularProjectivization_neg ModularGroup.S)⟩

theorem SpecialPeriods.triangleModularA_smul_rhoPoint : triangleModularA • rhoPoint = rhoPoint := by
  rw [triangleModularA_eq_T_mul_S]
  exact TS_smul_rhoPoint

theorem SpecialPeriods.triangleModularA_pow_smul_rhoPoint (n : ℕ) :
    triangleModularA ^ n • rhoPoint = rhoPoint := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, SemigroupAction.mul_smul, triangleModularA_smul_rhoPoint, ih]

theorem SpecialPeriods.modularCyclicNormalizer_smul_rhoPoint (k : Fin 3) :
    modularCyclicNormalizer k • rhoPoint = rhoPoint := by
  rw [modularCyclicNormalizer, inv_smul_eq_iff]
  exact (triangleModularA_pow_smul_rhoPoint k).symm

theorem SpecialPeriods.modularCyclicNormalizer_intertwines_A (k : Fin 3) (z : ℍ) :
    modularCyclicNormalizer k • (triangleModularA • z) =
      triangleModularA • (modularCyclicNormalizer k • z) := by
  have he :=
    congrArg (fun C : SL(2, ℤ) => C • (modularCyclicNormalizer k • z))
      (modularCyclicNormalizer_conjugate_A k)
  simpa only [SemigroupAction.mul_smul, inv_smul_smul] using he

private theorem SpecialPeriods.normalized_B_action_mo1973_17159 (k : Fin 3) (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S)
    (z : ℍ) :
    modularCyclicNormalizer k • (B • z) = ModularGroup.S • (modularCyclicNormalizer k • z) := by
  have he :=
    congrArg (fun C : PSL(2, ℤ) => modularPSLPermutation C (modularCyclicNormalizer k • z)) hB
  simpa only [modularPSLPermutation_projectivization, SemigroupAction.mul_smul,
    inv_smul_smul] using he

private theorem SpecialPeriods.normalized_product_projective_mo1973_17160 (k : Fin 3)
    (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S) :
    modularProjectivization
        (modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization ModularGroup.T := by
  have he :
    modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹ =
      (modularCyclicNormalizer k * triangleModularA * (modularCyclicNormalizer k)⁻¹) *
        (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) := by group
  rw [he, map_mul, modularCyclicNormalizer_conjugate_A, hB]
  exact triangleModularGenerator₁_mul_generator₂

private theorem SpecialPeriods.normalized_cusp_projective_mo1973_17161 (k : Fin 3) (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S) :
    modularProjectivization
        (modularCyclicNormalizer k * (triangleModularA * B)⁻¹ * (modularCyclicNormalizer k)⁻¹) =
      modularProjectivization ModularGroup.T⁻¹ := by
  have he :
    modularCyclicNormalizer k * (triangleModularA * B)⁻¹ * (modularCyclicNormalizer k)⁻¹ =
      (modularCyclicNormalizer k * (triangleModularA * B) * (modularCyclicNormalizer k)⁻¹)⁻¹ := by
    group
  rw [he, map_inv, normalized_product_projective_mo1973_17160 k B hB, ← map_inv]

private theorem SpecialPeriods.normalized_cusp_action_mo1973_17162 (k : Fin 3) (B : SL(2, ℤ))
    (hB :
      modularProjectivization (modularCyclicNormalizer k * B * (modularCyclicNormalizer k)⁻¹) =
        modularProjectivization ModularGroup.S)
    (z : ℍ) :
    modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
      ModularGroup.T⁻¹ • (modularCyclicNormalizer k • z) := by
  have he :=
    congrArg (fun C : PSL(2, ℤ) => modularPSLPermutation C (modularCyclicNormalizer k • z))
      (normalized_cusp_projective_mo1973_17161 k B hB)
  simpa only [modularPSLPermutation_projectivization, SemigroupAction.mul_smul,
    inv_smul_smul] using he

theorem SpecialPeriods.modular_pair_cyclic_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨
        Matrix.trace (triangleModularA * B).val = -2) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
        (∀ z : ℍ,
            modularCyclicNormalizer k • (triangleModularA • z) =
              triangleModularA • (modularCyclicNormalizer k • z)) ∧
          (∀ z : ℍ,
              modularCyclicNormalizer k • (B • z) =
                ModularGroup.S • (modularCyclicNormalizer k • z)) ∧
            (∀ z : ℍ,
              modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • z) =
                ModularGroup.T⁻¹ • (modularCyclicNormalizer k • z)) := by
  obtain ⟨k, hk⟩ := modular_pair_projective_conjugation_normalization B htr hprod
  exact
    ⟨k, modularCyclicNormalizer_smul_rhoPoint k, modularCyclicNormalizer_intertwines_A k,
      normalized_B_action_mo1973_17159 k B hk, normalized_cusp_action_mo1973_17162 k B hk⟩

theorem SpecialPeriods.modular_pair_elliptic_value_normalization (B : SL(2, ℤ))
    (htr : Matrix.trace B.val = 0)
    (hprod :
      Matrix.trace (triangleModularA * B).val = 2 ∨ Matrix.trace (triangleModularA * B).val = -2)
    (z : ℍ) (hz : B • z = z) :
    ∃ k : Fin 3,
      modularCyclicNormalizer k • rhoPoint = rhoPoint ∧
        modularCyclicNormalizer k • z = UpperHalfPlane.I ∧
          (∀ w : ℍ,
              modularCyclicNormalizer k • (triangleModularA • w) =
                triangleModularA • (modularCyclicNormalizer k • w)) ∧
            (∀ w : ℍ,
                modularCyclicNormalizer k • (B • w) =
                  ModularGroup.S • (modularCyclicNormalizer k • w)) ∧
              (∀ w : ℍ,
                modularCyclicNormalizer k • ((triangleModularA * B)⁻¹ • w) =
                  ModularGroup.T⁻¹ • (modularCyclicNormalizer k • w)) := by
  obtain ⟨k, hρ, hA, hB, hcusp⟩ := modular_pair_cyclic_normalization B htr hprod
  refine ⟨k, hρ, ?_, hA, hB, hcusp⟩
  apply (modularI_fixed_iff _).mp
  exact (hB z).symm.trans (congrArg (fun w : ℍ => modularCyclicNormalizer k • w) hz)

theorem SpecialPeriods.realSL_fixed_multiplier_eq_neg_one_iff_trace_zero (B : SL(2, ℝ)) (b : ℍ)
    (hfix : B • b = b) : Triangle.slMultiplier B b = -1 ↔ Matrix.trace B.val = 0 := by
  have hd := Triangle.slDenom_ne_zero B b
  have hidentity := Triangle.sl_fixed_denominator_identity B b hfix
  constructor
  · intro hmul
    have hsquare : Triangle.slDenom B b ^ 2 = -1 := by
      have he := (div_eq_iff (pow_ne_zero 2 hd)).mp hmul
      linear_combination he
    have hproduct : ((B 0 0 : ℂ) + (B 1 1 : ℂ)) * Triangle.slDenom B b = 0 := by
      dsimp [Triangle.slDenom] at hidentity hsquare ⊢
      linear_combination hidentity + hsquare
    have hsum := (mul_eq_zero.mp hproduct).resolve_right hd
    rw [Matrix.trace_fin_two]
    exact_mod_cast hsum
  · intro htrace
    rw [Matrix.trace_fin_two] at htrace
    have hsum : (B 0 0 : ℂ) + (B 1 1 : ℂ) = 0 := by exact_mod_cast htrace
    have hsquare : Triangle.slDenom B b ^ 2 = -1 := by
      dsimp [Triangle.slDenom] at hidentity ⊢
      linear_combination -hidentity + ((B 1 0 : ℂ) * (b : ℂ) + (B 1 1 : ℂ)) * hsum
    rw [Triangle.slMultiplier, hsquare]
    norm_num

theorem SpecialPeriods.realSL_fixed_deriv_eq_neg_one_iff_trace_zero (B : SL(2, ℝ)) (b : ℍ)
    (hfix : B • b = b) :
    deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1 ↔
      Matrix.trace B.val = 0 := by
  rw [Triangle.sl_deriv_smul]
  exact realSL_fixed_multiplier_eq_neg_one_iff_trace_zero B b hfix

theorem SpecialPeriods.modularSL_fixed_deriv_eq_neg_one_iff_trace_zero (B : SL(2, ℤ)) (b : ℍ)
    (hfix : B • b = b) :
    deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1 ↔
      Matrix.trace B.val = 0 := by
  have hfixR : Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B • b = b := by
    rw [integerSL_real_action]
    exact hfix
  have htrace :
    Matrix.trace (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B).val = 0 ↔
      Matrix.trace B.val = 0 := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    change (B 0 0 : ℝ) + (B 1 1 : ℝ) = 0 ↔ B 0 0 + B 1 1 = 0
    rw [← Int.cast_add, Int.cast_eq_zero]
  have h :=
    (realSL_fixed_deriv_eq_neg_one_iff_trace_zero
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B) b hfixR).trans
      htrace
  simpa only [integerSL_real_action] using h

theorem SpecialPeriods.modularSL_trace_zero_of_fixed_deriv_neg_one (B : SL(2, ℤ)) (b : ℍ)
    (hfix : B • b = b)
    (hderiv : deriv (fun z : ℂ => ((B • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) (b : ℂ) = -1) :
    Matrix.trace B.val = 0 :=
  (modularSL_fixed_deriv_eq_neg_one_iff_trace_zero B b hfix).mp hderiv

theorem SpecialPeriods.modularSL_trace_inv (B : SL(2, ℤ)) :
    Matrix.trace (B⁻¹).val = Matrix.trace B.val := by
  change Matrix.trace (Matrix.adjugate B.val) = Matrix.trace B.val
  simp [Matrix.trace_fin_two, Matrix.adjugate_fin_two, add_comm]

theorem SpecialPeriods.modularSL_trace_conjugate (u B : SL(2, ℤ)) :
    Matrix.trace (u * B * u⁻¹).val = Matrix.trace B.val := by
  change
    Matrix.trace
        ((u : Matrix (Fin 2) (Fin 2) ℤ) * B.val * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) =
      _
  have hinv :
    ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (u : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    exact congrArg (fun C : SL(2, ℤ) => C.val) (inv_mul_cancel u)
  rw [Matrix.trace_mul_cycle, hinv, one_mul]

theorem SpecialPeriods.modularSL_actions_eq_iff (B C : SL(2, ℤ)) :
    (∀ z : ℍ, B • z = C • z) ↔ B = C ∨ B = -C := by
  constructor
  · intro h
    have he :
      Triangle.realSLPermutation (B : SL(2, ℝ)) = Triangle.realSLPermutation (C : SL(2, ℝ)) := by
      apply Equiv.ext
      intro z
      change
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B) • z =
          (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C) • z
      simpa only [integerSL_real_action] using h z
    rcases (Triangle.realSLPermutation_eq_iff _ _).mp he with he | he
    · exact Or.inl (Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ) he)
    · right
      apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
      simpa only [Matrix.SpecialLinearGroup.coe_int_neg] using he
  · rintro (rfl | rfl) z
    · rfl
    · exact ModularGroup.SL_neg_smul C z

theorem SpecialPeriods.modularSL_trace_two_or_neg_two_of_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B • z = C • z) (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2 := by
  rcases (modularSL_actions_eq_iff B C).mp h with rfl | rfl
  · exact hC
  · change Matrix.trace (-C.val) = 2 ∨ Matrix.trace (-C.val) = -2
    rw [Matrix.trace_neg]
    rcases hC with hC | hC
    · right
      rw [hC]
    · left
      rw [hC, neg_neg]

theorem SpecialPeriods.modularSL_trace_two_or_neg_two_of_inverse_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, B⁻¹ • z = C • z) (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace B.val = 2 ∨ Matrix.trace B.val = -2 := by
  simpa only [modularSL_trace_inv] using modularSL_trace_two_or_neg_two_of_actions_eq B⁻¹ C h hC

theorem SpecialPeriods.modular_pair_trace_two_or_neg_two_of_cusp_actions_eq (B C : SL(2, ℤ))
    (h : ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = C • z)
    (hC : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2) :
    Matrix.trace (triangleModularA * B).val = 2 ∨ Matrix.trace (triangleModularA * B).val = -2 :=
  modularSL_trace_two_or_neg_two_of_inverse_actions_eq (triangleModularA * B) C h hC

theorem SpecialPeriods.exists_cyclic_normalization_of_rho_lift (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (ha : τ Triangle.centerOne = rhoPoint) (hFb : F Triangle.centerTwo = 1728)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
          (Triangle.centerTwo : ℂ) =
        4)
    (C : SL(2, ℤ)) (hCtr : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2)
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∃ k : Fin 3,
      TauCovariant (fun z => modularCyclicNormalizer k • τ z) ∧
        modularCyclicNormalizer k • τ Triangle.centerOne = rhoPoint ∧
          modularCyclicNormalizer k • τ Triangle.centerTwo = UpperHalfPlane.I := by
  have hJa : modularJ (τ Triangle.centerOne) = 0 := by rw [ha, modularJ_rhoPoint]
  have hJb : modularJ (τ Triangle.centerTwo) = 1728 := (hJ _).trans hFb
  have hFa : F Triangle.centerOne = 0 := (hJ _).symm.trans hJa
  obtain ⟨x, hx⟩ :=
    exists_regular_modular_value_of_j_values hτ.continuous Triangle.centerOne Triangle.centerTwo
      hJa hJb
  have hτMD := hτ.mdifferentiable (by simp)
  have ho₁ :=
    ModularGermLift.native_modularJ_lift_order_of_zero hτMD hJ (n := 1) hFa
      (by simpa using horder₁)
  have ho₂ :=
    ModularGermLift.native_modularJ_lift_order_of_1728 hτMD hJ (n := 2) hFb
      (by simpa using horder₂)
  have hA :=
    modular_lift_first_generator_of_rho_order hτ ha (by simpa [ha] using ho₁)
      (by intro z; rw [hJ, hJ, hF₁]) x hx
  obtain ⟨B, hB⟩ :=
    modularJ_invariant_lift_action hτ Triangle.generatorTwoSL (by intro z; rw [hJ, hJ, hF₂]) x hx
  have hBfix :=
    modular_lift_monodromy_fixes_image Triangle.generatorTwoSL Triangle.centerTwo
      Triangle.generatorTwo_fix B hB
  have hBderiv := modular_lift_generatorTwo_monodromy_deriv hτ (by simpa using ho₂) B hB
  have hBtr := modularSL_trace_zero_of_fixed_deriv_neg_one B (τ Triangle.centerTwo) hBfix hBderiv
  have hab : τ Triangle.centerOne ≠ τ Triangle.centerTwo := by
    intro he
    have hh := congrArg modularJ he
    rw [hJa, hJb] at hh
    norm_num at hh
  have hcomp :=
    modular_lift_cusp_monodromy_comparison B C hA hB hC Triangle.centerOne Triangle.centerTwo hab
  have hprod := modular_pair_trace_two_or_neg_two_of_cusp_actions_eq B C hcomp hCtr
  obtain ⟨k, hkρ, hki, hkA, hkB, _⟩ :=
    modular_pair_elliptic_value_normalization B hBtr hprod (τ Triangle.centerTwo) hBfix
  refine ⟨k, ⟨?_, ?_⟩, ?_, hki⟩
  · intro z
    change ((modularCyclicNormalizer k • τ (Triangle.generatorOneSL • z) : ℍ) : ℂ) = _
    rw [hA, hkA, triangleModularA_eq_T_mul_S, ← modularRhoAction_coe]
    rfl
  · intro z
    change ((modularCyclicNormalizer k • τ (Triangle.generatorTwoSL • z) : ℍ) : ℂ) = _
    rw [← hB z, hkB, ← modularIAction_coe]
    rfl
  · rw [ha, hkρ]

theorem SpecialPeriods.exists_normalized_covariant_modular_translate (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (hFa : F Triangle.centerOne = 0) (hFb : F Triangle.centerTwo = 1728)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
          (Triangle.centerTwo : ℂ) =
        4)
    (C : SL(2, ℤ)) (hCtr : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2)
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∃ γ : SL(2, ℤ),
      TauCovariant (fun z => γ • τ z) ∧
        γ • τ Triangle.centerOne = rhoPoint ∧ γ • τ Triangle.centerTwo = UpperHalfPlane.I := by
  have hzero : modularJ rhoPoint = modularJ (τ Triangle.centerOne) := by
    rw [modularJ_rhoPoint, hJ, hFa]
  obtain ⟨δ, hδ⟩ := (modularJ_eq_iff_exists_smul rhoPoint (τ Triangle.centerOne)).mp hzero
  let σ : ℍ → ℍ := fun z => δ • τ z
  have hσ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω σ := (modularSL_holomorphic δ).comp hτ
  have hσJ : ∀ z : ℍ, modularJ (σ z) = F z := by
    intro z
    exact (modularJ_SL_invariant δ (τ z)).trans (hJ z)
  have hσa : σ Triangle.centerOne = rhoPoint := hδ
  have hCtr' : Matrix.trace (δ * C * δ⁻¹).val = 2 ∨ Matrix.trace (δ * C * δ⁻¹).val = -2 := by
    simpa only [modularSL_trace_conjugate] using hCtr
  have hC' : ∀ z : ℍ, σ (Triangle.cuspSL • z) = (δ * C * δ⁻¹) • σ z :=
    modular_lift_cusp_monodromy_conjugate δ C hC
  obtain ⟨k, hkc, hka, hkb⟩ :=
    exists_cyclic_normalization_of_rho_lift F hσ hσJ hσa hFb hF₁ hF₂ horder₁ horder₂ (δ * C * δ⁻¹)
      hCtr' hC'
  refine ⟨modularCyclicNormalizer k * δ, ?_, ?_, ?_⟩
  · simpa only [TauCovariant, σ, SemigroupAction.mul_smul] using hkc
  · simpa only [σ, SemigroupAction.mul_smul] using hka
  · simpa only [σ, SemigroupAction.mul_smul] using hkb

def SpecialPeriods.TauCusp.simplePoleCoordinate (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  1728 * t / a t

def SpecialPeriods.TauCusp.simplePoleQ (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  SpecialPeriods.modularCuspQ (simplePoleCoordinate a t)

def SpecialPeriods.TauCusp.simplePoleUnit (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  (1728 / a t) * SpecialPeriods.modularCuspUnit (simplePoleCoordinate a t)

@[simp]
theorem SpecialPeriods.TauCusp.simplePoleCoordinate_zero (a : ℂ → ℂ) :
    simplePoleCoordinate a 0 = 0 := by simp [simplePoleCoordinate]

@[simp]
theorem SpecialPeriods.TauCusp.simplePoleQ_zero (a : ℂ → ℂ) : simplePoleQ a 0 = 0 := by
  simp [simplePoleQ]

@[simp]
theorem SpecialPeriods.TauCusp.simplePoleUnit_zero (a : ℂ → ℂ) : simplePoleUnit a 0 = 1 / a 0 := by
  simp [simplePoleUnit]
  ring

theorem SpecialPeriods.TauCusp.simplePoleCoordinate_analyticAt {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleCoordinate a) 0 :=
  (analyticAt_const.mul analyticAt_id).div ha ha0

theorem SpecialPeriods.TauCusp.simplePoleQ_analyticAt {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleQ a) 0 := by
  have hq : AnalyticAt ℂ SpecialPeriods.modularCuspQ (simplePoleCoordinate a 0) := by
    simpa only [simplePoleCoordinate_zero] using SpecialPeriods.modularCuspQ_analyticAt_zero
  exact hq.comp (simplePoleCoordinate_analyticAt ha ha0)

theorem SpecialPeriods.TauCusp.simplePoleUnit_analyticAt {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleUnit a) 0 := by
  have hu : AnalyticAt ℂ SpecialPeriods.modularCuspUnit (simplePoleCoordinate a 0) := by
    simpa only [simplePoleCoordinate_zero] using SpecialPeriods.modularCuspUnit_analyticAt_zero
  exact (analyticAt_const.div ha ha0).mul (hu.comp (simplePoleCoordinate_analyticAt ha ha0))

theorem SpecialPeriods.TauCusp.simplePoleQ_eq_mul_unit (a : ℂ → ℂ) (t : ℂ) :
    simplePoleQ a t = t * simplePoleUnit a t := by
  rw [simplePoleQ, SpecialPeriods.modularCuspQ_eq_mul_unit]
  simp only [simplePoleCoordinate, simplePoleUnit]
  ring

theorem SpecialPeriods.TauCusp.simplePoleQ_eventually_j_eq {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → SpecialPeriods.modularJInQ (simplePoleQ a t) = a t / t := by
  have hj :
    ∀ᶠ u in 𝓝 (0 : ℂ),
      u ≠ 0 → SpecialPeriods.modularJInQ (SpecialPeriods.modularCuspQ u) = 1728 / u :=
    eventually_nhdsWithin_iff.mp SpecialPeriods.modularCuspQ_eventually_j_eq
  have hc : Filter.Tendsto (simplePoleCoordinate a) (𝓝 0) (𝓝 0) := by
    simpa only [simplePoleCoordinate_zero] using
      (simplePoleCoordinate_analyticAt ha ha0).continuousAt.tendsto
  filter_upwards [hc.eventually hj, ha.continuousAt.eventually_ne ha0] with t hjt hat
  intro ht
  have hct : simplePoleCoordinate a t ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) ht) hat
  rw [simplePoleQ, hjt hct, simplePoleCoordinate]
  field_simp

theorem SpecialPeriods.TauCusp.exists_simplePoleQ_coordinate {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ r > 0,
      AnalyticOnNhd ℂ (simplePoleQ a) (Metric.ball 0 r) ∧
        AnalyticOnNhd ℂ (simplePoleUnit a) (Metric.ball 0 r) ∧
          ∀ t ∈ Metric.ball (0 : ℂ) r,
            a t ≠ 0 ∧
              simplePoleUnit a t ≠ 0 ∧
                ‖simplePoleQ a t‖ < R ∧
                  (t ≠ 0 → SpecialPeriods.modularJInQ (simplePoleQ a t) = a t / t) := by
  have hq := simplePoleQ_analyticAt ha ha0
  have hu := simplePoleUnit_analyticAt ha ha0
  have hu0 : simplePoleUnit a 0 ≠ 0 := by
    rw [simplePoleUnit_zero]
    exact one_div_ne_zero ha0
  have hn : ∀ᶠ t in 𝓝 (0 : ℂ), ‖simplePoleQ a t‖ < R := by
    have h :=
      hq.continuousAt.preimage_mem_nhds
        (show Metric.ball (0 : ℂ) R ∈ 𝓝 (simplePoleQ a 0)
          by
          rw [simplePoleQ_zero]
          exact Metric.ball_mem_nhds _ hR)
    filter_upwards [h] with t ht
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using ht
  have hall :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      AnalyticAt ℂ (simplePoleQ a) t ∧
        AnalyticAt ℂ (simplePoleUnit a) t ∧
          a t ≠ 0 ∧
            simplePoleUnit a t ≠ 0 ∧
              ‖simplePoleQ a t‖ < R ∧
                (t ≠ 0 → SpecialPeriods.modularJInQ (simplePoleQ a t) = a t / t) := by
    filter_upwards [hq.eventually_analyticAt, hu.eventually_analyticAt,
      ha.continuousAt.eventually_ne ha0, hu.continuousAt.eventually_ne hu0, hn,
      simplePoleQ_eventually_j_eq ha ha0] with t hqt hut hat hut0 hnt hjt
    exact ⟨hqt, hut, hat, hut0, hnt, hjt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨r, hr, fun t ht => (hball ht).1, fun t ht => (hball ht).2.1, fun t ht => (hball ht).2.2⟩

theorem SpecialPeriods.TauCusp.mem_logBase_iff_im (r : ℝ) (hr : 0 < r) (s : ℂ) :
    s ∈ SpecialPeriods.CuspFamily.logBase r ↔ -Real.log r / (2 * Real.pi) < s.im :=
  CuspUniformization.mem_logDomain_iff_im r hr (s, 0)

theorem SpecialPeriods.TauCusp.logBase_eq_halfSpace (r : ℝ) (hr : 0 < r) :
    (SpecialPeriods.CuspFamily.logBase r : Set ℂ) = {s | -Real.log r / (2 * Real.pi) < s.im} := by
  ext s
  exact mem_logBase_iff_im r hr s

theorem SpecialPeriods.TauCusp.logBase_convex (r : ℝ) (hr : 0 < r) :
    Convex ℝ (SpecialPeriods.CuspFamily.logBase r : Set ℂ) := by
  rw [logBase_eq_halfSpace r hr]
  exact (convex_Ioi (-Real.log r / (2 * Real.pi))).linear_preimage Complex.imLm

theorem SpecialPeriods.TauCusp.logBase_set_nonempty (r : ℝ) (hr : 0 < r) :
    (SpecialPeriods.CuspFamily.logBase r : Set ℂ).Nonempty := by
  obtain ⟨p, hp⟩ := CuspUniformization.logDomain_nonempty r hr
  exact ⟨p.1, hp⟩

theorem SpecialPeriods.TauCusp.exponential_eq_qParam_one (s : ℂ) :
    CuspUniformization.exponential s = Function.Periodic.qParam 1 s := by
  simp only [CuspUniformization.exponential, Function.Periodic.qParam, Complex.ofReal_one,
    div_one]

theorem SpecialPeriods.TauCusp.qParam_eq_exponential_div (w : ℝ) (s : ℂ) :
    Function.Periodic.qParam w s = CuspUniformization.exponential (s / w) := by
  simp only [CuspUniformization.exponential, Function.Periodic.qParam, mul_div_assoc]

theorem SpecialPeriods.TauCusp.norm_exponential_lt_one_iff (s : ℂ) :
    ‖CuspUniformization.exponential s‖ < 1 ↔ 0 < s.im := by
  simpa only [SpecialPeriods.CuspFamily.mem_logBase, Real.log_one, neg_zero, zero_div] using
    mem_logBase_iff_im 1 zero_lt_one s

theorem SpecialPeriods.TauCusp.upperHalfPlane_of_exponential_norm_lt_one {s : ℂ}
    (hs : ‖CuspUniformization.exponential s‖ < 1) : 0 < s.im :=
  (norm_exponential_lt_one_iff s).mp hs

theorem SpecialPeriods.TauCusp.exponential_norm_lt_one_of_upperHalfPlane {s : ℂ} (hs : 0 < s.im) :
    ‖CuspUniformization.exponential s‖ < 1 :=
  (norm_exponential_lt_one_iff s).mpr hs

theorem SpecialPeriods.TauCusp.analytic_unit_normalized_logarithm {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    ∃ r > 0,
      ∃ h : ℂ → ℂ,
        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
          h 0 = CuspUniformization.logarithm (u 0) ∧
            ∀ t ∈ Metric.ball 0 r, CuspUniformization.exponential (h t) = u t := by
  let s := CuspUniformization.logarithm (u 0)
  let e := SpecialPeriods.CuspFamily.scalarExponentialChart s
  have hs : s ∈ e.source := SpecialPeriods.CuspFamily.scalarExponentialChart_mem_source s
  have he0 : e s = u 0 := CuspUniformization.exponential_logarithm hu0
  have huT : u 0 ∈ e.target := he0 ▸ e.map_source hs
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ u t ∧ u t ∈ e.target :=
    hu.eventually_analyticAt.and (hu.continuousAt (e.open_target.mem_nhds huT))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨r, hr, e.symm ∘ u, ?_, ?_, ?_⟩
  · intro t ht
    have hInv : ContDiffOn ℂ ω e.symm e.target :=
      SpecialPeriods.CuspFamily.scalarExponentialChart_symm_holomorphic s
    exact
      ((hInv (u t) (hball ht).2).contDiffAt (e.open_target.mem_nhds (hball ht).2)).analyticAt.comp
        (hball ht).1
  · change e.symm (u 0) = s
    rw [← he0]
    exact e.left_inv hs
  · intro t ht
    exact e.right_inv (hball ht).2

theorem SpecialPeriods.TauCusp.modularJInQ_exponential {z : ℂ} (hz : 0 < z.im) :
    SpecialPeriods.modularJInQ (CuspUniformization.exponential z) =
      SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) := by
  simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one,
    CuspUniformization.exponential, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    SpecialPeriods.modularJInQ_qParam (UpperHalfPlane.ofComplex z)

def SpecialPeriods.TauCusp.correctedLogarithm (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  s + h (CuspUniformization.exponential s)

theorem SpecialPeriods.TauCusp.correctedLogarithm_exponential (h : ℂ → ℂ) (s : ℂ) :
    CuspUniformization.exponential (correctedLogarithm h s) =
      CuspUniformization.exponential s *
        CuspUniformization.exponential (h (CuspUniformization.exponential s)) :=
  CuspUniformization.exponential_add _ _

theorem SpecialPeriods.TauCusp.correctedLogarithm_sub_int (h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    correctedLogarithm h (s - k) = correctedLogarithm h s - k := by
  simp only [correctedLogarithm, SpecialPeriods.CuspFamily.exponential_sub_int]
  abel

theorem SpecialPeriods.TauCusp.correctedLogarithm_analyticAt {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {s : ℂ}
    (hs : s ∈ SpecialPeriods.CuspFamily.logBase r) : AnalyticAt ℂ (correctedLogarithm h) s :=
  analyticAt_id.add
    ((hh (CuspUniformization.exponential s) hs).comp
      CuspUniformization.exponential_holomorphic.contDiffAt.analyticAt)

theorem SpecialPeriods.TauCusp.exists_simplePole_logarithmic_lift {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0,
      r < r₀ ∧
        r < 1 ∧
          ∃ h : ℂ → ℂ,
            AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
              h 0 = CuspUniformization.logarithm (1 / a 0) ∧
                (∀ t ∈ Metric.ball 0 r,
                    CuspUniformization.exponential (h t) = simplePoleUnit a t) ∧
                  ∀ s ∈ SpecialPeriods.CuspFamily.logBase r,
                    CuspUniformization.exponential (correctedLogarithm h s) =
                        simplePoleQ a (CuspUniformization.exponential s) ∧
                      0 < (correctedLogarithm h s).im ∧
                        ‖CuspUniformization.exponential (correctedLogarithm h s)‖ < R ∧
                          SpecialPeriods.modularJ
                              (UpperHalfPlane.ofComplex (correctedLogarithm h s)) =
                            a (CuspUniformization.exponential s) /
                              CuspUniformization.exponential s := by
  obtain ⟨rq, hrq, _, _, hq⟩ := exists_simplePoleQ_coordinate ha ha0 (lt_min hR zero_lt_one)
  obtain ⟨rh, hrh, h, hh, hh0, he⟩ :=
    analytic_unit_normalized_logarithm (simplePoleUnit_analyticAt ha ha0)
      (by simpa using one_div_ne_zero ha0)
  obtain ⟨r, hr, hrr⟩ :=
    exists_between
      (show 0 < Min.min rq (Min.min rh (Min.min r₀ 1)) from
        lt_min hrq (lt_min hrh (lt_min hr₀ zero_lt_one)))
  have hparts : r < rq ∧ r < rh ∧ r < r₀ ∧ r < 1 := by simpa only [lt_min_iff] using hrr
  have hh' : AnalyticOnNhd ℂ h (Metric.ball 0 r) :=
    hh.mono (Metric.ball_subset_ball hparts.2.1.le)
  refine ⟨r, hr, hparts.2.2.1, hparts.2.2.2, h, hh', ?_, ?_, ?_⟩
  · simpa only [simplePoleUnit_zero] using hh0
  · intro t ht
    exact he t (Metric.ball_subset_ball hparts.2.1.le ht)
  · intro s hs
    have hst : CuspUniformization.exponential s ∈ Metric.ball (0 : ℂ) r := hs
    have hsq := hq (CuspUniformization.exponential s) (Metric.ball_subset_ball hparts.1.le hst)
    have hse := he (CuspUniformization.exponential s) (Metric.ball_subset_ball hparts.2.1.le hst)
    have hτq :
      CuspUniformization.exponential (correctedLogarithm h s) =
        simplePoleQ a (CuspUniformization.exponential s) := by
      rw [correctedLogarithm_exponential, hse, simplePoleQ_eq_mul_unit]
    have hτpos : 0 < (correctedLogarithm h s).im :=
      upperHalfPlane_of_exponential_norm_lt_one
        (by rw [hτq]; exact lt_of_lt_of_le hsq.2.2.1 (min_le_right R 1))
    refine ⟨hτq, hτpos, ?_, ?_⟩
    · rw [hτq]
      exact lt_of_lt_of_le hsq.2.2.1 (min_le_left R 1)
    · rw [← modularJInQ_exponential hτpos, hτq]
      exact hsq.2.2.2 (CuspUniformization.exponential_ne_zero s)

def SpecialPeriods.TauCusp.correctedLogarithmWidth (w : ℝ) (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  s / w + h (Function.Periodic.qParam w s)

theorem SpecialPeriods.TauCusp.correctedLogarithmWidth_eq_correctedLogarithm (w : ℝ) (h : ℂ → ℂ)
    (s : ℂ) : correctedLogarithmWidth w h s = correctedLogarithm h (s / w) := by
  simp only [correctedLogarithmWidth, correctedLogarithm, qParam_eq_exponential_div]

theorem SpecialPeriods.TauCusp.correctedLogarithmWidth_exponential (w : ℝ) (h : ℂ → ℂ) (s : ℂ) :
    CuspUniformization.exponential (correctedLogarithmWidth w h s) =
      Function.Periodic.qParam w s *
        CuspUniformization.exponential (h (Function.Periodic.qParam w s)) := by
  rw [correctedLogarithmWidth_eq_correctedLogarithm, correctedLogarithm_exponential, ←
    qParam_eq_exponential_div]

theorem SpecialPeriods.TauCusp.correctedLogarithmWidth_analyticAt (w : ℝ) {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {s : ℂ} (hs : ‖Function.Periodic.qParam w s‖ < r) :
    AnalyticAt ℂ (correctedLogarithmWidth w h) s := by
  have hs' : s / w ∈ SpecialPeriods.CuspFamily.logBase r := by
    rw [SpecialPeriods.CuspFamily.mem_logBase]
    simpa only [qParam_eq_exponential_div] using hs
  have hcomp :=
    (correctedLogarithm_analyticAt hh hs').comp (f := fun z : ℂ => z / (w : ℂ))
      (show AnalyticAt ℂ (fun z : ℂ => z / (w : ℂ)) s from analyticAt_id.div_const)
  have hfun : correctedLogarithmWidth w h = correctedLogarithm h ∘ (fun z : ℂ => z / (w : ℂ)) :=
    funext (correctedLogarithmWidth_eq_correctedLogarithm w h)
  rw [hfun]
  exact hcomp

theorem SpecialPeriods.TauCusp.correctedLogarithmWidth_analyticOnNhd (w : ℝ) {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (correctedLogarithmWidth w h) {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  fun _ hs => correctedLogarithmWidth_analyticAt w hh hs

theorem SpecialPeriods.TauCusp.div_sub_int_mul_width (w : ℝ) (hw : w ≠ 0) (s : ℂ) (k : ℤ) :
    (s - (k : ℂ) * w) / w = s / w - k := by
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  rw [sub_div, mul_div_cancel_right₀ _ hwC]

theorem SpecialPeriods.TauCusp.qParam_sub_int_mul_width (w : ℝ) (hw : w ≠ 0) (s : ℂ) (k : ℤ) :
    Function.Periodic.qParam w (s - (k : ℂ) * w) = Function.Periodic.qParam w s := by
  rw [qParam_eq_exponential_div, div_sub_int_mul_width w hw,
    SpecialPeriods.CuspFamily.exponential_sub_int, qParam_eq_exponential_div]

theorem SpecialPeriods.TauCusp.correctedLogarithmWidth_sub_int_mul_width (w : ℝ) (hw : w ≠ 0)
    (h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    correctedLogarithmWidth w h (s - (k : ℂ) * w) = correctedLogarithmWidth w h s - k := by
  simp only [correctedLogarithmWidth_eq_correctedLogarithm, div_sub_int_mul_width w hw,
    correctedLogarithm_sub_int]

theorem SpecialPeriods.TauCusp.exists_simplePole_logarithmic_lift_width (w : ℝ) (hw : 0 < w)
    {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0,
      r < r₀ ∧
        r < 1 ∧
          ∃ h : ℂ → ℂ,
            AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
              h 0 = CuspUniformization.logarithm (1 / a 0) ∧
                (∀ t ∈ Metric.ball 0 r,
                    CuspUniformization.exponential (h t) = simplePoleUnit a t) ∧
                  ∀ s ∈ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r},
                    CuspUniformization.exponential (correctedLogarithmWidth w h s) =
                        simplePoleQ a (Function.Periodic.qParam w s) ∧
                      0 < (correctedLogarithmWidth w h s).im ∧
                        ‖CuspUniformization.exponential (correctedLogarithmWidth w h s)‖ < R ∧
                          SpecialPeriods.modularJ
                              (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s)) =
                            a (Function.Periodic.qParam w s) / Function.Periodic.qParam w s := by
  obtain ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, hτ⟩ :=
    exists_simplePole_logarithmic_lift ha ha0 hR hr₀
  refine ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, ?_⟩
  intro s hs
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  obtain ⟨z, rfl⟩ := mul_right_surjective₀ hwC s
  have hz : z ∈ SpecialPeriods.CuspFamily.logBase r := by
    apply (SpecialPeriods.CuspFamily.mem_logBase r z).mpr
    simpa only [Set.mem_ofPred_eq, qParam_eq_exponential_div, mul_div_cancel_right₀ _ hwC] using
      hs
  simpa only [correctedLogarithmWidth_eq_correctedLogarithm, qParam_eq_exponential_div,
    mul_div_cancel_right₀ _ hwC] using hτ z hz

theorem SpecialPeriods.TauCusp.upperHalfPlane_ambient_analyticAt {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ) {s : ℂ} (hs : 0 < s.im) :
    AnalyticAt ℂ (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) s := by
  have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) s :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ) (UpperHalfPlane.ofComplex s)).comp s
      (UpperHalfPlane.contMDiffAt_ofComplex hs)
  exact hc.contDiffAt.analyticAt

theorem SpecialPeriods.TauCusp.widthLogBase_convex (w : ℝ) {r : ℝ} (hr : 0 < r) :
    Convex ℝ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} := by
  have hset :
    {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} =
      (LinearMap.mulRight ℝ (w : ℂ)⁻¹) ⁻¹' (SpecialPeriods.CuspFamily.logBase r : Set ℂ) := by
    ext s
    change
      ‖Function.Periodic.qParam w s‖ < r ↔ s * (w : ℂ)⁻¹ ∈ SpecialPeriods.CuspFamily.logBase r
    rw [SpecialPeriods.CuspFamily.mem_logBase, qParam_eq_exponential_div, div_eq_mul_inv]
  rw [hset]
  exact (logBase_convex r hr).linear_preimage (LinearMap.mulRight ℝ (w : ℂ)⁻¹)

theorem SpecialPeriods.TauCusp.upperHalfPlane_of_qParam_norm_lt_one (w : ℝ) (hw : 0 < w) {s : ℂ}
    (hs : ‖Function.Periodic.qParam w s‖ < 1) : 0 < s.im := by
  have hsd : 0 < (s / (w : ℂ)).im :=
    upperHalfPlane_of_exponential_norm_lt_one (by simpa only [qParam_eq_exponential_div] using hs)
  rw [Complex.div_ofReal_im] at hsd
  exact (div_pos_iff_of_pos_right hw).mp hsd

theorem SpecialPeriods.TauCusp.eqOn_correctedLogarithmWidth_of_eventuallyEq (w : ℝ) {r : ℝ}
    (hr : 0 < r) {h τ : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r))
    (hτ : AnalyticOnNhd ℂ τ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r}) {a : ℂ}
    (ha : ‖Function.Periodic.qParam w a‖ < r) (heq : τ =ᶠ[𝓝 a] correctedLogarithmWidth w h) :
    Set.EqOn τ (correctedLogarithmWidth w h) {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  hτ.eqOn_of_preconnected_of_eventuallyEq (correctedLogarithmWidth_analyticOnNhd w hh)
    (widthLogBase_convex w hr).isPreconnected ha heq

theorem SpecialPeriods.TauCusp.native_eqOn_correctedLogarithmWidth_of_eventuallyEq (w : ℝ)
    (hw : 0 < w) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : ‖Function.Periodic.qParam w a‖ < r)
    (heq :
      (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 a] correctedLogarithmWidth w h) :
    Set.EqOn (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) (correctedLogarithmWidth w h)
      {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} := by
  apply eqOn_correctedLogarithmWidth_of_eventuallyEq w hr hh ?_ ha heq
  intro s hs
  exact
    upperHalfPlane_ambient_analyticAt hτ
      (upperHalfPlane_of_qParam_norm_lt_one w hw (lt_trans hs hr1))

private theorem SpecialPeriods.TauCusp.exists_native_source_cusp_point_mo1973_17243 (w : ℝ)
    (hw : 0 < w) {r : ℝ} (hr : 0 < r) : ∃ a : ℍ, ‖Function.Periodic.qParam w (a : ℂ)‖ < r := by
  obtain ⟨s, hs⟩ := logBase_set_nonempty (Min.min r 1) (lt_min hr zero_lt_one)
  have hsn : ‖CuspUniformization.exponential s‖ < Min.min r 1 :=
    (SpecialPeriods.CuspFamily.mem_logBase (Min.min r 1) s).mp hs
  have hspos : 0 < s.im :=
    upperHalfPlane_of_exponential_norm_lt_one (lt_of_lt_of_le hsn (min_le_right r 1))
  have hswpos : 0 < (s * (w : ℂ)).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.mul_zero,
      zero_add] using mul_pos hspos hw
  refine ⟨⟨s * w, hswpos⟩, ?_⟩
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  simpa only [qParam_eq_exponential_div, mul_div_cancel_right₀ _ hwC] using
    lt_of_lt_of_le hsn (min_le_left r 1)

private theorem SpecialPeriods.TauCusp.sub_int_mul_width_im_pos_mo1973_17244 (w : ℝ) (k : ℤ)
    {s : ℂ} (hs : 0 < s.im) : 0 < (s - (k : ℂ) * w).im := by
  simpa only [Complex.sub_im, Complex.mul_im, Complex.intCast_im, Complex.ofReal_im,
    MulZeroClass.mul_zero, MulZeroClass.zero_mul, add_zero, sub_zero] using hs

theorem SpecialPeriods.TauCusp.global_native_sub_int_mul_width_of_cuspFormula (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    (hcusp :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam w (z : ℂ)‖ < r → (τ z : ℂ) = correctedLogarithmWidth w h z)
    (k : ℤ) (z : ℍ) :
    (τ (UpperHalfPlane.ofComplex ((z : ℂ) - (k : ℂ) * w)) : ℂ) = (τ z : ℂ) - k := by
  have hleft :
    AnalyticOnNhd ℂ (fun s : ℂ => (τ (UpperHalfPlane.ofComplex (s - (k : ℂ) * w)) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := by
    intro s hs
    have hshift : AnalyticAt ℂ (fun t : ℂ => t - (k : ℂ) * w) s :=
      analyticAt_id.sub analyticAt_const
    exact
      (upperHalfPlane_ambient_analyticAt hτ (sub_int_mul_width_im_pos_mo1973_17244 w k hs)).comp
        (f := fun t : ℂ => t - (k : ℂ) * w) (x := s) hshift
  have hright :
    AnalyticOnNhd ℂ (fun s : ℂ => (τ (UpperHalfPlane.ofComplex s) : ℂ) - k)
      UpperHalfPlane.upperHalfPlaneSet :=
    fun s hs => (upperHalfPlane_ambient_analyticAt hτ hs).sub analyticAt_const
  have hconnected : IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm).isPreconnected
  obtain ⟨a, ha⟩ := exists_native_source_cusp_point_mo1973_17243 w hw hr
  have hcuspAmbient {s : ℂ} (hs : 0 < s.im) (hsq : ‖Function.Periodic.qParam w s‖ < r) :
    (τ (UpperHalfPlane.ofComplex s) : ℂ) = correctedLogarithmWidth w h s := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hs] using hcusp ⟨s, hs⟩ hsq
  have hqOpen : IsOpen {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
    isOpen_lt (Function.Periodic.continuous_qParam (h := w)).norm continuous_const
  have heq :
    (fun s : ℂ => (τ (UpperHalfPlane.ofComplex (s - (k : ℂ) * w)) : ℂ)) =ᶠ[𝓝 (a : ℂ)]
      (fun s : ℂ => (τ (UpperHalfPlane.ofComplex s) : ℂ) - k) := by
    filter_upwards [hqOpen.mem_nhds ha,
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos] with s hsq hs
    have hskq : ‖Function.Periodic.qParam w (s - (k : ℂ) * w)‖ < r := by
      rw [qParam_sub_int_mul_width w hw.ne']
      exact hsq
    rw [hcuspAmbient (sub_int_mul_width_im_pos_mo1973_17244 w k hs) hskq, hcuspAmbient hs hsq,
      correctedLogarithmWidth_sub_int_mul_width w hw.ne']
  have hglobal := hleft.eqOn_of_preconnected_of_eventuallyEq hright hconnected a.im_pos heq
  have hz :
    (τ (UpperHalfPlane.ofComplex ((z : ℂ) - (k : ℂ) * w)) : ℂ) =
      (τ (UpperHalfPlane.ofComplex (z : ℂ)) : ℂ) - k :=
    hglobal z.im_pos
  simpa only [UpperHalfPlane.ofComplex_apply] using hz

theorem SpecialPeriods.modular_Tinv_vadd (z : ℍ) : ModularGroup.T⁻¹ • z = (-1 : ℝ) +ᵥ z := by
  simpa using UpperHalfPlane.modular_T_zpow_smul z (-1)

theorem SpecialPeriods.tau_cusp_monodromy_of_formula {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ}
    (hformula :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r →
          (τ z : ℂ) = TauCusp.correctedLogarithmWidth Triangle.width h (z : ℂ)) :
    ∀ z : ℍ, τ (Triangle.cuspSL • z) = ModularGroup.T⁻¹ • τ z := by
  intro z
  have he :=
    TauCusp.global_native_sub_int_mul_width_of_cuspFormula Triangle.width Triangle.width_pos hr hτ
      hformula (1 : ℤ) z
  have hz : ((Triangle.cuspSL • z : ℍ) : ℂ) = (z : ℂ) - Triangle.width := by
    rw [Triangle.cuspSL_apply, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have harg :
    UpperHalfPlane.ofComplex ((z : ℂ) - (1 : ℂ) * Triangle.width) = Triangle.cuspSL • z := by
    rw [one_mul, ← hz, UpperHalfPlane.ofComplex_apply]
  apply UpperHalfPlane.ext
  calc
    (τ (Triangle.cuspSL • z) : ℂ) = (τ z : ℂ) - 1 := by simpa only [Int.cast_one, harg] using he
    _ = ((ModularGroup.T⁻¹ • τ z : ℍ) : ℂ) := by
      rw [modular_Tinv_vadd, UpperHalfPlane.coe_vadd]
      push_cast
      ring

theorem SpecialPeriods.tau_covariant_cuspSL {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    τ (Triangle.cuspSL • z) = ModularGroup.T⁻¹ • τ z := by
  rw [Triangle.cuspSL_apply, modular_Tinv_vadd]
  simpa only [triangleGeometricRepresentation_cusp_apply] using tau_covariant_cusp hτ z

theorem SpecialPeriods.modular_translate_commutes_Tinv_of_cusp_covariance {τ : ℍ → ℍ}
    (γ : SL(2, ℤ)) (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = ModularGroup.T⁻¹ • τ z)
    (hcov : TauCovariant (fun z => γ • τ z)) (a b : ℍ) (hab : τ a ≠ τ b) :
    ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z) := by
  have hvalues (z : ℍ) : (γ * ModularGroup.T⁻¹) • τ z = (ModularGroup.T⁻¹ * γ) • τ z := by
    rw [SemigroupAction.mul_smul, SemigroupAction.mul_smul, ← hC z]
    exact tau_covariant_cuspSL hcov z
  simpa only [SemigroupAction.mul_smul] using
    modularSL_actions_eq_of_two_values (γ * ModularGroup.T⁻¹) (ModularGroup.T⁻¹ * γ) (τ a) (τ b)
      hab (hvalues a) (hvalues b)

theorem SpecialPeriods.modularSL_commutes_T_inv_of_actions_commute (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z)) :
    Commute γ ModularGroup.T⁻¹ := by
  have hconj : ∀ z : ℍ, (γ * ModularGroup.T⁻¹ * γ⁻¹) • z = ModularGroup.T⁻¹ • z := by
    intro z
    simp only [SemigroupAction.mul_smul]
    rw [h, smul_inv_smul]
  rcases (modularSL_actions_eq_iff (γ * ModularGroup.T⁻¹ * γ⁻¹) ModularGroup.T⁻¹).mp hconj with
    he | he
  · change γ * ModularGroup.T⁻¹ = ModularGroup.T⁻¹ * γ
    have hm := congrArg (fun B : SL(2, ℤ) => B * γ) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
  · have ht := congrArg (fun B : SL(2, ℤ) => Matrix.trace B.val) he
    rw [modularSL_trace_conjugate] at ht
    change
      Matrix.trace (ModularGroup.T⁻¹ : SL(2, ℤ)).val =
        Matrix.trace (-((ModularGroup.T⁻¹ : SL(2, ℤ)).val)) at ht
    have hT : Matrix.trace (ModularGroup.T⁻¹ : SL(2, ℤ)).val = 2 := by decide
    rw [Matrix.trace_neg, hT] at ht
    norm_num at ht

private theorem SpecialPeriods.modularSL_lower_left_zero_of_commutes_T_inv_mo1973_17251
    (γ : SL(2, ℤ)) (h : Commute γ ModularGroup.T⁻¹) : γ 1 0 = 0 := by
  have he := congrArg (fun B : SL(2, ℤ) => B 0 0) h.eq
  change
    (γ.val * (ModularGroup.T⁻¹ : SL(2, ℤ)).val) 0 0 =
      ((ModularGroup.T⁻¹ : SL(2, ℤ)).val * γ.val) 0 0 at he
  rw [ModularGroup.coe_T_inv] at he
  simp [Matrix.mul_apply, Fin.sum_univ_two] at he
  omega

theorem SpecialPeriods.modularSL_integer_translation_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z)) :
    ∃ n : ℤ, ∀ z : ℍ, γ • z = (n : ℝ) +ᵥ z := by
  have hc :=
    modularSL_lower_left_zero_of_commutes_T_inv_mo1973_17251 γ
      (modularSL_commutes_T_inv_of_actions_commute γ h)
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero (g := γ) hc
  exact ⟨n, fun z => (hn z).trans (UpperHalfPlane.modular_T_zpow_smul z n)⟩

theorem SpecialPeriods.modularSL_integer_translation_coe_of_commutes_T_inv_action (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, γ • (ModularGroup.T⁻¹ • z) = ModularGroup.T⁻¹ • (γ • z)) :
    ∃ n : ℤ, ∀ z : ℍ, ((γ • z : ℍ) : ℂ) = (z : ℂ) + (n : ℂ) := by
  obtain ⟨n, hn⟩ := modularSL_integer_translation_of_commutes_T_inv_action γ h
  refine ⟨n, fun z => ?_⟩
  rw [hn z, UpperHalfPlane.coe_vadd]
  simp [add_comm]

theorem SpecialPeriods.TauCusp.simplePole_factorization {F : ℂ → ℂ} (hF : MeromorphicAt F 0)
    (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) :
    ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧ a 0 ≠ 0 ∧ ∃ r > 0, ∀ t ∈ Metric.ball 0 r, t ≠ 0 → F t = a t / t := by
  obtain ⟨a, ha, ha0, heq⟩ := (meromorphicOrderAt_eq_int_iff hF).mp horder
  have heq' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), F t = a t / t := by
    filter_upwards [heq] with t ht
    simpa [sub_zero, zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  rw [eventually_nhdsWithin_iff] at heq'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp heq'
  exact ⟨a, ha, ha0, r, hr, fun t ht hne => hball ht hne⟩

theorem SpecialPeriods.TauCusp.simplePole_factorization_of_tendsto {F : ℂ → ℂ}
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) {c : ℂ}
    (hc : Filter.Tendsto (fun t => t * F t) (𝓝[≠] 0) (𝓝 c)) :
    ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧
        a 0 ≠ 0 ∧ a 0 = c ∧ ∃ r > 0, ∀ t ∈ Metric.ball 0 r, t ≠ 0 → F t = a t / t := by
  obtain ⟨a, ha, ha0, r, hr, hball⟩ := simplePole_factorization hF horder
  have heq : (fun t => t * F t) =ᶠ[𝓝[≠] (0 : ℂ)] a := by
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ Metric.ball 0 r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [hball t ht ht0]
    field_simp [ht0]
  have hvalue : a 0 = c := tendsto_nhds_unique ha.continuousAt.continuousWithinAt (hc.congr' heq)
  exact ⟨a, ha, ha0, hvalue, r, hr, hball⟩

theorem SpecialPeriods.ModularGermLift.analyticAt_modular_smul_of_im_pos (γ : SL(2, ℤ)) {w : ℂ}
    (hw : 0 < w.im) : AnalyticAt ℂ (fun v : ℂ => ((γ • UpperHalfPlane.ofComplex v : ℍ) : ℂ)) w := by
  change
    AnalyticAt ℂ
      (fun v : ℂ => ((Matrix.SpecialLinearGroup.mapGL ℝ γ • UpperHalfPlane.ofComplex v : ℍ) : ℂ))
      w
  apply UpperHalfPlane.analyticAt_smul (τ := (⟨w, hw⟩ : ℍ))
  change 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ γ).det : ℝ)
  simp

theorem SpecialPeriods.ModularGermLift.analyticAt_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ} {a : ℂ}
    (hσ : AnalyticAt ℂ σ a) (hσa : 0 < (σ a).im) :
    AnalyticAt ℂ (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) a :=
  (analyticAt_modular_smul_of_im_pos γ hσa).comp hσ

theorem SpecialPeriods.ModularGermLift.analyticOnNhd_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ}
    {U : Set ℂ} (hσ : AnalyticOnNhd ℂ σ U)
    (hσU : Set.MapsTo σ U UpperHalfPlane.upperHalfPlaneSet) :
    AnalyticOnNhd ℂ (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) U := fun a ha =>
  analyticAt_modular_smul γ (hσ a ha) (hσU ha)

theorem SpecialPeriods.ModularGermLift.modularJ_modular_smul (γ : SL(2, ℤ)) (w : ℂ) :
    SpecialPeriods.modularJ
        (UpperHalfPlane.ofComplex ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =
      SpecialPeriods.modularJ (UpperHalfPlane.ofComplex w) := by
  rw [UpperHalfPlane.ofComplex_apply]
  exact SpecialPeriods.modularJ_SL_invariant γ (UpperHalfPlane.ofComplex w)

theorem SpecialPeriods.ModularGermLift.modularGroup_countable : Countable SL(2, ℤ) := by
  unfold Matrix.SpecialLinearGroup Matrix
  infer_instance

theorem SpecialPeriods.ModularGermLift.exists_eqOn_of_countable_analytic_cover {ι : Type*}
    [Countable ι] {U : Set ℂ} {f : ℂ → ℂ} {g : ι → ℂ → ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUn : U.Nonempty) (hf : AnalyticOnNhd ℂ f U) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hcover : ∀ z ∈ U, ∃ i, f z = g i z) : ∃ i, Set.EqOn f (g i) U := by
  let : BaireSpace U := hU.baireSpace
  obtain ⟨a, ha⟩ := hUn
  let : Nonempty U := ⟨⟨a, ha⟩⟩
  let C : ι → Set U := fun i => {z | f z = g i z}
  have hC (i : ι) : IsClosed (C i) :=
    isClosed_eq hf.continuousOn.domRestrict (hg i).continuousOn.domRestrict
  have hCU : ⋃ i, C i = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcover z z.2
  obtain ⟨i, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hC hCU
  let V : Set ℂ := Subtype.val '' interior (C i)
  have hV : IsOpen V := hU.isOpenMap_subtype_val _ isOpen_interior
  have hzV : (z : ℂ) ∈ V := Set.mem_image_of_mem Subtype.val hz
  have heq : f =ᶠ[𝓝 (z : ℂ)] g i := by
    filter_upwards [hV.mem_nhds hzV] with w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvC : v ∈ C i := interior_subset hv
    exact hvC
  exact ⟨i, hf.eqOn_of_preconnected_of_eventuallyEq (hg i) hUc z.2 heq⟩

theorem SpecialPeriods.ModularGermLift.exists_modular_alignment {U : Set ℂ} {τ σ : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUn : U.Nonempty) (hτ : AnalyticOnNhd ℂ τ U)
    (hσ : AnalyticOnNhd ℂ σ U) (hτU : Set.MapsTo τ U UpperHalfPlane.upperHalfPlaneSet)
    (hσU : Set.MapsTo σ U UpperHalfPlane.upperHalfPlaneSet)
    (hJ :
      Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)))
        (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (σ z))) U) :
    ∃ γ : SL(2, ℤ), Set.EqOn τ (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) U := by
  let : Countable SL(2, ℤ) := modularGroup_countable
  apply
    exists_eqOn_of_countable_analytic_cover hU hUc hUn hτ
      (fun γ => analyticOnNhd_modular_smul γ hσ hσU)
  intro z hz
  obtain ⟨γ, hγ⟩ :=
    (SpecialPeriods.modularJ_eq_iff_exists_smul (UpperHalfPlane.ofComplex (τ z))
          (UpperHalfPlane.ofComplex (σ z))).mp
      (hJ hz)
  refine ⟨γ, ?_⟩
  have hc := congrArg (fun w : ℍ => (w : ℂ)) hγ
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hτU hz)] at hc
  exact hc.symm

theorem SpecialPeriods.ModularGermLift.exists_modular_alignment_germ {τ σ : ℂ → ℂ} {a : ℂ}
    (hτ : AnalyticAt ℂ τ a) (hσ : AnalyticAt ℂ σ a) (hτa : 0 < (τ a).im) (hσa : 0 < (σ a).im)
    (hJ :
      (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) =ᶠ[𝓝 a]
        (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (σ z)))) :
    ∃ γ : SL(2, ℤ), τ =ᶠ[𝓝 a] (fun z => ((γ • UpperHalfPlane.ofComplex (σ z) : ℍ) : ℂ)) := by
  have hpτ : ∀ᶠ z in 𝓝 a, τ z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    hτ.continuousAt.preimage_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hτa)
  have hpσ : ∀ᶠ z in 𝓝 a, σ z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    hσ.continuousAt.preimage_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hσa)
  have hn :
    {z |
        AnalyticAt ℂ τ z ∧
          AnalyticAt ℂ σ z ∧
            τ z ∈ UpperHalfPlane.upperHalfPlaneSet ∧
              σ z ∈ UpperHalfPlane.upperHalfPlaneSet ∧
                SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) =
                  SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (σ z))} ∈
      𝓝 a :=
    hτ.eventually_analyticAt.and (hσ.eventually_analyticAt.and (hpτ.and (hpσ.and hJ)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨γ, hγ⟩ :=
    exists_modular_alignment Metric.isOpen_ball (convex_ball a ε).isPreconnected
      ⟨a, Metric.mem_ball_self hε⟩ (fun z hz => (hball hz).1) (fun z hz => (hball hz).2.1)
      (fun z hz => (hball hz).2.2.1) (fun z hz => (hball hz).2.2.2.1)
      (fun z hz => (hball hz).2.2.2.2)
  exact ⟨γ, Filter.eventually_of_mem (Metric.ball_mem_nhds a hε) (fun _ hz => hγ hz)⟩

def SpecialPeriods.ModularGermLift.extendLiftSection (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℍ) : ℂ → ℂ :=
  AnalyticRootCover.extendSection S V (fun x => (s x : ℂ))

@[simp]
theorem SpecialPeriods.ModularGermLift.extendLiftSection_apply (S : TopologicalSpace.Opens ℂ)
    (V : TopologicalSpace.Opens S) (s : V → ℍ) (x : V) :
    extendLiftSection S V s (AnalyticRootCover.ambientVal S V x) = (s x : ℂ) :=
  AnalyticRootCover.extendSection_apply S V (fun y => (s y : ℂ)) x

theorem SpecialPeriods.ModularGermLift.extendLiftSection_restrict_eventuallyEq
    (S : TopologicalSpace.Opens ℂ) {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : V → ℍ)
    (x : U) :
    extendLiftSection S U
        (fun y => s (Set.inclusion i.le y)) =ᶠ[𝓝 (AnalyticRootCover.ambientVal S U x)]
      extendLiftSection S V s :=
  AnalyticRootCover.extendSection_restrict_eventuallyEq S i (fun y => (s y : ℂ)) x

def SpecialPeriods.ModularGermLift.IsLiftSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (s : V → ℍ) : Prop :=
  ∀ x : V,
    AnalyticAt ℂ (extendLiftSection S V s) (AnalyticRootCover.ambientVal S V x) ∧
      SpecialPeriods.modularJ (s x) = F (AnalyticRootCover.ambientVal S V x)

def SpecialPeriods.ModularGermLift.liftLocalPredicate (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of S => ℍ)
    where
  pred {_} s := IsLiftSection S F s
  res {_ _} i s
    hs := by
    intro x
    refine ⟨?_, (hs (Set.inclusion i.le x)).2⟩
    exact
      (hs (Set.inclusion i.le x)).1.congr (extendLiftSection_restrict_eventuallyEq S i s x).symm
  locality {U} s
    hs := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hs x
    let y : V := ⟨(x : S), hxV⟩
    have hix : Set.inclusion i.le y = x := Subtype.ext rfl
    refine ⟨?_, ?_⟩
    · exact (hV y).1.congr (extendLiftSection_restrict_eventuallyEq S i s y)
    · have he :
        SpecialPeriods.modularJ (s (Set.inclusion i.le y)) =
          F (AnalyticRootCover.ambientVal S U x) :=
        (hV y).2
      rwa [hix] at he

def SpecialPeriods.ModularGermLift.liftPresheaf (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) :
    (TopCat.of S).Presheaf (Type 0) :=
  TopCat.subpresheafToTypes (liftLocalPredicate S F).toPrelocalPredicate

abbrev SpecialPeriods.ModularGermLift.LiftSection (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    (V : TopologicalSpace.Opens S) :=
  (liftPresheaf S F).obj (Opposite.op V)

theorem SpecialPeriods.ModularGermLift.liftSection_analytic (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (s : LiftSection S F V) (x : V) :
    AnalyticAt ℂ (extendLiftSection S V s.1) (AnalyticRootCover.ambientVal S V x) :=
  (s.2 x).1

theorem SpecialPeriods.ModularGermLift.liftSection_modular (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (s : LiftSection S F V) (x : V) :
    SpecialPeriods.modularJ (s.1 x) = F (AnalyticRootCover.ambientVal S V x) :=
  (s.2 x).2

@[simp]
theorem SpecialPeriods.ModularGermLift.liftPresheaf_map_apply (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {U V : TopologicalSpace.Opens S} (i : U ⟶ V) (s : LiftSection S F V) (x : U) :
    ((liftPresheaf S F).map i.op s).1 x = s.1 (Set.inclusion i.le x) :=
  rfl

theorem SpecialPeriods.ModularGermLift.LiftSection.analyticOnNhd_extend
    {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ} {V : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F V) :
    AnalyticOnNhd ℂ (SpecialPeriods.ModularGermLift.extendLiftSection S V s.1)
      (AnalyticRootCover.ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  exact SpecialPeriods.ModularGermLift.liftSection_analytic S F s x

theorem SpecialPeriods.ModularGermLift.LiftSection.mapsTo_extend {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {V : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F V) :
    Set.MapsTo (SpecialPeriods.ModularGermLift.extendLiftSection S V s.1)
      (AnalyticRootCover.ambientOpen S V) UpperHalfPlane.upperHalfPlaneSet := by
  intro z hz
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  rw [SpecialPeriods.ModularGermLift.extendLiftSection_apply]
  exact (s.1 x).im_pos

theorem SpecialPeriods.ModularGermLift.LiftSection.modular_eq {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {V : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F V) {z : ℂ}
    (hz : z ∈ AnalyticRootCover.ambientOpen S V) :
    SpecialPeriods.modularJ
        (UpperHalfPlane.ofComplex (SpecialPeriods.ModularGermLift.extendLiftSection S V s.1 z)) =
      F z := by
  obtain ⟨x, rfl⟩ := (AnalyticRootCover.mem_ambientOpen S V).mp hz
  rw [SpecialPeriods.ModularGermLift.extendLiftSection_apply, UpperHalfPlane.ofComplex_apply]
  exact SpecialPeriods.ModularGermLift.liftSection_modular S F s x

@[ext]
theorem SpecialPeriods.ModularGermLift.LiftSection.ext {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {V : TopologicalSpace.Opens S} {s t : SpecialPeriods.ModularGermLift.LiftSection S F V}
    (he : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext he)

def SpecialPeriods.ModularGermLift.liftSectionOfComplex (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ)
    {V : TopologicalSpace.Opens S} (r : ℂ → ℂ)
    (hr : AnalyticOnNhd ℂ r (AnalyticRootCover.ambientOpen S V))
    (hpos : Set.MapsTo r (AnalyticRootCover.ambientOpen S V) UpperHalfPlane.upperHalfPlaneSet)
    (hJ :
      Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (r z))) F
        (AnalyticRootCover.ambientOpen S V)) :
    LiftSection S F V := by
  refine
    ⟨fun x =>
      ⟨r (AnalyticRootCover.ambientVal S V x), hpos (AnalyticRootCover.ambientVal_mem S V x)⟩,
      fun x => ⟨?_, ?_⟩⟩
  · apply (hr _ (AnalyticRootCover.ambientVal_mem S V x)).congr
    filter_upwards [(AnalyticRootCover.ambientOpen S V).isOpen.mem_nhds
        (AnalyticRootCover.ambientVal_mem S V x)] with
      z hz
    exact (AnalyticRootCover.extension_agreement S V r hz).symm
  · simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos
          (hpos (AnalyticRootCover.ambientVal_mem S V x))] using
      hJ (AnalyticRootCover.ambientVal_mem S V x)

theorem SpecialPeriods.ModularGermLift.extend_liftSectionOfComplex_eqOn
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) {V : TopologicalSpace.Opens S} (r : ℂ → ℂ)
    (hr : AnalyticOnNhd ℂ r (AnalyticRootCover.ambientOpen S V))
    (hpos : Set.MapsTo r (AnalyticRootCover.ambientOpen S V) UpperHalfPlane.upperHalfPlaneSet)
    (hJ :
      Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (r z))) F
        (AnalyticRootCover.ambientOpen S V)) :
    Set.EqOn (extendLiftSection S V (liftSectionOfComplex S F r hr hpos hJ).1) r
      (AnalyticRootCover.ambientOpen S V) :=
  AnalyticRootCover.extension_agreement S V r

theorem SpecialPeriods.ModularGermLift.germ_eq_iff_eventuallyEq (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {U V : TopologicalSpace.Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : LiftSection S F U) (t : LiftSection S F V) :
    (liftPresheaf S F).germ U x hxU s = (liftPresheaf S F).germ V x hxV t ↔
      extendLiftSection S U s.1 =ᶠ[𝓝 (x : ℂ)] extendLiftSection S V t.1 := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hst⟩ := (liftPresheaf S F).germ_eq x hxU hxV s t h
    have hxA : (x : ℂ) ∈ AnalyticRootCover.ambientOpen S W :=
      AnalyticRootCover.ambientVal_mem S W ⟨x, hxW⟩
    filter_upwards [(AnalyticRootCover.ambientOpen S W).isOpen.mem_nhds hxA] with z hz
    obtain ⟨y, hyW, rfl⟩ := hz
    have hval := congrArg (fun r : LiftSection S F W => r.1 ⟨y, hyW⟩) hst
    rw [liftPresheaf_map_apply, liftPresheaf_map_apply] at hval
    calc
      extendLiftSection S U s.1 (y : ℂ) = (s.1 (Set.inclusion iU.le ⟨y, hyW⟩) : ℂ) :=
        extendLiftSection_apply S U s.1 (Set.inclusion iU.le ⟨y, hyW⟩)
      _ = (t.1 (Set.inclusion iV.le ⟨y, hyW⟩) : ℂ) := (congrArg (fun w : ℍ => (w : ℂ)) hval)
      _ = extendLiftSection S V t.1 (y : ℂ) :=
        (extendLiftSection_apply S V t.1 (Set.inclusion iV.le ⟨y, hyW⟩)).symm
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    let B : TopologicalSpace.Opens (TopCat.of S) :=
      TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ ⟨A, hAo⟩
    let W : TopologicalSpace.Opens (TopCat.of S) := (U ⊓ V) ⊓ B
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxA⟩
    let iU : W ⟶ U := CategoryTheory.homOfLE (inf_le_left.trans inf_le_left)
    let iV : W ⟶ V := CategoryTheory.homOfLE (inf_le_left.trans inf_le_right)
    apply (liftPresheaf S F).germ_ext W hxW iU iV
    apply Subtype.ext
    funext y
    rw [liftPresheaf_map_apply, liftPresheaf_map_apply]
    apply UpperHalfPlane.coe_injective
    calc
      (s.1 (Set.inclusion iU.le y) : ℂ) =
          extendLiftSection S U s.1 (AnalyticRootCover.ambientVal S W y) :=
        (extendLiftSection_apply S U s.1 (Set.inclusion iU.le y)).symm
      _ = extendLiftSection S V t.1 (AnalyticRootCover.ambientVal S W y) := (hA y.2.2)
      _ = (t.1 (Set.inclusion iV.le y) : ℂ) :=
        extendLiftSection_apply S V t.1 (Set.inclusion iV.le y)

theorem SpecialPeriods.exists_analytic_lift_through_power_chart {F G : ℂ → ℂ} {a b : ℂ} {m k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (m * k : ℕ)) (hm : 0 < m) (hk : 0 < k)
    (e : OpenPartialHomeomorph ℂ ℂ) (hb : b ∈ e.source) (he : e b = 0)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    (hG : ∀ z ∈ e.target, G (e.symm z) = z ^ m) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = b ∧
              Set.MapsTo τ (Metric.ball a r) e.source ∧
                (∀ z ∈ Metric.ball a r, G (τ z) = F z) ∧
                  analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞) := by
  obtain ⟨d, ha, hd, hdf, hdi, hp⟩ := exists_analytic_power_chart hF horder (Nat.mul_pos hm hk)
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source hb
  have hc : ContinuousAt (fun z : ℂ => d z ^ k) a := (hdf a ha).continuousAt.pow k
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, d z ^ k ∈ e.target := by
    apply hc.preimage_mem_nhds
    simpa only [hd, zero_pow hk.ne'] using e.open_target.mem_nhds ht
  have hsrc : ∀ᶠ z : ℂ in 𝓝 a, z ∈ d.source := d.open_source.mem_nhds ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hsrc.and hnear)
  refine ⟨r, hr, fun z => e.symm (d z ^ k), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hi _ (hball hz).2).comp (f := fun w : ℂ => d w ^ k) ((hdf z (hball hz).1).pow k)
  · change e.symm (d a ^ k) = b
    rw [hd, zero_pow hk.ne', ← he, e.left_inv hb]
  · intro z hz
    exact e.map_target (hball hz).2
  · intro z hz
    change G (e.symm (d z ^ k)) = F z
    rw [hG _ (hball hz).2, hp _ (hball hz).1, ← pow_mul, Nat.mul_comm k m]
  · calc
      analyticOrderAt (fun z => e.symm (d z ^ k) - b) a =
          analyticOrderAt (fun z : ℂ => e.symm (z ^ k) - b) (d a) :=
        analyticOrderAt_comp_of_deriv_ne_zero (f := fun z : ℂ => e.symm (z ^ k) - b) (hdf a ha)
          (analytic_chart_deriv_ne_zero d ha hdf hdi)
      _ = (k : ℕ∞) := by
        rw [hd]
        simpa only [one_mul] using
          analytic_chart_inverse_power_order e hb he hf hi 1 one_ne_zero k hk

theorem SpecialPeriods.exists_modularJ_lift_of_order_multiple_three {F : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (3 * k : ℕ)) (hk : 0 < k) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = rho ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                (∀ z ∈ Metric.ball a r, modularJ (UpperHalfPlane.ofComplex (τ z)) = F z) ∧
                  analyticOrderAt (fun z => τ z - rho) a = (k : ℕ∞) := by
  obtain ⟨e, hb, he, hU, hf, hi, _, hp⟩ := modularJ_rhoPoint_cubic_chart
  obtain ⟨r, hr, τ, hτ, hτa, hτU, hτj, hτord⟩ :=
    exists_analytic_lift_through_power_chart (G := fun w => modularJ (UpperHalfPlane.ofComplex w))
      hF horder (by decide : 0 < 3) hk e hb he hf hi hp
  exact ⟨r, hr, τ, hτ, hτa, fun z hz => hU (hτU hz), hτj, hτord⟩

theorem SpecialPeriods.exists_modularJ_lift_of_order_multiple_two {F : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (hk : 0 < k) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = Complex.I ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                (∀ z ∈ Metric.ball a r, modularJ (UpperHalfPlane.ofComplex (τ z)) = F z) ∧
                  analyticOrderAt (fun z => τ z - Complex.I) a = (k : ℕ∞) := by
  obtain ⟨e, hb, he, hU, hf, hi, _, hp⟩ := modularJ_I_quadratic_chart
  obtain ⟨r, hr, τ, hτ, hτa, hτU, hτj, hτord⟩ :=
    exists_analytic_lift_through_power_chart (G := fun w =>
      modularJ (UpperHalfPlane.ofComplex w) - 1728) (hF.sub analyticAt_const) horder
      (by decide : 0 < 2) hk e hb he hf hi hp
  refine ⟨r, hr, τ, hτ, hτa, fun z hz => hU (hτU hz), ?_, hτord⟩
  intro z hz
  exact sub_left_inj.mp (hτj z hz)

theorem SpecialPeriods.ModularGermLift.exists_regular_local_lift_at {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (b : ℍ) (hb : SpecialPeriods.modularJ b = F a) (h₀ : F a ≠ 0)
    (h₁ : F a ≠ 1728) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            τ a = (b : ℂ) ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                ∀ z ∈ Metric.ball a r,
                  SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z := by
  have hb₀ : SpecialPeriods.modularJ b ≠ 0 := hb ▸ h₀
  have hb₁ : SpecialPeriods.modularJ b ≠ 1728 := hb ▸ h₁
  let g : ℂ → ℂ := SpecialPeriods.modularLocalInverse b hb₀ hb₁
  let τ : ℂ → ℂ := fun z => g (F z)
  have hg : AnalyticAt ℂ g (F a) := by
    rw [← hb]
    exact SpecialPeriods.modularLocalInverse_analyticAt b hb₀ hb₁
  have hτ : AnalyticAt ℂ τ a := hg.comp hF
  have hτa : τ a = (b : ℂ) := by
    dsimp only [τ]
    rw [← hb]
    simpa only [UpperHalfPlane.ofComplex_apply] using
      (SpecialPeriods.modularLocalInverse_eventually_left_inverse b hb₀ hb₁).self_of_nhds
  have hU : ∀ᶠ z in 𝓝 a, τ z ∈ UpperHalfPlane.upperHalfPlaneSet := by
    apply hτ.continuousAt.preimage_mem_nhds
    rw [hτa]
    exact UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds b.im_pos
  have hinv : ∀ᶠ w in 𝓝 (F a), SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (g w)) = w := by
    rw [← hb]
    exact SpecialPeriods.modularLocalInverse_eventually_right_inverse b hb₀ hb₁
  have hj : ∀ᶠ z in 𝓝 a, SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z :=
    hF.continuousAt.tendsto.eventually hinv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hτ.eventually_analyticAt.and (hU.and hj))
  exact
    ⟨r, hr, τ, fun z hz => (hball hz).1, hτa, fun z hz => (hball hz).2.1, fun z hz =>
      (hball hz).2.2⟩

theorem SpecialPeriods.ModularGermLift.exists_local_lift {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (h₃ : F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ r : ℝ,
      0 < r ∧
        ∃ τ : ℂ → ℂ,
          AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
            Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
              ∀ z ∈ Metric.ball a r,
                SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z := by
  by_cases ha₀ : F a = 0
  · obtain ⟨k, hk⟩ := h₃ ha₀
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk₀
      exact
        (hF.analyticOrderAt_ne_zero.mpr ha₀)
          (by simpa only [hk₀, MulZeroClass.mul_zero, Nat.cast_zero] using hk)
    obtain ⟨r, hr, τ, hτ, -, hU, hj, -⟩ :=
      SpecialPeriods.exists_modularJ_lift_of_order_multiple_three hF hk hkpos
    exact ⟨r, hr, τ, hτ, hU, hj⟩
  · by_cases ha₁ : F a = 1728
    · obtain ⟨k, hk⟩ := h₂ ha₁
      have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hk₀
        have hshift : AnalyticAt ℂ (fun z => F z - 1728) a := hF.sub analyticAt_const
        have hn : analyticOrderAt (fun z => F z - 1728) a ≠ 0 :=
          hshift.analyticOrderAt_ne_zero.mpr (sub_eq_zero.mpr ha₁)
        exact hn (by simpa only [hk₀, MulZeroClass.mul_zero, Nat.cast_zero] using hk)
      obtain ⟨r, hr, τ, hτ, -, hU, hj, -⟩ :=
        SpecialPeriods.exists_modularJ_lift_of_order_multiple_two hF hk hkpos
      exact ⟨r, hr, τ, hτ, hU, hj⟩
    · obtain ⟨b, hb⟩ := SpecialPeriods.modularJ_surjective (F a)
      obtain ⟨r, hr, τ, hτ, -, hU, hj⟩ := exists_regular_local_lift_at hF b hb ha₀ ha₁
      exact ⟨r, hr, τ, hτ, hU, hj⟩

theorem SpecialPeriods.ModularGermLift.exists_local_lift_ball_subset {F : ℂ → ℂ} {a : ℂ}
    {S : Set ℂ} (hS : IsOpen S) (ha : a ∈ S) (hF : AnalyticAt ℂ F a)
    (h₃ : F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.ball a r ⊆ S ∧
          ∃ τ : ℂ → ℂ,
            AnalyticOnNhd ℂ τ (Metric.ball a r) ∧
              Set.MapsTo τ (Metric.ball a r) UpperHalfPlane.upperHalfPlaneSet ∧
                ∀ z ∈ Metric.ball a r,
                  SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z)) = F z := by
  obtain ⟨r, hr, τ, hτ, hU, hj⟩ := exists_local_lift hF h₃ h₂
  obtain ⟨s, hs, hsS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  have hsub : Metric.ball a (Min.min r s) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine
    ⟨Min.min r s, lt_min hr hs, (Metric.ball_subset_ball (min_le_right _ _)).trans hsS, τ,
      hτ.mono hsub, ?_, ?_⟩
  · exact hU.mono_left hsub
  · exact fun z hz => hj z (hsub hz)

def SpecialPeriods.ModularGermLift.LiftSection.smul {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : SpecialPeriods.ModularGermLift.LiftSection S F U)
    (γ : SL(2, ℤ)) : SpecialPeriods.ModularGermLift.LiftSection S F U :=
  SpecialPeriods.ModularGermLift.liftSectionOfComplex S F
    (fun z =>
      ((γ •
            UpperHalfPlane.ofComplex
              (SpecialPeriods.ModularGermLift.extendLiftSection S U s.1 z) :
          ℍ) :
        ℂ))
    (SpecialPeriods.ModularGermLift.analyticOnNhd_modular_smul γ s.analyticOnNhd_extend
      s.mapsTo_extend)
    (fun _ _ => (γ • UpperHalfPlane.ofComplex _).im_pos)
    (fun _ hz =>
      (SpecialPeriods.ModularGermLift.modularJ_modular_smul γ _).trans (s.modular_eq hz))

theorem SpecialPeriods.ModularGermLift.LiftSection.extend_smul_eqOn {S : TopologicalSpace.Opens ℂ}
    {F : ℂ → ℂ} {U : TopologicalSpace.Opens S}
    (s : SpecialPeriods.ModularGermLift.LiftSection S F U) (γ : SL(2, ℤ)) :
    Set.EqOn (SpecialPeriods.ModularGermLift.extendLiftSection S U (s.smul γ).1)
      (fun z =>
        ((γ •
              UpperHalfPlane.ofComplex
                (SpecialPeriods.ModularGermLift.extendLiftSection S U s.1 z) :
            ℍ) :
          ℂ))
      (AnalyticRootCover.ambientOpen S U) :=
  SpecialPeriods.ModularGermLift.extend_liftSectionOfComplex_eqOn S F _ _ _ _

theorem SpecialPeriods.ModularGermLift.germ_eq_smul {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U V : TopologicalSpace.Opens S} (x : S) (hxU : x ∈ U) (hxV : x ∈ V) (s : LiftSection S F U)
    (t : LiftSection S F V) :
    ∃ γ : SL(2, ℤ),
      (liftPresheaf S F).germ V x hxV t = (liftPresheaf S F).germ U x hxU (s.smul γ) := by
  have hxUA : (x : ℂ) ∈ AnalyticRootCover.ambientOpen S U :=
    (AnalyticRootCover.coe_mem_ambientOpen S U x).mpr hxU
  have hxVA : (x : ℂ) ∈ AnalyticRootCover.ambientOpen S V :=
    (AnalyticRootCover.coe_mem_ambientOpen S V x).mpr hxV
  have hJ :
    (fun z =>
        SpecialPeriods.modularJ
          (UpperHalfPlane.ofComplex (extendLiftSection S V t.1 z))) =ᶠ[𝓝 (x : ℂ)]
      (fun z =>
        SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (extendLiftSection S U s.1 z))) := by
    filter_upwards [(AnalyticRootCover.ambientOpen S U).isOpen.mem_nhds hxUA,
      (AnalyticRootCover.ambientOpen S V).isOpen.mem_nhds hxVA] with z hzU hzV
    exact (t.modular_eq hzV).trans (s.modular_eq hzU).symm
  obtain ⟨γ, hγ⟩ :=
    exists_modular_alignment_germ (t.analyticOnNhd_extend _ hxVA) (s.analyticOnNhd_extend _ hxUA)
      (t.mapsTo_extend hxVA) (s.mapsTo_extend hxUA) hJ
  refine ⟨γ, (germ_eq_iff_eventuallyEq S F x hxV hxU t (s.smul γ)).mpr ?_⟩
  filter_upwards [hγ, (AnalyticRootCover.ambientOpen S U).isOpen.mem_nhds hxUA] with z hz hzU
  exact hz.trans (s.extend_smul_eqOn γ hzU).symm

theorem SpecialPeriods.ModularGermLift.germ_injective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S}
    (hU : IsPreconnected (AnalyticRootCover.ambientOpen S U : Set ℂ)) (x : S) (hx : x ∈ U) :
    Function.Injective ((liftPresheaf S F).germ U x hx) := by
  intro s t hst
  have he :=
    AnalyticRootCover.eqOn_of_eventuallyEq (LiftSection.analyticOnNhd_extend s)
      (LiftSection.analyticOnNhd_extend t) hU
      ((AnalyticRootCover.coe_mem_ambientOpen S U x).mpr hx)
      ((germ_eq_iff_eventuallyEq S F x hx hx s t).mp hst)
  apply LiftSection.ext
  intro y
  apply UpperHalfPlane.coe_injective
  simpa only [extendLiftSection_apply] using he (AnalyticRootCover.ambientVal_mem S U y)

theorem SpecialPeriods.ModularGermLift.germ_surjective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S} (s : LiftSection S F U) (x : S) (hx : x ∈ U) :
    Function.Surjective ((liftPresheaf S F).germ U x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (liftPresheaf S F).exists_germ_eq g
  obtain ⟨γ, hγ⟩ := germ_eq_smul x hx hxV s t
  exact ⟨s.smul γ, hγ.symm.trans ht⟩

theorem SpecialPeriods.ModularGermLift.germ_bijective {S : TopologicalSpace.Opens ℂ} {F : ℂ → ℂ}
    {U : TopologicalSpace.Opens S}
    (hU : IsPreconnected (AnalyticRootCover.ambientOpen S U : Set ℂ)) (s : LiftSection S F U)
    (x : S) (hx : x ∈ U) : Function.Bijective ((liftPresheaf S F).germ U x hx) :=
  ⟨germ_injective hU x hx, germ_surjective s x hx⟩

theorem SpecialPeriods.ModularGermLift.exists_lift_neighborhood (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (x : S) :
    ∃ U : TopologicalSpace.Opens S,
      x ∈ U ∧
        IsPreconnected (AnalyticRootCover.ambientOpen S U : Set ℂ) ∧
          Nonempty (LiftSection S F U) := by
  obtain ⟨r, hr, hball, τ, hτ, hpos, hJ⟩ :=
    exists_local_lift_ball_subset S.isOpen x.2 (hF x x.2) (h₃ x x.2) (h₂ x x.2)
  let A : TopologicalSpace.Opens ℂ := ⟨Metric.ball (x : ℂ) r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens S :=
    TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : AnalyticRootCover.ambientOpen S U = A :=
    AnalyticRootCover.ambientOpen_comap_of_subset S A hball
  refine ⟨U, Metric.mem_ball_self hr, ?_, ?_⟩
  · rw [hUA]
    exact (convex_ball (x : ℂ) r).isPreconnected
  · have hτU : AnalyticOnNhd ℂ τ (AnalyticRootCover.ambientOpen S U) := by rwa [hUA]
    have hposU :
      Set.MapsTo τ (AnalyticRootCover.ambientOpen S U) UpperHalfPlane.upperHalfPlaneSet := by
      rwa [hUA]
    refine ⟨liftSectionOfComplex S F τ hτU hposU ?_⟩
    intro z hz
    apply hJ z
    rwa [hUA] at hz

theorem SpecialPeriods.ModularGermLift.liftPresheaf_locally_bijective
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∀ x : S,
      ∃ U : TopologicalSpace.Opens S,
        x ∈ U ∧ ∀ y (hy : y ∈ U), Function.Bijective ((liftPresheaf S F).germ U y hy) := by
  intro x
  obtain ⟨U, hx, hU, ⟨s⟩⟩ := exists_lift_neighborhood S F hF h₃ h₂ x
  exact ⟨U, hx, fun y hy => germ_bijective hU s y hy⟩

theorem SpecialPeriods.ModularGermLift.exists_global_liftSection_with_germ
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (x : S) (g : (liftPresheaf S F).stalk x) :
    ∃ s : LiftSection S F ⊤, (liftPresheaf S F).germ ⊤ x trivial s = g := by
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  exact
    AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
      (liftLocalPredicate S F) (liftPresheaf_locally_bijective S F hF h₃ h₂) x g

theorem SpecialPeriods.ModularGermLift.exists_analytic_modularJ_lift_on_with_germ
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    {U : TopologicalSpace.Opens S} (x : S) (hx : x ∈ U) (s : LiftSection S F U) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ S ∧
        Set.MapsTo τ S UpperHalfPlane.upperHalfPlaneSet ∧
          Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) F S ∧
            τ =ᶠ[𝓝 (x : ℂ)] extendLiftSection S U s.1 := by
  obtain ⟨t, ht⟩ :=
    exists_global_liftSection_with_germ S F hF h₃ h₂ x ((liftPresheaf S F).germ U x hx s)
  refine ⟨extendLiftSection S ⊤ t.1, ?_, ?_, ?_, ?_⟩
  · simpa only [AnalyticRootCover.ambientOpen_top] using t.analyticOnNhd_extend
  · simpa only [AnalyticRootCover.ambientOpen_top] using t.mapsTo_extend
  · intro z hz
    apply LiftSection.modular_eq (S := S) (F := F) (V := ⊤) t
    rwa [AnalyticRootCover.ambientOpen_top]
  · exact (germ_eq_iff_eventuallyEq S F (U := ⊤) (V := U) x trivial hx t s).mp ht

theorem SpecialPeriods.ModularGermLift.exists_liftSection_of_germ (S : TopologicalSpace.Opens ℂ)
    (F : ℂ → ℂ) {a : ℂ} (ha : a ∈ S) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ a) (hpos : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 a] F) :
    ∃ (U : TopologicalSpace.Opens S) (_hx : (⟨a, ha⟩ : S) ∈ U) (s : LiftSection S F U),
      extendLiftSection S U s.1 =ᶠ[𝓝 a] τ₀ := by
  have hposnear : ∀ᶠ z in 𝓝 a, τ₀ z ∈ UpperHalfPlane.upperHalfPlaneSet :=
    hτ₀.continuousAt.preimage_mem_nhds (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hpos)
  have hSnear : ∀ᶠ z in 𝓝 a, z ∈ S := S.isOpen.mem_nhds ha
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (hSnear.and (hτ₀.eventually_analyticAt.and (hposnear.and hJ₀)))
  let A : TopologicalSpace.Opens ℂ := ⟨Metric.ball a r, Metric.isOpen_ball⟩
  let U : TopologicalSpace.Opens S :=
    TopologicalSpace.Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : AnalyticRootCover.ambientOpen S U = A :=
    AnalyticRootCover.ambientOpen_comap_of_subset S A (fun _ hz => (hball hz).1)
  have hτU : AnalyticOnNhd ℂ τ₀ (AnalyticRootCover.ambientOpen S U) := by
    rw [hUA]
    exact fun z hz => (hball hz).2.1
  have hposU :
    Set.MapsTo τ₀ (AnalyticRootCover.ambientOpen S U) UpperHalfPlane.upperHalfPlaneSet := by
    rw [hUA]
    exact fun z hz => (hball hz).2.2.1
  have hJU :
    Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) F
      (AnalyticRootCover.ambientOpen S U) := by
    rw [hUA]
    exact fun z hz => (hball hz).2.2.2
  let s : LiftSection S F U := liftSectionOfComplex S F τ₀ hτU hposU hJU
  refine ⟨U, Metric.mem_ball_self hr, s, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
  apply extend_liftSectionOfComplex_eqOn S F τ₀ hτU hposU hJU
  rwa [hUA]

theorem SpecialPeriods.ModularGermLift.exists_analytic_modularJ_lift_extending
    (S : TopologicalSpace.Opens ℂ) (F : ℂ → ℂ) [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 → ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    {a : ℂ} (ha : a ∈ S) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ a) (hpos : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 a] F) :
    ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ S ∧
        Set.MapsTo τ S UpperHalfPlane.upperHalfPlaneSet ∧
          Set.EqOn (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ z))) F S ∧
            τ =ᶠ[𝓝 a] τ₀ := by
  obtain ⟨U, hx, s, hs⟩ := exists_liftSection_of_germ S F ha τ₀ hτ₀ hpos hJ₀
  obtain ⟨τ, hτ, hτpos, hJ, heq⟩ :=
    exists_analytic_modularJ_lift_on_with_germ S F hF h₃ h₂ ⟨a, ha⟩ hx s
  exact ⟨τ, hτ, hτpos, hJ, heq.trans hs⟩

def SpecialPeriods.ModularGermLift.upperHalfPlaneLift (g : ℂ → ℂ) : ℍ → ℍ := fun z =>
  UpperHalfPlane.ofComplex (g (z : ℂ))

theorem SpecialPeriods.ModularGermLift.upperHalfPlaneLift_holomorphic {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g UpperHalfPlane.upperHalfPlaneSet)
    (hpos : Set.MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (upperHalfPlaneLift g) := by
  intro z
  exact
    (UpperHalfPlane.contMDiffAt_ofComplex (hpos z.im_pos)).comp z
      ((hg z z.im_pos).contDiffAt.contMDiffAt.comp z (UpperHalfPlane.contMDiff_coe z))

theorem SpecialPeriods.ModularGermLift.upperHalfPlaneLift_eventuallyEq {g : ℂ → ℂ}
    (hpos : Set.MapsTo g UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.upperHalfPlaneSet)
    (a : ℍ) :
    (fun z => (upperHalfPlaneLift g (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 (a : ℂ)] g := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos] with z hz
  change (UpperHalfPlane.ofComplex (g (UpperHalfPlane.ofComplex z : ℂ)) : ℂ) = g z
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
    UpperHalfPlane.ofComplex_apply_of_im_pos (hpos hz)]

theorem SpecialPeriods.ModularGermLift.upperHalfPlane_critical_orders {F : ℍ → ℂ}
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ)) :
    (∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
        (F ∘ UpperHalfPlane.ofComplex) a = 0 →
          ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) a = (3 * k : ℕ)) ∧
      (∀ a ∈ UpperHalfPlane.upperHalfPlaneSet,
        (F ∘ UpperHalfPlane.ofComplex) a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => (F ∘ UpperHalfPlane.ofComplex) z - 1728) a = (2 * k : ℕ)) :=
  by
  constructor
  · intro a ha hFa
    apply h₃ ⟨a, ha⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hFa
  · intro a ha hFa
    apply h₂ ⟨a, ha⟩
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos ha] using hFa

theorem SpecialPeriods.ModularGermLift.exists_holomorphic_modularJ_lift_upperHalfPlane_extending
    (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (a : ℍ) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ (a : ℂ)) (hpos₀ : 0 < (τ₀ a).im)
    (hJ₀ :
      (fun z => SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (τ₀ z))) =ᶠ[𝓝 (a : ℂ)]
        F ∘ UpperHalfPlane.ofComplex) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
        (∀ z : ℍ, SpecialPeriods.modularJ (τ z) = F z) ∧
          (fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 (a : ℂ)] τ₀ := by
  have hF' : AnalyticOnNhd ℂ (F ∘ UpperHalfPlane.ofComplex) UpperHalfPlane.upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hF).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  obtain ⟨h₃', h₂'⟩ := upperHalfPlane_critical_orders h₃ h₂
  obtain ⟨g, hg, hpos, hJ, hg₀⟩ :=
    exists_analytic_modularJ_lift_extending AnalyticRootCover.upperHalfPlaneOpen
      (F ∘ UpperHalfPlane.ofComplex) hF' h₃' h₂' a.im_pos τ₀ hτ₀ hpos₀ hJ₀
  refine
    ⟨upperHalfPlaneLift g, upperHalfPlaneLift_holomorphic hg hpos, ?_,
      (upperHalfPlaneLift_eventuallyEq hpos a).trans hg₀⟩
  intro z
  simpa only [upperHalfPlaneLift, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    hJ z.im_pos

private theorem SpecialPeriods.TauCusp.exists_upperHalfPlane_qParam_small_mo1973_17412 (w : ℝ)
    (hw : 0 < w) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ a : ℍ, ‖Function.Periodic.qParam w (a : ℂ)‖ < r := by
  obtain ⟨s, hs⟩ := logBase_set_nonempty r hr
  have hsNorm : ‖CuspUniformization.exponential s‖ < r :=
    (SpecialPeriods.CuspFamily.mem_logBase r s).mp hs
  have hsIm : 0 < s.im := upperHalfPlane_of_exponential_norm_lt_one (hsNorm.trans hr1)
  have hwsIm : 0 < ((w : ℂ) * s).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul,
      add_zero] using mul_pos hw hsIm
  refine ⟨⟨(w : ℂ) * s, hwsIm⟩, ?_⟩
  change ‖Function.Periodic.qParam w ((w : ℂ) * s)‖ < r
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  rw [qParam_eq_exponential_div, mul_div_cancel_left₀ s hwC]
  exact hsNorm

private theorem SpecialPeriods.TauCusp.isOpen_qParam_norm_lt_mo1973_17413 (w r : ℝ) :
    IsOpen {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  isOpen_lt (Function.Periodic.continuous_qParam (h := w)).norm continuous_const

theorem SpecialPeriods.TauCusp.exists_global_normalized_lift_of_meromorphic_cusp (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (w : ℝ) (hw : 0 < w) (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0)
    (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) {c : ℂ}
    (hc : Filter.Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam w (z : ℂ)‖ < r₀ →
          F z = Fc (Function.Periodic.qParam w (z : ℂ))) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
        (∀ z : ℍ, SpecialPeriods.modularJ (τ z) = F z) ∧
          ∃ r > 0,
            r < r₀ ∧
              r < 1 ∧
                ∃ h : ℂ → ℂ,
                  AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                    h 0 = CuspUniformization.logarithm (1 / c) ∧
                      ∀ z : ℍ,
                        ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
                          (τ z : ℂ) = correctedLogarithmWidth w h (z : ℂ) := by
  obtain ⟨a, ha, ha0, hac, rF, hrF, hfactor⟩ := simplePole_factorization_of_tendsto hFc horder hc
  obtain ⟨r, hr, hrr, hr1, h, hh, hh0, _, hlift⟩ :=
    exists_simplePole_logarithmic_lift_width w hw ha ha0 (R := 1) (r₀ := Min.min r₀ rF)
      zero_lt_one (lt_min hr₀ hrF)
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrr (min_le_left r₀ rF)
  have hrrF : r < rF := lt_of_lt_of_le hrr (min_le_right r₀ rF)
  have hlocalJ (s : ℂ) (hs : ‖Function.Periodic.qParam w s‖ < r) :
    SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s)) =
      F (UpperHalfPlane.ofComplex s) := by
    have hspos : 0 < s.im := upperHalfPlane_of_qParam_norm_lt_one w hw (hs.trans hr1)
    have hqt : Function.Periodic.qParam w s ∈ Metric.ball (0 : ℂ) rF := by
      simpa only [Metric.mem_ball, dist_zero_right] using hs.trans hrrF
    have hfactorq :=
      hfactor (Function.Periodic.qParam w s) hqt (Function.Periodic.qParam_ne_zero (h := w) s)
    have hsourceq : F (UpperHalfPlane.ofComplex s) = Fc (Function.Periodic.qParam w s) := by
      have he :=
        hsource (UpperHalfPlane.ofComplex s)
          (by simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hspos] using hs.trans hrr₀)
      simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hspos] using he
    exact (hlift s hs).2.2.2.trans (hfactorq.symm.trans hsourceq.symm)
  obtain ⟨z₀, hz₀⟩ := exists_upperHalfPlane_qParam_small_mo1973_17412 w hw r hr hr1
  have hJgerm :
    (fun s =>
        SpecialPeriods.modularJ
          (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s))) =ᶠ[𝓝 (z₀ : ℂ)]
      F ∘ UpperHalfPlane.ofComplex := by
    filter_upwards [(isOpen_qParam_norm_lt_mo1973_17413 w r).mem_nhds hz₀] with s hs
    exact hlocalJ s hs
  obtain ⟨τ, hτ, hJ, hgerm⟩ :=
    SpecialPeriods.ModularGermLift.exists_holomorphic_modularJ_lift_upperHalfPlane_extending F hF
      h₃ h₂ z₀ (correctedLogarithmWidth w h) (correctedLogarithmWidth_analyticAt w hh hz₀)
      (hlift z₀ hz₀).2.1 hJgerm
  have hformula := native_eqOn_correctedLogarithmWidth_of_eventuallyEq w hw hr hr1 hh hτ hz₀ hgerm
  refine ⟨τ, hτ, hJ, r, hr, hrr₀, hr1, h, hh, ?_, ?_⟩
  · simpa only [hac] using hh0
  · intro z hz
    have hzEq :
      (τ (UpperHalfPlane.ofComplex (z : ℂ)) : ℂ) = correctedLogarithmWidth w h (z : ℂ) :=
      hformula hz
    simpa only [UpperHalfPlane.ofComplex_apply] using hzEq

private theorem SpecialPeriods.TauCusp.exists_simplePole_normalized_limit_mo1973_17415
    {Fc : ℂ → ℂ} (hFc : MeromorphicAt Fc 0) (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨a, ha, ha0, r, hr, hball⟩ := simplePole_factorization hFc horder
  refine ⟨a 0, ha0, ?_⟩
  have heq : (fun t => t * Fc t) =ᶠ[𝓝[≠] (0 : ℂ)] a := by
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ Metric.ball 0 r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [hball t ht ht0]
    field_simp [ht0]
  exact ha.continuousAt.continuousWithinAt.congr' heq.symm

theorem SpecialPeriods.TauCusp.exists_global_normalized_lift_of_simplePole_cusp (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (w : ℝ) (hw : 0 < w) (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0)
    (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam w (z : ℂ)‖ < r₀ →
          F z = Fc (Function.Periodic.qParam w (z : ℂ))) :
    ∃ c : ℂ,
      c ≠ 0 ∧
        Filter.Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c) ∧
          ∃ τ : ℍ → ℍ,
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
              (∀ z : ℍ, SpecialPeriods.modularJ (τ z) = F z) ∧
                ∃ r > 0,
                  r < r₀ ∧
                    r < 1 ∧
                      ∃ h : ℂ → ℂ,
                        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                          h 0 = CuspUniformization.logarithm (1 / c) ∧
                            ∀ z : ℍ,
                              ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
                                (τ z : ℂ) = correctedLogarithmWidth w h (z : ℂ) := by
  obtain ⟨c, hc0, hc⟩ := exists_simplePole_normalized_limit_mo1973_17415 hFc horder
  exact
    ⟨c, hc0, hc,
      exists_global_normalized_lift_of_meromorphic_cusp F hF h₃ h₂ w hw Fc hFc horder hc hr₀
        hsource⟩

theorem SpecialPeriods.exists_covariant_tau_of_triangle_source (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
          (Triangle.centerTwo : ℂ) =
        4)
    (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0) (hFcorder : meromorphicOrderAt Fc 0 = (-1 : ℤ))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r₀ →
          F z = Fc (Function.Periodic.qParam Triangle.width (z : ℂ))) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧
        (∀ z : ℍ, modularJ (τ z) = F z) ∧
          TauCovariant τ ∧
            τ Triangle.centerOne = rhoPoint ∧
              τ Triangle.centerTwo = UpperHalfPlane.I ∧
                ∃ r > 0,
                  r < r₀ ∧
                    r < 1 ∧
                      ∃ h : ℂ → ℂ,
                        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                          ∀ z : ℍ,
                            ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r →
                              (τ z : ℂ) =
                                TauCusp.correctedLogarithmWidth Triangle.width h (z : ℂ) := by
  have hFa : F Triangle.centerOne = 0 := by
    have hh :=
      (analyticOrderAt_ne_zero.mp
          (show analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) ≠ 0 by
            rw [horder₁]; norm_num)).2
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh
  have hFb : F Triangle.centerTwo = 1728 := by
    have hh :=
      (analyticOrderAt_ne_zero.mp
          (show
            analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
                (Triangle.centerTwo : ℂ) ≠
              0
            by rw [horder₂]; norm_num)).2
    exact sub_eq_zero.mp (by simpa only [UpperHalfPlane.ofComplex_apply] using hh)
  obtain ⟨_, _, _, τ, hτ, hJ, r, hr, hrr₀, hr1, h, hh, _, hformula⟩ :=
    TauCusp.exists_global_normalized_lift_of_simplePole_cusp F hF h₃ h₂ Triangle.width
      Triangle.width_pos Fc hFc hFcorder hr₀ hsource
  have hC := tau_cusp_monodromy_of_formula hτ hr hformula
  have hCtr :
    Matrix.trace (ModularGroup.T⁻¹).val = 2 ∨ Matrix.trace (ModularGroup.T⁻¹).val = -2 := by
    left
    rw [modularSL_trace_inv]
    norm_num [Matrix.trace_fin_two, ModularGroup.T]
  obtain ⟨γ, hcov, hγa, hγb⟩ :=
    exists_normalized_covariant_modular_translate F hτ hJ hFa hFb hF₁ hF₂ horder₁ horder₂
      ModularGroup.T⁻¹ hCtr hC
  have hab : τ Triangle.centerOne ≠ τ Triangle.centerTwo := by
    intro he
    have hj := congrArg modularJ he
    rw [hJ, hJ, hFa, hFb] at hj
    norm_num at hj
  have hcomm :=
    modular_translate_commutes_Tinv_of_cusp_covariance γ hC hcov Triangle.centerOne
      Triangle.centerTwo hab
  obtain ⟨n, hn⟩ := modularSL_integer_translation_coe_of_commutes_T_inv_action γ hcomm
  refine
    ⟨fun z => γ • τ z, (modularSL_holomorphic γ).comp hτ,
      (fun z => (modularJ_SL_invariant γ (τ z)).trans (hJ z)), hcov, hγa, hγb, r, hr, hrr₀, hr1,
      fun q => h q + (n : ℂ), hh.add analyticOnNhd_const, ?_⟩
  intro z hz
  rw [hn, hformula z hz]
  simp only [TauCusp.correctedLogarithmWidth]
  ring

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.exists_tau_of_normalized_sphere_equivalence
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧
        (∀ z : ℍ,
            SpecialPeriods.modularJ (τ z) = SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z) ∧
          SpecialPeriods.TauCovariant τ ∧
            τ SpecialPeriods.Triangle.centerOne = SpecialPeriods.rhoPoint ∧
              τ SpecialPeriods.Triangle.centerTwo = UpperHalfPlane.I ∧
                ∃ r > 0,
                  r < 1 ∧
                    ∃ h : ℂ → ℂ,
                      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                        ∀ z : ℍ,
                          ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r →
                            (τ z : ℂ) =
                              SpecialPeriods.TauCusp.correctedLogarithmWidth
                                SpecialPeriods.Triangle.width h (z : ℂ) := by
  have h₃ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z = 0 →
        ∃ k : ℕ,
          analyticOrderAt
              (SpecialPeriods.MuTorsor.SourceOrders.sourceJ π ∘ UpperHalfPlane.ofComplex)
              (z : ℂ) =
            (3 * k : ℕ) := by
    intro z hz
    exact
      ⟨1, by
        simpa using SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_of_eq_zero π hπ h₀ z hz⟩
  have h₂ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z = 1728 →
        ∃ k : ℕ,
          analyticOrderAt
              (fun w =>
                SpecialPeriods.MuTorsor.SourceOrders.sourceJ π (UpperHalfPlane.ofComplex w) -
                  1728)
              (z : ℂ) =
            (2 * k : ℕ) := by
    intro z hz
    exact
      ⟨2, by
        simpa using
          SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_of_eq π hπ h₁ z hz⟩
  have hG₁ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π
          (SpecialPeriods.Triangle.generatorOneSL • z) =
        SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z := by
    intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] using
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ_invariant π SpecialPeriods.triangleGenerator₁ z
  have hG₂ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π
          (SpecialPeriods.Triangle.generatorTwoSL • z) =
        SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z := by
    intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply] using
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ_invariant π SpecialPeriods.triangleGenerator₂ z
  obtain ⟨r₀, hr₀, hsource⟩ := exists_cusp_formula_radius π hπ
  obtain ⟨τ, hτ, hJ, hcov, ha, hb, r, hr, _, hr1, h, hh, hformula⟩ :=
    SpecialPeriods.exists_covariant_tau_of_triangle_source
      (SpecialPeriods.MuTorsor.SourceOrders.sourceJ π)
      ((SpecialPeriods.MuTorsor.SourceOrders.sourceJ_holomorphic π hπ).mdifferentiable (by simp))
      h₃ h₂ hG₁ hG₂ (SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_centerOne π hπ h₀)
      (SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_centerTwo π hπ h₁)
      (meromorphicCuspJ π) (meromorphicCuspJ_meromorphicAt π hπ) (meromorphicCuspJ_order π hπ) hr₀
      hsource
  exact ⟨τ, hτ, hJ, hcov, ha, hb, r, hr, hr1, h, hh, hformula⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.TriangleSource.tauOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ℍ → ℍ :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.tauOfSphere_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (tauOfSphere π hπ h₀ h₁) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.tauOfSphere_modular
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    SpecialPeriods.modularJ (tauOfSphere π hπ h₀ h₁ z) =
      1728 * SpecialPeriods.BetaTorsor.finiteProjection π z :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.1 z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.tauOfSphere_covariant
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    SpecialPeriods.TauCovariant (tauOfSphere π hπ h₀ h₁) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.tauOfSphere_cusp
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ r > 0,
      r < 1 ∧
        ∃ h : ℂ → ℂ,
          AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
            ∀ z : ℍ,
              ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r →
                (tauOfSphere π hπ h₀ h₁ z : ℂ) =
                  SpecialPeriods.TauCusp.correctedLogarithmWidth SpecialPeriods.Triangle.width h
                    (z : ℂ) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.2.2.2

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.TriangleSource.cuspCorrectionUnit (h : ℂ → ℂ) (q : ℂ) : ℂ :=
  CuspUniformization.exponential (h q)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.cuspCorrectionUnit_analyticOnNhd {h : ℂ → ℂ} {r : ℝ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (cuspCorrectionUnit h) (Metric.ball 0 r) := by
  intro q hq
  exact CuspUniformization.exponential_holomorphic.contDiffAt.analyticAt.comp (hh q hq)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.TriangleSource.cuspCorrectionUnit_ne_zero (h : ℂ → ℂ) (q : ℂ) :
    cuspCorrectionUnit h q ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.TriangleSource.tauOfSphere_cusp_unit
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ r > 0,
      ∃ u : ℂ → ℂ,
        AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
          u 0 ≠ 0 ∧
            ∀ z : ℍ,
              ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r →
                Function.Periodic.qParam 1 (tauOfSphere π hπ h₀ h₁ z : ℂ) =
                  Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ) *
                    u (Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)) := by
  obtain ⟨r, hr, _, h, hh, hformula⟩ := tauOfSphere_cusp π hπ h₀ h₁
  refine
    ⟨r, hr, cuspCorrectionUnit h, cuspCorrectionUnit_analyticOnNhd hh,
      cuspCorrectionUnit_ne_zero h 0, ?_⟩
  intro z hz
  rw [← SpecialPeriods.TauCusp.exponential_eq_qParam_one, hformula z hz]
  exact
    SpecialPeriods.TauCusp.correctedLogarithmWidth_exponential SpecialPeriods.Triangle.width h z

def SpecialPeriods.MuTorsor.affinePermutation {B : Type*} (e : Equiv.Perm B) (a : B → ℂˣ)
    (b : B → ℂ) : Equiv.Perm (B × ℂ)
    where
  toFun p := (e p.1, (a p.1 : ℂ) * p.2 + b p.1)
  invFun p := (e.symm p.1, (a (e.symm p.1) : ℂ)⁻¹ * (p.2 - b (e.symm p.1)))
  left_inv := by
    rintro ⟨z, u⟩
    apply Prod.ext
    · exact e.symm_apply_apply z
    · simp only [Equiv.symm_apply_apply]
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (a z).ne_zero, one_mul]
  right_inv := by
    rintro ⟨z, u⟩
    apply Prod.ext
    · exact e.apply_symm_apply z
    · dsimp
      rw [← mul_assoc, mul_inv_cancel₀ (a (e.symm z)).ne_zero, one_mul, sub_add_cancel]

def SpecialPeriods.MuTorsor.generatorOneScale (τ : ℍ → ℍ) (z : ℍ) : ℂˣ :=
  Units.mk0 (-1 / (τ z : ℂ)) (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (τ z).ne_zero)

def SpecialPeriods.MuTorsor.generatorTwoScale (τ : ℍ → ℍ) (z : ℍ) : ℂˣ :=
  Units.mk0 (1 / (τ z : ℂ)) (div_ne_zero one_ne_zero (τ z).ne_zero)

def SpecialPeriods.MuTorsor.generatorOneShift (τ : ℍ → ℍ) (z : ℍ) : ℂ :=
  1 / (τ z : ℂ)

def SpecialPeriods.MuTorsor.generatorTwoShift (_z : ℍ) : ℂ :=
  1

@[simp]
theorem SpecialPeriods.MuTorsor.generatorOneScale_val (τ : ℍ → ℍ) (z : ℍ) :
    (generatorOneScale τ z : ℂ) = -1 / (τ z : ℂ) :=
  rfl

@[simp]
theorem SpecialPeriods.MuTorsor.generatorTwoScale_val (τ : ℍ → ℍ) (z : ℍ) :
    (generatorTwoScale τ z : ℂ) = 1 / (τ z : ℂ) :=
  rfl

def SpecialPeriods.MuTorsor.generatorOne (τ : ℍ → ℍ) : Equiv.Perm (ℍ × ℂ) :=
  affinePermutation SpecialPeriods.Triangle.generatorOnePerm (generatorOneScale τ)
    (generatorOneShift τ)

def SpecialPeriods.MuTorsor.generatorTwo (τ : ℍ → ℍ) : Equiv.Perm (ℍ × ℂ) :=
  affinePermutation SpecialPeriods.Triangle.generatorTwoPerm (generatorTwoScale τ)
    generatorTwoShift

@[simp]
theorem SpecialPeriods.MuTorsor.generatorOne_apply (τ : ℍ → ℍ) (z : ℍ) (u : ℂ) :
    generatorOne τ (z, u) = (SpecialPeriods.Triangle.generatorOneSL • z, (1 - u) / (τ z : ℂ)) := by
  apply Prod.ext
  · rfl
  · change (-1 / (τ z : ℂ)) * u + 1 / (τ z : ℂ) = _
    ring

@[simp]
theorem SpecialPeriods.MuTorsor.generatorTwo_apply (τ : ℍ → ℍ) (z : ℍ) (u : ℂ) :
    generatorTwo τ (z, u) = (SpecialPeriods.Triangle.generatorTwoSL • z, 1 + u / (τ z : ℂ)) := by
  apply Prod.ext
  · rfl
  · change (1 / (τ z : ℂ)) * u + 1 = _
    ring

theorem SpecialPeriods.MuTorsor.generatorOne_cube {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) : generatorOne τ ^ 3 = 1 := by
  apply Equiv.ext
  rintro ⟨z, u⟩
  change generatorOne τ (generatorOne τ (generatorOne τ (z, u))) = (z, u)
  simp only [generatorOne_apply]
  apply Prod.ext
  · exact congrArg (fun e : Equiv.Perm ℍ => e z) SpecialPeriods.Triangle.generatorOnePerm_cube
  · dsimp
    rw [hτ.1 (SpecialPeriods.Triangle.generatorOneSL • z), hτ.1 z]
    have ht : (τ z : ℂ) ≠ 0 := (τ z).ne_zero
    have ht1 : (τ z : ℂ) - 1 ≠ 0 :=
      sub_ne_zero.mpr (by simpa only [Int.cast_one] using (τ z).ne_intCast 1)
    field_simp [ht, ht1]
    ring

theorem SpecialPeriods.MuTorsor.generatorTwo_fourth {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) : generatorTwo τ ^ 4 = 1 := by
  apply Equiv.ext
  rintro ⟨z, u⟩
  change generatorTwo τ (generatorTwo τ (generatorTwo τ (generatorTwo τ (z, u)))) = (z, u)
  simp only [generatorTwo_apply]
  apply Prod.ext
  · exact congrArg (fun e : Equiv.Perm ℍ => e z) SpecialPeriods.Triangle.generatorTwoPerm_fourth
  · dsimp
    rw [hτ.2
        (SpecialPeriods.Triangle.generatorTwoSL • (SpecialPeriods.Triangle.generatorTwoSL • z)),
      hτ.2 (SpecialPeriods.Triangle.generatorTwoSL • z), hτ.2 z]
    field_simp [(τ z).ne_zero]
    ring

def SpecialPeriods.MuTorsor.representation {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ) :
    SpecialPeriods.TriangleGroup →* Equiv.Perm (ℍ × ℂ) :=
  SpecialPeriods.triangleLift (generatorOne τ) (generatorTwo τ) (generatorOne_cube hτ)
    (generatorTwo_fourth hτ)

@[simp]
theorem SpecialPeriods.MuTorsor.representation_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) :
    representation hτ SpecialPeriods.triangleGenerator₁ = generatorOne τ :=
  SpecialPeriods.triangleLift_generator₁ ..

@[simp]
theorem SpecialPeriods.MuTorsor.representation_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) :
    representation hτ SpecialPeriods.triangleGenerator₂ = generatorTwo τ :=
  SpecialPeriods.triangleLift_generator₂ ..

theorem SpecialPeriods.MuTorsor.generatorOne_mul_generatorTwo_apply {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    (generatorOne τ * generatorTwo τ) (z, u) =
      (SpecialPeriods.Triangle.generatorOneSL • (SpecialPeriods.Triangle.generatorTwoSL • z),
        u) := by
  change generatorOne τ (generatorTwo τ (z, u)) = _
  rw [generatorTwo_apply, generatorOne_apply, hτ.2 z]
  congr 1
  field_simp [(τ z).ne_zero]
  ring

theorem SpecialPeriods.MuTorsor.representation_cusp_snd {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    (representation hτ SpecialPeriods.triangleCuspGenerator (z, u)).2 = u := by
  rw [representation, SpecialPeriods.triangleLift_cusp]
  have he := (generatorOne τ * generatorTwo τ).apply_symm_apply (z, u)
  have hc := congrArg Prod.snd he
  rw [generatorOne_mul_generatorTwo_apply hτ] at hc
  exact hc

theorem SpecialPeriods.MuTorsor.generatorOneScale_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (generatorOneScale τ z : ℂ)) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

theorem SpecialPeriods.MuTorsor.generatorTwoScale_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (generatorTwoScale τ z : ℂ)) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

theorem SpecialPeriods.MuTorsor.generatorOneShift_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (generatorOneShift τ) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

theorem SpecialPeriods.MuTorsor.generatorTwoShift_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω generatorTwoShift :=
  contMDiff_const

def SpecialPeriods.MuTorsor.AffineFibres {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (g : G) : Prop :=
  ∃ a : B → ℂˣ, ∃ b : B → ℂ, ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)

theorem SpecialPeriods.MuTorsor.affine_coefficients_unique {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g : G} {a c : B → ℂˣ} {b d : B → ℂ}
    (hf : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (hf' : ∀ z u, ρ g (z, u) = (β g z, (c z : ℂ) * u + d z)) : a = c ∧ b = d := by
  have hb : ∀ z, b z = d z := by
    intro z
    have h := congrArg Prod.snd ((hf z 0).symm.trans (hf' z 0))
    simpa only [MulZeroClass.mul_zero, zero_add] using h
  refine ⟨?_, funext hb⟩
  funext z
  apply Units.ext
  have h : (a z : ℂ) + b z = (c z : ℂ) + d z := by
    simpa only [mul_one] using congrArg Prod.snd ((hf z 1).symm.trans (hf' z 1))
  rw [hb z] at h
  exact add_right_cancel h

theorem SpecialPeriods.MuTorsor.affine_one_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (z : B) (u : ℂ) :
    ρ 1 (z, u) = (β 1 z, ((1 : ℂˣ) : ℂ) * u + 0) := by simp

theorem SpecialPeriods.MuTorsor.affine_mul_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g h : G} {a c : B → ℂˣ} {b d : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (hh : ∀ z u, ρ h (z, u) = (β h z, (c z : ℂ) * u + d z)) (z : B) (u : ℂ) :
    ρ (g * h) (z, u) =
      (β (g * h) z, ((a (β h z) * c z : ℂˣ) : ℂ) * u + ((a (β h z) : ℂ) * d z + b (β h z))) := by
  rw [map_mul, Equiv.Perm.mul_apply, hh, hg]
  apply Prod.ext
  · simp only [map_mul, Equiv.Perm.mul_apply]
  · simp only [Units.val_mul]
    ring

theorem SpecialPeriods.MuTorsor.affine_inv_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g : G} {a : B → ℂˣ} {b : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) (z : B) (u : ℂ) :
    ρ g⁻¹ (z, u) =
      (β g⁻¹ z, (((a (β g⁻¹ z))⁻¹ : ℂˣ) : ℂ) * u + (-((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)))) := by
  apply (ρ g).injective
  have hc : ρ g (ρ g⁻¹ (z, u)) = (z, u) := by
    rw [map_inv, Equiv.Perm.inv_def]
    exact (ρ g).apply_symm_apply _
  rw [hc, hg]
  apply Prod.ext
  · rw [map_inv, Equiv.Perm.inv_def]
    exact ((β g).apply_symm_apply z).symm
  · simp only [Units.val_inv_eq_inv_val, mul_add, mul_neg, ← mul_assoc,
      mul_inv_cancel₀ (a (β g⁻¹ z)).ne_zero, one_mul, neg_add_cancel_right]

theorem SpecialPeriods.MuTorsor.affineFibres_one {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) : AffineFibres ρ β 1 :=
  ⟨fun _ => 1, fun _ => 0, affine_one_formula ρ β⟩

theorem SpecialPeriods.MuTorsor.affineFibres_mul {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g h : G} (hg : AffineFibres ρ β g)
    (hh : AffineFibres ρ β h) : AffineFibres ρ β (g * h) := by
  obtain ⟨a, b, ha⟩ := hg
  obtain ⟨c, d, hc⟩ := hh
  exact
    ⟨fun z => a (β h z) * c z, fun z => (a (β h z) : ℂ) * d z + b (β h z),
      affine_mul_formula ρ β ha hc⟩

theorem SpecialPeriods.MuTorsor.affineFibres_inv {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g : G} (hg : AffineFibres ρ β g) :
    AffineFibres ρ β g⁻¹ := by
  obtain ⟨a, b, ha⟩ := hg
  exact
    ⟨fun z => (a (β g⁻¹ z))⁻¹, fun z => -((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)),
      affine_inv_formula ρ β ha⟩

def SpecialPeriods.MuTorsor.affineSubgroup {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) : Subgroup G
    where
  carrier := AffineFibres ρ β
  one_mem' := affineFibres_one ρ β
  mul_mem' := affineFibres_mul ρ β
  inv_mem' := affineFibres_inv ρ β

def SpecialPeriods.MuTorsor.scale {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g : G) : B → ℂˣ :=
  (h_all g).choose

def SpecialPeriods.MuTorsor.shift {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g : G) : B → ℂ :=
  (h_all g).choose_spec.choose

theorem SpecialPeriods.MuTorsor.action_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g)
    (g : G) (z : B) (u : ℂ) :
    ρ g (z, u) = (β g z, (scale ρ β h_all g z : ℂ) * u + shift ρ β h_all g z) :=
  (h_all g).choose_spec.choose_spec z u

theorem SpecialPeriods.MuTorsor.scale_eq_of_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g)
    {g : G} {a : B → ℂˣ} {b : B → ℂ} (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) :
    scale ρ β h_all g = a :=
  (affine_coefficients_unique ρ β (action_formula ρ β h_all g) hg).1

theorem SpecialPeriods.MuTorsor.shift_eq_of_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g)
    {g : G} {a : B → ℂˣ} {b : B → ℂ} (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) :
    shift ρ β h_all g = b :=
  (affine_coefficients_unique ρ β (action_formula ρ β h_all g) hg).2

@[simp]
theorem SpecialPeriods.MuTorsor.scale_one {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (z : B) : scale ρ β h_all 1 z = 1 :=
  congrFun (scale_eq_of_formula ρ β h_all (affine_one_formula ρ β)) z

@[simp]
theorem SpecialPeriods.MuTorsor.shift_one {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (z : B) : shift ρ β h_all 1 z = 0 :=
  congrFun (shift_eq_of_formula ρ β h_all (affine_one_formula ρ β)) z

theorem SpecialPeriods.MuTorsor.scale_mul {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g h : G) (z : B) :
    scale ρ β h_all (g * h) z = scale ρ β h_all g (β h z) * scale ρ β h_all h z :=
  congrFun
    (scale_eq_of_formula ρ β h_all
      (affine_mul_formula ρ β (action_formula ρ β h_all g) (action_formula ρ β h_all h)))
    z

theorem SpecialPeriods.MuTorsor.shift_mul {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g h : G) (z : B) :
    shift ρ β h_all (g * h) z =
      (scale ρ β h_all g (β h z) : ℂ) * shift ρ β h_all h z + shift ρ β h_all g (β h z) :=
  congrFun
    (shift_eq_of_formula ρ β h_all
      (affine_mul_formula ρ β (action_formula ρ β h_all g) (action_formula ρ β h_all h)))
    z

def SpecialPeriods.MuTorsor.HolomorphicAffineFibres {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (g : G) : Prop :=
  ∃ a : B → ℂˣ,
    ∃ b : B → ℂ,
      (∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) ∧
        ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (a z : ℂ)) ∧
          ContMDiff I (modelWithCornersSelf ℂ ℂ) ω b

theorem SpecialPeriods.MuTorsor.holomorphicAffineFibres_one {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) : HolomorphicAffineFibres ρ β I 1 :=
  ⟨fun _ => 1, fun _ => 0, affine_one_formula ρ β, contMDiff_const, contMDiff_const⟩

theorem SpecialPeriods.MuTorsor.holomorphicAffineFibres_mul {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (hβ : ∀ g, ContMDiff I I ω (β g)) {g h : G}
    (hg : HolomorphicAffineFibres ρ β I g) (hh : HolomorphicAffineFibres ρ β I h) :
    HolomorphicAffineFibres ρ β I (g * h) := by
  obtain ⟨a, b, hf, ha, hb⟩ := hg
  obtain ⟨c, d, hf', hc, hd⟩ := hh
  refine
    ⟨fun z => a (β h z) * c z, fun z => (a (β h z) : ℂ) * d z + b (β h z),
      affine_mul_formula ρ β hf hf', ?_, ?_⟩
  · change ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (a (β h z) : ℂ) * (c z : ℂ))
    exact (ha.comp (hβ h)).mul hc
  · exact ((ha.comp (hβ h)).mul hd).add (hb.comp (hβ h))

theorem SpecialPeriods.MuTorsor.holomorphicAffineFibres_inv {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (hβ : ∀ g, ContMDiff I I ω (β g)) {g : G}
    (hg : HolomorphicAffineFibres ρ β I g) : HolomorphicAffineFibres ρ β I g⁻¹ := by
  obtain ⟨a, b, hf, ha, hb⟩ := hg
  have hInv : ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (a (β g⁻¹ z) : ℂ)⁻¹) :=
    (ha.comp (hβ g⁻¹)).inv₀ (fun z => (a (β g⁻¹ z)).ne_zero)
  refine
    ⟨fun z => (a (β g⁻¹ z))⁻¹, fun z => -((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)),
      affine_inv_formula ρ β hf, ?_, ?_⟩
  · simpa only [Units.val_inv_eq_inv_val] using hInv
  · exact (hInv.mul (hb.comp (hβ g⁻¹))).neg

def SpecialPeriods.MuTorsor.holomorphicAffineSubgroup {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (hβ : ∀ g, ContMDiff I I ω (β g)) : Subgroup G
    where
  carrier := HolomorphicAffineFibres ρ β I
  one_mem' := holomorphicAffineFibres_one ρ β I
  mul_mem' := holomorphicAffineFibres_mul ρ β I hβ
  inv_mem' := holomorphicAffineFibres_inv ρ β I hβ

theorem SpecialPeriods.MuTorsor.scale_holomorphic {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (h_all : ∀ g, AffineFibres ρ β g) (g : G)
    (hg : HolomorphicAffineFibres ρ β I g) :
    ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (scale ρ β h_all g z : ℂ)) := by
  obtain ⟨a, b, hf, ha, _⟩ := hg
  rw [scale_eq_of_formula ρ β h_all hf]
  exact ha

theorem SpecialPeriods.MuTorsor.shift_holomorphic {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (h_all : ∀ g, AffineFibres ρ β g) (g : G)
    (hg : HolomorphicAffineFibres ρ β I g) :
    ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (shift ρ β h_all g) := by
  obtain ⟨a, b, hf, _, hb⟩ := hg
  rw [shift_eq_of_formula ρ β h_all hf]
  exact hb

structure SpecialPeriods.MuTorsor.AffineCocycle where
  scale : SpecialPeriods.TriangleGroup → ℍ → ℂˣ
  shift : SpecialPeriods.TriangleGroup → ℍ → ℂ
  scale_one : ∀ z, scale 1 z = 1
  shift_one : ∀ z, shift 1 z = 0
  scale_mul :
    ∀ g h z,
      scale (g * h) z = scale g (SpecialPeriods.triangleGeometricRepresentation h z) * scale h z
  shift_mul :
    ∀ g h z,
      shift (g * h) z =
        (scale g (SpecialPeriods.triangleGeometricRepresentation h z) : ℂ) * shift h z +
          shift g (SpecialPeriods.triangleGeometricRepresentation h z)
  scale_holomorphic : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (scale g z : ℂ))
  shift_holomorphic : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (shift g)

def SpecialPeriods.MuTorsor.AffineCocycle.fibreMap (c : SpecialPeriods.MuTorsor.AffineCocycle)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (u : ℂ) : ℂ :=
  (c.scale g z : ℂ) * u + c.shift g z

@[simp]
theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_one
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (z : ℍ) (u : ℂ) : c.fibreMap 1 z u = u := by
  simp only [fibreMap, c.scale_one, c.shift_one, Units.val_one, one_mul, add_zero]

theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_mul
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g h : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u : ℂ) :
    c.fibreMap (g * h) z u =
      c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation h z) (c.fibreMap h z u) := by
  simp only [fibreMap, c.scale_mul, c.shift_mul, Units.val_mul]
  ring

theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_inv
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u : ℂ) :
    c.fibreMap g⁻¹ (SpecialPeriods.triangleGeometricRepresentation g z) (c.fibreMap g z u) = u := by
  rw [← c.fibreMap_mul, inv_mul_cancel, c.fibreMap_one]

theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_injective
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    Function.Injective (c.fibreMap g z) := by
  intro u v huv
  exact mul_left_cancel₀ (c.scale g z).ne_zero (add_right_cancel huv)

theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_sub
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u v : ℂ) : c.fibreMap g z u - c.fibreMap g z v = (c.scale g z : ℂ) * (u - v) := by
  simp only [fibreMap]
  ring

def SpecialPeriods.MuTorsor.AffineCocycle.EquivariantOn
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) (V : Set ℍ) : Prop :=
  ∀ g z, z ∈ V → f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z)

structure SpecialPeriods.MuTorsor.PreciselyInvariantPatch where
  sheet : TopologicalSpace.Opens ℍ
  stabilizer : Subgroup SpecialPeriods.TriangleGroup
  mapsTo :
    ∀ g : stabilizer,
      Set.MapsTo
        (SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup)) sheet
        sheet
  returning :
    ∀ g : SpecialPeriods.TriangleGroup,
      ((SpecialPeriods.triangleGeometricRepresentation g '' (sheet : Set ℍ)) ∩ sheet).Nonempty →
        g ∈ stabilizer

def SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) : Set ℍ :=
  {z |
    ∃ g : SpecialPeriods.TriangleGroup,
      ∃ x : ℍ, x ∈ P.sheet ∧ SpecialPeriods.triangleGeometricRepresentation g x = z}

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation_invariant
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (g : SpecialPeriods.TriangleGroup)
    (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ P.saturation ↔ z ∈ P.saturation := by
  constructor
  · rintro ⟨h, x, hx, he⟩
    refine ⟨g⁻¹ * h, x, hx, ?_⟩
    rw [map_mul]
    change
      SpecialPeriods.triangleGeometricRepresentation g⁻¹
          (SpecialPeriods.triangleGeometricRepresentation h x) =
        z
    rw [he, map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply z
  · rintro ⟨h, x, hx, rfl⟩
    exact ⟨g * h, x, hx, by simp⟩

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation_isOpen
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) : IsOpen P.saturation := by
  have he :
    P.saturation =
      ⋃ g : SpecialPeriods.TriangleGroup,
        SpecialPeriods.triangleGeometricRepresentation g '' (P.sheet : Set ℍ) := by
    ext z
    simp only [saturation, Set.mem_iUnion, Set.mem_image]
    rfl
  rw [he]
  exact
    isOpen_iUnion fun g =>
      (SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph.isOpenMap _ P.sheet.isOpen

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation_eq_preimage_image
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) :
    P.saturation =
      SpecialPeriods.triangleOrbitProjection ⁻¹'
        (SpecialPeriods.triangleOrbitProjection '' P.sheet) := by
  ext z
  constructor
  · rintro ⟨g, x, hx, rfl⟩
    exact ⟨x, hx, (SpecialPeriods.triangleOrbitProjection_smul g x).symm⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff z x).mp he.symm
    exact ⟨g, x, hx, hg⟩

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.stabilizer_mem_iff
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (g : SpecialPeriods.TriangleGroup)
    (x : ℍ) (hx : x ∈ P.sheet) :
    SpecialPeriods.triangleGeometricRepresentation g x ∈ P.sheet ↔ g ∈ P.stabilizer := by
  constructor
  · intro hgx
    exact P.returning g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  · intro hg
    exact P.mapsTo ⟨g, hg⟩ hx

structure SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch)
    (c : SpecialPeriods.MuTorsor.AffineCocycle) where
  toFun : ℍ → ℂ
  holomorphic : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω toFun P.sheet
  equivariant :
    ∀ g : P.stabilizer,
      ∀ z ∈ P.sheet,
        toFun
            (SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup)
              z) =
          c.fibreMap g z (toFun z)

def SpecialPeriods.MuTorsor.AffineCocycle.sectionStabilizer
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) :
    Subgroup SpecialPeriods.TriangleGroup
    where
  carrier :=
    {g | ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z)}
  one_mem' := by
    intro z
    simp only [map_one, Equiv.Perm.one_apply, c.fibreMap_one]
  mul_mem' := by
    intro g h hg hh z
    calc
      f (SpecialPeriods.triangleGeometricRepresentation (g * h) z) =
          f
            (SpecialPeriods.triangleGeometricRepresentation g
              (SpecialPeriods.triangleGeometricRepresentation h z)) := by
        rw [map_mul, Equiv.Perm.mul_apply]
      _ =
          c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation h z)
            (f (SpecialPeriods.triangleGeometricRepresentation h z)) :=
        (hg _)
      _ =
          c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation h z)
            (c.fibreMap h z (f z)) := by rw [hh z]
      _ = c.fibreMap (g * h) z (f z) := (c.fibreMap_mul g h z (f z)).symm
  inv_mem' := by
    intro g hg z
    apply c.fibreMap_injective g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
    have hbase :
      SpecialPeriods.triangleGeometricRepresentation g
          (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) =
        z := by
      rw [map_inv, Equiv.Perm.inv_def]
      exact (SpecialPeriods.triangleGeometricRepresentation g).apply_symm_apply z
    calc
      c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
            (f (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)) =
          f
            (SpecialPeriods.triangleGeometricRepresentation g
              (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)) :=
        (hg _).symm
      _ = f z := (congrArg f hbase)
      _ =
          c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
            (c.fibreMap g⁻¹ z (f z)) := by
        simpa only [inv_inv] using (c.fibreMap_inv g⁻¹ z (f z)).symm

theorem SpecialPeriods.MuTorsor.AffineCocycle.zpowers_le_sectionStabilizer
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z)) :
    Subgroup.zpowers g ≤ c.sectionStabilizer f :=
  Subgroup.zpowers_le.mpr hg

theorem SpecialPeriods.MuTorsor.AffineCocycle.equivariant_of_mem_zpowers
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z))
    {h : SpecialPeriods.TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    f (SpecialPeriods.triangleGeometricRepresentation h z) = c.fibreMap h z (f z) :=
  c.zpowers_le_sectionStabilizer f g hg hh z

private theorem SpecialPeriods.MuTorsor.mem_subgroup_of_triangle_generators_mo1973_17509
    (K : Subgroup SpecialPeriods.TriangleGroup) (h₁ : SpecialPeriods.triangleGenerator₁ ∈ K)
    (h₂ : SpecialPeriods.triangleGenerator₂ ∈ K) (g : SpecialPeriods.TriangleGroup) : g ∈ K := by
  have hle :
    Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) ≤
      K :=
    (Subgroup.closure_le _).mpr
      (by
        intro x hx
        rcases hx with rfl | rfl
        · exact h₁
        · exact h₂)
  rw [SpecialPeriods.triangle_generators_generate] at hle
  exact hle (Subgroup.mem_top g)

theorem SpecialPeriods.MuTorsor.representation_generatorOne_formula {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleGenerator₁ (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z,
        (generatorOneScale τ z : ℂ) * u + generatorOneShift τ z) := by
  rw [representation_generator₁, SpecialPeriods.triangleGeometricRepresentation_generator₁]
  rfl

theorem SpecialPeriods.MuTorsor.representation_generatorTwo_formula {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleGenerator₂ (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z,
        (generatorTwoScale τ z : ℂ) * u + generatorTwoShift z) := by
  rw [representation_generator₂, SpecialPeriods.triangleGeometricRepresentation_generator₂]
  rfl

theorem SpecialPeriods.MuTorsor.representation_affine {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (g : SpecialPeriods.TriangleGroup) :
    AffineFibres (representation hτ) SpecialPeriods.triangleGeometricRepresentation g := by
  apply
    mem_subgroup_of_triangle_generators_mo1973_17509
      (affineSubgroup (representation hτ) SpecialPeriods.triangleGeometricRepresentation)
  · exact ⟨generatorOneScale τ, generatorOneShift τ, representation_generatorOne_formula hτ⟩
  · exact ⟨generatorTwoScale τ, generatorTwoShift, representation_generatorTwo_formula hτ⟩

theorem SpecialPeriods.MuTorsor.representation_fst {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (g : SpecialPeriods.TriangleGroup) (z : ℍ) (u : ℂ) :
    (representation hτ g (z, u)).1 = SpecialPeriods.triangleGeometricRepresentation g z :=
  congrArg Prod.fst
    (action_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) g z u)

theorem SpecialPeriods.MuTorsor.representation_cusp_formula {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleCuspGenerator (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator z,
        u) :=
  Prod.ext (representation_fst hτ _ z u) (representation_cusp_snd hτ z u)

theorem SpecialPeriods.MuTorsor.representation_holomorphic_affine {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (g : SpecialPeriods.TriangleGroup) :
    HolomorphicAffineFibres (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      𝓘(ℂ) g := by
  apply
    mem_subgroup_of_triangle_generators_mo1973_17509
      (holomorphicAffineSubgroup (representation hτ)
        SpecialPeriods.triangleGeometricRepresentation 𝓘(ℂ)
        SpecialPeriods.triangleGeometricRepresentation_holomorphic)
  · exact
      ⟨generatorOneScale τ, generatorOneShift τ, representation_generatorOne_formula hτ,
        generatorOneScale_holomorphic hτa, generatorOneShift_holomorphic hτa⟩
  · exact
      ⟨generatorTwoScale τ, generatorTwoShift, representation_generatorTwo_formula hτ,
        generatorTwoScale_holomorphic hτa, generatorTwoShift_holomorphic⟩

def SpecialPeriods.MuTorsor.cocycle {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : AffineCocycle
    where
  scale :=
    scale (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  shift :=
    shift (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  scale_one :=
    scale_one (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  shift_one :=
    shift_one (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  scale_mul :=
    scale_mul (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  shift_mul :=
    shift_mul (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  scale_holomorphic
    g :=
    scale_holomorphic (representation hτ) SpecialPeriods.triangleGeometricRepresentation 𝓘(ℂ)
      (representation_affine hτ) g (representation_holomorphic_affine hτ hτa g)
  shift_holomorphic
    g :=
    shift_holomorphic (representation hτ) SpecialPeriods.triangleGeometricRepresentation 𝓘(ℂ)
      (representation_affine hτ) g (representation_holomorphic_affine hτ hτa g)

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₁ z = generatorOneScale τ z :=
  congrFun
    (scale_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorOne_formula hτ))
    z

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₂ z = generatorTwoScale τ z :=
  congrFun
    (scale_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorTwo_formula hτ))
    z

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_shift_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).shift SpecialPeriods.triangleGenerator₁ z = 1 / (τ z : ℂ) :=
  congrFun
    (shift_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorOne_formula hτ))
    z

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_shift_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).shift SpecialPeriods.triangleGenerator₂ z = 1 :=
  congrFun
    (shift_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorTwo_formula hτ))
    z

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₁_val {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    ((cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₁ z : ℂ) = -1 / (τ z : ℂ) := by
  rw [cocycle_scale_generator₁, generatorOneScale_val]

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₂_val {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    ((cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₂ z : ℂ) = 1 / (τ z : ℂ) := by
  rw [cocycle_scale_generator₂, generatorTwoScale_val]

theorem SpecialPeriods.MuTorsor.cocycle_fibreMap_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap SpecialPeriods.triangleGenerator₁ z u = (1 - u) / (τ z : ℂ) := by
  rw [AffineCocycle.fibreMap, cocycle_scale_generator₁_val, cocycle_shift_generator₁]
  ring

theorem SpecialPeriods.MuTorsor.cocycle_fibreMap_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap SpecialPeriods.triangleGenerator₂ z u = 1 + u / (τ z : ℂ) := by
  rw [AffineCocycle.fibreMap, cocycle_scale_generator₂_val, cocycle_shift_generator₂]
  ring

private theorem SpecialPeriods.MuTorsor.representation_cusp_affine_formula_mo1973_17526
    {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleCuspGenerator (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator z,
        ((1 : ℂˣ) : ℂ) * u + 0) := by
  simpa only [Units.val_one, one_mul, add_zero] using representation_cusp_formula hτ z u

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_scale_cusp {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).scale SpecialPeriods.triangleCuspGenerator z = 1 :=
  congrFun
    (scale_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_cusp_affine_formula_mo1973_17526 hτ))
    z

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_shift_cusp {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).shift SpecialPeriods.triangleCuspGenerator z = 0 :=
  congrFun
    (shift_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_cusp_affine_formula_mo1973_17526 hτ))
    z

@[simp]
theorem SpecialPeriods.MuTorsor.cocycle_fibreMap_cusp {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap SpecialPeriods.triangleCuspGenerator z u = u := by
  simp only [AffineCocycle.fibreMap, cocycle_scale_cusp, cocycle_shift_cusp, Units.val_one,
    one_mul, add_zero]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.MuTorsor.Cover.regularRepresentative
    (x : SpecialPeriods.TriangleRegularQuotient) : SpecialPeriods.TriangleRegularPoint :=
  CoveringQuotient.representative SpecialPeriods.triangleRegularProject_covering x

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_project
    (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.triangleRegularProject (regularRepresentative x) = x :=
  CoveringQuotient.project_representative SpecialPeriods.triangleRegularProject_covering x

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.MuTorsor.Cover.regularLift (x : SpecialPeriods.TriangleRegularQuotient) :
    OpenPartialHomeomorph SpecialPeriods.TriangleRegularQuotient
      SpecialPeriods.TriangleRegularPoint :=
  CoveringQuotient.localInverse SpecialPeriods.triangleRegularProject_covering
    (regularRepresentative x)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.regularLift_symm
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularLift x).symm = SpecialPeriods.triangleRegularProject :=
  CoveringQuotient.localInverse_symm SpecialPeriods.triangleRegularProject_covering
    (regularRepresentative x)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_mem_target
    (x : SpecialPeriods.TriangleRegularQuotient) :
    regularRepresentative x ∈ (regularLift x).target :=
  IsLocalHomeomorph.self_mem_localInverseAt_target
    SpecialPeriods.triangleRegularProject_covering.isCoveringMap.isLocalHomeomorph

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.MuTorsor.Cover.regularSheet (x : SpecialPeriods.TriangleRegularQuotient) :
    TopologicalSpace.Opens ℍ :=
  ⟨Subtype.val '' (regularLift x).target,
    SpecialPeriods.triangleRegularDomain.isOpen.isOpenMap_subtype_val _
      (regularLift x).open_target⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.regularSheet_subset_regularLocus
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularSheet x : Set ℍ) ⊆ SpecialPeriods.triangleRegularLocus := by
  rintro z ⟨a, ha, rfl⟩
  exact a.property

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_mem_sheet
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularRepresentative x).val ∈ regularSheet x :=
  ⟨regularRepresentative x, regularRepresentative_mem_target x, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.regularSheet_no_return
    (x : SpecialPeriods.TriangleRegularQuotient) (g : SpecialPeriods.TriangleGroup)
    (hg :
      ((SpecialPeriods.triangleGeometricRepresentation g '' (regularSheet x : Set ℍ)) ∩
          regularSheet x).Nonempty) :
    g = 1 := by
  rcases hg with ⟨z, ⟨w, ⟨a, ha, rfl⟩, hga⟩, ⟨b, hb, rfl⟩⟩
  have hab : g • a = b := Subtype.ext hga
  have hproj :
    SpecialPeriods.triangleRegularProject b = SpecialPeriods.triangleRegularProject a := by
    rw [← hab]
    exact SpecialPeriods.triangleRegularProject_covering.map_smul g
  have hba : b = a :=
    (regularLift x).symm.injOn hb ha (by simpa only [regularLift_symm] using hproj)
  exact
    (SpecialPeriods.mem_triangleRegularLocus_iff a.val).mp a.property g
      (congrArg Subtype.val (hab.trans hba))

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_orbitProjection
    (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.triangleOrbitProjection (regularRepresentative x).val =
      SpecialPeriods.triangleRegularToOrbit x := by
  rw [← SpecialPeriods.triangleRegularToOrbit_project, regularRepresentative_project]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.MuTorsor.Cover.regularImage (x : SpecialPeriods.TriangleRegularQuotient) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  ⟨SpecialPeriods.triangleOrbitProjection '' (regularSheet x : Set ℍ),
    SpecialPeriods.triangleOrbitProjection_isOpenMap _ (regularSheet x).isOpen⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.regularImage_subset_regularDomain
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularImage x : Set SpecialPeriods.TriangleOrbitSpace) ⊆
      SpecialPeriods.triangleOrbitRegularDomain := by
  rintro y ⟨z, hz, rfl⟩
  exact
    (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mpr
      (regularSheet_subset_regularLocus x hz)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.regularImage_mem
    (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.triangleRegularToOrbit x ∈ regularImage x :=
  ⟨(regularRepresentative x).val, regularRepresentative_mem_sheet x,
    regularRepresentative_orbitProjection x⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Cover.exists_regularImage (y : SpecialPeriods.TriangleOrbitSpace)
    (hy : y ∈ SpecialPeriods.triangleOrbitRegularDomain) :
    ∃ x : SpecialPeriods.TriangleRegularQuotient, y ∈ regularImage x := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, regularImage_mem x⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
abbrev SpecialPeriods.MuTorsor.Cover.Index :=
  Option (SpecialPeriods.TriangleRegularQuotient ⊕ Elliptic.Kind)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.cuspIndex : Index :=
  Option.none

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.regularIndex (x : SpecialPeriods.TriangleRegularQuotient) :
    Index :=
  Option.some (.inl x)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.ellipticIndex (j : Elliptic.Kind) : Index :=
  Option.some (.inr j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.cuspPatch : SpecialPeriods.MuTorsor.PreciselyInvariantPatch
    where
  sheet := SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width
  stabilizer := Subgroup.zpowers SpecialPeriods.triangleCuspGenerator
  mapsTo := SpecialPeriods.Triangle.cusp_horodisc_invariant SpecialPeriods.Triangle.width
  returning :=
    SpecialPeriods.Triangle.triangle_horodisc_overlap_mem_cusp SpecialPeriods.Triangle.width
      le_rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.regularPatch (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.MuTorsor.PreciselyInvariantPatch
    where
  sheet := regularSheet x
  stabilizer := ⊥
  mapsTo := by
    intro g z hz
    have hg : (g : SpecialPeriods.TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    simpa only [hg, map_one, Equiv.Perm.one_apply] using hz
  returning := fun g hg => Subgroup.mem_bot.mpr (regularSheet_no_return x g hg)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.ellipticPatch (j : Elliptic.Kind) :
    SpecialPeriods.MuTorsor.PreciselyInvariantPatch
    where
  sheet := SpecialPeriods.Triangle.ellipticNeighborhood j
  stabilizer := SpecialPeriods.Triangle.ellipticStabilizer j
  mapsTo := SpecialPeriods.Triangle.ellipticNeighborhood_mapsTo j
  returning := SpecialPeriods.Triangle.ellipticNeighborhood_return j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.patch : Index → SpecialPeriods.MuTorsor.PreciselyInvariantPatch
  | none => cuspPatch
  | some (.inl x) => regularPatch x
  | some (.inr j) => ellipticPatch j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.compactImage
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace) :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  ⟨SpecialPeriods.triangleOpenInclusion '' (V : Set SpecialPeriods.TriangleOrbitSpace),
    SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.isOpenMap _ V.isOpen⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.openInclusion_mem_compactImage
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ compactImage V ↔ q ∈ V :=
  SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.injective.mem_set_image

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.compactPatch :
    Index → TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace
  | none => SpecialPeriods.Triangle.cuspNeighborhood SpecialPeriods.Triangle.width
  | some (.inl x) => compactImage (regularImage x)
  | some (.inr j) => compactImage (SpecialPeriods.Triangle.ellipticNeighborhoodImage j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.compactPatch_preimage_openInclusion (i : Index) :
    SpecialPeriods.triangleOpenInclusion ⁻¹'
        (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      SpecialPeriods.triangleOrbitProjection '' ((patch i).sheet : Set ℍ) := by
  cases i with
  | none => exact SpecialPeriods.Triangle.cuspNeighborhood_preimage SpecialPeriods.Triangle.width
  | some i =>
    cases i with
    | inl x =>
      ext q
      exact openInclusion_mem_compactImage (regularImage x) q
    | inr j =>
      ext q
      exact openInclusion_mem_compactImage (SpecialPeriods.Triangle.ellipticNeighborhoodImage j) q

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.compactPatch_preimage_projection (i : Index) :
    SpecialPeriods.triangleCompactifiedProjection ⁻¹'
        (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      (patch i).saturation := by
  change
    SpecialPeriods.triangleOrbitProjection ⁻¹'
        (SpecialPeriods.triangleOpenInclusion ⁻¹'
          (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)) =
      _
  rw [compactPatch_preimage_openInclusion, (patch i).saturation_eq_preimage_image]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.Cover.compactifiedProjection_mem_compactPatch (i : Index)
    (z : ℍ) :
    SpecialPeriods.triangleCompactifiedProjection z ∈ compactPatch i ↔ z ∈ (patch i).saturation :=
  by
  change
    z ∈
        SpecialPeriods.triangleCompactifiedProjection ⁻¹'
          (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ↔
      _
  rw [compactPatch_preimage_projection]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.exists_compactPatch
    (q : SpecialPeriods.TriangleCompactifiedOrbitSpace) : ∃ i : Index, q ∈ compactPatch i := by
  induction q using OnePoint.rec with
  | infty =>
    exact
      ⟨cuspIndex,
        SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood SpecialPeriods.Triangle.width⟩
  | coe q =>
    by_cases h₁ : q = SpecialPeriods.triangleOrbitCenterOne
    · subst q
      exact
        ⟨ellipticIndex .three, SpecialPeriods.triangleOrbitCenterOne,
          SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage .three, rfl⟩
    by_cases h₂ : q = SpecialPeriods.triangleOrbitCenterTwo
    · subst q
      exact
        ⟨ellipticIndex .four, SpecialPeriods.triangleOrbitCenterTwo,
          SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage .four, rfl⟩
    obtain ⟨x, hx⟩ :=
      exists_regularImage q ((SpecialPeriods.triangleOrbitRegularDomain_mem_iff q).mpr ⟨h₁, h₂⟩)
    exact ⟨regularIndex x, q, hx, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.ellipticOrbitCenter_not_mem_regularDomain
    (j : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticOrbitCenter j ∉ SpecialPeriods.triangleOrbitRegularDomain := by
  cases j with
  | three => exact fun h => ((SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mp h).1 rfl
  | four => exact fun h => ((SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mp h).2 rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.ellipticOrbitCenter_mem_neighborhoodImage_iff
    (j k : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticOrbitCenter j ∈
        SpecialPeriods.Triangle.ellipticNeighborhoodImage k ↔
      j = k := by
  by_cases h : j = k
  · subst j
    exact iff_of_true (SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage k) rfl
  · have hj : j = SpecialPeriods.Triangle.ellipticOtherKind k := by
      cases j <;> cases k <;> simp_all [SpecialPeriods.Triangle.ellipticOtherKind]
    exact
      iff_of_false
        (by
          rw [hj]
          exact SpecialPeriods.Triangle.ellipticOtherOrbitCenter_not_mem_neighborhoodImage k)
        h

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.compactPatch_center_unique (j : Elliptic.Kind) (i : Index) :
    SpecialPeriods.triangleOpenInclusion (SpecialPeriods.Triangle.ellipticOrbitCenter j) ∈
        compactPatch i ↔
      i = ellipticIndex j := by
  cases i with
  | none =>
    apply iff_of_false
    · intro h
      exact
        ellipticOrbitCenter_not_mem_regularDomain j
          (SpecialPeriods.Triangle.cuspImage_subset_regularDomain SpecialPeriods.Triangle.width
            le_rfl
            ((SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood
                  SpecialPeriods.Triangle.width _).mp
              h))
    · intro h
      cases h
  | some i =>
    cases i with
    | inl x =>
      apply iff_of_false
      · intro h
        exact
          ellipticOrbitCenter_not_mem_regularDomain j
            (regularImage_subset_regularDomain x
              ((openInclusion_mem_compactImage (regularImage x) _).mp h))
      · intro h
        cases h
    | inr
      k =>
      change
        SpecialPeriods.triangleOpenInclusion (SpecialPeriods.Triangle.ellipticOrbitCenter j) ∈
            compactImage (SpecialPeriods.Triangle.ellipticNeighborhoodImage k) ↔
          Option.some (Sum.inr k) = Option.some (Sum.inr j)
      rw [openInclusion_mem_compactImage, ellipticOrbitCenter_mem_neighborhoodImage_iff]
      simp only [Option.some.injEq, Sum.inr.injEq, eq_comm]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.distinct_compactPatch_overlap_avoids_center {i k : Index}
    (hik : i ≠ k) (j : Elliptic.Kind) :
    SpecialPeriods.triangleOpenInclusion (SpecialPeriods.Triangle.ellipticOrbitCenter j) ∉
      (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∩ compactPatch k := by
  intro h
  exact
    hik
      (((compactPatch_center_unique j i).mp h.1).trans
        ((compactPatch_center_unique j k).mp h.2).symm)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.distinct_saturation_overlap_subset_regularLocus
    {i k : Index} (hik : i ≠ k) :
    (patch i).saturation ∩ (patch k).saturation ⊆ SpecialPeriods.triangleRegularLocus := by
  intro z hz
  have hq :
    SpecialPeriods.triangleCompactifiedProjection z ∈
      (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∩ compactPatch k :=
    ⟨(compactifiedProjection_mem_compactPatch i z).mpr hz.1,
      (compactifiedProjection_mem_compactPatch k z).mpr hz.2⟩
  apply (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mp
  apply (SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mpr
  constructor
  · intro h
    have he :
      SpecialPeriods.triangleCompactifiedProjection z =
        SpecialPeriods.triangleOpenInclusion
          (SpecialPeriods.Triangle.ellipticOrbitCenter .three) :=
      congrArg SpecialPeriods.triangleOpenInclusion h
    exact distinct_compactPatch_overlap_avoids_center hik .three (he ▸ hq)
  · intro h
    have he :
      SpecialPeriods.triangleCompactifiedProjection z =
        SpecialPeriods.triangleOpenInclusion
          (SpecialPeriods.Triangle.ellipticOrbitCenter .four) :=
      congrArg SpecialPeriods.triangleOpenInclusion h
    exact distinct_compactPatch_overlap_avoids_center hik .four (he ▸ hq)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.Cover.finitePatch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (i : Index) : TopologicalSpace.Opens ℂ :=
  finitePullback π (compactPatch i)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.exists_finitePatch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℂ) : ∃ i : Index, z ∈ finitePatch π i :=
  exists_compactPatch (finiteInverse π z)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.Cover.finitePatch_cusp_contains_exterior
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ finitePatch π cuspIndex :=
  finitePullback_contains_exterior π hπ
    (SpecialPeriods.Triangle.cuspNeighborhood SpecialPeriods.Triangle.width)
    (SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood SpecialPeriods.Triangle.width)

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.translated_values_agree
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c)
    (g h : SpecialPeriods.TriangleGroup) (x y : ℍ) (hx : x ∈ P.sheet) (hy : y ∈ P.sheet)
    (he :
      SpecialPeriods.triangleGeometricRepresentation g x =
        SpecialPeriods.triangleGeometricRepresentation h y) :
    c.fibreMap g x (s.toFun x) = c.fibreMap h y (s.toFun y) := by
  have hxy : SpecialPeriods.triangleGeometricRepresentation (h⁻¹ * g) x = y := by
    rw [map_mul]
    change
      SpecialPeriods.triangleGeometricRepresentation h⁻¹
          (SpecialPeriods.triangleGeometricRepresentation g x) =
        y
    rw [he, map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation h).symm_apply_apply y
  have hk : h⁻¹ * g ∈ P.stabilizer := (P.stabilizer_mem_iff (h⁻¹ * g) x hx).mp (hxy ▸ hy)
  have hs := s.equivariant ⟨h⁻¹ * g, hk⟩ x hx
  change
    s.toFun (SpecialPeriods.triangleGeometricRepresentation (h⁻¹ * g) x) =
      c.fibreMap (h⁻¹ * g) x (s.toFun x) at hs
  rw [hxy] at hs
  calc
    c.fibreMap g x (s.toFun x) = c.fibreMap (h * (h⁻¹ * g)) x (s.toFun x) := by
      rw [mul_inv_cancel_left]
    _ =
        c.fibreMap h (SpecialPeriods.triangleGeometricRepresentation (h⁻¹ * g) x)
          (c.fibreMap (h⁻¹ * g) x (s.toFun x)) :=
      c.fibreMap_mul ..
    _ = c.fibreMap h y (s.toFun y) := by rw [hxy, ← hs]

def SpecialPeriods.MuTorsor.PreciselyInvariantPatch.representative
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (z : P.saturation) :
    SpecialPeriods.TriangleGroup × P.sheet :=
  let hg := z.property.choose_spec
  ⟨z.property.choose, ⟨hg.choose, hg.choose_spec.1⟩⟩

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.representative_spec
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (z : P.saturation) :
    SpecialPeriods.triangleGeometricRepresentation (P.representative z).1 (P.representative z).2 =
      z :=
  z.property.choose_spec.choose_spec.2

def SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) (z : ℍ) : ℂ := by
  classical
    exact
    if hz : z ∈ P.saturation then
      let r := P.representative ⟨z, hz⟩
      c.fibreMap r.1 r.2 (s.toFun r.2)
    else 0

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_translate
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) (g : SpecialPeriods.TriangleGroup)
    (x : ℍ) (hx : x ∈ P.sheet) :
    s.extend (SpecialPeriods.triangleGeometricRepresentation g x) = c.fibreMap g x (s.toFun x) := by
  have hz : SpecialPeriods.triangleGeometricRepresentation g x ∈ P.saturation := ⟨g, x, hx, rfl⟩
  rw [SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend, dif_pos hz]
  exact
    s.translated_values_agree _ g _ x (P.representative ⟨_, hz⟩).2.property hx
      (P.representative_spec ⟨_, hz⟩)

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_eq
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) (x : ℍ) (hx : x ∈ P.sheet) :
    s.extend x = s.toFun x := by
  simpa only [map_one, Equiv.Perm.one_apply, c.fibreMap_one] using s.extend_translate 1 x hx

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_equivariant
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) :
    c.EquivariantOn s.extend P.saturation := by
  intro g z hz
  obtain ⟨h, x, hx, rfl⟩ := hz
  have hmul :
    SpecialPeriods.triangleGeometricRepresentation g
        (SpecialPeriods.triangleGeometricRepresentation h x) =
      SpecialPeriods.triangleGeometricRepresentation (g * h) x := by simp
  rw [hmul, s.extend_translate (g * h) x hx, s.extend_translate h x hx, c.fibreMap_mul]

theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_holomorphic
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω s.extend P.saturation := by
  rintro z ⟨g, x, hx, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  let v : ℍ → ℍ := SpecialPeriods.triangleGeometricRepresentation g⁻¹
  have hv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω v :=
    SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹
  have hvx : v (SpecialPeriods.triangleGeometricRepresentation g x) = x := by simp [v, map_inv]
  have hsx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s.toFun x :=
    s.holomorphic.contMDiffAt (P.sheet.isOpen.mem_nhds hx)
  have hcomp :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (s.toFun ∘ v) (SpecialPeriods.triangleGeometricRepresentation g x) :=
    hsx.comp_of_eq (hv _) hvx
  have ha :=
    ((c.scale_holomorphic g).comp hv) (SpecialPeriods.triangleGeometricRepresentation g x)
  have hb :=
    ((c.shift_holomorphic g).comp hv) (SpecialPeriods.triangleGeometricRepresentation g x)
  apply (ha.mul hcomp |>.add hb).congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 (SpecialPeriods.triangleGeometricRepresentation g x), v y ∈ P.sheet := by
    apply hv.continuous.continuousAt.preimage_mem_nhds
    rw [hvx]
    exact P.sheet.isOpen.mem_nhds hx
  filter_upwards [hnear] with y hy
  have hgy : SpecialPeriods.triangleGeometricRepresentation g (v y) = y := by simp [v, map_inv]
  have he := s.extend_translate g (v y) hy
  rw [hgy] at he
  exact he

def SpecialPeriods.MuTorsor.ellipticFormula (τ : ℍ → ℍ) : Elliptic.Kind → ℍ → ℂ
  | .three, z => (2 - (τ z : ℂ)) / 3
  | .four, z => (1 - (τ z : ℂ)) / 2

theorem SpecialPeriods.MuTorsor.ellipticFormula_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFormula τ j) := by
  have ht := UpperHalfPlane.contMDiff_coe.comp hτa
  cases j
  · exact (contMDiff_const.sub ht).div₀ contMDiff_const (fun _ => by norm_num)
  · exact (contMDiff_const.sub ht).div₀ contMDiff_const (fun _ => by norm_num)

theorem SpecialPeriods.MuTorsor.ellipticFormula_generator {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (j : Elliptic.Kind)
    (z : ℍ) :
    ellipticFormula τ j
        (SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.Triangle.ellipticGenerator j) z) =
      (cocycle hτ hτa).fibreMap (SpecialPeriods.Triangle.ellipticGenerator j) z
        (ellipticFormula τ j z) := by
  cases j
  · change
      (2 -
            (τ
                (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁
                  z) :
              ℂ)) /
          3 =
        _
    dsimp only [SpecialPeriods.Triangle.ellipticGenerator]
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply, hτ.1 z,
      cocycle_fibreMap_generator₁]
    dsimp only [ellipticFormula]
    field_simp [(τ z).ne_zero]
    ring
  · change
      (1 -
            (τ
                (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂
                  z) :
              ℂ)) /
          2 =
        _
    dsimp only [SpecialPeriods.Triangle.ellipticGenerator]
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply, hτ.2 z,
      cocycle_fibreMap_generator₂]
    dsimp only [ellipticFormula]
    field_simp [(τ z).ne_zero]
    ring

def SpecialPeriods.MuTorsor.regularSeed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (x : SpecialPeriods.TriangleRegularQuotient) :
    (Cover.regularPatch x).Seed (cocycle hτ hτa)
    where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    have hg : (g : SpecialPeriods.TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    simp only [hg, AffineCocycle.fibreMap_one]

def SpecialPeriods.MuTorsor.cuspSeed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : Cover.cuspPatch.Seed (cocycle hτ hτa)
    where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    exact
      (cocycle hτ hτa).equivariant_of_mem_zpowers (fun _ => 0)
        SpecialPeriods.triangleCuspGenerator (fun w => (cocycle_fibreMap_cusp hτ hτa w 0).symm)
        g.property z

def SpecialPeriods.MuTorsor.ellipticSeed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (j : Elliptic.Kind) :
    (Cover.ellipticPatch j).Seed (cocycle hτ hτa)
    where
  toFun := ellipticFormula τ j
  holomorphic := (ellipticFormula_holomorphic hτa j).contMDiffOn
  equivariant := by
    intro g z _
    have hg :
      (g : SpecialPeriods.TriangleGroup) ∈
        Subgroup.zpowers (SpecialPeriods.Triangle.ellipticGenerator j) := by
      rw [← SpecialPeriods.Triangle.ellipticStabilizer_eq_zpowers]
      exact g.property
    exact
      (cocycle hτ hτa).equivariant_of_mem_zpowers (ellipticFormula τ j)
        (SpecialPeriods.Triangle.ellipticGenerator j) (ellipticFormula_generator hτ hτa j) hg z

def SpecialPeriods.MuTorsor.seed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : (i : Cover.Index) → (Cover.patch i).Seed (cocycle hτ hτa)
  | none => cuspSeed hτ hτa
  | some (.inl x) => regularSeed hτ hτa x
  | some (.inr j) => ellipticSeed hτ hτa j

def SpecialPeriods.MuTorsor.localSection {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (i : Cover.Index) : ℍ → ℂ :=
  (seed hτ hτa i).extend

theorem SpecialPeriods.MuTorsor.localSection_holomorphic {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (i : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i) (Cover.patch i).saturation :=
  (seed hτ hτa i).extend_holomorphic

theorem SpecialPeriods.MuTorsor.localSection_equivariant {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (i : Cover.Index) :
    (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i) (Cover.patch i).saturation :=
  (seed hτ hτa i).extend_equivariant

theorem SpecialPeriods.MuTorsor.localSection_cusp {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) :
    localSection hτ hτa Cover.cuspIndex z = 0 :=
  (cuspSeed hτ hτa).extend_eq z hz

def SpecialPeriods.MuGenerator.FiniteEvenZeros (τ : ℍ → ℍ) : Prop :=
  ∀ a : ℍ,
    ModularForm.E₆ (τ a) = 0 →
      ∃ n : ℕ,
        analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
          (2 * n : ℕ)

theorem SpecialPeriods.MuGenerator.finiteEvenZeros_of_modular_equation {τ : ℍ → ℍ} {J : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = J a)
    (hsource :
      ∀ a : ℍ,
        J a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z : ℂ => J (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (4 * k : ℕ)) :
    FiniteEvenZeros τ :=
  SpecialPeriods.ModularGermLift.native_E₆_finite_even_zeros hτ hJ hsource

structure SpecialPeriods.MuGenerator.Root (τ : ℍ → ℍ) where
  toFun : ℍ → ℂ
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω toFun
  square : ∀ a : ℍ, toFun a ^ 2 = ModularForm.E₆ (τ a)

instance SpecialPeriods.MuGenerator.instCoeFun1 {τ : ℍ → ℍ} : CoeFun (Root τ) (fun _ => ℍ → ℂ) :=
  ⟨Root.toFun⟩

theorem SpecialPeriods.MuGenerator.nonempty_root {τ : ℍ → ℍ} (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hzero : FiniteEvenZeros τ) : Nonempty (Root τ) := by
  obtain ⟨r, hr, hrsq, _⟩ :=
    AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane
      (fun a => ModularForm.E₆ (τ a)) (ModularForm.E₆.holo'.comp hτ) hzero
  exact ⟨⟨r, hr, hrsq⟩⟩

def SpecialPeriods.MuGenerator.root (τ : ℍ → ℍ) (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hzero : FiniteEvenZeros τ) : Root τ :=
  Classical.choice (nonempty_root hτ hzero)

theorem SpecialPeriods.MuGenerator.modularForm_holomorphic {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  intro a
  exact UpperHalfPlane.contMDiffAt_iff.mpr (SpecialPeriods.modularForm_analyticAt f a).contDiffAt

theorem SpecialPeriods.MuGenerator.Root.analyticAt {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) :
    AnalyticAt ℂ (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp (r.holomorphic a)).analyticAt

@[simp]
theorem SpecialPeriods.MuGenerator.Root.eq_zero_iff {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) : r a = 0 ↔ ModularForm.E₆ (τ a) = 0 := by
  rw [← r.square a]
  exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).symm

theorem SpecialPeriods.MuGenerator.Root.order_of_square_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) (n : ℕ)
    (horder :
      analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = n := by
  apply AnalyticRootCover.square_root_order (r.analyticAt a) _ horder
  filter_upwards with z
  exact r.square (UpperHalfPlane.ofComplex z)

def SpecialPeriods.MuGenerator.Root.generator {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) : ℍ → ℂ := fun a =>
  ModularForm.E₄ (τ a) ^ 2 * r a / ModularForm.discriminant (τ a)

theorem SpecialPeriods.MuGenerator.Root.generator_holomorphic {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r.generator := by
  have h4 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun a => ModularForm.E₄ (τ a)) :=
    (SpecialPeriods.MuGenerator.modularForm_holomorphic ModularForm.E₄).comp hτ
  have hD : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun a => ModularForm.discriminant (τ a)) :=
    (SpecialPeriods.MuGenerator.modularForm_holomorphic
          (CuspForm.discriminant : ModularForm 𝒮ℒ 12)).comp
      hτ
  exact ((h4.pow 2).mul r.holomorphic).div₀ hD (fun a => ModularForm.discriminant_ne_zero (τ a))

theorem SpecialPeriods.MuGenerator.Root.generator_eq_zero_iff {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) :
    r.generator a = 0 ↔ ModularForm.E₄ (τ a) = 0 ∨ ModularForm.E₆ (τ a) = 0 := by
  simp only [generator, div_eq_zero_iff, ModularForm.discriminant_ne_zero, or_false, mul_eq_zero,
    pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), r.eq_zero_iff]

theorem SpecialPeriods.MuGenerator.Root.generator_eq_zero_iff_modularJ {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) :
    r.generator a = 0 ↔
      SpecialPeriods.modularJ (τ a) = 0 ∨ SpecialPeriods.modularJ (τ a) = 1728 := by
  rw [r.generator_eq_zero_iff, SpecialPeriods.modularJ_eq_zero_iff,
    SpecialPeriods.modularJ_eq_1728_iff]

theorem SpecialPeriods.MuGenerator.modularForm_pullback_analyticAt {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {k : ℤ} (f : ModularForm 𝒮ℒ k) (a : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => f (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp ((modularForm_holomorphic f).comp hτ a)).analyticAt

theorem SpecialPeriods.MuGenerator.Root.generator_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex) (a : ℂ) =
      2 • analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) +
        analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) := by
  let f4 : ℂ → ℂ := fun z => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))
  let fD : ℂ → ℂ := fun z => ModularForm.discriminant (τ (UpperHalfPlane.ofComplex z))
  have h4 : AnalyticAt ℂ f4 (a : ℂ) :=
    SpecialPeriods.MuGenerator.modularForm_pullback_analyticAt hτ ModularForm.E₄ a
  have hD : AnalyticAt ℂ fD (a : ℂ) :=
    SpecialPeriods.MuGenerator.modularForm_pullback_analyticAt hτ
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12) a
  have hD0 : fD (a : ℂ) ≠ 0 := by
    simpa only [fD, UpperHalfPlane.ofComplex_apply] using ModularForm.discriminant_ne_zero (τ a)
  have hDi := hD.inv hD0
  have hDiorder : analyticOrderAt fD⁻¹ (a : ℂ) = 0 :=
    hDi.analyticOrderAt_eq_zero.mpr (inv_ne_zero hD0)
  have he :
    r.generator ∘ UpperHalfPlane.ofComplex = (f4 ^ 2 * (r ∘ UpperHalfPlane.ofComplex)) * fD⁻¹ := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul ((h4.pow 2).mul (r.analyticAt a)) hDi,
    analyticOrderAt_mul (h4.pow 2) (r.analyticAt a), analyticOrderAt_pow h4, hDiorder, add_zero]

theorem SpecialPeriods.MuGenerator.Root.generator_order_of_pullback_orders {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) (m n : ℕ)
    (h4 :
      analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) = m)
    (h6 :
      analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * m + n : ℕ) := by
  rw [r.generator_order hτ, h4, r.order_of_square_order a n h6]
  simp only [two_nsmul, ← Nat.cast_add]
  congr 1
  omega

theorem SpecialPeriods.MuGenerator.Root.order_centerTwo_of_tau_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1 := by
  have hv := (SpecialPeriods.tau_covariant_values hc).2
  have h6 :=
    SpecialPeriods.ModularGermLift.native_E₆_lift_order_of_zero (hτ.mdifferentiable (by simp))
      (a := SpecialPeriods.Triangle.centerTwo) (by rw [hv, SpecialPeriods.E₆_I])
  rw [hv, UpperHalfPlane.coe_I] at h6
  apply r.order_of_square_order SpecialPeriods.Triangle.centerTwo 1
  simpa only [Nat.mul_one, Nat.cast_ofNat] using h6.trans ho

theorem SpecialPeriods.MuGenerator.Root.generator_order_centerOne_of_tau_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - SpecialPeriods.rho)
          (SpecialPeriods.Triangle.centerOne : ℂ) =
        1) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.Triangle.centerOne : ℂ) =
      2 := by
  have hv := (SpecialPeriods.tau_covariant_values hc).1
  have h4 :=
    SpecialPeriods.ModularGermLift.native_E₄_lift_order_of_zero (hτ.mdifferentiable (by simp))
      (a := SpecialPeriods.Triangle.centerOne) (by rw [hv, SpecialPeriods.E₄_rhoPoint])
  rw [hv, SpecialPeriods.coe_rhoPoint] at h4
  have h6 :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z)))
        (SpecialPeriods.Triangle.centerOne : ℂ) =
      (2 * 0 : ℕ) := by
    apply analyticOrderAt_eq_zero.mpr
    right
    simpa only [UpperHalfPlane.ofComplex_apply, hv] using SpecialPeriods.E₆_rhoPoint_ne_zero
  simpa only [Nat.mul_one, Nat.add_zero, Nat.cast_ofNat] using
    r.generator_order_of_pullback_orders hτ SpecialPeriods.Triangle.centerOne 1 0 (h4.trans ho) h6

theorem SpecialPeriods.MuGenerator.Root.generator_order_centerTwo_of_tau_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.Triangle.centerTwo : ℂ) =
      1 := by
  have hv := (SpecialPeriods.tau_covariant_values hc).2
  have h4 :
    analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z)))
        (SpecialPeriods.Triangle.centerTwo : ℂ) =
      0 := by
    apply analyticOrderAt_eq_zero.mpr
    right
    simpa only [UpperHalfPlane.ofComplex_apply, hv] using SpecialPeriods.E₄_I_ne_zero
  rw [r.generator_order hτ, h4, r.order_centerTwo_of_tau_order hτ hc ho, smul_zero, zero_add]

theorem SpecialPeriods.upperHalfPlane_holomorphic_sq_eq_sq_dichotomy {f g : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hsq : ∀ z, f z ^ 2 = g z ^ 2) :
    f = g ∨ f = -g := by
  have hprod : (f - g) * (f + g) = 0 := by
    funext z
    change (f z - g z) * (f z + g z) = 0
    calc
      _ = f z ^ 2 - g z ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr (hsq z)
  rcases
    (UpperHalfPlane.mul_eq_zero_iff ((hf.sub hg).mdifferentiable (by simp))
          ((hf.add hg).mdifferentiable (by simp))).mp
      hprod with
    h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem SpecialPeriods.eisensteinSix_root_generatorOne_sq {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) (z : ℍ) :
    r (Triangle.generatorOneSL • z) ^ 2 = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
  have hτg : τ (Triangle.generatorOneSL • z) = (ModularGroup.T * ModularGroup.S) • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    exact hτc.1 z
  have hd : UpperHalfPlane.denom (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) (τ z) = (τ z : ℂ) :=
    by
    have h10 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [ModularGroup.denom_apply, h10, h11]
    simp
  calc
    _ = ModularForm.E₆ (τ (Triangle.generatorOneSL • z)) := hrsq _
    _ = (τ z : ℂ) ^ 6 * ModularForm.E₆ (τ z) := by rw [hτg, levelOne_transform, hd, zpow_ofNat]
    _ = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
      rw [← hrsq z]
      ring

theorem SpecialPeriods.eisensteinSix_root_generatorTwo_sq {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) (z : ℍ) :
    r (Triangle.generatorTwoSL • z) ^ 2 = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
  have hτg : τ (Triangle.generatorTwoSL • z) = ModularGroup.S • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    exact hτc.2 z
  calc
    _ = ModularForm.E₆ (τ (Triangle.generatorTwoSL • z)) := hrsq _
    _ = (τ z : ℂ) ^ 6 * ModularForm.E₆ (τ z) := by
      rw [hτg, levelOne_transform, ModularGroup.denom_S, zpow_ofNat]
    _ = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
      rw [← hrsq z]
      ring

theorem SpecialPeriods.eisensteinSix_root_centerOne_ne_zero {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) :
    r Triangle.centerOne ≠ 0 := by
  intro hrzero
  have h := hrsq Triangle.centerOne
  rw [hrzero, zero_pow (by decide), (tau_covariant_values hτc).1] at h
  exact E₆_rhoPoint_ne_zero h.symm

theorem SpecialPeriods.eisensteinSix_root_generatorOne {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) :
    ∀ z, r (Triangle.generatorOneSL • z) = -(τ z : ℂ) ^ 3 * r z := by
  have hweight : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ) ^ 3 * r z) :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ).pow 3).mul hr
  rcases
    upperHalfPlane_holomorphic_sq_eq_sq_dichotomy
      (hr.comp (Triangle.specialLinear_holomorphic Triangle.generatorOneSL)) hweight
      (eisensteinSix_root_generatorOne_sq hτc hrsq) with
    hpos | hneg
  · exfalso
    have h := congrFun hpos Triangle.centerOne
    change
      r (Triangle.generatorOneSL • Triangle.centerOne) =
        (τ Triangle.centerOne : ℂ) ^ 3 * r Triangle.centerOne at h
    rw [Triangle.generatorOne_fix, (tau_covariant_values hτc).1, coe_rhoPoint, rho_cube,
      neg_one_mul] at h
    apply eisensteinSix_root_centerOne_ne_zero hτc hrsq
    linear_combination h / 2
  · intro z
    simpa only [Function.comp_apply, Pi.neg_apply, neg_mul] using congrFun hneg z

theorem SpecialPeriods.eisensteinSix_root_generatorTwo_dichotomy {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) :
    (∀ z, r (Triangle.generatorTwoSL • z) = (τ z : ℂ) ^ 3 * r z) ∨
      (∀ z, r (Triangle.generatorTwoSL • z) = -(τ z : ℂ) ^ 3 * r z) := by
  have hweight : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ) ^ 3 * r z) :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ).pow 3).mul hr
  rcases
    upperHalfPlane_holomorphic_sq_eq_sq_dichotomy
      (hr.comp (Triangle.specialLinear_holomorphic Triangle.generatorTwoSL)) hweight
      (eisensteinSix_root_generatorTwo_sq hτc hrsq) with
    hpos | hneg
  · exact Or.inl (congrFun hpos)
  · right
    intro z
    simpa only [Function.comp_apply, Pi.neg_apply, neg_mul] using congrFun hneg z

theorem SpecialPeriods.holomorphic_simple_zero_not_generatorTwo_negative {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (horder : analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ¬(∀ z, r (Triangle.generatorTwoSL • z) = -(τ z : ℂ) ^ 3 * r z) := by
  intro hneg
  let R : ℂ → ℂ := r ∘ UpperHalfPlane.ofComplex
  let T : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let B : ℂ → ℂ := fun z => ((Triangle.generatorTwoSL • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  let c : ℂ := (Triangle.centerTwo : ℂ)
  have hRA : AnalyticAt ℂ R c :=
    (UpperHalfPlane.contMDiffAt_iff.mp (hr Triangle.centerTwo)).analyticAt
  have hTA : AnalyticAt ℂ T c :=
    (UpperHalfPlane.contMDiffAt_iff.mp
        ((UpperHalfPlane.contMDiff_coe.comp hτ) Triangle.centerTwo)).analyticAt
  have hRorder : analyticOrderAt R c = 1 := horder
  have hRzero : R c = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [hRorder]; exact one_ne_zero)
  have hdOrder : analyticOrderAt (deriv R) c = 0 :=
    analyticOrderAt_deriv_of_pos hRA (n := 0) (by simpa using hRorder)
  have hd : deriv R c ≠ 0 := hRA.deriv.analyticOrderAt_eq_zero.mp hdOrder
  have hBc : B c = c := by
    dsimp only [B, c]
    rw [UpperHalfPlane.ofComplex_apply, Triangle.generatorTwo_fix]
  have hTc : T c = Complex.I := by
    dsimp only [T, c]
    rw [UpperHalfPlane.ofComplex_apply, (tau_covariant_values hτc).2]
    rfl
  have hB : HasDerivAt B (-Complex.I) c := Triangle.generatorTwo_hasStrictDerivAt.hasDerivAt
  have hRder : HasDerivAt R (deriv R c) (B c) := by
    rw [hBc]
    exact hRA.differentiableAt.hasDerivAt
  have hleft :
    HasDerivAt (fun z : ℂ => r (Triangle.generatorTwoSL • UpperHalfPlane.ofComplex z))
      (deriv R c * -Complex.I) c := by
    simpa only [Function.comp_def, R, B, UpperHalfPlane.ofComplex_apply] using hRder.comp c hB
  have hright : HasDerivAt (fun z : ℂ => -(T z) ^ 3 * R z) _ c :=
    ((hTA.differentiableAt.hasDerivAt.pow 3).neg).mul hRA.differentiableAt.hasDerivAt
  have hright' : HasDerivAt (fun z : ℂ => -(T z) ^ 3 * R z) (Complex.I * deriv R c) c := by
    simpa [hRzero, hTc, Complex.I_sq, pow_succ] using hright
  have hfun :
    (fun z : ℂ => r (Triangle.generatorTwoSL • UpperHalfPlane.ofComplex z)) =
      (fun z : ℂ => -(T z) ^ 3 * R z) := by
    funext z
    exact hneg (UpperHalfPlane.ofComplex z)
  rw [hfun] at hleft
  have heq := hleft.unique hright'
  have hI : -Complex.I = Complex.I := by
    apply mul_right_cancel₀ hd
    simpa only [mul_comm] using heq
  have him := congrArg Complex.im hI
  norm_num at him

theorem SpecialPeriods.eisensteinSix_root_generatorTwo {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z))
    (horder : analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∀ z, r (Triangle.generatorTwoSL • z) = (τ z : ℂ) ^ 3 * r z := by
  rcases eisensteinSix_root_generatorTwo_dichotomy hτ hτc hr hrsq with hpos | hneg
  · exact hpos
  · exact (holomorphic_simple_zero_not_generatorTwo_negative hτ hτc hr horder hneg).elim

theorem SpecialPeriods.MuGenerator.modularForm_generatorOne {τ : ℍ → ℍ} {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hτc : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    f (τ (SpecialPeriods.Triangle.generatorOneSL • z)) = (τ z : ℂ) ^ k * f (τ z) := by
  have hτg :
    τ (SpecialPeriods.Triangle.generatorOneSL • z) = (ModularGroup.T * ModularGroup.S) • τ z := by
    apply UpperHalfPlane.ext
    rw [← SpecialPeriods.modularRhoAction_coe]
    exact hτc.1 z
  have hd : UpperHalfPlane.denom (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) (τ z) = (τ z : ℂ) :=
    by
    have h10 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [ModularGroup.denom_apply, h10, h11]
    simp
  rw [hτg, SpecialPeriods.levelOne_transform, hd]

theorem SpecialPeriods.MuGenerator.modularForm_generatorTwo {τ : ℍ → ℍ} {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hτc : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    f (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) = (τ z : ℂ) ^ k * f (τ z) := by
  have hτg : τ (SpecialPeriods.Triangle.generatorTwoSL • z) = ModularGroup.S • τ z := by
    apply UpperHalfPlane.ext
    rw [← SpecialPeriods.modularIAction_coe]
    exact hτc.2 z
  rw [hτg, SpecialPeriods.levelOne_transform, ModularGroup.denom_S]

theorem SpecialPeriods.MuGenerator.triangle_invariant_of_generators (f : ℍ → ℂ)
    (h₁ : ∀ z, f (SpecialPeriods.Triangle.generatorOneSL • z) = f z)
    (h₂ : ∀ z, f (SpecialPeriods.Triangle.generatorTwoSL • z) = f z)
    (g : SpecialPeriods.TriangleGroup) :
    ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z := by
  let := SpecialPeriods.triangleGeometricAction
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    trivial
  change ∀ z, f (g • z) = f z
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · intro z
      change
        f (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z) =
          f z
      simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] using h₁ z
    · intro z
      change
        f (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z) =
          f z
      simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply] using h₂ z
  | one => intro z; rw [one_smul]
  | mul g h _ _ ihg ihh => intro z; rw [SemigroupAction.mul_smul, ihg, ihh]
  | inv g _ ih =>
    intro z
    simpa only [smul_inv_smul] using (ih (g⁻¹ • z)).symm

theorem SpecialPeriods.MuGenerator.Root.generator_generatorOne {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hτc : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    r.generator (SpecialPeriods.Triangle.generatorOneSL • z) = -r.generator z / (τ z : ℂ) := by
  have h4 :
    ModularForm.E₄ (τ (SpecialPeriods.Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ 4 * ModularForm.E₄ (τ z) := by
    simpa only [zpow_ofNat] using
      SpecialPeriods.MuGenerator.modularForm_generatorOne ModularForm.E₄ hτc z
  have hD :
    ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ 12 * ModularForm.discriminant (τ z) := by
    have h :=
      SpecialPeriods.MuGenerator.modularForm_generatorOne
        (CuspForm.discriminant : ModularForm 𝒮ℒ 12) hτc z
    change
      ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorOneSL • z)) =
        (τ z : ℂ) ^ (12 : ℤ) * ModularForm.discriminant (τ z) at h
    simpa only [zpow_ofNat] using h
  rw [generator, h4, hD,
    SpecialPeriods.eisensteinSix_root_generatorOne hτ hτc r.holomorphic r.square z]
  dsimp only [generator]
  field_simp [(τ z).ne_zero, ModularForm.discriminant_ne_zero (τ z)]

theorem SpecialPeriods.MuGenerator.Root.generator_generatorTwo {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hτc : SpecialPeriods.TauCovariant τ)
    (horder :
      analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (z : ℍ) :
    r.generator (SpecialPeriods.Triangle.generatorTwoSL • z) = r.generator z / (τ z : ℂ) := by
  have h4 :
    ModularForm.E₄ (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ 4 * ModularForm.E₄ (τ z) := by
    simpa only [zpow_ofNat] using
      SpecialPeriods.MuGenerator.modularForm_generatorTwo ModularForm.E₄ hτc z
  have hD :
    ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ 12 * ModularForm.discriminant (τ z) := by
    have h :=
      SpecialPeriods.MuGenerator.modularForm_generatorTwo
        (CuspForm.discriminant : ModularForm 𝒮ℒ 12) hτc z
    change
      ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) =
        (τ z : ℂ) ^ (12 : ℤ) * ModularForm.discriminant (τ z) at h
    simpa only [zpow_ofNat] using h
  rw [generator, h4, hD,
    SpecialPeriods.eisensteinSix_root_generatorTwo hτ hτc r.holomorphic r.square horder z]
  dsimp only [generator]
  field_simp [(τ z).ne_zero, ModularForm.discriminant_ne_zero (τ z)]

theorem SpecialPeriods.MuGenerator.scalar_analyticAt {f : ℍ → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (a : ℍ) : AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp (hf.mdifferentiable (by simp))).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos)

theorem SpecialPeriods.MuGenerator.homogeneous_centerOne_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    ν SpecialPeriods.Triangle.centerOne = 0 := by
  have he := hν₁ SpecialPeriods.Triangle.centerOne
  rw [SpecialPeriods.Triangle.generatorOne_fix] at he
  have hmul :
    ν SpecialPeriods.Triangle.centerOne * (τ SpecialPeriods.Triangle.centerOne : ℂ) =
      -ν SpecialPeriods.Triangle.centerOne :=
    (eq_div_iff (τ SpecialPeriods.Triangle.centerOne).ne_zero).mp he
  have hz :
    ν SpecialPeriods.Triangle.centerOne * ((τ SpecialPeriods.Triangle.centerOne : ℂ) + 1) = 0 := by
    calc
      _ =
          ν SpecialPeriods.Triangle.centerOne * (τ SpecialPeriods.Triangle.centerOne : ℂ) +
            ν SpecialPeriods.Triangle.centerOne := by ring
      _ = 0 := by rw [hmul]; ring
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at hi
  exact (τ SpecialPeriods.Triangle.centerOne).im_ne_zero hi

theorem SpecialPeriods.MuGenerator.homogeneous_centerTwo_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) :
    ν SpecialPeriods.Triangle.centerTwo = 0 := by
  have he := hν₂ SpecialPeriods.Triangle.centerTwo
  rw [SpecialPeriods.Triangle.generatorTwo_fix] at he
  have hmul :
    ν SpecialPeriods.Triangle.centerTwo * (τ SpecialPeriods.Triangle.centerTwo : ℂ) =
      ν SpecialPeriods.Triangle.centerTwo :=
    (eq_div_iff (τ SpecialPeriods.Triangle.centerTwo).ne_zero).mp he
  have hz :
    ν SpecialPeriods.Triangle.centerTwo * ((τ SpecialPeriods.Triangle.centerTwo : ℂ) - 1) = 0 := by
    calc
      _ =
          ν SpecialPeriods.Triangle.centerTwo * (τ SpecialPeriods.Triangle.centerTwo : ℂ) -
            ν SpecialPeriods.Triangle.centerTwo := by ring
      _ = 0 := by rw [hmul]; ring
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
  exact (τ SpecialPeriods.Triangle.centerTwo).im_ne_zero hi

theorem SpecialPeriods.MuGenerator.homogeneous_fixed_derivative_identity {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (g : SL(2, ℝ)) (a : ℍ) (c : ℂ)
    (hfix : g • a = a) (hzero : ν a = 0) (hlaw : ∀ z : ℍ, ν (g • z) * (τ z : ℂ) = c * ν z) :
    (deriv (ν ∘ UpperHalfPlane.ofComplex) (a : ℂ) * SpecialPeriods.Triangle.slMultiplier g a) *
        (τ a : ℂ) =
      c * deriv (ν ∘ UpperHalfPlane.ofComplex) (a : ℂ) := by
  let V : ℂ → ℂ := ν ∘ UpperHalfPlane.ofComplex
  let T : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let A : ℂ → ℂ := fun z => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  have hV := (scalar_analyticAt hν a).differentiableAt.hasDerivAt
  have hTa := scalar_analyticAt (UpperHalfPlane.contMDiff_coe.comp hτ) a
  have hT := hTa.differentiableAt.hasDerivAt
  have hA : HasDerivAt A (SpecialPeriods.Triangle.slMultiplier g a) (a : ℂ) :=
    (SpecialPeriods.Triangle.sl_hasStrictDerivAt_smul g a).hasDerivAt
  have hAa : A (a : ℂ) = (a : ℂ) := by simp [A, hfix]
  have hVo : HasDerivAt V (deriv V (a : ℂ)) (A (a : ℂ)) := by
    rw [hAa]
    exact hV
  have hcomp :
    HasDerivAt (fun z : ℂ => ν (g • UpperHalfPlane.ofComplex z))
      (deriv V (a : ℂ) * SpecialPeriods.Triangle.slMultiplier g a) (a : ℂ) := by
    simpa only [V, A, Function.comp_def, UpperHalfPlane.ofComplex_apply] using hVo.comp (a : ℂ) hA
  have hprod :
    HasDerivAt (fun z : ℂ => ν (g • UpperHalfPlane.ofComplex z) * T z)
      ((deriv V (a : ℂ) * SpecialPeriods.Triangle.slMultiplier g a) * (τ a : ℂ)) (a : ℂ) := by
    simpa only [T, Function.comp_def, Pi.mul_def, UpperHalfPlane.ofComplex_apply, hfix, hzero,
      MulZeroClass.zero_mul, add_zero] using hcomp.mul hT
  have he : (fun z : ℂ => ν (g • UpperHalfPlane.ofComplex z) * T z) = fun z => c * V z := by
    funext z
    exact hlaw (UpperHalfPlane.ofComplex z)
  rw [he] at hprod
  exact hprod.unique (hV.const_mul c)

theorem SpecialPeriods.MuGenerator.homogeneous_centerOne_deriv_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 0 := by
  have hzero := homogeneous_centerOne_eq_zero hν₁
  have hprod :
    ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) * (τ z : ℂ) = (-1 : ℂ) * ν z := by
    intro z
    rw [hν₁, div_mul_cancel₀ _ (τ z).ne_zero, neg_one_mul]
  have hd :=
    homogeneous_fixed_derivative_identity hτ hν SpecialPeriods.Triangle.generatorOneSL
      SpecialPeriods.Triangle.centerOne (-1) SpecialPeriods.Triangle.generatorOne_fix hzero hprod
  rw [SpecialPeriods.Triangle.generatorOne_multiplier,
    (SpecialPeriods.tau_covariant_values hτc).1] at hd
  change
    (deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) *
          -SpecialPeriods.rho) *
        SpecialPeriods.rho =
      -1 * deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) at hd
  have hz :
    deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) *
        (SpecialPeriods.rho ^ 2 - 1) =
      0 := by linear_combination -hd
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  rw [SpecialPeriods.rho_sq] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
  exact SpecialPeriods.rho_im_pos.ne' hi

theorem SpecialPeriods.MuGenerator.exists_analytic_factor_of_order_le {ν f : ℂ → ℂ} {a : ℂ}
    {n : ℕ} (hν : AnalyticAt ℂ ν a) (hf : AnalyticAt ℂ f a)
    (hforder : analyticOrderAt f a = (n : ℕ∞)) (hνorder : (n : ℕ∞) ≤ analyticOrderAt ν a) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ ν =ᶠ[𝓝 a] fun z => f z * h z := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp hforder
  obtain ⟨v, hv, hνv⟩ := (natCast_le_analyticOrderAt hν).mp hνorder
  refine ⟨fun z => v z / u z, hv.div hu hu0, ?_⟩
  filter_upwards [hfu, hνv, hu.continuousAt.eventually_ne hu0] with z hfz hνz huz
  simp only [smul_eq_mul] at hfz hνz
  rw [hfz, hνz]
  field_simp

theorem SpecialPeriods.MuGenerator.homogeneous_centerOne_order_ge_two {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    (2 : ℕ∞) ≤
      analyticOrderAt (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) := by
  rw [show (2 : ℕ∞) = (2 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt hν _)]
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa only [iteratedDeriv_zero, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      homogeneous_centerOne_eq_zero hν₁
  · simpa only [iteratedDeriv_one] using homogeneous_centerOne_deriv_eq_zero hτ hτc hν hν₁

theorem SpecialPeriods.MuGenerator.homogeneous_centerTwo_order_ge_one {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) :
    (1 : ℕ∞) ≤
      analyticOrderAt (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) := by
  rw [show (1 : ℕ∞) = (1 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt hν _)]
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa only [iteratedDeriv_zero, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    homogeneous_centerTwo_eq_zero hν₂

theorem SpecialPeriods.MuGenerator.exists_division_at_centerOne {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hforder :
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) =
        2) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (SpecialPeriods.Triangle.centerOne : ℂ) ∧
        (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.centerOne : ℂ)] fun z =>
          (f ∘ UpperHalfPlane.ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt hν _) (scalar_analyticAt hf _) (n := 2)
    hforder (homogeneous_centerOne_order_ge_two hτ hτc hν hν₁)

theorem SpecialPeriods.MuGenerator.exists_division_at_centerTwo {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hforder :
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) =
        1) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (SpecialPeriods.Triangle.centerTwo : ℂ) ∧
        (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.centerTwo : ℂ)] fun z =>
          (f ∘ UpperHalfPlane.ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt hν _) (scalar_analyticAt hf _) (n := 1)
    hforder (homogeneous_centerTwo_order_ge_one hν hν₂)

def SpecialPeriods.MuGenerator.Homogeneous (τ : ℍ → ℍ) (F : ℍ → ℂ) : Prop :=
  (∀ z, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ)) ∧
    (∀ z, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))

theorem SpecialPeriods.MuGenerator.Root.generator_eq_zero_iff_normalized_source {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) {π : ℍ → ℂ}
    (hJ : ∀ z, SpecialPeriods.modularJ (τ z) = 1728 * π z) (z : ℍ) :
    r.generator z = 0 ↔ π z = 0 ∨ π z = 1 := by
  rw [r.generator_eq_zero_iff_modularJ, hJ z]
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  constructor
  · rintro (h | h)
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left h1728)
    · right
      apply mul_left_cancel₀ h1728
      simpa only [mul_one] using h
  · rintro (h | h)
    · left
      rw [h, MulZeroClass.mul_zero]
    · right
      rw [h, mul_one]

theorem SpecialPeriods.MuGenerator.Root.generator_homogeneous {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho₂ :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    SpecialPeriods.MuGenerator.Homogeneous τ r.generator :=
  ⟨r.generator_generatorOne hτ hc,
    r.generator_generatorTwo hτ hc (r.order_centerTwo_of_tau_order hτ hc ho₂)⟩

theorem SpecialPeriods.MuGenerator.exists_homogeneous_generator {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : SpecialPeriods.TauCovariant τ)
    (heven : FiniteEvenZeros τ)
    (ho₁ :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - SpecialPeriods.rho)
          (SpecialPeriods.Triangle.centerOne : ℂ) =
        1)
    (ho₂ :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    ∃ F : ℍ → ℂ,
      (∃ r : Root τ, F = r.generator) ∧
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧
          Homogeneous τ F ∧
            (∀ z,
                F z = 0 ↔
                  SpecialPeriods.modularJ (τ z) = 0 ∨ SpecialPeriods.modularJ (τ z) = 1728) ∧
              analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerOne : ℂ) =
                  2 ∧
                analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerTwo : ℂ) =
                  1 := by
  let r := root τ (hτ.mdifferentiable (by simp)) heven
  exact
    ⟨r.generator, ⟨r, rfl⟩, r.generator_holomorphic hτ, r.generator_homogeneous hτ hc ho₂,
      r.generator_eq_zero_iff_modularJ, r.generator_order_centerOne_of_tau_order hτ hc ho₁,
      r.generator_order_centerTwo_of_tau_order hτ hc ho₂⟩

theorem SpecialPeriods.MuGenerator.exists_homogeneous_generator_of_modular_equation {τ : ℍ → ℍ}
    {J : ℍ → ℂ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : SpecialPeriods.TauCovariant τ)
    (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = J a)
    (hzero : ∀ a : ℍ, J a = 0 → analyticOrderAt (J ∘ UpperHalfPlane.ofComplex) (a : ℂ) = 3)
    (h1728 :
      ∀ a : ℍ,
        J a = 1728 →
          analyticOrderAt (fun z : ℂ => J (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) = 4) :
    ∃ F : ℍ → ℂ,
      (∃ r : Root τ, F = r.generator) ∧
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧
          Homogeneous τ F ∧
            (∀ z, F z = 0 ↔ J z = 0 ∨ J z = 1728) ∧
              analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerOne : ℂ) =
                  2 ∧
                analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerTwo : ℂ) =
                  1 := by
  have hτd := hτ.mdifferentiable (by simp)
  have heven : FiniteEvenZeros τ :=
    finiteEvenZeros_of_modular_equation hτd hJ
      (fun a ha => ⟨1, by simpa only [Nat.mul_one, Nat.cast_ofNat] using h1728 a ha⟩)
  have hJ₁ : J SpecialPeriods.Triangle.centerOne = 0 := by
    rw [← hJ, (SpecialPeriods.tau_covariant_values hc).1, SpecialPeriods.modularJ_rhoPoint]
  have hJ₂ : J SpecialPeriods.Triangle.centerTwo = 1728 := by
    rw [← hJ, (SpecialPeriods.tau_covariant_values hc).2, SpecialPeriods.modularJ_I]
  have ho₁ :=
    SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_zero hτd hJ (a :=
      SpecialPeriods.Triangle.centerOne) (n := 1) hJ₁
      (by
        simpa only [Nat.mul_one, Nat.cast_ofNat] using
          hzero SpecialPeriods.Triangle.centerOne hJ₁)
  rw [(SpecialPeriods.tau_covariant_values hc).1, SpecialPeriods.coe_rhoPoint] at ho₁
  have ho₂ :=
    SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_1728 hτd hJ (a :=
      SpecialPeriods.Triangle.centerTwo) (n := 2) hJ₂
      (by simpa using h1728 SpecialPeriods.Triangle.centerTwo hJ₂)
  rw [(SpecialPeriods.tau_covariant_values hc).2, UpperHalfPlane.coe_I] at ho₂
  obtain ⟨F, hFroot, hF, hFc, hFzero, hF₁, hF₂⟩ :=
    exists_homogeneous_generator hτ hc heven ho₁ ho₂
  exact ⟨F, hFroot, hF, hFc, fun z => by rw [hFzero z, hJ z], hF₁, hF₂⟩

def SpecialPeriods.MuTorsor.AffineCocycle.linearPart (c : SpecialPeriods.MuTorsor.AffineCocycle) :
    SpecialPeriods.MuTorsor.AffineCocycle
    where
  scale := c.scale
  shift _ _ := 0
  scale_one := c.scale_one
  shift_one _ := rfl
  scale_mul := c.scale_mul
  shift_mul _ _ _ := by simp
  scale_holomorphic := c.scale_holomorphic
  shift_holomorphic _ := contMDiff_const

@[simp]
theorem SpecialPeriods.MuTorsor.AffineCocycle.linearPart_fibreMap
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u : ℂ) : c.linearPart.fibreMap g z u = (c.scale g z : ℂ) * u := by exact add_zero _

theorem SpecialPeriods.MuTorsor.homogeneous_scale_law {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {F : ℍ → ℂ}
    (hF : SpecialPeriods.MuGenerator.Homogeneous τ F) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    F (SpecialPeriods.triangleGeometricRepresentation g z) =
      ((cocycle hτ hτa).scale g z : ℂ) * F z := by
  let K := (cocycle hτ hτa).linearPart.sectionStabilizer F
  have h₁ : SpecialPeriods.triangleGenerator₁ ∈ K := by
    intro w
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      AffineCocycle.linearPart_fibreMap, cocycle_scale_generator₁_val, hF.1 w]
    ring
  have h₂ : SpecialPeriods.triangleGenerator₂ ∈ K := by
    intro w
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
      AffineCocycle.linearPart_fibreMap, cocycle_scale_generator₂_val, hF.2 w]
    ring
  have hle :
    Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) ≤
      K :=
    (Subgroup.closure_le _).mpr
      (by
        intro x hx
        rcases hx with rfl | rfl
        · exact h₁
        · exact h₂)
  rw [SpecialPeriods.triangle_generators_generate] at hle
  have hz := hle (Subgroup.mem_top g) z
  simpa only [AffineCocycle.linearPart_fibreMap] using hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
def SpecialPeriods.MuTorsor.descentDomain (V : TopologicalSpace.Opens ℍ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  LocalOrbitQuotient.imageOpen (G := SpecialPeriods.TriangleGroup) V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.project_mem_descentDomain (V : TopologicalSpace.Opens ℍ) {z : ℍ}
    (hz : z ∈ V) : SpecialPeriods.triangleOrbitProjection z ∈ descentDomain V :=
  ⟨z, hz, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
def SpecialPeriods.MuTorsor.descentProjection (V : TopologicalSpace.Opens ℍ) :
    V → descentDomain V :=
  LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup) V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.descentProjection_isOpenQuotientMap
    (V : TopologicalSpace.Opens ℍ) : IsOpenQuotientMap (descentProjection V) :=
  LocalOrbitQuotient.imageProjection_isOpenQuotientMap V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
def SpecialPeriods.MuTorsor.orbitRepresentative (q : SpecialPeriods.TriangleOrbitSpace) : ℍ :=
  (SpecialPeriods.triangleOrbitProjection_surjective q).choose

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
@[simp]
theorem SpecialPeriods.MuTorsor.project_orbitRepresentative
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOrbitProjection (orbitRepresentative q) = q :=
  (SpecialPeriods.triangleOrbitProjection_surjective q).choose_spec

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
def SpecialPeriods.MuTorsor.descend (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (q : SpecialPeriods.TriangleOrbitSpace) : ℂ := by
  classical exact if orbitRepresentative q ∈ V then f (orbitRepresentative q) else 0

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.project_mem_descentDomain_iff (V : TopologicalSpace.Opens ℍ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (z : ℍ) : SpecialPeriods.triangleOrbitProjection z ∈ descentDomain V ↔ z ∈ V := by
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp h
    exact (hV g z).mp (hg ▸ hw)
  · exact project_mem_descentDomain V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.orbitRepresentative_mem_iff (V : TopologicalSpace.Opens ℍ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (q : SpecialPeriods.TriangleOrbitSpace) : orbitRepresentative q ∈ V ↔ q ∈ descentDomain V := by
  rw [← project_mem_descentDomain_iff V hV, project_orbitRepresentative]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.descend_project (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    {z : ℍ} (hz : z ∈ V) : descend V f (SpecialPeriods.triangleOrbitProjection z) = f z := by
  have hr : orbitRepresentative (SpecialPeriods.triangleOrbitProjection z) ∈ V :=
    (orbitRepresentative_mem_iff V hV _).mpr (project_mem_descentDomain V hz)
  obtain ⟨g, hg⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff
          (orbitRepresentative (SpecialPeriods.triangleOrbitProjection z)) z).mp
      (project_orbitRepresentative (SpecialPeriods.triangleOrbitProjection z))
  simp only [descend, if_pos hr]
  rw [← hg]
  exact hInv g z hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.descend_continuousOn (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContinuousOn f V) : ContinuousOn (descend V f) (descentDomain V) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply (descentProjection_isOpenQuotientMap V).isQuotientMap.continuous_iff.mpr
  have he : (fun q : descentDomain V => descend V f q) ∘ descentProjection V = fun z : V => f z :=
    by
    funext z
    exact descend_project V f hV hInv z.property
  change Continuous ((fun q : descentDomain V => descend V f q) ∘ descentProjection V)
  rw [he]
  exact hf.domRestrict

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.descend_contMDiffAt_of_not_elliptic (V : TopologicalSpace.Opens ℍ)
    (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) {q : SpecialPeriods.TriangleOrbitSpace}
    (hq : q ∈ descentDomain V) (h₁ : q ≠ SpecialPeriods.triangleOrbitCenterOne)
    (h₂ : q ≠ SpecialPeriods.triangleOrbitCenterTwo) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) q := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hp := SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic h₁ h₂
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f ∘ SpecialPeriods.triangleOrbitProjection) z :=
    by
    apply (hf.contMDiffAt (V.isOpen.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [V.isOpen.mem_nhds hz] with w hw
    exact descend_project V f hV hInv hw
  have h :=
    hcomp.comp_of_eq hp.localInverse_contMDiffAt
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with r hr
  change descend V f r = descend V f (SpecialPeriods.triangleOrbitProjection (hp.localInverse r))
  rw [show SpecialPeriods.triangleOrbitProjection (hp.localInverse r) = r from hr]

theorem SpecialPeriods.MuTorsor.contMDiffAt_of_continuousAt_of_eventually_punctured {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} {x : M}
    (hc : ContinuousAt f x) (hd : ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hxe : e x ∈ e.target := e.map_source hx
  have hc' : ContinuousAt (f ∘ e.symm) (e x) :=
    (e.symm.continuousAt_iff_continuousAt_comp_right hx).mp hc
  have hp : Filter.Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(e.tendsto_symm hx).mono_left nhdsWithin_le_nhds, ?_⟩
    simpa only [e.left_inv hx, Set.mem_compl_iff, Set.mem_singleton_iff] using
      e.symm.eventually_ne_nhdsWithin hxe
  have hd' : ∀ᶠ z in 𝓝[≠] e x, DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [hp.eventually hd,
      eventually_nhdsWithin_of_eventually_nhds (e.open_target.eventually_mem hxe)] with z hz hzt
    have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) x) hzt
    exact (hz.comp z he).contDiffAt.differentiableAt (by simp)
  have ha := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd' hc'
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) x) hx
  apply (ha.contDiffAt.contMDiffAt.comp x he).congr_of_eventuallyEq
  filter_upwards [e.eventually_left_inverse hx] with y hy
  exact (congrArg f hy).symm

theorem SpecialPeriods.MuTorsor.contMDiffOn_of_continuousOn_of_finite {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} [T1Space M]
    {U s : Set M} (hU : IsOpen U) (hs : s.Finite) (hc : ContinuousOn f U)
    (hd : ∀ x ∈ U, x ∉ s → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply
    contMDiffAt_of_continuousAt_of_eventually_punctured ((hc x hx).continuousAt (hU.mem_nhds hx))
  have hclosed : IsClosed (s \ { x }) := (hs.subset Set.sdiff_subset).isClosed
  have havoid : (s \ { x })ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx), nhdsWithin_le_nhds havoid,
    self_mem_nhdsWithin] with y hy hyavoid hyne
  apply hd y hy
  intro hys
  exact hyavoid ⟨hys, hyne⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.instIsManifold1 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold1 in
theorem SpecialPeriods.MuTorsor.descend_holomorphic (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) (descentDomain V) := by
  apply
    contMDiffOn_of_continuousOn_of_finite (s :=
      { SpecialPeriods.triangleOrbitCenterOne, SpecialPeriods.triangleOrbitCenterTwo })
      (descentDomain V).isOpen
      ((Set.finite_singleton SpecialPeriods.triangleOrbitCenterTwo).insert
        SpecialPeriods.triangleOrbitCenterOne)
      (descend_continuousOn V f hV hInv hf.continuousOn)
  intro q hq hnot
  have h₁ : q ≠ SpecialPeriods.triangleOrbitCenterOne := fun h => hnot (by simp [h])
  have h₂ : q ≠ SpecialPeriods.triangleOrbitCenterTwo := fun h => hnot (by simp [h])
  exact descend_contMDiffAt_of_not_elliptic V f hV hInv hf hq h₁ h₂

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold1 in
theorem SpecialPeriods.MuTorsor.descend_holomorphicAt (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) {q : SpecialPeriods.TriangleOrbitSpace}
    (hq : q ∈ descentDomain V) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) q :=
  (descend_holomorphic V f hV hInv hf).contMDiffAt ((descentDomain V).isOpen.mem_nhds hq)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.finiteDescentDomain
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) : TopologicalSpace.Opens ℂ :=
  ⟨finiteOrbitInverse π hπ ⁻¹'
      (SpecialPeriods.MuTorsor.descentDomain V : Set SpecialPeriods.TriangleOrbitSpace),
    (SpecialPeriods.MuTorsor.descentDomain V).isOpen.preimage
      (finiteOrbitInverse_holomorphic π hπ).continuous⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.finiteDescent
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ) : ℂ → ℂ :=
  SpecialPeriods.MuTorsor.descend V f ∘ finiteOrbitInverse π hπ

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteDescentDomain_projection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (z : ℍ) : finiteProjection π z ∈ finiteDescentDomain π hπ V ↔ z ∈ V := by
  change
    finiteOrbitInverse π hπ (finiteOrbitCoordinate π (SpecialPeriods.triangleOrbitProjection z)) ∈
        SpecialPeriods.MuTorsor.descentDomain V ↔
      z ∈ V
  rw [finiteOrbitInverse_coordinate]
  exact SpecialPeriods.MuTorsor.project_mem_descentDomain_iff V hV z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteDescent_projection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    {z : ℍ} (hz : z ∈ V) : finiteDescent π hπ V f (finiteProjection π z) = f z := by
  simp only [finiteDescent, finiteProjection, Function.comp_apply, finiteOrbitInverse_coordinate]
  exact SpecialPeriods.MuTorsor.descend_project V f hV hInv hz

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteDescent_analytic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) :
    AnalyticOnNhd ℂ (finiteDescent π hπ V f) (finiteDescentDomain π hπ V) :=
  analyticOnNhd_finite_pullback π hπ (SpecialPeriods.MuTorsor.descentDomain V)
    (SpecialPeriods.MuTorsor.descend_holomorphic V f hV hInv hf)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.overlap (i j : Cover.Index) : TopologicalSpace.Opens ℍ :=
  ⟨(Cover.patch i).saturation ∩ (Cover.patch j).saturation,
    (Cover.patch i).saturation_isOpen.inter (Cover.patch j).saturation_isOpen⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.overlap_invariant (i j : Cover.Index)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ overlap i j ↔ z ∈ overlap i j := by
  change (_ ∈ (Cover.patch i).saturation ∧ _ ∈ (Cover.patch j).saturation) ↔ _
  rw [(Cover.patch i).saturation_invariant, (Cover.patch j).saturation_invariant]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.overlapQuotient {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ) (i j : Cover.Index) (z : ℍ) : ℂ :=
  (localSection hτ hτa i z - localSection hτ hτa j z) / F z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.overlapQuotient_invariant {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F) (i j : Cover.Index)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (hz : z ∈ overlap i j) :
    overlapQuotient hτ hτa F i j (SpecialPeriods.triangleGeometricRepresentation g z) =
      overlapQuotient hτ hτa F i j z := by
  unfold overlapQuotient
  rw [localSection_equivariant hτ hτa i g z hz.1, localSection_equivariant hτ hτa j g z hz.2,
    AffineCocycle.fibreMap_sub, homogeneous_scale_law hτ hτa hFc]
  exact mul_div_mul_left _ _ (cocycle hτ hτa |>.scale g z).ne_zero

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.overlap_generator_ne_zero (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    {i j : Cover.Index} (hij : i ≠ j) {z : ℍ} (hz : z ∈ overlap i j) : F z ≠ 0 := by
  have hr := Cover.distinct_saturation_overlap_subset_regularLocus hij hz
  have hq :=
    (SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mp
      ((SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mpr hr)
  intro hf
  rcases (hFzero z).mp hf with h | h
  · exact hq.1 h
  · exact hq.2 h

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.overlapQuotient_holomorphic {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (i j : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (overlapQuotient hτ hτa F i j) (overlap i j) := by
  by_cases hij : i = j
  · subst j
    have he : overlapQuotient hτ hτa F i i = fun _ => 0 := by
      funext z
      simp only [overlapQuotient, sub_self, zero_div]
    rw [he]
    exact contMDiffOn_const
  · have h₁ :=
      (localSection_holomorphic hτ hτa i).mono
        (show (overlap i j : Set ℍ) ⊆ (Cover.patch i).saturation from Set.inter_subset_left)
    have h₂ :=
      (localSection_holomorphic hτ hτa j).mono
        (show (overlap i j : Set ℍ) ⊆ (Cover.patch j).saturation from Set.inter_subset_right)
    exact (h₁.sub h₂).div₀ hF.contMDiffOn (fun z hz => overlap_generator_ne_zero F hFzero hij hz)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.localSection_eq_at_generator_zero {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (i j : Cover.Index) (z : ℍ) (hi : z ∈ (Cover.patch i).saturation)
    (hj : z ∈ (Cover.patch j).saturation) (hz : F z = 0) :
    localSection hτ hτa i z = localSection hτ hτa j z := by
  have hij : i = j := by
    by_contra h
    exact overlap_generator_ne_zero F hFzero h ⟨hi, hj⟩ hz
  rw [hij]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.finiteProjection_mem_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : Cover.Index) (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i ↔
      z ∈ (Cover.patch i).saturation :=
  (SpecialPeriods.BetaTorsor.finiteProjection_mem_pullback π hπ (Cover.compactPatch i) z).trans
    (Cover.compactifiedProjection_mem_compactPatch i z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.finiteProjection_preimage_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : Cover.Index) :
    SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ) =
      (Cover.patch i).saturation := by
  ext z
  exact finiteProjection_mem_patch π hπ i z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.finiteDescentDomain_overlap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : Cover.Index) :
    (SpecialPeriods.BetaTorsor.finiteDescentDomain π hπ (overlap i j) : Set ℂ) =
      (Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j := by
  ext w
  obtain ⟨z, rfl⟩ := SpecialPeriods.BetaTorsor.finiteProjection_surjective π hπ w
  change
    SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.BetaTorsor.finiteDescentDomain π hπ (overlap i j) ↔
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i ∧
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j
  rw [SpecialPeriods.BetaTorsor.finiteDescentDomain_projection π hπ (overlap i j)
      (overlap_invariant i j)]
  rw [finiteProjection_mem_patch π hπ, finiteProjection_mem_patch π hπ]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.MuTorsor.descendedOverlap {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : Cover.Index) : ℂ → ℂ :=
  SpecialPeriods.BetaTorsor.finiteDescent π hπ (overlap i j) (overlapQuotient hτ hτa F i j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.descendedOverlap_projection {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F) (i j : Cover.Index) (z : ℍ)
    (hi : SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i)
    (hj : SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j) :
    descendedOverlap hτ hτa F π hπ i j (SpecialPeriods.BetaTorsor.finiteProjection π z) =
      (localSection hτ hτa i z - localSection hτ hτa j z) / F z := by
  exact
    SpecialPeriods.BetaTorsor.finiteDescent_projection π hπ (overlap i j)
      (overlapQuotient hτ hτa F i j) (overlap_invariant i j)
      (overlapQuotient_invariant hτ hτa F hFc i j)
      ⟨(finiteProjection_mem_patch π hπ i z).mp hi, (finiteProjection_mem_patch π hπ j z).mp hj⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.descendedOverlap_analytic {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F)
    (i j : Cover.Index) :
    AnalyticOnNhd ℂ (descendedOverlap hτ hτa F π hπ i j)
      ((Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j) := by
  rw [← finiteDescentDomain_overlap π hπ]
  exact
    SpecialPeriods.BetaTorsor.finiteDescent_analytic π hπ (overlap i j)
      (overlapQuotient hτ hτa F i j) (overlap_invariant i j)
      (overlapQuotient_invariant hτ hτa F hFc i j)
      (overlapQuotient_holomorphic hτ hτa F hFzero hF i j)

theorem SpecialPeriods.MuTorsor.Gluing.descended_quotient_cocycle {X ι : Type*} {p : X → ℂ}
    (hp : Function.Surjective p) {U : ι → Set ℂ} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j → h i j (p z) = (μ i z - μ j z) / F z) :
    ∀ i j k w, w ∈ U i → w ∈ U j → w ∈ U k → h i j w + h j k w = h i k w := by
  intro i j k w hi hj hk
  obtain ⟨z, rfl⟩ := hp w
  rw [hq i j z hi hj, hq j k z hj hk, hq i k z hi hk]
  ring

theorem SpecialPeriods.MuTorsor.Gluing.difference_eq_mul_quotient {X ι : Type*} {p : X → ℂ}
    {U : ι → Set ℂ} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j → h i j (p z) = (μ i z - μ j z) / F z)
    (hz : ∀ i j z, p z ∈ U i → p z ∈ U j → F z = 0 → μ i z = μ j z) (i j : ι) (z : X)
    (hi : p z ∈ U i) (hj : p z ∈ U j) : μ i z - μ j z = F z * h i j (p z) := by
  rw [hq i j z hi hj]
  by_cases hF : F z = 0
  · rw [hz i j z hi hj hF, sub_self, zero_div, MulZeroClass.mul_zero]
  · exact (mul_div_cancel₀ (μ i z - μ j z) hF).symm

def SpecialPeriods.MuTorsor.Gluing.correctedGlue {X ι : Type*} (p : X → ℂ) (U : ι → Set ℂ)
    (hcover : ∀ w, ∃ i, w ∈ U i) (μ : ι → X → ℂ) (F : X → ℂ) {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R) (z : X) : ℂ :=
  μ (hcover (p z)).choose z - F z * s.localPart (hcover (p z)).choose (p z)

theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_eq {X ι : Type*} {p : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z)) {i : ι} {z : X}
    (hz : p z ∈ U i) : correctedGlue p U hcover μ F s z = μ i z - F z * s.localPart i (p z) := by
  let j := (hcover (p z)).choose
  have hj : p z ∈ U j := (hcover (p z)).choose_spec
  change μ j z - F z * s.localPart j (p z) = μ i z - F z * s.localPart i (p z)
  have hd := hdiff j i z hj hz
  have hs := s.equation j i (p z) hj hz
  linear_combination hd - F z * hs

theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_eventuallyEq {X ι : Type*}
    [TopologicalSpace X] {p : X → ℂ} (hp : Continuous p) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z)) {i : ι} {z : X}
    (hz : p z ∈ U i) :
    correctedGlue p U hcover μ F s =ᶠ[𝓝 z] fun w => μ i w - F w * s.localPart i (p w) := by
  filter_upwards [((hU i).preimage hp).mem_nhds hz] with w hw
  exact correctedGlue_eq s hdiff hw

theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_holomorphic {ι : Type*} {p : ℍ → ℂ}
    (hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω p) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → ℍ → ℂ}
    (hμ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (μ i) (p ⁻¹' U i)) {F : ℍ → ℂ}
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue p U hcover μ F s) := by
  intro z
  obtain ⟨i, hi⟩ := hcover (p z)
  have hm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (μ i) z :=
    (hμ i).contMDiffAt (((hU i).preimage hp.continuous).mem_nhds hi)
  have hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => s.localPart i (p w)) z :=
    (s.local_analytic i (p z) hi).contDiffAt.contMDiffAt.comp z (hp z)
  exact
    (hm.sub ((hF z).mul hs)).congr_of_eventuallyEq
      (correctedGlue_eventuallyEq hp.continuous hU s hdiff hi)

theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_affine_law {ι : Type*} {p : ℍ → ℂ}
    {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → ℍ → ℂ} {F : ℍ → ℂ} {h : ι → ι → ℂ → ℂ}
    {i₀ : ι} {R : ℝ} (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z))
    (c : SpecialPeriods.MuTorsor.AffineCocycle)
    (hp : ∀ g z, p (SpecialPeriods.triangleGeometricRepresentation g z) = p z)
    (hμ : ∀ i, c.EquivariantOn (μ i) (p ⁻¹' U i))
    (hF : ∀ g z, F (SpecialPeriods.triangleGeometricRepresentation g z) = (c.scale g z : ℂ) * F z)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    correctedGlue p U hcover μ F s (SpecialPeriods.triangleGeometricRepresentation g z) =
      c.fibreMap g z (correctedGlue p U hcover μ F s z) := by
  obtain ⟨i, hi⟩ := hcover (p z)
  have hig : p (SpecialPeriods.triangleGeometricRepresentation g z) ∈ U i := by rwa [hp g z]
  rw [correctedGlue_eq s hdiff hig, correctedGlue_eq s hdiff hi, hp g z, hμ i g z hi, hF g z]
  simp only [SpecialPeriods.MuTorsor.AffineCocycle.fibreMap]
  ring

theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_cusp {X ι : Type*} {p : X → ℂ}
    {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    {i₀ : ι} {R : ℝ} (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z))
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) {W : Set X} (hμ₀ : ∀ z ∈ W, μ i₀ z = 0) {z : X}
    (hz : z ∈ W) (hlarge : R < ‖p z‖) :
    correctedGlue p U hcover μ F s z = -F z * (p z)⁻¹ * s.infinityPart (p z)⁻¹ := by
  have hzU : p z ∈ U i₀ :=
    hRU
      (by
        simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hlarge.le)
  rw [correctedGlue_eq s hdiff hzU, hμ₀ z hz, s.atInfinity (p z) hlarge]
  ring

theorem SpecialPeriods.MuTorsor.Gluing.exists_corrected_gluing {ι : Type*} {p : ℍ → ℂ}
    (hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω p) (hps : Function.Surjective p) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i) {μ : ι → ℍ → ℂ}
    (hμ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (μ i) (p ⁻¹' U i)) {F : ℍ → ℂ}
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j → h i j (p z) = (μ i z - μ j z) / F z)
    (hz : ∀ i j z, p z ∈ U i → p z ∈ U j → F z = 0 → μ i z = μ j z) (i₀ : ι) {R : ℝ} (hR : 0 < R)
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue p U hcover μ F s) ∧
        ∀ i,
          Set.EqOn (correctedGlue p U hcover μ F s) (fun z => μ i z - F z * s.localPart i (p z))
            (p ⁻¹' U i) := by
  obtain ⟨s⟩ :=
    HolomorphicCousin.exists_negativeOne_holomorphic_cocycle_solution hU hcover hh
      (descended_quotient_cocycle hps hq) i₀ hR hRU
  have hd := difference_eq_mul_quotient hq hz
  exact ⟨s, correctedGlue_holomorphic hp hU hμ hF s hd, fun _ _ hi => correctedGlue_eq s hd hi⟩

def SpecialPeriods.MuTorsor.CuspRegular (f : ℍ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ,
    AnalyticAt ℂ M 0 ∧ ∀ᶠ z in UpperHalfPlane.atImInfty, f z = M (SpecialPeriods.Triangle.cuspQ z)

theorem SpecialPeriods.MuTorsor.CuspRegular.sub {f g : ℍ → ℂ}
    (hf : SpecialPeriods.MuTorsor.CuspRegular f) (hg : SpecialPeriods.MuTorsor.CuspRegular g) :
    SpecialPeriods.MuTorsor.CuspRegular (f - g) := by
  obtain ⟨M, hM, hfM⟩ := hf
  obtain ⟨N, hN, hgN⟩ := hg
  refine ⟨M - N, hM.sub hN, ?_⟩
  filter_upwards [hfM, hgN] with z hfz hgz
  simp only [Pi.sub_apply, hfz, hgz]

theorem SpecialPeriods.MuTorsor.factor_cusp_germ {ν F H : ℍ → ℂ} {v : ℂ → ℂ} (hνc : CuspRegular ν)
    (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0)
    (hF :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z))
    (hfac : ∀ z : ℍ, ν z = F z * H z) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
        g 0 = 0 ∧ ∀ᶠ z in UpperHalfPlane.atImInfty, H z = g (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨M, hM, hνM⟩ := hνc
  refine ⟨fun q => q * M q / v q, (analyticAt_id.mul hM).div hv hv0, by simp, ?_⟩
  have hvne : ∀ᶠ z in UpperHalfPlane.atImInfty, v (SpecialPeriods.Triangle.cuspQ z) ≠ 0 :=
    (SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds).eventually
      (hv.continuousAt.eventually_ne hv0)
  filter_upwards [hνM, hF, hvne] with z hνz hFz hvz
  apply (eq_div_iff hvz).mpr
  have he := hfac z
  rw [hνz, hFz] at he
  calc
    H z * v (SpecialPeriods.Triangle.cuspQ z) = v (SpecialPeriods.Triangle.cuspQ z) * H z :=
      mul_comm _ _
    _ =
        (SpecialPeriods.Triangle.cuspQ z * (SpecialPeriods.Triangle.cuspQ z)⁻¹) *
          (v (SpecialPeriods.Triangle.cuspQ z) * H z) := by
      rw [mul_inv_cancel₀ (SpecialPeriods.Triangle.cuspQ_ne_zero z), one_mul]
    _ =
        SpecialPeriods.Triangle.cuspQ z *
          ((SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z) * H z) := by
      ring
    _ = SpecialPeriods.Triangle.cuspQ z * M (SpecialPeriods.Triangle.cuspQ z) := by rw [← he]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.correctedGlue_cuspRegular
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {F : ℍ → ℂ}
    {h : Cover.Index → Cover.Index → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ Cover.finitePatch π Cover.cuspIndex)
    (s :
      HolomorphicCousin.NegativeOneCocycleSolution (fun i => (Cover.finitePatch π i : Set ℂ)) h
        Cover.cuspIndex R)
    (hdiff :
      ∀ i j z,
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i →
          SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j →
            localSection hτ hτa i z - localSection hτ hτa j z =
              F z * h i j (SpecialPeriods.BetaTorsor.finiteProjection π z))
    (hFpole :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    CuspRegular
      (Gluing.correctedGlue (SpecialPeriods.BetaTorsor.finiteProjection π)
        (fun i => (Cover.finitePatch π i : Set ℂ)) (Cover.exists_finitePatch π)
        (localSection hτ hτa) F s) := by
  obtain ⟨v, hv, _hv0, hFv⟩ := hFpole
  have hS : AnalyticAt ℂ s.infinityPart 0 :=
    s.infinity_analytic 0 (Metric.mem_ball_self (inv_pos.mpr hR))
  refine
    ⟨fun q => -v q * CuspCoordinates.tDivQ π q * s.infinityPart (CuspCoordinates.t π q),
      CuspCoordinates.analyticAt_correction π hπ hv hS, ?_⟩
  filter_upwards [hFv, CuspCoordinates.eventually_mem_horodisc SpecialPeriods.Triangle.width,
    CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R,
    CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ] with z hFz hz hlarge ht
  rw [Gluing.correctedGlue_cusp s hdiff hRU (fun z hz => localSection_cusp hτ hτa z hz) hz hlarge,
    hFz, ← ht]
  have hc :
    -((SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) *
        CuspCoordinates.t π (SpecialPeriods.Triangle.cuspQ z) =
      -v (SpecialPeriods.Triangle.cuspQ z) *
        CuspCoordinates.tDivQ π (SpecialPeriods.Triangle.cuspQ z) := by
    rw [CuspCoordinates.t_eq_mul_tDivQ π hπ]
    field_simp [SpecialPeriods.Triangle.cuspQ_ne_zero z]
  rw [hc]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.exists_holomorphic_affine_cuspRegular
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hFpole :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ μ : ℍ → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
        (∀ g z,
            μ (SpecialPeriods.triangleGeometricRepresentation g z) =
              (cocycle hτ hτa).fibreMap g z (μ z)) ∧
          (∀ z, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)) ∧
            (∀ z, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) ∧
              CuspRegular μ := by
  let U : Cover.Index → Set ℂ := fun i => Cover.finitePatch π i
  let h := descendedOverlap hτ hτa F π hπ
  have hlocal :
    ∀ i,
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' U i) := by
    intro i
    change
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ))
    rw [finiteProjection_preimage_patch π hπ]
    exact localSection_holomorphic hτ hτa i
  have hq :
    ∀ i j z,
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U i →
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U j →
          h i j (SpecialPeriods.BetaTorsor.finiteProjection π z) =
            (localSection hτ hτa i z - localSection hτ hτa j z) / F z :=
    descendedOverlap_projection hτ hτa F π hπ hFc
  have hz :
    ∀ i j z,
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U i →
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U j →
          F z = 0 → localSection hτ hτa i z = localSection hτ hτa j z := by
    intro i j z hi hj hzero
    exact
      localSection_eq_at_generator_zero hτ hτa F hFzero i j z
        ((finiteProjection_mem_patch π hπ i z).mp hi)
        ((finiteProjection_mem_patch π hπ j z).mp hj) hzero
  have hd := Gluing.difference_eq_mul_quotient hq hz
  obtain ⟨R, hR, hRU⟩ := Cover.finitePatch_cusp_contains_exterior π hπ
  obtain ⟨s, hs, _⟩ :=
    Gluing.exists_corrected_gluing (SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ)
      (SpecialPeriods.BetaTorsor.finiteProjection_surjective π hπ)
      (fun i => (Cover.finitePatch π i).isOpen) (Cover.exists_finitePatch π) hlocal hF
      (descendedOverlap_analytic hτ hτa F hFzero π hπ hF hFc) hq hz Cover.cuspIndex hR hRU
  let μ :=
    Gluing.correctedGlue (SpecialPeriods.BetaTorsor.finiteProjection π) U
      (Cover.exists_finitePatch π) (localSection hτ hτa) F s
  have hlocalLaw :
    ∀ i,
      (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' U i) := by
    intro i
    change
      (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ))
    rw [finiteProjection_preimage_patch π hπ]
    exact localSection_equivariant hτ hτa i
  have hμ :
    ∀ g z,
      μ (SpecialPeriods.triangleGeometricRepresentation g z) =
        (cocycle hτ hτa).fibreMap g z (μ z) :=
    Gluing.correctedGlue_affine_law s hd (cocycle hτ hτa)
      (SpecialPeriods.BetaTorsor.finiteProjection_invariant π) hlocalLaw
      (homogeneous_scale_law hτ hτa hFc)
  refine ⟨μ, hs, hμ, ?_, ?_, ?_⟩
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      cocycle_fibreMap_generator₁] using hμ SpecialPeriods.triangleGenerator₁ z
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
      cocycle_fibreMap_generator₂] using hμ SpecialPeriods.triangleGenerator₂ z
  · exact correctedGlue_cuspRegular π hπ hτ hτa hR hRU s hd hFpole

theorem SpecialPeriods.MuTorsor.Division.quotient_invariant {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    ν (SpecialPeriods.triangleGeometricRepresentation g z) /
        F (SpecialPeriods.triangleGeometricRepresentation g z) =
      ν z / F z := by
  apply SpecialPeriods.MuGenerator.triangle_invariant_of_generators (fun w => ν w / F w) _ _ g z
  · intro w
    rw [hν₁, hF₁, div_div_div_cancel_right₀ (τ w).ne_zero, neg_div_neg_eq]
  · intro w
    rw [hν₂, hF₂, div_div_div_cancel_right₀ (τ w).ne_zero]

theorem SpecialPeriods.MuTorsor.Division.zero_invariant {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    ν (SpecialPeriods.triangleGeometricRepresentation g z) = 0 ↔ ν z = 0 := by
  have h := quotient_invariant hν₁ hν₂ hν₁ hν₂ g z
  have hz :
    ν (SpecialPeriods.triangleGeometricRepresentation g z) /
          ν (SpecialPeriods.triangleGeometricRepresentation g z) =
        0 ↔
      ν z / ν z = 0 := by rw [h]
  simpa only [div_eq_zero_iff, or_self] using hz

theorem SpecialPeriods.MuTorsor.Division.zero_of_centerOneOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne) :
    ν z = 0 := by
  obtain ⟨g, hg⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerOne).mp hz
  rw [← hg]
  exact
    (zero_invariant hν₁ hν₂ g SpecialPeriods.Triangle.centerOne).mpr
      (SpecialPeriods.MuGenerator.homogeneous_centerOne_eq_zero hν₁)

theorem SpecialPeriods.MuTorsor.Division.zero_of_centerTwoOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo) :
    ν z = 0 := by
  obtain ⟨g, hg⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerTwo).mp hz
  rw [← hg]
  exact
    (zero_invariant hν₁ hν₂ g SpecialPeriods.Triangle.centerTwo).mpr
      (SpecialPeriods.MuGenerator.homogeneous_centerTwo_eq_zero hν₂)

theorem SpecialPeriods.MuTorsor.Division.zero_of_ellipticOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) {z : ℍ}
    (hz :
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
        SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo) :
    ν z = 0 :=
  hz.elim (zero_of_centerOneOrbit hν₁ hν₂) (zero_of_centerTwoOrbit hν₁ hν₂)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.ellipticNeighborhood_projection_eq_iff
    (j : Elliptic.Kind) (z : ℍ) (hz : z ∈ SpecialPeriods.Triangle.ellipticNeighborhood j) :
    SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.Triangle.ellipticOrbitCenter j ↔
      z = SpecialPeriods.Triangle.ellipticCenter j := by
  constructor
  · intro he
    obtain ⟨g, hg⟩ :=
      (SpecialPeriods.triangleOrbitProjection_eq_iff z
            (SpecialPeriods.Triangle.ellipticCenter j)).mp
        he
    have hr : g ∈ SpecialPeriods.Triangle.ellipticStabilizer j :=
      SpecialPeriods.Triangle.ellipticNeighborhood_return j g
        ⟨z,
          ⟨SpecialPeriods.Triangle.ellipticCenter j,
            SpecialPeriods.Triangle.ellipticCenter_mem_neighborhood j, hg⟩,
          hz⟩
    have hfix :
      SpecialPeriods.triangleGeometricRepresentation g
          (SpecialPeriods.Triangle.ellipticCenter j) =
        SpecialPeriods.Triangle.ellipticCenter j :=
      hr
    exact hg.symm.trans hfix
  · rintro rfl
    rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.ellipticNeighborhood_projection_ne_centers
    (j : Elliptic.Kind) (z : ℍ) (hz : z ∈ SpecialPeriods.Triangle.ellipticNeighborhood j)
    (hne : z ≠ SpecialPeriods.Triangle.ellipticCenter j) :
    SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterOne ∧
      SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterTwo := by
  have hself :
    SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.Triangle.ellipticOrbitCenter j :=
    fun h => hne ((ellipticNeighborhood_projection_eq_iff j z hz).mp h)
  have hother := SpecialPeriods.Triangle.ellipticNeighborhood_avoids_other j z hz
  cases j
  · exact ⟨hself, hother⟩
  · exact ⟨hother, hself⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
def SpecialPeriods.MuTorsor.Division.completedQuotient (ν F : ℍ → ℂ) (v : Elliptic.Kind → ℂ)
    (z : ℍ) : ℂ := by
  classical
    exact
    if SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne then
      v .three
    else
      if SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo then
        v .four
      else ν z / F z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.completedQuotient_center (ν F : ℍ → ℂ)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) :
    completedQuotient ν F v (SpecialPeriods.Triangle.ellipticCenter j) = v j := by
  cases j
  · simp only [SpecialPeriods.Triangle.ellipticCenter, completedQuotient,
      SpecialPeriods.triangleOrbitCenterOne, if_true]
  · have hne :
      SpecialPeriods.triangleOrbitProjection SpecialPeriods.Triangle.centerTwo ≠
        SpecialPeriods.triangleOrbitCenterOne :=
      SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo.symm
    simp only [SpecialPeriods.Triangle.ellipticCenter, completedQuotient, hne, if_false,
      SpecialPeriods.triangleOrbitCenterTwo, if_true]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.completedQuotient_eq_div (ν F : ℍ → ℂ)
    (v : Elliptic.Kind → ℂ) (z : ℍ)
    (h₁ : SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterOne)
    (h₂ : SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterTwo) :
    completedQuotient ν F v z = ν z / F z := by simp only [completedQuotient, h₁, h₂, if_false]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.completedQuotient_eventuallyEq_germ {ν F : ℍ → ℂ}
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) (h : ℂ → ℂ)
    (hv : v j = h (SpecialPeriods.Triangle.ellipticCenter j : ℂ))
    (hfactor :
      (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j : ℂ)] fun w =>
        (F ∘ UpperHalfPlane.ofComplex) w * h w) :
    completedQuotient ν F v =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j)] fun z => h (z : ℂ) :=
  by
  have he : ∀ᶠ z : ℍ in 𝓝 (SpecialPeriods.Triangle.ellipticCenter j), ν z = F z * h (z : ℂ) := by
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      UpperHalfPlane.continuous_coe.continuousAt.eventually hfactor
  filter_upwards [he, SpecialPeriods.Triangle.ellipticNeighborhood_mem_nhds j] with z hez hzn
  by_cases hz : z = SpecialPeriods.Triangle.ellipticCenter j
  · subst z
    exact (completedQuotient_center ν F v j).trans hv
  · obtain ⟨h₁, h₂⟩ := ellipticNeighborhood_projection_ne_centers j z hzn hz
    have hFz : F z ≠ 0 := fun hzero => (hFzero z).mp hzero |>.elim h₁ h₂
    rw [completedQuotient_eq_div ν F v z h₁ h₂, hez]
    exact mul_div_cancel_left₀ _ hFz

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.completedQuotient_contMDiffAt_center {ν F : ℍ → ℂ}
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h (SpecialPeriods.Triangle.ellipticCenter j : ℂ))
    (hv : v j = h (SpecialPeriods.Triangle.ellipticCenter j : ℂ))
    (hfactor :
      (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j : ℂ)] fun w =>
        (F ∘ UpperHalfPlane.ofComplex) w * h w) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v)
      (SpecialPeriods.Triangle.ellipticCenter j) := by
  exact
    (hh.contDiffAt.contMDiffAt.comp _ (UpperHalfPlane.contMDiff_coe _)).congr_of_eventuallyEq
      (completedQuotient_eventuallyEq_germ hFzero v j h hv hfactor)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.completedQuotient_contMDiffAt_of_ne_zero {ν F : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (z : ℍ) (hz : F z ≠ 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) z := by
  apply ((hν z).div₀ (hF z) hz).congr_of_eventuallyEq
  filter_upwards [(hF z).continuousAt.eventually_ne hz] with w hw
  have hn :
    ¬(SpecialPeriods.triangleOrbitProjection w = SpecialPeriods.triangleOrbitCenterOne ∨
        SpecialPeriods.triangleOrbitProjection w = SpecialPeriods.triangleOrbitCenterTwo) :=
    fun he => hw ((hFzero w).mpr he)
  exact completedQuotient_eq_div ν F v w (fun h => hn (.inl h)) (fun h => hn (.inr h))

attribute [local instance] SpecialPeriods.triangleGeometricAction in
theorem SpecialPeriods.MuTorsor.Division.contMDiffAt_orbit {H : ℍ → ℂ}
    (hH :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z)
    {a : ℍ} (ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H a) (g : SpecialPeriods.TriangleGroup) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H (SpecialPeriods.triangleGeometricRepresentation g a) := by
  have hi :
    SpecialPeriods.triangleGeometricRepresentation g⁻¹
        (SpecialPeriods.triangleGeometricRepresentation g a) =
      a := by
    rw [map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply a
  have hh :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H
      (SpecialPeriods.triangleGeometricRepresentation g⁻¹
        (SpecialPeriods.triangleGeometricRepresentation g a)) :=
    hi.symm ▸ ha
  apply
    (hh.comp _
        (SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹ _)).congr_of_eventuallyEq
  filter_upwards with z
  exact (hH g⁻¹ z).symm

theorem SpecialPeriods.MuTorsor.Division.completedQuotient_invariant {ν F : ℍ → ℂ}
    (v : Elliptic.Kind → ℂ)
    (hinv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ,
          ν (SpecialPeriods.triangleGeometricRepresentation g z) /
              F (SpecialPeriods.triangleGeometricRepresentation g z) =
            ν z / F z)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    completedQuotient ν F v (SpecialPeriods.triangleGeometricRepresentation g z) =
      completedQuotient ν F v z := by
  unfold completedQuotient
  rw [SpecialPeriods.triangleOrbitProjection_smul g z, hinv g z]

theorem SpecialPeriods.MuTorsor.Division.completedQuotient_factorization {ν F : ℍ → ℂ}
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hνzero : ∀ z : ℍ, F z = 0 → ν z = 0) (v : Elliptic.Kind → ℂ) (z : ℍ) :
    ν z = F z * completedQuotient ν F v z := by
  by_cases hz : F z = 0
  · rw [hz, hνzero z hz, MulZeroClass.zero_mul]
  · have hn :
      ¬(SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo) :=
      fun he => hz ((hFzero z).mpr he)
    rw [completedQuotient_eq_div ν F v z (fun h => hn (.inl h)) (fun h => hn (.inr h))]
    exact (mul_div_cancel₀ (ν z) hz).symm.trans (by ring)

theorem SpecialPeriods.MuTorsor.Division.completedQuotient_holomorphic {ν F : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ)
    (hinv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ,
          completedQuotient ν F v (SpecialPeriods.triangleGeometricRepresentation g z) =
            completedQuotient ν F v z)
    (hcenter :
      ∀ j : Elliptic.Kind,
        ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v)
          (SpecialPeriods.Triangle.ellipticCenter j)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) := by
  intro z
  by_cases hz : F z = 0
  · rcases (hFzero z).mp hz with h₁ | h₂
    · obtain ⟨g, hg⟩ :=
        (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerOne).mp h₁
      rw [← hg]
      exact contMDiffAt_orbit hinv (hcenter .three) g
    · obtain ⟨g, hg⟩ :=
        (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerTwo).mp h₂
      rw [← hg]
      exact contMDiffAt_orbit hinv (hcenter .four) g
  · exact completedQuotient_contMDiffAt_of_ne_zero hν hF hFzero v z hz

theorem SpecialPeriods.MuTorsor.Division.exists_holomorphic_invariant_factor {τ : ℍ → ℍ}
    {ν F : ℍ → ℂ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) =
        1) :
    ∃ H : ℍ → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H ∧
        (∀ g : SpecialPeriods.TriangleGroup,
            ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z) ∧
          ∀ z : ℍ, ν z = F z * H z := by
  obtain ⟨h₁, hh₁, he₁⟩ :=
    SpecialPeriods.MuGenerator.exists_division_at_centerOne hτ hτc hν hν₁ hF hForder₁
  obtain ⟨h₂, hh₂, he₂⟩ :=
    SpecialPeriods.MuGenerator.exists_division_at_centerTwo hν hν₂ hF hForder₂
  let v : Elliptic.Kind → ℂ
    | .three => h₁ (SpecialPeriods.Triangle.centerOne : ℂ)
    | .four => h₂ (SpecialPeriods.Triangle.centerTwo : ℂ)
  have hinv := completedQuotient_invariant v (quotient_invariant hν₁ hν₂ hF₁ hF₂)
  refine ⟨completedQuotient ν F v, ?_, hinv, ?_⟩
  · apply completedQuotient_holomorphic hν hF hFzero v hinv
    intro j
    cases j
    · exact completedQuotient_contMDiffAt_center hFzero v .three h₁ hh₁ rfl he₁
    · exact completedQuotient_contMDiffAt_center hFzero v .four h₂ hh₂ rfl he₂
  · apply completedQuotient_factorization hFzero
    intro z hz
    exact zero_of_ellipticOrbit hν₁ hν₂ ((hFzero z).mp hz)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.instIsManifold2 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2 in
theorem SpecialPeriods.MuTorsor.instIsManifold3 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
def SpecialPeriods.MuTorsor.compactExtension (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (c : ℂ) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace → ℂ :=
  OnePoint.rec c f

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
theorem SpecialPeriods.MuTorsor.compactExtension_holomorphicAt_openInclusion
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (c : ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f c) (SpecialPeriods.triangleOpenInclusion q) := by
  have hp := SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph q
  have hcomp :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f c ∘ SpecialPeriods.triangleOpenInclusion) q :=
    hf q
  have h :=
    hcomp.comp_of_eq hp.localInverse_contMDiffAt
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with x hx
  change
    compactExtension f c x =
      compactExtension f c (SpecialPeriods.triangleOpenInclusion (hp.localInverse x))
  rw [show SpecialPeriods.triangleOpenInclusion (hp.localInverse x) = x from hx]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
theorem SpecialPeriods.MuTorsor.compactExtension_eventuallyEq_cuspChart
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    compactExtension f (g 0) =ᶠ[𝓝 SpecialPeriods.triangleCuspPoint]
      g ∘ SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl := by
  filter_upwards [SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds Y] with x hx
  induction x using OnePoint.rec with
  |
    infty =>
    change
      g 0 =
        g
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
            SpecialPeriods.triangleCuspPoint)
    rw [SpecialPeriods.Triangle.cuspFullChart_cuspPoint]
  | coe
    q =>
    change
      f q =
        g
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
            (SpecialPeriods.triangleOpenInclusion q))
    exact h q ((SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood Y q).mp hx)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
theorem SpecialPeriods.MuTorsor.compactExtension_holomorphicAt_cusp_of_cuspImage
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ) (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) SpecialPeriods.triangleCuspPoint := by
  have hc :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl)
      SpecialPeriods.triangleCuspPoint :=
    SpecialPeriods.triangleCompactified_cuspChart_holomorphic.contMDiffAt
      (SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds SpecialPeriods.Triangle.width)
  have hgc :=
    hg.contDiffAt.contMDiffAt.comp_of_eq hc
      (SpecialPeriods.Triangle.cuspFullChart_cuspPoint SpecialPeriods.Triangle.width le_rfl)
  exact hgc.congr_of_eventuallyEq (compactExtension_eventuallyEq_cuspChart f g Y h)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
theorem SpecialPeriods.MuTorsor.compactExtension_holomorphic_of_cuspImage
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) := by
  intro x
  induction x using OnePoint.rec with
  | infty => exact compactExtension_holomorphicAt_cusp_of_cuspImage f g Y hg h
  | coe q => exact compactExtension_holomorphicAt_openInclusion f (g 0) hf q

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
theorem SpecialPeriods.MuTorsor.eq_const_of_cuspImage (f : SpecialPeriods.TriangleOrbitSpace → ℂ)
    (g : ℂ → ℂ) (Y : ℝ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    ∀ q, f q = g 0 := by
  let := SpecialPeriods.triangleCompactifiedOrbitSpace_compact
  let := SpecialPeriods.triangleCompactifiedOrbitSpace_connected
  have he := compactExtension_holomorphic_of_cuspImage f g Y hf hg h
  intro q
  exact
    (he.mdifferentiable (by simp)).apply_eq_of_compactSpace
      (SpecialPeriods.triangleOpenInclusion q) SpecialPeriods.triangleCuspPoint

theorem SpecialPeriods.MuTorsor.exists_cuspImage_eq_of_eventually_atImInfty
    {f : SpecialPeriods.TriangleOrbitSpace → ℂ} {g : ℂ → ℂ}
    (h :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        f (SpecialPeriods.triangleOrbitProjection z) = g (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ Y : ℝ,
      SpecialPeriods.Triangle.width ≤ Y ∧
        ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
          f q =
            g
              (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
                (SpecialPeriods.triangleOpenInclusion q)) := by
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp h
  refine ⟨Max.max SpecialPeriods.Triangle.width A, le_max_left _ _, ?_⟩
  intro q hq
  obtain ⟨z, hz, rfl⟩ := (SpecialPeriods.Triangle.mem_cuspImage _ _).mp hq
  have hzwidth : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width :=
    (le_max_left _ _).trans_lt hz
  rw [SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl ⟨z, hzwidth⟩]
  exact hA z ((le_max_right _ _).trans hz.le)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.eq_const_of_eventually_cusp
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        f (SpecialPeriods.triangleOrbitProjection z) = g (SpecialPeriods.Triangle.cuspQ z)) :
    ∀ q, f q = g 0 := by
  obtain ⟨Y, _, hY⟩ := exists_cuspImage_eq_of_eventually_atImInfty h
  exact eq_const_of_cuspImage f g Y hf hg hY

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.eq_zero_of_eventually_cusp
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (h :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        f (SpecialPeriods.triangleOrbitProjection z) = g (SpecialPeriods.Triangle.cuspQ z)) :
    f = 0 := by
  funext q
  exact (eq_const_of_eventually_cusp f g hf hg h q).trans hg0

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.descend_top_project {H : ℍ → ℂ}
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z)
    (z : ℍ) : descend ⊤ H (SpecialPeriods.triangleOrbitProjection z) = H z := by
  apply descend_project ⊤ H
  · intro g w
    rfl
  · intro g w _
    exact hInv g w
  · trivial

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.descend_top_holomorphic {H : ℍ → ℂ} (hH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (descend ⊤ H) := by
  intro q
  apply descend_holomorphicAt ⊤ H
  · intro g w
    rfl
  · intro g w _
    exact hInv g w
  · exact hH.contMDiffOn
  · exact ⟨orbitRepresentative q, trivial, project_orbitRepresentative q⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
theorem SpecialPeriods.MuTorsor.invariant_eq_zero_of_eventually_cusp {H : ℍ → ℂ}
    (hH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (he : ∀ᶠ z in UpperHalfPlane.atImInfty, H z = g (SpecialPeriods.Triangle.cuspQ z)) : H = 0 := by
  have hd : descend ⊤ H = 0 := by
    apply eq_zero_of_eventually_cusp (descend ⊤ H) g (descend_top_holomorphic hH hInv) hg hg0
    filter_upwards [he] with z hz
    exact (descend_top_project hInv z).trans hz
  funext z
  exact
    (descend_top_project hInv z).symm.trans
      (congrFun hd (SpecialPeriods.triangleOrbitProjection z))

theorem SpecialPeriods.MuTorsor.homogeneous_eq_zero_of_cuspRegular {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hνc : CuspRegular ν) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (hFcusp :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    ν = 0 := by
  obtain ⟨H, hH, hInv, hfactor⟩ :=
    Division.exists_holomorphic_invariant_factor hτ hτc hν hν₁ hν₂ hF hF₁ hF₂ hFzero hForder₁
      hForder₂
  obtain ⟨v, hv, hv0, hFv⟩ := hFcusp
  obtain ⟨g, hg, hg0, hHg⟩ := factor_cusp_germ hνc hv hv0 hFv hfactor
  have hH0 : H = 0 := invariant_eq_zero_of_eventually_cusp hH hInv hg hg0 hHg
  funext z
  calc
    ν z = F z * H z := hfactor z
    _ = 0 := by simp only [hH0, Pi.zero_apply, MulZeroClass.mul_zero]

theorem SpecialPeriods.MuTorsor.affine_sub_homogeneous {τ : ℍ → ℍ} {μ μ' : ℍ → ℂ}
    (hμ₁ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ)) :
    (∀ z : ℍ, (μ - μ') (SpecialPeriods.Triangle.generatorOneSL • z) = -(μ - μ') z / (τ z : ℂ)) ∧
      (∀ z : ℍ, (μ - μ') (SpecialPeriods.Triangle.generatorTwoSL • z) = (μ - μ') z / (τ z : ℂ)) :=
  by
  constructor
  · intro z
    simp only [Pi.sub_apply, hμ₁ z, hμ'₁ z]
    ring
  · intro z
    simp only [Pi.sub_apply, hμ₂ z, hμ'₂ z]
    ring

theorem SpecialPeriods.MuTorsor.affine_eq_of_cuspRegular {τ : ℍ → ℍ} {μ μ' F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) (hμ' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ')
    (hμ₁ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ))
    (hμc : CuspRegular μ) (hμ'c : CuspRegular μ') (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (hFcusp :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    μ = μ' := by
  obtain ⟨hν₁, hν₂⟩ := affine_sub_homogeneous hμ₁ hμ₂ hμ'₁ hμ'₂
  exact
    sub_eq_zero.mp
      (homogeneous_eq_zero_of_cuspRegular hτ hτc (hμ.sub hμ') hν₁ hν₂ (hμc.sub hμ'c) hF hF₁ hF₂
        hFzero hForder₁ hForder₂ hFcusp)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
structure SpecialPeriods.MuTorsor.IsSolution (τ : ℍ → ℍ) (μ : ℍ → ℂ) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ
  generatorOne : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)
  generatorTwo : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)
  cuspRegular : CuspRegular μ

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.exists_unique_solution_from_generator
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F)
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (hFcusp :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ := by
  obtain ⟨μ, hμ, _, hμ₁, hμ₂, hμc⟩ :=
    exists_holomorphic_affine_cuspRegular π hπ hτ hτa F hF hFc hFzero hFcusp
  refine ⟨μ, ⟨hμ, hμ₁, hμ₂, hμc⟩, ?_⟩
  intro μ' hμ'
  exact
    affine_eq_of_cuspRegular hτa hτ hμ'.holomorphic hμ hμ'.generatorOne hμ'.generatorTwo hμ₁ hμ₂
      hμ'.cuspRegular hμc hF hFc.1 hFc.2 hFzero hForder₁ hForder₂ hFcusp

theorem SpecialPeriods.MuGenerator.E₆_cuspFunction_zero :
    UpperHalfPlane.cuspFunction 1 ModularForm.E₆ 0 = 1 := by
  have h :=
    EisensteinSeries.E_qExpansion_coeff_zero (show 3 ≤ 6 by decide) (show Even 6 by decide)
  simpa [UpperHalfPlane.qExpansion_coeff] using h

def SpecialPeriods.MuGenerator.cuspModularParameter (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  t * u t

@[simp]
theorem SpecialPeriods.MuGenerator.cuspModularParameter_zero (u : ℂ → ℂ) :
    cuspModularParameter u 0 = 0 := by simp [cuspModularParameter]

theorem SpecialPeriods.MuGenerator.cuspModularParameter_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspModularParameter u) 0 :=
  analyticAt_id.mul hu

def SpecialPeriods.MuGenerator.cuspEisensteinFour (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  UpperHalfPlane.cuspFunction 1 ModularForm.E₄ (cuspModularParameter u t)

def SpecialPeriods.MuGenerator.cuspEisensteinSix (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  UpperHalfPlane.cuspFunction 1 ModularForm.E₆ (cuspModularParameter u t)

def SpecialPeriods.MuGenerator.cuspDiscriminantUnit (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  u t * SpecialPeriods.discriminantUnit (cuspModularParameter u t)

@[simp]
theorem SpecialPeriods.MuGenerator.cuspEisensteinFour_zero (u : ℂ → ℂ) :
    cuspEisensteinFour u 0 = 1 := by
  simp [cuspEisensteinFour, SpecialPeriods.E₄_cuspFunction_zero]

@[simp]
theorem SpecialPeriods.MuGenerator.cuspEisensteinSix_zero (u : ℂ → ℂ) :
    cuspEisensteinSix u 0 = 1 := by simp [cuspEisensteinSix, E₆_cuspFunction_zero]

@[simp]
theorem SpecialPeriods.MuGenerator.cuspDiscriminantUnit_zero (u : ℂ → ℂ) :
    cuspDiscriminantUnit u 0 = u 0 := by simp [cuspDiscriminantUnit]

theorem SpecialPeriods.MuGenerator.cuspEisensteinFour_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspEisensteinFour u) 0 := by
  have h :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact
      ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ zero_lt_one
        one_mem_strictPeriods_SL
  exact h.comp (cuspModularParameter_analyticAt hu)

theorem SpecialPeriods.MuGenerator.cuspEisensteinSix_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspEisensteinSix u) 0 := by
  have h :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.E₆) (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact
      ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ zero_lt_one
        one_mem_strictPeriods_SL
  exact h.comp (cuspModularParameter_analyticAt hu)

theorem SpecialPeriods.MuGenerator.cuspDiscriminantUnit_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspDiscriminantUnit u) 0 := by
  have h : AnalyticAt ℂ SpecialPeriods.discriminantUnit (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact SpecialPeriods.discriminantUnit_analyticAt_zero
  exact hu.mul (h.comp (cuspModularParameter_analyticAt hu))

def SpecialPeriods.MuGenerator.cuspGeneratorUnit (u b : ℂ → ℂ) (t : ℂ) : ℂ :=
  cuspEisensteinFour u t ^ 2 * b t / cuspDiscriminantUnit u t

@[simp]
theorem SpecialPeriods.MuGenerator.cuspGeneratorUnit_zero (u b : ℂ → ℂ) :
    cuspGeneratorUnit u b 0 = b 0 / u 0 := by simp [cuspGeneratorUnit]

theorem SpecialPeriods.MuGenerator.cuspGeneratorUnit_analyticAt {u b : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hb : AnalyticAt ℂ b 0) (hu0 : u 0 ≠ 0) :
    AnalyticAt ℂ (cuspGeneratorUnit u b) 0 :=
  ((cuspEisensteinFour_analyticAt hu).pow 2 |>.mul hb).div (cuspDiscriminantUnit_analyticAt hu)
    (by simpa only [cuspDiscriminantUnit_zero] using hu0)

theorem SpecialPeriods.MuGenerator.cuspGeneratorUnit_zero_ne_zero {u b : ℂ → ℂ} (hu0 : u 0 ≠ 0)
    (hb0 : b 0 ≠ 0) : cuspGeneratorUnit u b 0 ≠ 0 := by
  rw [cuspGeneratorUnit_zero]
  exact div_ne_zero hb0 hu0

theorem SpecialPeriods.MuGenerator.Root.square_eq_cuspEisensteinSix {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (u : ℂ → ℂ) (z : ℍ)
    (hq :
      Function.Periodic.qParam 1 (τ z) =
        SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    r z ^ 2 = SpecialPeriods.MuGenerator.cuspEisensteinSix u (SpecialPeriods.Triangle.cuspQ z) := by
  rw [r.square z, ←
    SlashInvariantFormClass.eq_cuspFunction ModularForm.E₆ (τ z) one_mem_strictPeriods_SL
      one_ne_zero,
    hq]
  rfl

theorem SpecialPeriods.MuGenerator.Root.generator_eq_inv_q_mul_unit {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (u b : ℂ → ℂ) (z : ℍ)
    (hq :
      Function.Periodic.qParam 1 (τ z) =
        SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z))
    (hr : r z = b (SpecialPeriods.Triangle.cuspQ z)) :
    r.generator z =
      (SpecialPeriods.Triangle.cuspQ z)⁻¹ *
        SpecialPeriods.MuGenerator.cuspGeneratorUnit u b (SpecialPeriods.Triangle.cuspQ z) := by
  have hE :
    ModularForm.E₄ (τ z) =
      SpecialPeriods.MuGenerator.cuspEisensteinFour u (SpecialPeriods.Triangle.cuspQ z) := by
    rw [←
      SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ (τ z) one_mem_strictPeriods_SL
        one_ne_zero,
      hq]
    rfl
  have hD :
    ModularForm.discriminant (τ z) =
      SpecialPeriods.Triangle.cuspQ z *
        SpecialPeriods.MuGenerator.cuspDiscriminantUnit u (SpecialPeriods.Triangle.cuspQ z) := by
    have h := ModularForm.discriminant_eq_q_prod (τ z)
    change
      ModularForm.discriminant (τ z) =
        Function.Periodic.qParam 1 (τ z) *
          SpecialPeriods.discriminantUnit (Function.Periodic.qParam 1 (τ z)) at h
    rw [h, hq, SpecialPeriods.MuGenerator.cuspDiscriminantUnit,
      SpecialPeriods.MuGenerator.cuspModularParameter]
    ring
  rw [generator, hE, hr, hD, SpecialPeriods.MuGenerator.cuspGeneratorUnit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem SpecialPeriods.MuGenerator.exists_analytic_sqrt_germ_one {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧ b 0 = 1 ∧ ∀ᶠ t in 𝓝 0, b t ^ 2 = h t := by
  obtain ⟨r, hr, hr0, hrpow⟩ :=
    AnalyticRootCover.exists_analytic_unit_root hh (by simp [h0]) (by norm_num : 0 < (2 : ℕ))
  have hr02 : r 0 ^ 2 = 1 := by simpa only [h0] using hrpow.self_of_nhds
  refine ⟨fun t => r t / r 0, hr.div analyticAt_const hr0, div_self hr0, ?_⟩
  filter_upwards [hrpow] with t ht
  simp only [div_pow, hr02, div_one, ht]

theorem SpecialPeriods.MuGenerator.exists_analytic_sqrt_ball_one {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ ε > 0,
      ∃ b : ℂ → ℂ,
        AnalyticOnNhd ℂ b (Metric.ball 0 ε) ∧
          b 0 = 1 ∧
            (∀ t ∈ Metric.ball 0 ε, b t ≠ 0) ∧ Set.EqOn (fun t => b t ^ 2) h (Metric.ball 0 ε) := by
  obtain ⟨b, hb, hb0, hbpow⟩ := exists_analytic_sqrt_germ_one hh h0
  have hbne : ∀ᶠ t in 𝓝 0, b t ≠ 0 := hb.continuousAt.eventually_ne (by simp [hb0])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.eventually_analyticAt.and (hbne.and hbpow))
  refine ⟨ε, hε, b, ?_, hb0, ?_, ?_⟩
  · exact fun t ht => (hball ht).1
  · exact fun t ht => (hball ht).2.1
  · exact fun t ht => (hball ht).2.2

theorem SpecialPeriods.MuGenerator.cuspHorodisc_isPreconnected (Y : ℝ) (hY : 0 ≤ Y) :
    IsPreconnected (SpecialPeriods.Triangle.horodisc Y : Set ℍ) := by
  apply UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.isPreconnected_image.mp
  have he :
    (UpperHalfPlane.coe '' (SpecialPeriods.Triangle.horodisc Y : Set ℍ)) = {w : ℂ | Y < w.im} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hw
      exact ⟨⟨w, hY.trans_lt hw⟩, hw, rfl⟩
  rw [he]
  exact (convex_halfSpace_im_gt Y).isPreconnected

theorem SpecialPeriods.MuGenerator.Root.exists_cusp_root_unit {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0)
    (hq :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ b : ℂ → ℂ,
      AnalyticAt ℂ b 0 ∧
        (b 0 = 1 ∨ b 0 = -1) ∧
          ∀ᶠ z in UpperHalfPlane.atImInfty, r z = b (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨R, hR, b, hb, hb0, hbne, hbsq⟩ :=
    SpecialPeriods.MuGenerator.exists_analytic_sqrt_ball_one
      (SpecialPeriods.MuGenerator.cuspEisensteinSix_analyticAt hu)
      (SpecialPeriods.MuGenerator.cuspEisensteinSix_zero u)
  have hsmall :
    ∀ᶠ z in UpperHalfPlane.atImInfty, SpecialPeriods.Triangle.cuspQ z ∈ Metric.ball 0 R :=
    (UpperHalfPlane.qParam_tendsto_atImInfty SpecialPeriods.Triangle.width_pos).eventually
      (Metric.ball_mem_nhds 0 hR)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp (hq.and hsmall)
  let Y := Max.max A SpecialPeriods.Triangle.width
  have hY : 0 ≤ Y := SpecialPeriods.Triangle.width_pos.le.trans (le_max_right _ _)
  have hhigh :
    ∀ z ∈ SpecialPeriods.Triangle.horodisc Y,
      Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z) ∧
        SpecialPeriods.Triangle.cuspQ z ∈ Metric.ball 0 R := by
    intro z hz
    change Y < z.im at hz
    exact hA z ((le_max_left _ _).trans hz.le)
  have hcont :
    ContinuousOn (b ∘ SpecialPeriods.Triangle.cuspQ)
      (SpecialPeriods.Triangle.horodisc Y : Set ℍ) :=
    hb.continuousOn.comp SpecialPeriods.Triangle.cuspQ_continuous.continuousOn
      (fun z hz => (hhigh z hz).2)
  have hsq :
    Set.EqOn ((r : ℍ → ℂ) ^ 2) ((b ∘ SpecialPeriods.Triangle.cuspQ) ^ 2)
      (SpecialPeriods.Triangle.horodisc Y : Set ℍ) := by
    intro z hz
    change r z ^ 2 = b (SpecialPeriods.Triangle.cuspQ z) ^ 2
    exact (r.square_eq_cuspEisensteinSix u z (hhigh z hz).1).trans (hbsq (hhigh z hz).2).symm
  have hne :
    ∀ {z : ℍ},
      z ∈ SpecialPeriods.Triangle.horodisc Y → (b ∘ SpecialPeriods.Triangle.cuspQ) z ≠ 0 :=
    fun {z} hz => hbne _ (hhigh z hz).2
  have hYe : ∀ᶠ z in UpperHalfPlane.atImInfty, z ∈ SpecialPeriods.Triangle.horodisc Y := by
    apply (UpperHalfPlane.atImInfty_mem _).mpr
    refine ⟨Y + 1, fun z hz => ?_⟩
    change Y < z.im
    linarith
  have hbAt : AnalyticAt ℂ b 0 := hb 0 (Metric.mem_ball_self hR)
  rcases
    (SpecialPeriods.MuGenerator.cuspHorodisc_isPreconnected Y hY).eq_or_eq_neg_of_sq_eq
      r.holomorphic.continuous.continuousOn hcont hsq hne with
    h | h
  · exact ⟨b, hbAt, Or.inl hb0, hYe.mono fun z hz => h hz⟩
  · refine ⟨-b, hbAt.neg, Or.inr ?_, ?_⟩
    · simp only [Pi.neg_apply, hb0]
    · filter_upwards [hYe] with z hz
      simpa only [Pi.neg_apply, Function.comp_apply] using h hz

theorem SpecialPeriods.MuGenerator.Root.exists_cusp_unit {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ v : ℂ → ℂ,
      AnalyticAt ℂ v 0 ∧
        v 0 ≠ 0 ∧
          ∀ᶠ z in UpperHalfPlane.atImInfty,
            r.generator z =
              (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨b, hb, hb0, hrb⟩ := r.exists_cusp_root_unit hu hq
  have hbne : b 0 ≠ 0 := by rcases hb0 with h | h <;> simp [h]
  refine
    ⟨SpecialPeriods.MuGenerator.cuspGeneratorUnit u b,
      SpecialPeriods.MuGenerator.cuspGeneratorUnit_analyticAt hu hb hu0,
      SpecialPeriods.MuGenerator.cuspGeneratorUnit_zero_ne_zero hu0 hbne, ?_⟩
  filter_upwards [hq, hrb] with z hqz hrz
  exact r.generator_eq_inv_q_mul_unit u b z hqz hrz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.generator_zero_iff_orbits
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ}
    (hJ :
      ∀ z, SpecialPeriods.modularJ (τ z) = 1728 * SpecialPeriods.BetaTorsor.finiteProjection π z)
    (r : SpecialPeriods.MuGenerator.Root τ) (z : ℍ) :
    r.generator z = 0 ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
        SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo := by
  rw [r.generator_eq_zero_iff_normalized_source hJ,
    SourceOrders.finiteProjection_eq_zero_iff π hπ h₀,
    SourceOrders.finiteProjection_eq_one_iff π hπ h₁]

theorem SpecialPeriods.MuTorsor.CuspRegular.bounded {f : ℍ → ℂ}
    (hf : SpecialPeriods.MuTorsor.CuspRegular f) : UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨M, hM, he⟩ := hf
  have he' : f =ᶠ[UpperHalfPlane.atImInfty] fun z => M (SpecialPeriods.Triangle.cuspQ z) := he
  have ht : Filter.Tendsto f UpperHalfPlane.atImInfty (𝓝 (M 0)) :=
    (hM.continuousAt.tendsto.comp
          (SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)).congr'
      he'.symm
  exact ht.isBigO_one ℝ

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.MuTorsor.exists_unique_solution
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hJ :
      ∀ z, SpecialPeriods.modularJ (τ z) = 1728 * SpecialPeriods.BetaTorsor.finiteProjection π z)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ := by
  have hJ' : ∀ z, SpecialPeriods.modularJ (τ z) = SourceOrders.sourceJ π z := hJ
  obtain ⟨F, ⟨r, rfl⟩, hF, hFc, _, hF₁, hF₂⟩ :=
    SpecialPeriods.MuGenerator.exists_homogeneous_generator_of_modular_equation hτa hτ hJ'
      (SourceOrders.sourceJ_order_of_eq_zero π hπ h₀)
      (SourceOrders.sourceJ_sub_1728_order_of_eq π hπ h₁)
  exact
    exists_unique_solution_from_generator π hπ hτ hτa r.generator hF hFc
      (generator_zero_iff_orbits π hπ h₀ h₁ hJ r) hF₁ hF₂ (r.exists_cusp_unit hu hu0 hq)

def SpecialPeriods.phiThree (p : PeriodPoint) : ℂ :=
  2 - 6 * (1 - p.μ) ^ 2 / p.τ

def SpecialPeriods.phiFour (p : PeriodPoint) : ℂ :=
  -3 - 6 * p.μ ^ 2 / p.τ

theorem SpecialPeriods.phiThree_eq_beta_sub (p : PeriodPoint) : phiThree p = p.step₁.β - p.β := by
  simp only [phiThree, PeriodPoint.step₁]
  ring

theorem SpecialPeriods.phiFour_eq_beta_sub (p : PeriodPoint) : phiFour p = p.step₂.β - p.β := by
  simp only [phiFour, PeriodPoint.step₂]
  ring

theorem SpecialPeriods.phiThree_cyclic_sum (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p + phiThree p.step₁ + phiThree p.step₁.step₁ = 0 := by
  simp only [phiThree_eq_beta_sub]
  rw [p.step₁_cube h₀ h₁]
  ring

theorem SpecialPeriods.phiFour_cyclic_sum (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p + phiFour p.step₂ + phiFour p.step₂.step₂ + phiFour p.step₂.step₂.step₂ = 0 := by
  simp only [phiFour_eq_beta_sub]
  rw [p.step₂_fourth h₀]
  ring

def SpecialPeriods.betaAverageThree (p : PeriodPoint) : ℂ :=
  (phiThree p.step₁ + 2 * phiThree p.step₁.step₁) / 3

def SpecialPeriods.betaAverageFour (p : PeriodPoint) : ℂ :=
  (phiFour p.step₂ + 2 * phiFour p.step₂.step₂ + 3 * phiFour p.step₂.step₂.step₂) / 4

theorem SpecialPeriods.betaAverageThree_difference (p : PeriodPoint) (h₀ : p.τ ≠ 0)
    (h₁ : p.τ - 1 ≠ 0) : betaAverageThree p.step₁ - betaAverageThree p = phiThree p := by
  unfold betaAverageThree
  rw [p.step₁_cube h₀ h₁]
  linear_combination -(1 / 3 : ℂ) * phiThree_cyclic_sum p h₀ h₁

theorem SpecialPeriods.betaAverageFour_difference (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    betaAverageFour p.step₂ - betaAverageFour p = phiFour p := by
  unfold betaAverageFour
  rw [p.step₂_fourth h₀]
  linear_combination -(1 / 4 : ℂ) * phiFour_cyclic_sum p h₀

def SpecialPeriods.betaPrimitiveThree (τ μ : ℂ) : ℂ :=
  (2 - 6 * (τ - 1 + μ) ^ 2 / (τ * (τ - 1)) + 2 * (2 + 6 * μ ^ 2 / (τ - 1))) / 3

def SpecialPeriods.betaPrimitiveFour (τ μ : ℂ) : ℂ :=
  ((-3 + 6 * (τ + μ) ^ 2 / τ) + 2 * (-3 - 6 * (1 - τ - μ) ^ 2 / τ) +
      3 * (-3 + 6 * (1 - μ) ^ 2 / τ)) /
    4

theorem SpecialPeriods.phiThree_step (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p.step₁ = 2 - 6 * (p.τ - 1 + p.μ) ^ 2 / (p.τ * (p.τ - 1)) := by
  simp only [phiThree, PeriodPoint.step₁]
  field_simp
  ring

theorem SpecialPeriods.phiThree_step_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p.step₁.step₁ = 2 + 6 * p.μ ^ 2 / (p.τ - 1) := by
  rw [p.step₁_sq h₀ h₁]
  simp only [phiThree]
  field_simp
  ring

theorem SpecialPeriods.phiFour_step (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂ = -3 + 6 * (p.τ + p.μ) ^ 2 / p.τ := by
  simp only [phiFour, PeriodPoint.step₂]
  field_simp
  ring

theorem SpecialPeriods.phiFour_step_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂.step₂ = -3 - 6 * (1 - p.τ - p.μ) ^ 2 / p.τ := by
  rw [p.step₂_sq h₀]
  rfl

theorem SpecialPeriods.phiFour_step_cube (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂.step₂.step₂ = -3 + 6 * (1 - p.μ) ^ 2 / p.τ := by
  rw [phiFour_step _ (by simpa only [p.step₂_sq h₀] using h₀), p.step₂_sq h₀]
  ring

theorem SpecialPeriods.betaAverageThree_eq_primitive (p : PeriodPoint) (h₀ : p.τ ≠ 0)
    (h₁ : p.τ - 1 ≠ 0) : betaAverageThree p = betaPrimitiveThree p.τ p.μ := by
  rw [betaAverageThree, phiThree_step p h₀ h₁, phiThree_step_sq p h₀ h₁]
  rfl

theorem SpecialPeriods.betaAverageFour_eq_primitive (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    betaAverageFour p = betaPrimitiveFour p.τ p.μ := by
  rw [betaAverageFour, phiFour_step p h₀, phiFour_step_sq p h₀, phiFour_step_cube p h₀]
  rfl

theorem SpecialPeriods.betaPrimitiveThree_difference (τ μ : ℂ) (h₀ : τ ≠ 0) (h₁ : τ - 1 ≠ 0) :
    betaPrimitiveThree ((τ - 1) / τ) ((1 - μ) / τ) - betaPrimitiveThree τ μ =
      2 - 6 * (1 - μ) ^ 2 / τ := by
  let p : PeriodPoint := ⟨τ, μ, 0⟩
  have hs₀ : p.step₁.τ ≠ 0 := div_ne_zero h₁ h₀
  have hs₁ : p.step₁.τ - 1 ≠ 0 := by
    have he : p.step₁.τ - 1 = -1 / τ := by
      dsimp [p, PeriodPoint.step₁]
      field_simp
      ring
    rw [he]
    exact div_ne_zero (by norm_num) h₀
  change betaPrimitiveThree p.step₁.τ p.step₁.μ - betaPrimitiveThree p.τ p.μ = phiThree p
  rw [← betaAverageThree_eq_primitive p.step₁ hs₀ hs₁, ← betaAverageThree_eq_primitive p h₀ h₁]
  exact betaAverageThree_difference p h₀ h₁

theorem SpecialPeriods.betaPrimitiveFour_difference (τ μ : ℂ) (h₀ : τ ≠ 0) :
    betaPrimitiveFour (-1 / τ) (1 + μ / τ) - betaPrimitiveFour τ μ = -3 - 6 * μ ^ 2 / τ := by
  let p : PeriodPoint := ⟨τ, μ, 0⟩
  have hs₀ : p.step₂.τ ≠ 0 := div_ne_zero (by norm_num) h₀
  change betaPrimitiveFour p.step₂.τ p.step₂.μ - betaPrimitiveFour p.τ p.μ = phiFour p
  rw [← betaAverageFour_eq_primitive p.step₂ hs₀, ← betaAverageFour_eq_primitive p h₀]
  exact betaAverageFour_difference p h₀

def SpecialPeriods.BetaTorsor.phiOne (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  2 - 6 * (1 - μ z) ^ 2 / (τ z : ℂ)

def SpecialPeriods.BetaTorsor.phiTwo (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  -3 - 6 * μ z ^ 2 / (τ z : ℂ)

def SpecialPeriods.BetaTorsor.primitiveOne (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  SpecialPeriods.betaPrimitiveThree (τ z) (μ z)

def SpecialPeriods.BetaTorsor.primitiveTwo (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  SpecialPeriods.betaPrimitiveFour (τ z) (μ z)

private theorem SpecialPeriods.BetaTorsor.tau_sub_one_ne_zero_mo1973_17984 (τ : ℍ → ℍ) (z : ℍ) :
    (τ z : ℂ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (by simpa only [Complex.ofReal_one] using (τ z).ne_ofReal 1)

theorem SpecialPeriods.BetaTorsor.phiOne_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (phiOne τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  exact
    contMDiff_const.sub
      ((contMDiff_const.mul ((contMDiff_const.sub hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero))

theorem SpecialPeriods.BetaTorsor.phiTwo_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (phiTwo τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  exact contMDiff_const.sub ((contMDiff_const.mul (hμ.pow 2)).div₀ ht (fun z => (τ z).ne_zero))

theorem SpecialPeriods.BetaTorsor.primitiveOne_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (primitiveOne τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  have ha :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z => 6 * ((τ z : ℂ) - 1 + μ z) ^ 2 / ((τ z : ℂ) * ((τ z : ℂ) - 1))) :=
    (contMDiff_const.mul (((ht.sub contMDiff_const).add hμ).pow 2)).div₀
      (ht.mul (ht.sub contMDiff_const))
      (fun z => mul_ne_zero (τ z).ne_zero (tau_sub_one_ne_zero_mo1973_17984 τ z))
  have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * μ z ^ 2 / ((τ z : ℂ) - 1)) :=
    (contMDiff_const.mul (hμ.pow 2)).div₀ (ht.sub contMDiff_const)
      (tau_sub_one_ne_zero_mo1973_17984 τ)
  exact ((contMDiff_const.sub ha).add (contMDiff_const.mul (contMDiff_const.add hb))).div_const 3

theorem SpecialPeriods.BetaTorsor.primitiveTwo_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (primitiveTwo τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  have ha : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * ((τ z : ℂ) + μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul ((ht.add hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero)
  have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * (1 - (τ z : ℂ) - μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul (((contMDiff_const.sub ht).sub hμ).pow 2)).div₀ ht
      (fun z => (τ z).ne_zero)
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * (1 - μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul ((contMDiff_const.sub hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero)
  exact
    (((contMDiff_const.add ha).add (contMDiff_const.mul (contMDiff_const.sub hb))).add
          (contMDiff_const.mul (contMDiff_const.add hc))).div_const
      4

theorem SpecialPeriods.BetaTorsor.primitiveOne_difference {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    primitiveOne τ μ (SpecialPeriods.Triangle.generatorOneSL • z) - primitiveOne τ μ z =
      phiOne τ μ z := by
  simp only [primitiveOne, phiOne, hτ.1, hμ]
  exact
    SpecialPeriods.betaPrimitiveThree_difference (τ z) (μ z) (τ z).ne_zero
      (tau_sub_one_ne_zero_mo1973_17984 τ z)

theorem SpecialPeriods.BetaTorsor.primitiveTwo_difference {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    primitiveTwo τ μ (SpecialPeriods.Triangle.generatorTwoSL • z) - primitiveTwo τ μ z =
      phiTwo τ μ z := by
  simp only [primitiveTwo, phiTwo, hτ.2, hμ]
  exact SpecialPeriods.betaPrimitiveFour_difference (τ z) (μ z) (τ z).ne_zero

private theorem SpecialPeriods.BetaTorsor.generatorOne_triple_mo1973_17991 (z : ℍ) :
    SpecialPeriods.Triangle.generatorOneSL •
        (SpecialPeriods.Triangle.generatorOneSL • (SpecialPeriods.Triangle.generatorOneSL • z)) =
      z := by
  have he := congrArg (fun g : Equiv.Perm ℍ => g z) SpecialPeriods.Triangle.generatorOnePerm_cube
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    SpecialPeriods.Triangle.generatorOnePerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using he

private theorem SpecialPeriods.BetaTorsor.generatorTwo_quadruple_mo1973_17992 (z : ℍ) :
    SpecialPeriods.Triangle.generatorTwoSL •
        (SpecialPeriods.Triangle.generatorTwoSL •
          (SpecialPeriods.Triangle.generatorTwoSL •
            (SpecialPeriods.Triangle.generatorTwoSL • z))) =
      z := by
  have he :=
    congrArg (fun g : Equiv.Perm ℍ => g z) SpecialPeriods.Triangle.generatorTwoPerm_fourth
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    SpecialPeriods.Triangle.generatorTwoPerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using he

theorem SpecialPeriods.BetaTorsor.phiOne_cyclic_sum {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    phiOne τ μ z + phiOne τ μ (SpecialPeriods.Triangle.generatorOneSL • z) +
        phiOne τ μ
          (SpecialPeriods.Triangle.generatorOneSL •
            (SpecialPeriods.Triangle.generatorOneSL • z)) =
      0 := by
  have h₀ := primitiveOne_difference hτ hμ z
  have h₁ := primitiveOne_difference hτ hμ (SpecialPeriods.Triangle.generatorOneSL • z)
  have h₂ :=
    primitiveOne_difference hτ hμ
      (SpecialPeriods.Triangle.generatorOneSL • (SpecialPeriods.Triangle.generatorOneSL • z))
  rw [generatorOne_triple_mo1973_17991] at h₂
  linear_combination -h₀ - h₁ - h₂

theorem SpecialPeriods.BetaTorsor.phiTwo_cyclic_sum {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    phiTwo τ μ z + phiTwo τ μ (SpecialPeriods.Triangle.generatorTwoSL • z) +
          phiTwo τ μ
            (SpecialPeriods.Triangle.generatorTwoSL •
              (SpecialPeriods.Triangle.generatorTwoSL • z)) +
        phiTwo τ μ
          (SpecialPeriods.Triangle.generatorTwoSL •
            (SpecialPeriods.Triangle.generatorTwoSL •
              (SpecialPeriods.Triangle.generatorTwoSL • z))) =
      0 := by
  have h₀ := primitiveTwo_difference hτ hμ z
  have h₁ := primitiveTwo_difference hτ hμ (SpecialPeriods.Triangle.generatorTwoSL • z)
  have h₂ :=
    primitiveTwo_difference hτ hμ
      (SpecialPeriods.Triangle.generatorTwoSL • (SpecialPeriods.Triangle.generatorTwoSL • z))
  have h₃ :=
    primitiveTwo_difference hτ hμ
      (SpecialPeriods.Triangle.generatorTwoSL •
        (SpecialPeriods.Triangle.generatorTwoSL • (SpecialPeriods.Triangle.generatorTwoSL • z)))
  rw [generatorTwo_quadruple_mo1973_17992] at h₃
  linear_combination -h₀ - h₁ - h₂ - h₃

theorem SpecialPeriods.BetaTorsor.phiOne_sum_range {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    (∑ k ∈ Finset.range 3, phiOne τ μ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_succ, pow_zero, one_mul,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, SpecialPeriods.Triangle.generatorOnePerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using phiOne_cyclic_sum hτ hμ z

theorem SpecialPeriods.BetaTorsor.phiTwo_sum_range {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    (∑ k ∈ Finset.range 4, phiTwo τ μ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_succ, pow_zero, one_mul,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, SpecialPeriods.Triangle.generatorTwoPerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using phiTwo_cyclic_sum hτ hμ z

theorem SpecialPeriods.BetaTorsor.phi_product_relation {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    phiOne τ μ (SpecialPeriods.Triangle.generatorTwoSL • z) + phiTwo τ μ z = -1 := by
  let p : PeriodPoint := ⟨τ z, μ z, 0⟩
  have hp : SpecialPeriods.phiThree p.step₂ + SpecialPeriods.phiFour p = -1 := by
    rw [SpecialPeriods.phiThree_eq_beta_sub, SpecialPeriods.phiFour_eq_beta_sub,
      p.step₁_step₂ (τ z).ne_zero]
    simp only
    ring
  simp only [phiOne, phiTwo, hτ.2, hμ]
  exact hp

def SpecialPeriods.BetaTorsor.cuspPrimitive (τ : ℍ → ℍ) (z : ℍ) : ℂ :=
  -(τ z : ℂ)

theorem SpecialPeriods.BetaTorsor.cuspPrimitive_holomorphic {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspPrimitive τ) :=
  (UpperHalfPlane.contMDiff_coe.comp hτ).neg

theorem SpecialPeriods.BetaTorsor.cuspPrimitive_difference {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    cuspPrimitive τ
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator
            z) -
        cuspPrimitive τ z =
      1 := by
  rw [cuspPrimitive, cuspPrimitive, SpecialPeriods.tau_covariant_cusp_coe hτ]
  ring

def SpecialPeriods.BetaTorsor.skewPerm {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ) :
    Equiv.Perm (X × ℂ) where
  toFun x := (e x.1, x.2 + φ x.1)
  invFun x := (e.symm x.1, x.2 - φ (e.symm x.1))
  left_inv := by
    rintro ⟨z, b⟩
    simp
  right_inv := by
    rintro ⟨z, b⟩
    simp

@[simp]
theorem SpecialPeriods.BetaTorsor.skewPerm_apply {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ)
    (z : X) (b : ℂ) : skewPerm e φ (z, b) = (e z, b + φ z) :=
  rfl

theorem SpecialPeriods.BetaTorsor.skewPerm_pow_apply {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ)
    (n : ℕ) (z : X) (b : ℂ) :
    (skewPerm e φ ^ n) (z, b) = ((e ^ n) z, b + ∑ k ∈ Finset.range n, φ ((e ^ k) z)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, skewPerm_apply]
    rw [pow_succ', Equiv.Perm.mul_apply, Finset.sum_range_succ]
    simp only [add_assoc]

theorem SpecialPeriods.BetaTorsor.skewPerm_pow_eq_one {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ)
    (m : ℕ) (he : e ^ m = 1) (hφ : ∀ z, (∑ k ∈ Finset.range m, φ ((e ^ k) z)) = 0) :
    skewPerm e φ ^ m = 1 := by
  apply Equiv.ext
  rintro ⟨z, b⟩
  rw [skewPerm_pow_apply, he, hφ z]
  simp

def SpecialPeriods.BetaTorsor.IsAdditiveSkewOver {X : Type*} (e : Equiv.Perm X)
    (p : Equiv.Perm (X × ℂ)) : Prop :=
  ∀ z b, p (z, b) = (e z, b + (p (z, 0)).2)

theorem SpecialPeriods.BetaTorsor.isAdditiveSkewOver_skewPerm {X : Type*} (e : Equiv.Perm X)
    (φ : X → ℂ) : IsAdditiveSkewOver e (skewPerm e φ) := by
  intro z b
  simp

theorem SpecialPeriods.BetaTorsor.isAdditiveSkewOver_one {X : Type*} :
    IsAdditiveSkewOver (1 : Equiv.Perm X) (1 : Equiv.Perm (X × ℂ)) := by
  intro z b
  simp

theorem SpecialPeriods.BetaTorsor.IsAdditiveSkewOver.mul {X : Type*} {e f : Equiv.Perm X}
    {p q : Equiv.Perm (X × ℂ)} (hp : SpecialPeriods.BetaTorsor.IsAdditiveSkewOver e p)
    (hq : SpecialPeriods.BetaTorsor.IsAdditiveSkewOver f q) :
    SpecialPeriods.BetaTorsor.IsAdditiveSkewOver (e * f) (p * q) := by
  intro z b
  have hzero : ((p * q) (z, 0)).2 = (q (z, 0)).2 + (p (f z, 0)).2 := by
    change (p (q (z, 0))).2 = _
    rw [hq z 0]
    simpa only [zero_add] using congrArg Prod.snd (hp (f z) ((q (z, 0)).2))
  change p (q (z, b)) = (e (f z), b + ((p * q) (z, 0)).2)
  rw [hq z b, hp (f z) (b + (q (z, 0)).2), hzero]
  simp only [add_assoc]

theorem SpecialPeriods.BetaTorsor.IsAdditiveSkewOver.inv {X : Type*} {e : Equiv.Perm X}
    {p : Equiv.Perm (X × ℂ)} (hp : SpecialPeriods.BetaTorsor.IsAdditiveSkewOver e p) :
    SpecialPeriods.BetaTorsor.IsAdditiveSkewOver e⁻¹ p⁻¹ := by
  have hpi (z : X) (b : ℂ) : p.symm (z, b) = (e.symm z, b - (p (e.symm z, 0)).2) := by
    apply p.injective
    rw [p.apply_symm_apply, hp]
    simp
  intro z b
  change p.symm (z, b) = (e.symm z, b + (p.symm (z, 0)).2)
  rw [hpi z b, hpi z 0]
  simp only [sub_eq_add_neg, zero_add]

def SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ :
      ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0) :
    SpecialPeriods.TriangleGroup →* Equiv.Perm (ℍ × ℂ) :=
  SpecialPeriods.triangleLift (skewPerm SpecialPeriods.Triangle.generatorOnePerm φ₁)
    (skewPerm SpecialPeriods.Triangle.generatorTwoPerm φ₂)
    (skewPerm_pow_eq_one _ _ _ SpecialPeriods.Triangle.generatorOnePerm_cube h₁)
    (skewPerm_pow_eq_one _ _ _ SpecialPeriods.Triangle.generatorTwoPerm_fourth h₂)

@[simp]
theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_generator₁ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ :
      ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁ =
      skewPerm SpecialPeriods.Triangle.generatorOnePerm φ₁ :=
  SpecialPeriods.triangleLift_generator₁ ..

@[simp]
theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_generator₂ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ :
      ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂ =
      skewPerm SpecialPeriods.Triangle.generatorTwoPerm φ₂ :=
  SpecialPeriods.triangleLift_generator₂ ..

theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_isAdditiveSkewOver
    (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) :
    IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation g)
      (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g) := by
  let H : Subgroup SpecialPeriods.TriangleGroup :=
    { carrier :=
        {g |
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation g)
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g)}
      one_mem' := by
        change
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation 1)
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ 1)
        simpa only [map_one] using (isAdditiveSkewOver_one (X := ℍ))
      mul_mem' := by
        intro g h hg hh
        change
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation (g * h))
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ (g * h))
        simpa only [map_mul] using (IsAdditiveSkewOver.mul hg hh)
      inv_mem' := by
        intro g hg
        change
          IsAdditiveSkewOver (SpecialPeriods.triangleGeometricRepresentation g⁻¹)
            (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g⁻¹)
        simpa only [map_inv] using (IsAdditiveSkewOver.inv hg) }
  have hgen :
    ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
        Set SpecialPeriods.TriangleGroup) ⊆
      H := by
    intro g hg
    rcases hg with rfl | rfl
    · change
        IsAdditiveSkewOver
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁)
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁)
      rw [SpecialPeriods.triangleGeometricRepresentation_generator₁,
        triangleAdditiveRepresentation_generator₁]
      exact isAdditiveSkewOver_skewPerm _ _
    · change
        IsAdditiveSkewOver
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂)
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂)
      rw [SpecialPeriods.triangleGeometricRepresentation_generator₂,
        triangleAdditiveRepresentation_generator₂]
      exact isAdditiveSkewOver_skewPerm _ _
  have hclosure :
    Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) ≤
      H :=
    (Subgroup.closure_le H).mpr hgen
  apply hclosure
  rw [SpecialPeriods.triangle_generators_generate]
  exact Subgroup.mem_top g

def SpecialPeriods.BetaTorsor.triangleAdditiveShift (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) : ℂ :=
  (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, 0)).2

theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_apply (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (b : ℂ) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b) =
      (SpecialPeriods.triangleGeometricRepresentation g z,
        b + triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z) :=
  triangleAdditiveRepresentation_isAdditiveSkewOver φ₁ φ₂ h₁ h₂ g z b

@[simp]
theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_one (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (z : ℍ) : triangleAdditiveShift φ₁ φ₂ h₁ h₂ 1 z = 0 := by
  simp only [triangleAdditiveShift, map_one, Equiv.Perm.one_apply]

theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_mul (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g h : SpecialPeriods.TriangleGroup) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (g * h) z =
      triangleAdditiveShift φ₁ φ₂ h₁ h₂ g (SpecialPeriods.triangleGeometricRepresentation h z) +
        triangleAdditiveShift φ₁ φ₂ h₁ h₂ h z := by
  change (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ (g * h) (z, 0)).2 = _
  rw [map_mul, Equiv.Perm.mul_apply, triangleAdditiveRepresentation_apply,
    triangleAdditiveRepresentation_apply]
  simp only [zero_add, add_comm]

theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_inv (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ g⁻¹ z =
      -triangleAdditiveShift φ₁ φ₂ h₁ h₂ g
          (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) := by
  have h := triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂ g g⁻¹ z
  rw [mul_inv_cancel, triangleAdditiveShift_one] at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h.symm

@[simp]
theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₁ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (z : ℍ) : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁ z = φ₁ z := by
  simp only [triangleAdditiveShift, triangleAdditiveRepresentation_generator₁, skewPerm_apply,
    zero_add]

@[simp]
theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₂ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (z : ℍ) : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂ z = φ₂ z := by
  simp only [triangleAdditiveShift, triangleAdditiveRepresentation_generator₂, skewPerm_apply,
    zero_add]

private theorem SpecialPeriods.BetaTorsor.additive_cocycle_holomorphic_mo1973_18030
    (b : SpecialPeriods.TriangleGroup → ℍ → ℂ) (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
    (h₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b SpecialPeriods.triangleGenerator₁))
    (h₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b SpecialPeriods.triangleGenerator₂))
    (g : SpecialPeriods.TriangleGroup) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b g) := by
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact h₁
    · have he : g = SpecialPeriods.triangleGenerator₂ := Set.mem_singleton_iff.mp hg
      subst g
      exact h₂
  | one =>
    have he : b 1 = fun _ => 0 := funext hone
    rw [he]
    exact contMDiff_const
  | mul g h _ _ ihg
    ihh =>
    have he :
      b (g * h) = fun z => b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z :=
      funext (hmul g h)
    rw [he]
    exact (ihg.comp (SpecialPeriods.triangleGeometricRepresentation_holomorphic h)).add ihh
  | inv g _
    ihg =>
    have he : b g⁻¹ = fun z => -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) :=
      funext (hinv g)
    rw [he]
    exact (ihg.comp (SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹)).neg

private def SpecialPeriods.BetaTorsor.additiveAffineCocycle_mo1973_18031
    (b : SpecialPeriods.TriangleGroup → ℍ → ℂ) (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hhol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b g)) : SpecialPeriods.MuTorsor.AffineCocycle
    where
  scale _ _ := 1
  shift := b
  scale_one _ := rfl
  shift_one := hone
  scale_mul _ _ _ := by simp
  shift_mul g h z := by simpa only [Units.val_one, one_mul, add_comm] using hmul g h z
  scale_holomorphic _ := contMDiff_const
  shift_holomorphic := hhol

theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_holomorphic (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, ∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z) = 0)
    (h₂ : ∀ z, ∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z) = 0)
    (hφ₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₁) (hφ₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₂)
    (g : SpecialPeriods.TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (triangleAdditiveShift φ₁ φ₂ h₁ h₂ g) := by
  refine
    additive_cocycle_holomorphic_mo1973_18030 (triangleAdditiveShift φ₁ φ₂ h₁ h₂)
      (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂) (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
      (triangleAdditiveShift_inv φ₁ φ₂ h₁ h₂) ?_ ?_ g
  · have he : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁ = φ₁ :=
      funext (triangleAdditiveShift_generator₁ φ₁ φ₂ h₁ h₂)
    rw [he]
    exact hφ₁
  · have he : triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂ = φ₂ :=
      funext (triangleAdditiveShift_generator₂ φ₁ φ₂ h₁ h₂)
    rw [he]
    exact hφ₂

def SpecialPeriods.BetaTorsor.triangleAdditiveCocycle (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, ∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z) = 0)
    (h₂ : ∀ z, ∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z) = 0)
    (hφ₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₁) (hφ₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₂) :
    SpecialPeriods.MuTorsor.AffineCocycle :=
  additiveAffineCocycle_mo1973_18031 (triangleAdditiveShift φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂) (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_holomorphic φ₁ φ₂ h₁ h₂ hφ₁ hφ₂)

def SpecialPeriods.BetaTorsor.covarianceSubgroup (b : SpecialPeriods.TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
    (β : ℍ → ℂ) : Subgroup SpecialPeriods.TriangleGroup
    where
  carrier := {g | ∀ z, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + b g z}
  one_mem' := by
    intro z
    simp only [map_one, Equiv.Perm.one_apply, hone, add_zero]
  mul_mem' := by
    intro g h hg hh z
    rw [map_mul, Equiv.Perm.mul_apply, hg, hh, hmul]
    abel
  inv_mem' := by
    intro g hg z
    have he := hg (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
    have hc :
      SpecialPeriods.triangleGeometricRepresentation g
          (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) =
        z := by
      rw [map_inv]
      exact (SpecialPeriods.triangleGeometricRepresentation g).apply_symm_apply z
    rw [hc] at he
    rw [hinv, he]
    abel

theorem SpecialPeriods.BetaTorsor.covariance_zpowers (b : SpecialPeriods.TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul :
      ∀ g h z, b (g * h) z = b g (SpecialPeriods.triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z))
    (β : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + b g z)
    {h : SpecialPeriods.TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (SpecialPeriods.triangleGeometricRepresentation h z) = β z + b h z :=
  (Subgroup.zpowers_le.mpr (show g ∈ covarianceSubgroup b hone hmul hinv β from hg)) hh z

theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_product (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (hproduct : ∀ z, φ₁ (SpecialPeriods.Triangle.generatorTwoPerm z) + φ₂ z = -1) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂
        (SpecialPeriods.triangleGenerator₁ * SpecialPeriods.triangleGenerator₂) z =
      -1 := by
  rw [triangleAdditiveShift_mul, triangleAdditiveShift_generator₁,
    triangleAdditiveShift_generator₂, SpecialPeriods.triangleGeometricRepresentation_generator₂]
  exact hproduct z

theorem SpecialPeriods.BetaTorsor.triangleAdditiveShift_cusp (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0)
    (hproduct : ∀ z, φ₁ (SpecialPeriods.Triangle.generatorTwoPerm z) + φ₂ z = -1) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleCuspGenerator z = 1 := by
  rw [SpecialPeriods.triangleCuspGenerator, triangleAdditiveShift_inv,
    triangleAdditiveShift_product φ₁ φ₂ h₁ h₂ hproduct]
  norm_num

structure SpecialPeriods.BetaTorsor.Data where
  tau : ℍ → ℍ
  mu : ℍ → ℂ
  tau_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω tau
  mu_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω mu
  tau_covariant : SpecialPeriods.TauCovariant tau
  mu_one : ∀ z : ℍ, mu (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - mu z) / (tau z : ℂ)
  mu_two : ∀ z : ℍ, mu (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + mu z / (tau z : ℂ)

def SpecialPeriods.BetaTorsor.Data.cocycle (D : SpecialPeriods.BetaTorsor.Data) :
    SpecialPeriods.MuTorsor.AffineCocycle :=
  SpecialPeriods.BetaTorsor.triangleAdditiveCocycle (SpecialPeriods.BetaTorsor.phiOne D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiOne_sum_range D.tau_covariant D.mu_one)
    (SpecialPeriods.BetaTorsor.phiTwo_sum_range D.tau_covariant D.mu_two)
    (SpecialPeriods.BetaTorsor.phiOne_holomorphic D.tau_holomorphic D.mu_holomorphic)
    (SpecialPeriods.BetaTorsor.phiTwo_holomorphic D.tau_holomorphic D.mu_holomorphic)

def SpecialPeriods.BetaTorsor.Data.shift (D : SpecialPeriods.BetaTorsor.Data) :
    SpecialPeriods.TriangleGroup → ℍ → ℂ :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift (SpecialPeriods.BetaTorsor.phiOne D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiOne_sum_range D.tau_covariant D.mu_one)
    (SpecialPeriods.BetaTorsor.phiTwo_sum_range D.tau_covariant D.mu_two)

@[simp]
theorem SpecialPeriods.BetaTorsor.Data.cocycle_scale (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) : D.cocycle.scale g z = 1 :=
  rfl

@[simp]
theorem SpecialPeriods.BetaTorsor.Data.cocycle_shift (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) : D.cocycle.shift g z = D.shift g z :=
  rfl

theorem SpecialPeriods.BetaTorsor.Data.cocycle_fibreMap (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (u : ℂ) :
    D.cocycle.fibreMap g z u = u + D.shift g z := by
  simp only [SpecialPeriods.MuTorsor.AffineCocycle.fibreMap, D.cocycle_scale, Units.val_one,
    one_mul, D.cocycle_shift]

@[simp]
theorem SpecialPeriods.BetaTorsor.Data.shift_one (D : SpecialPeriods.BetaTorsor.Data) (z : ℍ) :
    D.shift 1 z = 0 :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_one ..

theorem SpecialPeriods.BetaTorsor.Data.shift_mul (D : SpecialPeriods.BetaTorsor.Data)
    (g h : SpecialPeriods.TriangleGroup) (z : ℍ) :
    D.shift (g * h) z =
      D.shift g (SpecialPeriods.triangleGeometricRepresentation h z) + D.shift h z :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_mul ..

theorem SpecialPeriods.BetaTorsor.Data.shift_inv (D : SpecialPeriods.BetaTorsor.Data)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    D.shift g⁻¹ z = -D.shift g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_inv ..

@[simp]
theorem SpecialPeriods.BetaTorsor.Data.shift_generator₁ (D : SpecialPeriods.BetaTorsor.Data)
    (z : ℍ) :
    D.shift SpecialPeriods.triangleGenerator₁ z = SpecialPeriods.BetaTorsor.phiOne D.tau D.mu z :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₁ ..

@[simp]
theorem SpecialPeriods.BetaTorsor.Data.shift_generator₂ (D : SpecialPeriods.BetaTorsor.Data)
    (z : ℍ) :
    D.shift SpecialPeriods.triangleGenerator₂ z = SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu z :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_generator₂ ..

@[simp]
theorem SpecialPeriods.BetaTorsor.Data.shift_cusp (D : SpecialPeriods.BetaTorsor.Data) (z : ℍ) :
    D.shift SpecialPeriods.triangleCuspGenerator z = 1 :=
  SpecialPeriods.BetaTorsor.triangleAdditiveShift_cusp
    (SpecialPeriods.BetaTorsor.phiOne D.tau D.mu) (SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu)
    (SpecialPeriods.BetaTorsor.phiOne_sum_range D.tau_covariant D.mu_one)
    (SpecialPeriods.BetaTorsor.phiTwo_sum_range D.tau_covariant D.mu_two)
    (SpecialPeriods.BetaTorsor.phi_product_relation D.tau_covariant D.mu_two) z

theorem SpecialPeriods.BetaTorsor.Data.covariance_zpowers (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z : ℍ, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + D.shift g z)
    {h : SpecialPeriods.TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (SpecialPeriods.triangleGeometricRepresentation h z) = β z + D.shift h z :=
  SpecialPeriods.BetaTorsor.covariance_zpowers D.shift D.shift_one D.shift_mul D.shift_inv β g hg
    hh z

def SpecialPeriods.BetaTorsor.Data.ellipticPrimitive (D : SpecialPeriods.BetaTorsor.Data) :
    Elliptic.Kind → ℍ → ℂ
  | .three => SpecialPeriods.BetaTorsor.primitiveOne D.tau D.mu
  | .four => SpecialPeriods.BetaTorsor.primitiveTwo D.tau D.mu

theorem SpecialPeriods.BetaTorsor.Data.ellipticPrimitive_holomorphic
    (D : SpecialPeriods.BetaTorsor.Data) (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.ellipticPrimitive j) := by
  cases j
  · exact SpecialPeriods.BetaTorsor.primitiveOne_holomorphic D.tau_holomorphic D.mu_holomorphic
  · exact SpecialPeriods.BetaTorsor.primitiveTwo_holomorphic D.tau_holomorphic D.mu_holomorphic

theorem SpecialPeriods.BetaTorsor.Data.ellipticPrimitive_generator
    (D : SpecialPeriods.BetaTorsor.Data) (j : Elliptic.Kind) (z : ℍ) :
    D.ellipticPrimitive j
        (SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.Triangle.ellipticGenerator j) z) =
      D.ellipticPrimitive j z + D.shift (SpecialPeriods.Triangle.ellipticGenerator j) z := by
  cases j
  · change
      SpecialPeriods.BetaTorsor.primitiveOne D.tau D.mu
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z) =
        SpecialPeriods.BetaTorsor.primitiveOne D.tau D.mu z +
          D.shift SpecialPeriods.triangleGenerator₁ z
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply, D.shift_generator₁]
    exact
      sub_eq_iff_eq_add'.mp
        (SpecialPeriods.BetaTorsor.primitiveOne_difference D.tau_covariant D.mu_one z)
  · change
      SpecialPeriods.BetaTorsor.primitiveTwo D.tau D.mu
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z) =
        SpecialPeriods.BetaTorsor.primitiveTwo D.tau D.mu z +
          D.shift SpecialPeriods.triangleGenerator₂ z
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply, D.shift_generator₂]
    exact
      sub_eq_iff_eq_add'.mp
        (SpecialPeriods.BetaTorsor.primitiveTwo_difference D.tau_covariant D.mu_two z)

theorem SpecialPeriods.BetaTorsor.Data.ellipticPrimitive_additive
    (D : SpecialPeriods.BetaTorsor.Data) (j : Elliptic.Kind) {g : SpecialPeriods.TriangleGroup}
    (hg : g ∈ SpecialPeriods.Triangle.ellipticStabilizer j) (z : ℍ) :
    D.ellipticPrimitive j (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.ellipticPrimitive j z + D.shift g z := by
  apply
    D.covariance_zpowers (D.ellipticPrimitive j) (SpecialPeriods.Triangle.ellipticGenerator j)
      (D.ellipticPrimitive_generator j)
  simpa only [SpecialPeriods.Triangle.ellipticStabilizer_eq_zpowers] using hg

theorem SpecialPeriods.BetaTorsor.Data.cuspPrimitive_generator
    (D : SpecialPeriods.BetaTorsor.Data) (z : ℍ) :
    SpecialPeriods.BetaTorsor.cuspPrimitive D.tau
        (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator z) =
      SpecialPeriods.BetaTorsor.cuspPrimitive D.tau z +
        D.shift SpecialPeriods.triangleCuspGenerator z := by
  rw [D.shift_cusp]
  exact
    sub_eq_iff_eq_add'.mp (SpecialPeriods.BetaTorsor.cuspPrimitive_difference D.tau_covariant z)

theorem SpecialPeriods.BetaTorsor.Data.cuspPrimitive_additive (D : SpecialPeriods.BetaTorsor.Data)
    {g : SpecialPeriods.TriangleGroup}
    (hg : g ∈ Subgroup.zpowers SpecialPeriods.triangleCuspGenerator) (z : ℍ) :
    SpecialPeriods.BetaTorsor.cuspPrimitive D.tau
        (SpecialPeriods.triangleGeometricRepresentation g z) =
      SpecialPeriods.BetaTorsor.cuspPrimitive D.tau z + D.shift g z :=
  D.covariance_zpowers (SpecialPeriods.BetaTorsor.cuspPrimitive D.tau)
    SpecialPeriods.triangleCuspGenerator D.cuspPrimitive_generator hg z

def SpecialPeriods.BetaTorsor.Data.regularSeed (D : SpecialPeriods.BetaTorsor.Data)
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (SpecialPeriods.MuTorsor.Cover.regularPatch x).Seed D.cocycle
    where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    have hg : (g : SpecialPeriods.TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    rw [hg, D.cocycle.fibreMap_one]

def SpecialPeriods.BetaTorsor.Data.ellipticSeed (D : SpecialPeriods.BetaTorsor.Data)
    (j : Elliptic.Kind) : (SpecialPeriods.MuTorsor.Cover.ellipticPatch j).Seed D.cocycle
    where
  toFun := D.ellipticPrimitive j
  holomorphic := (D.ellipticPrimitive_holomorphic j).contMDiffOn
  equivariant := by
    intro g z _
    rw [D.cocycle_fibreMap]
    exact D.ellipticPrimitive_additive j g.property z

def SpecialPeriods.BetaTorsor.Data.cuspSeed (D : SpecialPeriods.BetaTorsor.Data) :
    SpecialPeriods.MuTorsor.Cover.cuspPatch.Seed D.cocycle
    where
  toFun := SpecialPeriods.BetaTorsor.cuspPrimitive D.tau
  holomorphic :=
    (SpecialPeriods.BetaTorsor.cuspPrimitive_holomorphic D.tau_holomorphic).contMDiffOn
  equivariant := by
    intro g z _
    rw [D.cocycle_fibreMap]
    exact D.cuspPrimitive_additive g.property z

def SpecialPeriods.BetaTorsor.Data.seed (D : SpecialPeriods.BetaTorsor.Data)
    (i : SpecialPeriods.MuTorsor.Cover.Index) :
    (SpecialPeriods.MuTorsor.Cover.patch i).Seed D.cocycle :=
  match i with
  | none => D.cuspSeed
  | some (.inl x) => D.regularSeed x
  | some (.inr j) => D.ellipticSeed j

def SpecialPeriods.BetaTorsor.Data.localSection (D : SpecialPeriods.BetaTorsor.Data)
    (i : SpecialPeriods.MuTorsor.Cover.Index) : ℍ → ℂ :=
  (D.seed i).extend

theorem SpecialPeriods.BetaTorsor.Data.localSection_holomorphic
    (D : SpecialPeriods.BetaTorsor.Data) (i : SpecialPeriods.MuTorsor.Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.localSection i)
      (SpecialPeriods.MuTorsor.Cover.patch i).saturation :=
  (D.seed i).extend_holomorphic

theorem SpecialPeriods.BetaTorsor.Data.localSection_additive (D : SpecialPeriods.BetaTorsor.Data)
    (i : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (hz : z ∈ (SpecialPeriods.MuTorsor.Cover.patch i).saturation) :
    D.localSection i (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.localSection i z + D.shift g z := by
  have he := (D.seed i).extend_equivariant g z hz
  rwa [D.cocycle_fibreMap] at he

theorem SpecialPeriods.BetaTorsor.Data.localSection_cusp (D : SpecialPeriods.BetaTorsor.Data)
    (z : ℍ) (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) :
    D.localSection SpecialPeriods.MuTorsor.Cover.cuspIndex z = -(D.tau z : ℂ) :=
  D.cuspSeed.extend_eq z hz

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.patchSaturation (i : SpecialPeriods.MuTorsor.Cover.Index) :
    TopologicalSpace.Opens ℍ :=
  ⟨(SpecialPeriods.MuTorsor.Cover.patch i).saturation,
    (SpecialPeriods.MuTorsor.Cover.patch i).saturation_isOpen⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.patchSaturation_invariant
    (i : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ patchSaturation i ↔
      z ∈ patchSaturation i :=
  (SpecialPeriods.MuTorsor.Cover.patch i).saturation_invariant g z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.overlapDomain (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    TopologicalSpace.Opens ℍ :=
  patchSaturation i ⊓ patchSaturation j

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.overlapDomain_invariant
    (i j : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ overlapDomain i j ↔
      z ∈ overlapDomain i j :=
  (patchSaturation_invariant i g z).and (patchSaturation_invariant j g z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteProjection_mem_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) (z : ℍ) :
    finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π i ↔
      z ∈ patchSaturation i := by
  rw [SpecialPeriods.MuTorsor.Cover.finitePatch, finiteProjection_mem_pullback π hπ]
  change
    z ∈
        SpecialPeriods.triangleCompactifiedProjection ⁻¹'
          (SpecialPeriods.MuTorsor.Cover.compactPatch i :
            Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ↔
      _
  rw [SpecialPeriods.MuTorsor.Cover.compactPatch_preimage_projection]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteProjection_preimage_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) :
    finiteProjection π ⁻¹' (SpecialPeriods.MuTorsor.Cover.finitePatch π i : Set ℂ) =
      patchSaturation i := by
  ext z
  exact finiteProjection_mem_patch π hπ i z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.finiteDescentDomain_overlap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    finiteDescentDomain π hπ (overlapDomain i j) =
      SpecialPeriods.MuTorsor.Cover.finitePatch π i ⊓
        SpecialPeriods.MuTorsor.Cover.finitePatch π j := by
  ext t
  obtain ⟨z, rfl⟩ := finiteProjection_surjective π hπ t
  change
    finiteProjection π z ∈ finiteDescentDomain π hπ (overlapDomain i j) ↔
      finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π i ∧
        finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π j
  rw [finiteDescentDomain_projection π hπ _ (overlapDomain_invariant i j)]
  change
    z ∈ patchSaturation i ∧ z ∈ patchSaturation j ↔
      finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π i ∧
        finiteProjection π z ∈ SpecialPeriods.MuTorsor.Cover.finitePatch π j
  rw [finiteProjection_mem_patch π hπ i, finiteProjection_mem_patch π hπ j]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.Data.overlapDifference (D : SpecialPeriods.BetaTorsor.Data)
    (i j : SpecialPeriods.MuTorsor.Cover.Index) (z : ℍ) : ℂ :=
  D.localSection i z - D.localSection j z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.overlapDifference_invariant
    (D : SpecialPeriods.BetaTorsor.Data) (i j : SpecialPeriods.MuTorsor.Cover.Index)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (hz : z ∈ SpecialPeriods.BetaTorsor.overlapDomain i j) :
    D.overlapDifference i j (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.overlapDifference i j z := by
  dsimp only [overlapDifference]
  rw [D.localSection_additive i g z hz.1, D.localSection_additive j g z hz.2]
  ring

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.overlapDifference_holomorphic
    (D : SpecialPeriods.BetaTorsor.Data) (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.overlapDifference i j)
      (SpecialPeriods.BetaTorsor.overlapDomain i j) :=
  ((D.localSection_holomorphic i).mono (fun _ hz => hz.1)).sub
    ((D.localSection_holomorphic j).mono (fun _ hz => hz.2))

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.Data.overlapCocycle (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) : ℂ → ℂ :=
  SpecialPeriods.BetaTorsor.finiteDescent π hπ (SpecialPeriods.BetaTorsor.overlapDomain i j)
    (D.overlapDifference i j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.overlapCocycle_analytic
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) :
    AnalyticOnNhd ℂ (D.overlapCocycle π hπ i j)
      ((SpecialPeriods.MuTorsor.Cover.finitePatch π i : Set ℂ) ∩
        SpecialPeriods.MuTorsor.Cover.finitePatch π j) := by
  have h :=
    SpecialPeriods.BetaTorsor.finiteDescent_analytic π hπ
      (SpecialPeriods.BetaTorsor.overlapDomain i j) (D.overlapDifference i j)
      (SpecialPeriods.BetaTorsor.overlapDomain_invariant i j) (D.overlapDifference_invariant i j)
      (D.overlapDifference_holomorphic i j)
  rw [SpecialPeriods.BetaTorsor.finiteDescentDomain_overlap] at h
  exact h

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.localSection_difference
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : SpecialPeriods.MuTorsor.Cover.Index) (z : ℍ)
    (hi :
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.MuTorsor.Cover.finitePatch π i)
    (hj :
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.MuTorsor.Cover.finitePatch π j) :
    D.localSection i z - D.localSection j z =
      D.overlapCocycle π hπ i j (SpecialPeriods.BetaTorsor.finiteProjection π z) :=
  (SpecialPeriods.BetaTorsor.finiteDescent_projection π hπ
      (SpecialPeriods.BetaTorsor.overlapDomain i j) (D.overlapDifference i j)
      (SpecialPeriods.BetaTorsor.overlapDomain_invariant i j) (D.overlapDifference_invariant i j)
      ⟨(SpecialPeriods.BetaTorsor.finiteProjection_mem_patch π hπ i z).mp hi,
        (SpecialPeriods.BetaTorsor.finiteProjection_mem_patch π hπ j z).mp hj⟩).symm

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.localSection_holomorphic_finite
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.localSection i)
      (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹'
        (SpecialPeriods.MuTorsor.Cover.finitePatch π i : Set ℂ)) := by
  rw [SpecialPeriods.BetaTorsor.finiteProjection_preimage_patch π hπ]
  exact D.localSection_holomorphic i

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.localSection_additive_finite
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : SpecialPeriods.MuTorsor.Cover.Index) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (hz :
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.MuTorsor.Cover.finitePatch π i) :
    D.localSection i (SpecialPeriods.triangleGeometricRepresentation g z) =
      D.localSection i z + D.shift g z :=
  D.localSection_additive i g z
    ((SpecialPeriods.BetaTorsor.finiteProjection_mem_patch π hπ i z).mp hz)

theorem SpecialPeriods.BetaTorsorGluing.descended_difference_cocycle {X ι : Type*} {π : X → ℂ}
    (hπ : Function.Surjective π) {U : ι → Set ℂ} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) :
    ∀ i j k w, w ∈ U i → w ∈ U j → w ∈ U k → h i j w + h j k w = h i k w := by
  intro i j k w hi hj hk
  obtain ⟨z, rfl⟩ := hπ w
  rw [← hdiff i j z hi hj, ← hdiff j k z hj hk, ← hdiff i k z hi hk]
  ring

def SpecialPeriods.BetaTorsorGluing.correctedGlue {X ι : Type*} (π : X → ℂ) (U : ι → Set ℂ)
    (hcover : ∀ w, ∃ i, w ∈ U i) (βlocal : ι → X → ℂ) {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R) (z : X) : ℂ :=
  βlocal (hcover (π z)).choose z - c.localPart (hcover (π z)).choose (π z)

theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_eq {X ι : Type*} {π : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) {i : ι}
    {z : X} (hz : π z ∈ U i) :
    correctedGlue π U hcover βlocal c z = βlocal i z - c.localPart i (π z) := by
  let j := (hcover (π z)).choose
  have hj : π z ∈ U j := (hcover (π z)).choose_spec
  change βlocal j z - c.localPart j (π z) = βlocal i z - c.localPart i (π z)
  have hb := hdiff j i z hj hz
  have hc := c.equation j i (π z) hj hz
  linear_combination hb - hc

theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_eventuallyEq {X ι : Type*}
    [TopologicalSpace X] {π : X → ℂ} (hπ : Continuous π) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) {i : ι}
    {z : X} (hz : π z ∈ U i) :
    correctedGlue π U hcover βlocal c =ᶠ[𝓝 z] fun w => βlocal i w - c.localPart i (π w) := by
  filter_upwards [((hU i).preimage hπ).mem_nhds hz] with w hw
  exact correctedGlue_eq c hdiff hw

theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_holomorphic {ι : Type*} {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i)) {h : ι → ι → ℂ → ℂ} {i₀ : ι}
    {R : ℝ} (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue π U hcover βlocal c) := by
  intro z
  obtain ⟨i, hi⟩ := hcover (π z)
  have hb : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) z :=
    (hβ i).contMDiffAt (((hU i).preimage hπ.continuous).mem_nhds hi)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => c.localPart i (π w)) z :=
    (c.local_analytic i (π z) hi).contDiffAt.contMDiffAt.comp z (hπ z)
  exact (hb.sub hc).congr_of_eventuallyEq (correctedGlue_eventuallyEq hπ.continuous hU c hdiff hi)

theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_additive_law {X ι : Type*} {G : Type*}
    {π : X → ℂ} {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z))
    (A : G → X → X) (δ : G → X → ℂ) (hπA : ∀ g z, π (A g z) = π z)
    (hβA : ∀ i g z, π z ∈ U i → βlocal i (A g z) = βlocal i z + δ g z) (g : G) (z : X) :
    correctedGlue π U hcover βlocal c (A g z) = correctedGlue π U hcover βlocal c z + δ g z := by
  obtain ⟨i, hi⟩ := hcover (π z)
  have hiA : π (A g z) ∈ U i := by rwa [hπA g z]
  rw [correctedGlue_eq c hdiff hiA, correctedGlue_eq c hdiff hi, hπA g z, hβA i g z hi]
  ring

theorem SpecialPeriods.BetaTorsorGluing.correctedGlue_cusp {X ι : Type*} {π : X → ℂ}
    {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {βlocal : ι → X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι}
    {R : ℝ} (c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z))
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) {τ : X → ℂ} {W : Set X}
    (hβ₀ : ∀ z ∈ W, βlocal i₀ z = -τ z) {z : X} (hz : z ∈ W) (hlarge : R < ‖π z‖) :
    correctedGlue π U hcover βlocal c z + τ z = -c.infinityPart (π z)⁻¹ := by
  have hzU : π z ∈ U i₀ :=
    hRU
      (by
        simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hlarge.le)
  rw [correctedGlue_eq c hdiff hzU, hβ₀ z hz, c.atInfinity (π z) hlarge]
  ring

theorem SpecialPeriods.BetaTorsorGluing.exists_corrected_gluing {ι : Type*} {π : ℍ → ℂ}
    (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (hπsurj : Function.Surjective π) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i) {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i)) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) (i₀ : ι)
    {R : ℝ} (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ c : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue π U hcover βlocal c) ∧
        ∀ i,
          Set.EqOn (correctedGlue π U hcover βlocal c) (fun z => βlocal i z - c.localPart i (π z))
            (π ⁻¹' U i) := by
  obtain ⟨c⟩ :=
    HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution hU hcover hh
      (descended_difference_cocycle hπsurj hdiff) i₀ hR hRU
  exact ⟨c, correctedGlue_holomorphic hπ hU hβ c hdiff, fun _ _ hz => correctedGlue_eq c hdiff hz⟩

theorem SpecialPeriods.BetaTorsorGluing.exists_glued_beta_with_cusp {ι : Type*} {G : Type*}
    {π : ℍ → ℂ} (hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π) (hπsurj : Function.Surjective π) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i) {βlocal : ι → ℍ → ℂ}
    (hβ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (βlocal i) (π ⁻¹' U i)) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hdiff : ∀ i j z, π z ∈ U i → π z ∈ U j → βlocal i z - βlocal j z = h i j (π z)) (i₀ : ι)
    {R : ℝ} (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) (A : G → ℍ → ℍ) (δ : G → ℍ → ℂ)
    (hπA : ∀ g z, π (A g z) = π z)
    (hβA : ∀ i g z, π z ∈ U i → βlocal i (A g z) = βlocal i z + δ g z) (τ : ℍ → ℂ) (W : Set ℍ)
    (hβ₀ : ∀ z ∈ W, βlocal i₀ z = -τ z) :
    ∃ (β : ℍ → ℂ) (B : ℂ → ℂ),
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧
        AnalyticOnNhd ℂ B (Metric.ball 0 R⁻¹) ∧
          B 0 = 0 ∧
            (∀ g z, β (A g z) = β z + δ g z) ∧ ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹ := by
  obtain ⟨c, hc, _⟩ := exists_corrected_gluing hπ hπsurj hU hcover hβ hh hdiff i₀ hR hRU
  refine
    ⟨correctedGlue π U hcover βlocal c, fun u => -c.infinityPart u, hc, c.infinity_analytic.neg,
      ?_, ?_, ?_⟩
  · change -c.infinityPart 0 = 0
    rw [c.infinity_zero, neg_zero]
  · exact correctedGlue_additive_law c hdiff A δ hπA hβA
  · intro z hz hlarge
    exact correctedGlue_cusp c hdiff hRU hβ₀ hz hlarge

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.Data.GeneratorLaws (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) : Prop :=
  (∀ z : ℍ,
      β (SpecialPeriods.Triangle.generatorOneSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiOne D.tau D.mu z) ∧
    (∀ z : ℍ,
      β (SpecialPeriods.Triangle.generatorTwoSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.generatorLaws_of_all_words
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ}
    (hβ :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, β (SpecialPeriods.triangleGeometricRepresentation g z) = β z + D.shift g z) :
    D.GeneratorLaws β := by
  constructor
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      D.shift_generator₁] using hβ SpecialPeriods.triangleGenerator₁ z
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
      D.shift_generator₂] using hβ SpecialPeriods.triangleGenerator₂ z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.GeneratorLaws.add_const
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (c : ℂ) :
    D.GeneratorLaws (fun z => β z + c) := by
  constructor
  · intro z
    dsimp only
    rw [hβ.1 z]
    ring
  · intro z
    dsimp only
    rw [hβ.2 z]
    ring

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.exists_global_beta (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ R : ℝ,
      0 < R ∧
        ∃ (β : ℍ → ℂ) (B : ℂ → ℂ),
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β ∧
            D.GeneratorLaws β ∧
              AnalyticOnNhd ℂ B (Metric.ball 0 R⁻¹) ∧
                B 0 = 0 ∧
                  ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
                    R < ‖SpecialPeriods.BetaTorsor.finiteProjection π z‖ →
                      β z + (D.tau z : ℂ) =
                        B (SpecialPeriods.BetaTorsor.finiteProjection π z)⁻¹ := by
  obtain ⟨R, hR, hRU⟩ := SpecialPeriods.MuTorsor.Cover.finitePatch_cusp_contains_exterior π hπ
  obtain ⟨β, B, hβ, hB, hB0, hwords, hcusp⟩ :=
    SpecialPeriods.BetaTorsorGluing.exists_glued_beta_with_cusp
      (SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ)
      (SpecialPeriods.BetaTorsor.finiteProjection_surjective π hπ)
      (fun i => (SpecialPeriods.MuTorsor.Cover.finitePatch π i).isOpen)
      (SpecialPeriods.MuTorsor.Cover.exists_finitePatch π)
      (D.localSection_holomorphic_finite π hπ) (D.overlapCocycle_analytic π hπ)
      (D.localSection_difference π hπ) SpecialPeriods.MuTorsor.Cover.cuspIndex hR hRU
      (fun g z => SpecialPeriods.triangleGeometricRepresentation g z) D.shift
      (SpecialPeriods.BetaTorsor.finiteProjection_invariant π)
      (D.localSection_additive_finite π hπ) (fun z => (D.tau z : ℂ))
      (SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) D.localSection_cusp
  exact ⟨R, hR, β, B, hβ, D.generatorLaws_of_all_words hwords, hB, hB0, hcusp⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.BetaTorsor.qExtension
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (B : ℂ → ℂ) (q : ℂ) : ℂ :=
  B (SpecialPeriods.MuTorsor.CuspCoordinates.t π q)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.qExtension_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) (B : ℂ → ℂ) :
    qExtension π B 0 = B 0 := by
  rw [qExtension, SpecialPeriods.MuTorsor.CuspCoordinates.t_zero π hπ]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.qExtension_analyticAt_zero
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) : AnalyticAt ℂ (qExtension π B) 0 := by
  have ht : AnalyticAt ℂ B (SpecialPeriods.MuTorsor.CuspCoordinates.t π 0) := by
    rw [SpecialPeriods.MuTorsor.CuspCoordinates.t_zero π hπ]
    exact hB
  exact ht.comp (SpecialPeriods.MuTorsor.CuspCoordinates.t_analyticAt_zero π hπ)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.cusp_formula_eventually_q
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ}
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      β z + (τ z : ℂ) = qExtension π B (SpecialPeriods.Triangle.cuspQ z) := by
  filter_upwards [SpecialPeriods.MuTorsor.CuspCoordinates.eventually_mem_horodisc
      SpecialPeriods.Triangle.width,
    SpecialPeriods.MuTorsor.CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R,
    SpecialPeriods.MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ] with z hz hRz ht
  rw [hformula z hz hRz]
  change
    B (finiteProjection π z)⁻¹ =
      B (SpecialPeriods.MuTorsor.CuspCoordinates.t π (SpecialPeriods.Triangle.cuspQ z))
  rw [ht]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.analytic_cusp_formula_to_q_extension
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ} (hB : AnalyticAt ℂ B 0)
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∃ C : ℂ → ℂ,
      AnalyticAt ℂ C 0 ∧
        C 0 = B 0 ∧
          ∃ Y : ℝ, ∀ z : ℍ, Y < z.im → β z + (τ z : ℂ) = C (SpecialPeriods.Triangle.cuspQ z) := by
  refine ⟨qExtension π B, qExtension_analyticAt_zero π hπ hB, qExtension_zero π hπ B, ?_⟩
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp (cusp_formula_eventually_q π hπ hformula)
  exact ⟨Y, fun z hz => hY z hz.le⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.tendsto_of_analytic_cusp_formula
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ} (hB : AnalyticAt ℂ B 0)
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    Filter.Tendsto (fun z : ℍ => β z + (τ z : ℂ)) UpperHalfPlane.atImInfty (𝓝 (B 0)) := by
  have hlim :
    Filter.Tendsto (fun z : ℍ => B (finiteProjection π z)⁻¹) UpperHalfPlane.atImInfty (𝓝 (B 0)) :=
    hB.continuousAt.tendsto.comp
      ((SpecialPeriods.MuTorsor.CuspCoordinates.finiteProjection_inv_tendsto_zero π hπ).mono_right
        nhdsWithin_le_nhds)
  apply hlim.congr'
  filter_upwards [SpecialPeriods.MuTorsor.CuspCoordinates.eventually_mem_horodisc
      SpecialPeriods.Triangle.width,
    SpecialPeriods.MuTorsor.CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R] with z hz
    hRz
  exact (hformula z hz hRz).symm

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.bounded_of_analytic_cusp_formula
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {β : ℍ → ℂ}
    {τ : ℍ → ℍ} {B : ℂ → ℂ} {R : ℝ} (hB : AnalyticAt ℂ B 0)
    (hformula :
      ∀ z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width,
        R < ‖finiteProjection π z‖ → β z + (τ z : ℂ) = B (finiteProjection π z)⁻¹) :
    ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + (τ z : ℂ)‖ ≤ M := by
  have hlim := (tendsto_of_analytic_cusp_formula π hπ hB hformula).norm
  have hbound : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖β z + (τ z : ℂ)‖ < ‖B 0‖ + 1 :=
    hlim.eventually (Iio_mem_nhds (lt_add_one ‖B 0‖))
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound
  exact ⟨Y, ‖B 0‖ + 1, fun z hz => (hY z hz.le).le⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
structure SpecialPeriods.BetaTorsor.Data.IsSolution (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β
  generators : D.GeneratorLaws β
  cusp_bounded : ∃ Y M : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + (D.tau z : ℂ)‖ ≤ M

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.BetaTorsor.Data.exists_solution_with_cusp_extension
    (D : SpecialPeriods.BetaTorsor.Data)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ (β : ℍ → ℂ) (C : ℂ → ℂ),
      D.IsSolution β ∧
        AnalyticAt ℂ C 0 ∧
          C 0 = 0 ∧
            ∃ Y : ℝ,
              ∀ z : ℍ, Y < z.im → β z + (D.tau z : ℂ) = C (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨R, hR, β, B, hβ, hgen, hB, hB0, hformula⟩ := D.exists_global_beta π hπ
  have hBzero : AnalyticAt ℂ B 0 := hB 0 (Metric.mem_ball_self (inv_pos.mpr hR))
  obtain ⟨Y, M, hbound⟩ :=
    SpecialPeriods.BetaTorsor.bounded_of_analytic_cusp_formula π hπ hBzero hformula
  obtain ⟨C, hC, hC0, Y', hCformula⟩ :=
    SpecialPeriods.BetaTorsor.analytic_cusp_formula_to_q_extension π hπ hBzero hformula
  exact ⟨β, C, ⟨hβ, hgen, Y, M, hbound⟩, hC, hC0.trans hB0, Y', hCformula⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
structure SpecialPeriods.Construction.PeriodFunctions where
  data : SpecialPeriods.BetaTorsor.Data
  beta : ℍ → ℂ
  beta_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω beta
  beta_generators : data.GeneratorLaws beta
  tau_cusp :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h 0 ∧
        ∀ᶠ z in UpperHalfPlane.atImInfty,
          (data.tau z : ℂ) =
            (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z)
  mu_cusp : SpecialPeriods.MuTorsor.CuspRegular data.mu
  beta_cusp : SpecialPeriods.MuTorsor.CuspRegular (fun z => beta z + (data.tau z : ℂ))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Construction.eventually_norm_cuspQ_lt_mo1973_18146 {r : ℝ}
    (hr : 0 < r) : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖SpecialPeriods.Triangle.cuspQ z‖ < r := by
  have ht := SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  simpa only [Metric.mem_ball, dist_zero_right] using
    ht.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Construction.exists_periodFunctions_of_sphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ F : PeriodFunctions, F.data.tau = SpecialPeriods.TriangleSource.tauOfSphere π hπ h₀ h₁ := by
  let τ := SpecialPeriods.TriangleSource.tauOfSphere π hπ h₀ h₁
  have hτa := SpecialPeriods.TriangleSource.tauOfSphere_holomorphic π hπ h₀ h₁
  have hτc := SpecialPeriods.TriangleSource.tauOfSphere_covariant π hπ h₀ h₁
  have hJ := SpecialPeriods.TriangleSource.tauOfSphere_modular π hπ h₀ h₁
  obtain ⟨r, hr, _, h, hh, hτformula⟩ := SpecialPeriods.TriangleSource.tauOfSphere_cusp π hπ h₀ h₁
  have hh0 : AnalyticAt ℂ h 0 := hh 0 (Metric.mem_ball_self hr)
  have hτformula' :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (τ z : ℂ) = (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z) :=
    by
    filter_upwards [eventually_norm_cuspQ_lt_mo1973_18146 hr] with z hz
    exact hτformula z hz
  obtain ⟨ru, hru, u, hu, hu0, hqu⟩ :=
    SpecialPeriods.TriangleSource.tauOfSphere_cusp_unit π hπ h₀ h₁
  have hu0a : AnalyticAt ℂ u 0 := hu 0 (Metric.mem_ball_self hru)
  have hqu' :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      Function.Periodic.qParam 1 (τ z) =
        SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z) := by
    filter_upwards [eventually_norm_cuspQ_lt_mo1973_18146 hru] with z hz
    exact hqu z hz
  obtain ⟨μ, hμ, _⟩ :=
    SpecialPeriods.MuTorsor.exists_unique_solution π hπ h₀ h₁ hτc hτa hJ hu0a hu0 hqu'
  let D : SpecialPeriods.BetaTorsor.Data :=
    { tau := τ
      mu := μ
      tau_holomorphic := hτa
      mu_holomorphic := hμ.holomorphic
      tau_covariant := hτc
      mu_one := hμ.generatorOne
      mu_two := hμ.generatorTwo }
  obtain ⟨β, b, hβ, hb, _, Y, hβformula⟩ := D.exists_solution_with_cusp_extension π hπ
  have hβformula' :
    ∀ᶠ z in UpperHalfPlane.atImInfty, β z + (D.tau z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z) :=
    by
    apply (UpperHalfPlane.atImInfty_mem _).mpr
    exact ⟨Y + 1, fun z hz => hβformula z (by linarith)⟩
  exact
    ⟨{  data := D
        beta := β
        beta_holomorphic := hβ.holomorphic
        beta_generators := hβ.generators
        tau_cusp := ⟨h, hh0, hτformula'⟩
        mu_cusp := hμ.cuspRegular
        beta_cusp := ⟨b, hb, hβformula'⟩ }, rfl⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Construction.periodFunctionsOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    PeriodFunctions :=
  (exists_periodFunctions_of_sphere π hπ h₀ h₁).choose

theorem PeriodPoint.discriminant_le_im_beta (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    p.discriminant ≤ p.β.im := by
  exact sub_le_self _ (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hτ.le)

theorem PeriodPoint.discriminant_le_im_beta_add_tau_sub (p : PeriodPoint) (hτ : 0 < p.τ.im) :
    p.discriminant ≤ (p.β + p.τ).im - p.τ.im := by
  simpa only [Complex.add_im, add_sub_cancel_right] using p.discriminant_le_im_beta hτ

theorem PeriodPoint.tendsto_discriminant_atBot {X : Type*} {l : Filter X} (P : X → PeriodPoint)
    (hτ : ∀ᶠ z in l, 0 < (P z).τ.im) (hτinf : Filter.Tendsto (fun z => (P z).τ.im) l Filter.atTop)
    (hb : ∃ C : ℝ, ∀ᶠ z in l, ((P z).β + (P z).τ).im ≤ C) :
    Filter.Tendsto (fun z => (P z).discriminant) l Filter.atBot := by
  obtain ⟨C, hC⟩ := hb
  refine Filter.tendsto_atBot.mpr fun R => ?_
  filter_upwards [hτ, hC, hτinf.eventually_ge_atTop (C - R)] with z hzτ hzC hzR
  have hD := (P z).discriminant_le_im_beta_add_tau_sub hzτ
  linarith

theorem PeriodPoint.continuousOn_discriminant {X : Type*} [TopologicalSpace X]
    (P : X → PeriodPoint) {s : Set X} (hτ : ContinuousOn (fun z => (P z).τ) s)
    (hμ : ContinuousOn (fun z => (P z).μ) s) (hβ : ContinuousOn (fun z => (P z).β) s)
    (hτ₀ : ∀ z ∈ s, (P z).τ.im ≠ 0) : ContinuousOn (fun z => (P z).discriminant) s := by
  exact
    (Complex.continuous_im.comp_continuousOn hβ).sub
      ((continuousOn_const.mul ((Complex.continuous_im.comp_continuousOn hμ).pow 2)).div
        (Complex.continuous_im.comp_continuousOn hτ) hτ₀)

def PeriodPoint.shiftBeta (p : PeriodPoint) (c : ℂ) : PeriodPoint :=
  ⟨p.τ, p.μ, p.β + c⟩

@[simp]
theorem PeriodPoint.shiftBeta_discriminant (p : PeriodPoint) (c : ℂ) :
    (p.shiftBeta c).discriminant = p.discriminant + c.im := by
  simp only [discriminant, shiftBeta, Complex.add_im]
  ring

theorem PeriodPoint.exists_uniform_shift_of_bddAbove {X : Type*} (P : X → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im) (hD : BddAbove (Set.range fun z => (P z).discriminant)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℂ, c.im < -M → ∀ z, ((P z).shiftBeta c).Admissible := by
  obtain ⟨C, hC⟩ := hD
  refine ⟨Max.max C 0, le_max_right _ _, fun c hc z => ⟨hτ z, ?_⟩⟩
  rw [shiftBeta_discriminant]
  have hDz : (P z).discriminant ≤ C := hC (Set.mem_range_self z)
  have hCM : C ≤ Max.max C 0 := le_max_left _ _
  linarith

theorem PeriodPoint.exists_negative_imaginary_shift_of_bddAbove {X : Type*} (P : X → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im) (hD : BddAbove (Set.range fun z => (P z).discriminant)) :
    ∃ M : ℝ, 0 < M ∧ ∀ z, ((P z).shiftBeta (-((M : ℂ) * Complex.I))).Admissible := by
  obtain ⟨M, hM, hshift⟩ := exists_uniform_shift_of_bddAbove P hτ hD
  refine ⟨M + 1, by linarith, hshift _ ?_⟩
  simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, MulZeroClass.mul_zero, add_zero]
  linarith

theorem SpecialPeriods.exists_compact_cutoff_of_tendsto_atBot {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (f : B → ℝ) (hf : Filter.Tendsto f (𝓝[≠] p) Filter.atBot) :
    ∃ K : Set B,
      IsCompact K ∧ K ⊆ ({ p } : Set B)ᶜ ∧ ∀ x : B, x ∈ ({ p } : Set B)ᶜ → x ∉ K → f x < 0 := by
  obtain ⟨U, hU, hpU, hUf⟩ := mem_nhdsWithin.mp (hf.eventually_lt_atBot 0)
  refine ⟨Uᶜ, hU.isClosed_compl.isCompact, ?_, ?_⟩
  · intro x hx hp
    have hxp : x = p := by simpa only [Set.mem_singleton_iff] using hp
    exact hx (hxp ▸ hpU)
  · intro x hxp hx
    exact hUf ⟨Classical.not_not.mp hx, hxp⟩

theorem SpecialPeriods.bddAbove_image_punctured_of_tendsto_atBot {B : Type*} [TopologicalSpace B]
    [CompactSpace B] (p : B) (f : B → ℝ) (hc : ContinuousOn f ({ p } : Set B)ᶜ)
    (hf : Filter.Tendsto f (𝓝[≠] p) Filter.atBot) : BddAbove (f '' ({ p } : Set B)ᶜ) := by
  obtain ⟨K, hK, hKp, hneg⟩ := exists_compact_cutoff_of_tendsto_atBot p f hf
  obtain ⟨C, hC⟩ := hK.bddAbove_image (hc.mono hKp)
  refine ⟨Max.max C 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  by_cases hxK : x ∈ K
  · exact (hC (Set.mem_image_of_mem f hxK)).trans (le_max_left _ _)
  · exact (hneg x hx hxK).le.trans (le_max_right _ _)

theorem SpecialPeriods.Construction.triangle_invariant_of_generators {A : Type*} (f : ℍ → A)
    (h₁ : ∀ z, f (SpecialPeriods.Triangle.generatorOneSL • z) = f z)
    (h₂ : ∀ z, f (SpecialPeriods.Triangle.generatorTwoSL • z) = f z)
    (g : SpecialPeriods.TriangleGroup) :
    ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z := by
  let := SpecialPeriods.triangleGeometricAction
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    trivial
  change ∀ z, f (g • z) = f z
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · intro z
      change
        f (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z) =
          f z
      simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] using h₁ z
    · intro z
      change
        f (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z) =
          f z
      simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply] using h₂ z
  | one => intro z; rw [one_smul]
  | mul g h _ _ ihg ihh => intro z; rw [SemigroupAction.mul_smul, ihg, ihh]
  | inv g _ ih =>
    intro z
    simpa only [smul_inv_smul] using (ih (g⁻¹ • z)).symm

theorem SpecialPeriods.Construction.discriminant_invariant_of_generator_laws (P : ℍ → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im)
    (h₁ : ∀ z, P (SpecialPeriods.Triangle.generatorOneSL • z) = (P z).step₁)
    (h₂ : ∀ z, P (SpecialPeriods.Triangle.generatorTwoSL • z) = (P z).step₂) :
    ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
      (P (SpecialPeriods.triangleGeometricRepresentation g z)).discriminant =
        (P z).discriminant := by
  apply triangle_invariant_of_generators (fun z => (P z).discriminant)
  · intro z
    rw [h₁ z, PeriodPoint.step₁_discriminant (P z) (ne_of_gt (hτ z))]
  · intro z
    rw [h₂ z, PeriodPoint.step₂_discriminant (P z) (ne_of_gt (hτ z))]

def SpecialPeriods.BetaTorsor.Data.periodPoint (D : SpecialPeriods.BetaTorsor.Data) (β : ℍ → ℂ)
    (z : ℍ) : PeriodPoint :=
  ⟨(D.tau z : ℂ), D.mu z, β z⟩

def SpecialPeriods.BetaTorsor.Data.periodMap (D : SpecialPeriods.BetaTorsor.Data) (β : ℍ → ℂ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible) :
    HolomorphicPeriodMap ℂ ℍ
    where
  point z := ⟨D.periodPoint β z, hAdm z⟩
  holomorphic_tau := UpperHalfPlane.contMDiff_coe.comp D.tau_holomorphic
  holomorphic_mu := D.mu_holomorphic
  holomorphic_beta := hβ

def SpecialPeriods.BetaTorsor.Data.shiftedPeriodMap (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) : HolomorphicPeriodMap ℂ ℍ :=
  D.periodMap (fun z => β z + c) (hβ.add contMDiff_const) hAdm

theorem SpecialPeriods.Construction.periodPoint_im_tau_pos (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) (z : ℍ) : 0 < (D.periodPoint β z).τ.im :=
  (D.tau z).im_pos

theorem SpecialPeriods.Construction.periodPoint_generator₁_iff
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorOneSL • z) = (D.periodPoint β z).step₁ ↔
      β (SpecialPeriods.Triangle.generatorOneSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiOne D.tau D.mu z := by
  constructor
  · intro h
    have hb := congrArg PeriodPoint.β h
    simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₁,
      SpecialPeriods.BetaTorsor.phiOne, sub_eq_add_neg, add_assoc] using hb
  · intro hb
    apply PeriodPoint.ext
    · exact D.tau_covariant.1 z
    · exact D.mu_one z
    · simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₁,
        SpecialPeriods.BetaTorsor.phiOne, sub_eq_add_neg, add_assoc] using hb

theorem SpecialPeriods.Construction.periodPoint_generator₂_iff
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorTwoSL • z) = (D.periodPoint β z).step₂ ↔
      β (SpecialPeriods.Triangle.generatorTwoSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu z := by
  constructor
  · intro h
    have hb := congrArg PeriodPoint.β h
    simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₂,
      SpecialPeriods.BetaTorsor.phiTwo, sub_eq_add_neg, add_assoc] using hb
  · intro hb
    apply PeriodPoint.ext
    · exact D.tau_covariant.2 z
    · exact D.mu_two z
    · simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₂,
        SpecialPeriods.BetaTorsor.phiTwo, sub_eq_add_neg, add_assoc] using hb

theorem SpecialPeriods.Construction.periodPoint_generator₁ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorOneSL • z) = (D.periodPoint β z).step₁ :=
  (periodPoint_generator₁_iff D z).mpr (hβ.1 z)

theorem SpecialPeriods.Construction.periodPoint_generator₂ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorTwoSL • z) = (D.periodPoint β z).step₂ :=
  (periodPoint_generator₂_iff D z).mpr (hβ.2 z)

theorem SpecialPeriods.Construction.continuous_discriminant (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) :
    Continuous (fun z => (D.periodPoint β z).discriminant) := by
  exact
    continuousOn_univ.mp
      (PeriodPoint.continuousOn_discriminant (D.periodPoint β)
        (UpperHalfPlane.contMDiff_coe.comp D.tau_holomorphic).continuous.continuousOn
        D.mu_holomorphic.continuous.continuousOn hβ.continuous.continuousOn
        (fun z _ => (D.tau z).im_pos.ne'))

theorem SpecialPeriods.Construction.discriminant_invariant (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    (D.periodPoint β (SpecialPeriods.triangleGeometricRepresentation g z)).discriminant =
      (D.periodPoint β z).discriminant :=
  discriminant_invariant_of_generator_laws (D.periodPoint β) (periodPoint_im_tau_pos D β)
    (periodPoint_generator₁ D hβ) (periodPoint_generator₂ D hβ) g z

theorem SpecialPeriods.Construction.periodMap_generator₁ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (SpecialPeriods.Triangle.generatorOneSL • z) =
      ((D.periodMap β hβ hAdm).point z).step₁ :=
  Subtype.ext (periodPoint_generator₁ D hgen z)

theorem SpecialPeriods.Construction.periodMap_generator₂ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      ((D.periodMap β hβ hAdm).point z).step₂ :=
  Subtype.ext (periodPoint_generator₂ D hgen z)

theorem SpecialPeriods.Construction.shiftedPeriodMap_generator₁
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) (hgen : D.GeneratorLaws β)
    (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point (SpecialPeriods.Triangle.generatorOneSL • z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₁ :=
  periodMap_generator₁ D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

theorem SpecialPeriods.Construction.shiftedPeriodMap_generator₂
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) (hgen : D.GeneratorLaws β)
    (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₂ :=
  periodMap_generator₂ D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

theorem SpecialPeriods.Construction.exponential_normalized_eq_cuspQ (z : ℍ) :
    CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width) =
      SpecialPeriods.Triangle.cuspQ z := by
  simp only [CuspUniformization.exponential, SpecialPeriods.Triangle.cuspQ_eq_exp, mul_div_assoc]

theorem SpecialPeriods.Construction.cusp_analytic_tendsto {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    Filter.Tendsto (fun z : ℍ => f (SpecialPeriods.Triangle.cuspQ z)) UpperHalfPlane.atImInfty
      (𝓝 (f 0)) :=
  hf.continuousAt.tendsto.comp
    (SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)

theorem SpecialPeriods.Construction.tau_im_tendsto_atTop_of_cusp_formula {τ : ℍ → ℍ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0)
    (hτ :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        (τ z : ℂ) =
          (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z)) :
    Filter.Tendsto (fun z : ℍ => (τ z).im) UpperHalfPlane.atImInfty Filter.atTop := by
  have hheight :
    Filter.Tendsto (fun z : ℍ => z.im / SpecialPeriods.Triangle.width) UpperHalfPlane.atImInfty
      Filter.atTop :=
    (show Filter.Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty Filter.atTop from
          Filter.tendsto_comap).atTop_div_const
      SpecialPeriods.Triangle.width_pos
  have hremainder :
    Filter.Tendsto (fun z : ℍ => (h (SpecialPeriods.Triangle.cuspQ z)).im)
      UpperHalfPlane.atImInfty (𝓝 (h 0).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (cusp_analytic_tendsto hh)
  apply (hheight.atTop_add hremainder).congr'
  filter_upwards [hτ] with z hz
  simpa only [Complex.add_im, Complex.div_ofReal_im, UpperHalfPlane.coe_im] using
    (congrArg Complex.im hz).symm

theorem SpecialPeriods.Construction.periodPoint_eventually_eq_cuspPeriodPoint {τ : ℍ → ℍ}
    {μ β : ℍ → ℂ} {m b h : ℂ → ℂ}
    (hτ :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        (τ z : ℂ) = (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z))
    (hμ : ∀ᶠ z in UpperHalfPlane.atImInfty, μ z = m (SpecialPeriods.Triangle.cuspQ z))
    (hβ :
      ∀ᶠ z in UpperHalfPlane.atImInfty, β z + (τ z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z)) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (⟨(τ z : ℂ), μ z, β z⟩ : PeriodPoint) =
        SpecialPeriods.cuspPeriodPoint m b h ((z : ℂ) / SpecialPeriods.Triangle.width) := by
  filter_upwards [hτ, hμ, hβ] with z hτz hμz hβz
  apply PeriodPoint.ext
  · simpa only [SpecialPeriods.cuspPeriodPoint, exponential_normalized_eq_cuspQ] using hτz
  · simpa only [SpecialPeriods.cuspPeriodPoint, exponential_normalized_eq_cuspQ] using hμz
  · change
      β z =
        b (CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width)) -
            (z : ℂ) / SpecialPeriods.Triangle.width -
          h (CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width))
    rw [exponential_normalized_eq_cuspQ]
    calc
      β z = b (SpecialPeriods.Triangle.cuspQ z) - (τ z : ℂ) := eq_sub_of_add_eq hβz
      _ =
          b (SpecialPeriods.Triangle.cuspQ z) - (z : ℂ) / SpecialPeriods.Triangle.width -
            h (SpecialPeriods.Triangle.cuspQ z) := by
        rw [hτz]
        ring

theorem SpecialPeriods.Construction.eventual_cuspQ_radius {P : ℍ → Prop}
    (hP : ∀ᶠ z in UpperHalfPlane.atImInfty, P z) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℍ, ‖SpecialPeriods.Triangle.cuspQ z‖ < r → P z := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  refine ⟨Real.exp (-2 * Real.pi * Y / SpecialPeriods.Triangle.width), Real.exp_pos _, ?_⟩
  intro z hz
  exact hY z ((SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff Y z).mp hz).le

theorem SpecialPeriods.Construction.eventual_cuspQ_radius_lt {P : ℍ → Prop} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hP : ∀ᶠ z in UpperHalfPlane.atImInfty, P z) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ ∀ z : ℍ, ‖SpecialPeriods.Triangle.cuspQ z‖ < r → P z := by
  obtain ⟨r, hr, h⟩ := eventual_cuspQ_radius hP
  refine
    ⟨Min.min r (r₀ / 2), lt_min hr (half_pos hr₀), (min_le_right _ _).trans_lt (half_lt_self hr₀),
      ?_⟩
  intro z hz
  exact h z (hz.trans_le (min_le_left _ _))

theorem SpecialPeriods.Construction.beta_add_const_cusp_formula {τ : ℍ → ℍ} {β : ℍ → ℂ}
    {b : ℂ → ℂ}
    (hβ : ∀ᶠ z in UpperHalfPlane.atImInfty, β z + (τ z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z))
    (c : ℂ) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (β z + c) + (τ z : ℂ) = (fun q => b q + c) (SpecialPeriods.Triangle.cuspQ z) := by
  filter_upwards [hβ] with z hz
  simpa only [add_right_comm] using congrArg (fun w : ℂ => w + c) hz

def SpecialPeriods.Construction.orbitDescend (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z) :
    SpecialPeriods.TriangleOrbitSpace → ℝ :=
  Quotient.lift f fun x y hxy =>
    by
    change
      ∃ g : SpecialPeriods.TriangleGroup,
        SpecialPeriods.triangleGeometricRepresentation g y = x at hxy
    obtain ⟨g, hg⟩ := hxy
    exact (congrArg f hg).symm.trans (hinv g y)

theorem SpecialPeriods.Construction.orbitDescend_continuous (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : Continuous f) : Continuous (orbitDescend f hinv) :=
  hf.quotient_lift _

def SpecialPeriods.Construction.compactDescend (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) : SpecialPeriods.TriangleCompactifiedOrbitSpace → ℝ :=
  OnePoint.rec c (orbitDescend f hinv)

@[simp]
theorem SpecialPeriods.Construction.compactDescend_projection (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (z : ℍ) :
    compactDescend f hinv c
        (SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z)) =
      f z :=
  rfl

theorem SpecialPeriods.Construction.compactDescend_continuousAt_openInclusion (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (hf : Continuous f) (q : SpecialPeriods.TriangleOrbitSpace) :
    ContinuousAt (compactDescend f hinv c) (SpecialPeriods.triangleOpenInclusion q) :=
  OnePoint.continuousAt_coe.mpr (orbitDescend_continuous f hinv hf).continuousAt

theorem SpecialPeriods.Construction.compactDescend_continuousOn (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (hf : Continuous f) :
    ContinuousOn (compactDescend f hinv c)
      ({ SpecialPeriods.triangleCuspPoint } :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace)ᶜ := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx rfl).elim
  | coe q => exact (compactDescend_continuousAt_openInclusion f hinv c hf q).continuousWithinAt

theorem SpecialPeriods.Construction.compactDescend_eventually_of_atImInfty (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (P : ℝ → Prop) (hP : ∀ᶠ z in UpperHalfPlane.atImInfty, P (f z)) :
    ∀ᶠ x in 𝓝[≠] SpecialPeriods.triangleCuspPoint, P (compactDescend f hinv c x) := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  filter_upwards [nhdsWithin_le_nhds (SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds Y),
    self_mem_nhdsWithin] with x hx hxne
  induction x using OnePoint.rec with
  | infty => exact (hxne rfl).elim
  | coe
    q =>
    obtain ⟨z, hz, rfl⟩ :=
      (SpecialPeriods.Triangle.mem_cuspImage Y q).mp
        ((SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood Y q).mp hx)
    exact hY z hz.le

theorem SpecialPeriods.Construction.compactDescend_tendsto_atBot (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (hlim : Filter.Tendsto f UpperHalfPlane.atImInfty Filter.atBot) :
    Filter.Tendsto (compactDescend f hinv c) (𝓝[≠] SpecialPeriods.triangleCuspPoint)
      Filter.atBot := by
  refine Filter.tendsto_atBot.mpr fun R => ?_
  exact
    compactDescend_eventually_of_atImInfty f hinv c (fun t => t ≤ R) (hlim.eventually_le_atBot R)

theorem SpecialPeriods.Construction.bddAbove_range_of_triangle_invariant_tendsto_atBot (f : ℍ → ℝ)
    (hf : Continuous f)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hlim : Filter.Tendsto f UpperHalfPlane.atImInfty Filter.atBot) : BddAbove (Set.range f) := by
  apply
    (SpecialPeriods.bddAbove_image_punctured_of_tendsto_atBot SpecialPeriods.triangleCuspPoint
        (compactDescend f hinv 0) (compactDescend_continuousOn f hinv 0 hf)
        (compactDescend_tendsto_atBot f hinv 0 hlim)).mono
  rintro _ ⟨z, rfl⟩
  exact
    ⟨SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z),
      SpecialPeriods.triangleOpenInclusion_ne_cusp _, compactDescend_projection f hinv 0 z⟩

theorem SpecialPeriods.Construction.PeriodFunctions.tau_im_tendsto_atTop
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    Filter.Tendsto (fun z : ℍ => (F.data.tau z).im) UpperHalfPlane.atImInfty Filter.atTop := by
  obtain ⟨h, hh, hτ⟩ := F.tau_cusp
  exact SpecialPeriods.Construction.tau_im_tendsto_atTop_of_cusp_formula hh hτ

theorem SpecialPeriods.Construction.PeriodFunctions.beta_add_tau_im_eventually_bounded
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    ∃ M : ℝ, ∀ᶠ z in UpperHalfPlane.atImInfty, (F.beta z + (F.data.tau z : ℂ)).im ≤ M := by
  obtain ⟨M, Y, hM⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp F.beta_cusp.bounded
  refine ⟨M, (UpperHalfPlane.atImInfty_mem _).mpr ⟨Y, ?_⟩⟩
  intro z hz
  exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hM z hz)

theorem SpecialPeriods.Construction.PeriodFunctions.discriminant_tendsto_atBot
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    Filter.Tendsto (fun z => (F.data.periodPoint F.beta z).discriminant) UpperHalfPlane.atImInfty
      Filter.atBot :=
  PeriodPoint.tendsto_discriminant_atBot (F.data.periodPoint F.beta)
    (Filter.Eventually.of_forall fun z => (F.data.tau z).im_pos) F.tau_im_tendsto_atTop
    F.beta_add_tau_im_eventually_bounded

theorem SpecialPeriods.Construction.PeriodFunctions.discriminant_bddAbove
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    BddAbove (Set.range fun z => (F.data.periodPoint F.beta z).discriminant) :=
  SpecialPeriods.Construction.bddAbove_range_of_triangle_invariant_tendsto_atBot _
    (SpecialPeriods.Construction.continuous_discriminant F.data F.beta_holomorphic)
    (SpecialPeriods.Construction.discriminant_invariant F.data F.beta_generators)
    F.discriminant_tendsto_atBot

theorem SpecialPeriods.Construction.PeriodFunctions.exists_negative_imaginary_shift
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    ∃ M : ℝ,
      0 < M ∧
        ∀ z : ℍ, ((F.data.periodPoint F.beta z).shiftBeta (-((M : ℂ) * Complex.I))).Admissible :=
  PeriodPoint.exists_negative_imaginary_shift_of_bddAbove (F.data.periodPoint F.beta)
    (fun z => (F.data.tau z).im_pos) F.discriminant_bddAbove

def SpecialPeriods.Construction.PeriodFunctions.shiftHeight
    (F : SpecialPeriods.Construction.PeriodFunctions) : ℝ :=
  F.exists_negative_imaginary_shift.choose

def SpecialPeriods.Construction.PeriodFunctions.shiftConstant
    (F : SpecialPeriods.Construction.PeriodFunctions) : ℂ :=
  -((F.shiftHeight : ℂ) * Complex.I)

theorem SpecialPeriods.Construction.PeriodFunctions.shifted_admissible
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    ((F.data.periodPoint F.beta z).shiftBeta F.shiftConstant).Admissible :=
  F.exists_negative_imaginary_shift.choose_spec.2 z

def SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods
    (F : SpecialPeriods.Construction.PeriodFunctions) : HolomorphicPeriodMap ℂ ℍ :=
  F.data.shiftedPeriodMap F.beta F.beta_holomorphic F.shiftConstant F.shifted_admissible

@[simp]
theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_tau
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    (F.admissiblePeriods.point z).val.τ = (F.data.tau z : ℂ) :=
  rfl

@[simp]
theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_beta
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    (F.admissiblePeriods.point z).val.β = F.beta z + F.shiftConstant :=
  rfl

theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_generator₁
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    F.admissiblePeriods.point (SpecialPeriods.Triangle.generatorOneSL • z) =
      (F.admissiblePeriods.point z).step₁ :=
  SpecialPeriods.Construction.shiftedPeriodMap_generator₁ F.data F.beta_holomorphic
    F.shiftConstant F.shifted_admissible F.beta_generators z

theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_generator₂
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    F.admissiblePeriods.point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      (F.admissiblePeriods.point z).step₂ :=
  SpecialPeriods.Construction.shiftedPeriodMap_generator₂ F.data F.beta_holomorphic
    F.shiftConstant F.shifted_admissible F.beta_generators z

theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_beta_cusp
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    SpecialPeriods.MuTorsor.CuspRegular
      (fun z => (F.admissiblePeriods.point z).val.β + (F.admissiblePeriods.point z).val.τ) := by
  obtain ⟨b, hb, hβ⟩ := F.beta_cusp
  exact
    ⟨fun q => b q + F.shiftConstant, hb.add analyticAt_const,
      SpecialPeriods.Construction.beta_add_const_cusp_formula hβ F.shiftConstant⟩

theorem SpecialPeriods.Construction.PeriodFunctions.exists_cusp_data
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    ∃ C : SpecialPeriods.CuspFamily.Data,
      ∀ z : ℍ,
        ‖SpecialPeriods.Triangle.cuspQ z‖ < C.radius →
          (F.admissiblePeriods.point z).val =
            SpecialPeriods.cuspPeriodPoint C.μ C.b C.h
              ((z : ℂ) / SpecialPeriods.Triangle.width) := by
  obtain ⟨h, hh, hτ⟩ := F.tau_cusp
  obtain ⟨m, hm, hμ⟩ := F.mu_cusp
  obtain ⟨b, hb, hβ⟩ := F.admissiblePeriods_beta_cusp
  have hβ' :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (F.beta z + F.shiftConstant) + (F.data.tau z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z) := by
    simpa only [admissiblePeriods_beta, admissiblePeriods_tau] using hβ
  have hpoint :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (F.admissiblePeriods.point z).val =
        SpecialPeriods.cuspPeriodPoint m b h ((z : ℂ) / SpecialPeriods.Triangle.width) :=
    SpecialPeriods.Construction.periodPoint_eventually_eq_cuspPeriodPoint hτ hμ hβ'
  obtain ⟨ε, hε, hε1, hR, hC⟩ :=
    SpecialPeriods.exists_cuspCorrection_admissible_radius_of_analyticAt hm hb hh
  obtain ⟨r, hr, hrε, hmatch⟩ := SpecialPeriods.Construction.eventual_cuspQ_radius_lt hε hpoint
  refine
    ⟨{  μ := m
        b := b
        h := h
        radius := r
        radius_pos := hr
        radius_lt_one := hrε.trans hε1
        holomorphic := fun i j => (hC i j).mono (Metric.ball_subset_ball hrε.le)
        smallDrift := fun t ht0 htr => hR t ht0 (htr.trans hrε) }, hmatch⟩

def SpecialPeriods.Construction.PeriodFunctions.cuspData
    (F : SpecialPeriods.Construction.PeriodFunctions) : SpecialPeriods.CuspFamily.Data :=
  F.exists_cusp_data.choose

theorem SpecialPeriods.Construction.PeriodFunctions.cuspData_periodPoint
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ)
    (hz : ‖SpecialPeriods.Triangle.cuspQ z‖ < F.cuspData.radius) :
    (F.admissiblePeriods.point z).val =
      SpecialPeriods.cuspPeriodPoint F.cuspData.μ F.cuspData.b F.cuspData.h
        ((z : ℂ) / SpecialPeriods.Triangle.width) :=
  F.exists_cusp_data.choose_spec z hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Construction.periodMapOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    HolomorphicPeriodMap ℂ ℍ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Construction.periodMapOfSphere_generator₁
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point (SpecialPeriods.Triangle.generatorOneSL • z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₁ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_generator₁ z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Construction.periodMapOfSphere_generator₂
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₂ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_generator₂ z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
def SpecialPeriods.Construction.cuspDataOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    SpecialPeriods.CuspFamily.Data :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
theorem SpecialPeriods.Construction.cuspDataOfSphere_periodPoint
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : ‖SpecialPeriods.Triangle.cuspQ z‖ < (cuspDataOfSphere π hπ h₀ h₁).radius) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val =
      SpecialPeriods.cuspPeriodPoint (cuspDataOfSphere π hπ h₀ h₁).μ
        (cuspDataOfSphere π hπ h₀ h₁).b (cuspDataOfSphere π hπ h₀ h₁).h
        ((z : ℂ) / SpecialPeriods.Triangle.width) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData_periodPoint z hz


end
