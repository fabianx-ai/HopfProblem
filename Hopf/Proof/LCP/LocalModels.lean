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
Original source lines 105222--115134; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.Proof.Shortcuts
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

@[ext]
structure PeriodPoint where
  τ : ℂ
  μ : ℂ
  β : ℂ

def PeriodPoint.discriminant (p : PeriodPoint) : ℝ :=
  p.β.im - 6 * p.μ.im ^ 2 / p.τ.im

def PeriodPoint.Admissible (p : PeriodPoint) : Prop :=
  0 < p.τ.im ∧ p.discriminant < 0

def PeriodPoint.matrix (p : PeriodPoint) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![6 * p.μ, p.τ, 1, 0; p.β, p.μ, 0, 1]

def PeriodPoint.realMatrix (p : PeriodPoint) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![6 * p.μ.re, p.τ.re, 1, 0;
    6 * p.μ.im, p.τ.im, 0, 0;
    p.β.re, p.μ.re, 0, 1;
    p.β.im, p.μ.im, 0, 0]

def PeriodPoint.step₁ (p : PeriodPoint) : PeriodPoint :=
  ⟨(p.τ - 1) / p.τ, (1 - p.μ) / p.τ, p.β + 2 - 6 * (1 - p.μ) ^ 2 / p.τ⟩

def PeriodPoint.step₂ (p : PeriodPoint) : PeriodPoint :=
  ⟨-1 / p.τ, 1 + p.μ / p.τ, p.β - 3 - 6 * p.μ ^ 2 / p.τ⟩

def PeriodPoint.R₁ (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 / p.τ, 0; (1 - p.μ) / p.τ, 1]

def PeriodPoint.R₂ (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / p.τ, 0; -p.μ / p.τ, 1]

theorem PeriodPoint.τ_ne_zero (p : PeriodPoint) (h : 0 < p.τ.im) : p.τ ≠ 0 := by
  intro heq
  simp [heq] at h

theorem PeriodPoint.det_realMatrix (p : PeriodPoint) :
    p.realMatrix.det = p.τ.im * p.β.im - 6 * p.μ.im ^ 2 := by
  have hminor :
    p.realMatrix.submatrix (Fin.succAbove (0 : Fin 4)) (Fin.succAbove (2 : Fin 4)) =
      !![6 * p.μ.im, p.τ.im, 0; p.β.re, p.μ.re, 1; p.β.im, p.μ.im, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column _ 2, Fin.sum_univ_four, hminor]
  norm_num [realMatrix, Matrix.det_fin_three, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem PeriodPoint.det_realMatrix_eq_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.realMatrix.det = p.τ.im * p.discriminant := by
  rw [det_realMatrix]
  unfold discriminant
  field_simp

theorem PeriodPoint.det_realMatrix_neg (p : PeriodPoint) (h : p.Admissible) :
    p.realMatrix.det < 0 := by
  rw [det_realMatrix_eq_discriminant p (ne_of_gt h.1)]
  exact mul_neg_of_pos_of_neg h.1 h.2

theorem PeriodPoint.det_R₁ (p : PeriodPoint) : p.R₁.det = -1 / p.τ := by
  simp [R₁, Matrix.det_fin_two]

theorem PeriodPoint.det_R₂ (p : PeriodPoint) : p.R₂.det = 1 / p.τ := by
  simp [R₂, Matrix.det_fin_two]

theorem PeriodPoint.step₁_matrix (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₁.matrix = p.R₁ * p.matrix * (T₁.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
        simp [step₁, PeriodPoint.matrix, R₁, T₁, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;>
    ring

theorem PeriodPoint.step₂_matrix (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.matrix = p.R₂ * p.matrix * (T₂.map (Int.castRingHom ℂ)).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
        simp [step₂, PeriodPoint.matrix, R₂, T₂, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp <;>
    ring

theorem PeriodPoint.step₂_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.step₂.discriminant = p.discriminant := by
  have hτ : p.τ ≠ 0 := by
    intro heq
    exact h (by simp [heq])
  have hn : Complex.normSq p.τ ≠ 0 := mt Complex.normSq_eq_zero.mp hτ
  simp [step₂, discriminant, Complex.div_im, Complex.mul_im, Complex.mul_re, pow_two]
  field_simp
  simp [Complex.normSq_apply]
  ring

theorem PeriodPoint.step₁_discriminant (p : PeriodPoint) (h : p.τ.im ≠ 0) :
    p.step₁.discriminant = p.discriminant := by
  have hτ : p.τ ≠ 0 := by
    intro heq
    exact h (by simp [heq])
  have hs := step₂_discriminant ⟨p.τ, 1 - p.μ, p.β⟩ h
  simpa [step₁, step₂, discriminant, sub_div, hτ, Complex.div_im, neg_div] using hs

theorem PeriodPoint.step₁_im (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₁.τ.im = p.τ.im / Complex.normSq p.τ := by simp [step₁, sub_div, h, neg_div]

theorem PeriodPoint.step₂_im (p : PeriodPoint) : p.step₂.τ.im = p.τ.im / Complex.normSq p.τ := by
  simp [step₂, neg_div]

theorem PeriodPoint.step₁_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₁.Admissible := by
  refine ⟨?_, ?_⟩
  · rw [step₁_im p (p.τ_ne_zero h.1)]
    exact div_pos h.1 (Complex.normSq_pos.mpr (p.τ_ne_zero h.1))
  · rw [step₁_discriminant p (ne_of_gt h.1)]
    exact h.2

theorem PeriodPoint.step₂_admissible (p : PeriodPoint) (h : p.Admissible) : p.step₂.Admissible := by
  refine ⟨?_, ?_⟩
  · rw [step₂_im]
    exact div_pos h.1 (Complex.normSq_pos.mpr (p.τ_ne_zero h.1))
  · rw [step₂_discriminant p (ne_of_gt h.1)]
    exact h.2

theorem PeriodPoint.step₁_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    p.step₁.step₁ =
      ⟨-1 / (p.τ - 1), (p.τ - 1 + p.μ) / (p.τ - 1), p.β - 2 - 6 * p.μ ^ 2 / (p.τ - 1)⟩ := by
  apply PeriodPoint.ext <;> simp [step₁] <;> field_simp <;> ring

theorem PeriodPoint.step₂_sq (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₂ = ⟨p.τ, 1 - p.τ - p.μ, p.β - 6 + 6 * p.τ + 12 * p.μ⟩ := by
  apply PeriodPoint.ext <;> simp [step₂] <;> field_simp <;> ring

theorem PeriodPoint.step₁_cube (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    p.step₁.step₁.step₁ = p := by
  rw [step₁_sq p h₀ h₁]
  apply PeriodPoint.ext <;> simp [step₁] <;> field_simp <;> ring

theorem PeriodPoint.step₂_fourth (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₂.step₂.step₂ = p := by
  rw [step₂_sq (p.step₂.step₂), step₂_sq p h]
  · apply PeriodPoint.ext <;> simp
    all_goals ring
  · simpa [step₂] using h

theorem PeriodPoint.step₁_step₂ (p : PeriodPoint) (h : p.τ ≠ 0) :
    p.step₂.step₁ = ⟨p.τ + 1, p.μ, p.β - 1⟩ := by
  apply PeriodPoint.ext <;> simp [step₁, step₂] <;> field_simp <;> ring

abbrev ComplexPlane₂ :=
  Fin 2 → ℂ

def complexCoordinates : (Fin 4 → ℝ) ≃ₗ[ℝ] ComplexPlane₂
    where
  toFun x := ![⟨x 0, x 1⟩, ⟨x 2, x 3⟩]
  invFun z := ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r
    x := by
    ext i : 1
    fin_cases i <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

abbrev PeriodDomain :=
  { p : PeriodPoint // p.Admissible }

def PeriodDomain.realEquiv (p : PeriodDomain) : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 4)) p.val.realMatrix
    (isUnit_iff_ne_zero.mpr (ne_of_lt (p.val.det_realMatrix_neg p.property)))

theorem PeriodDomain.realEquiv_apply (p : PeriodDomain) (v : Fin 4 → ℝ) :
    p.realEquiv v = p.val.realMatrix *ᵥ v := by
  simp [realEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

def PeriodDomain.basis (p : PeriodDomain) : Module.Basis (Fin 4) ℝ ComplexPlane₂ :=
  (Pi.basisFun ℝ (Fin 4)).map (p.realEquiv.trans complexCoordinates)

theorem PeriodDomain.basis_apply (p : PeriodDomain) (j : Fin 4) :
    p.basis j = fun i => p.val.matrix i j := by
  simp only [basis, Module.Basis.map_apply, LinearEquiv.trans_apply, realEquiv_apply,
    Pi.basisFun_apply, Matrix.mulVec_single_one]
  ext i : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, PeriodPoint.matrix]

def PeriodDomain.lattice (p : PeriodDomain) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range (fun j i => p.val.matrix i j))

theorem PeriodDomain.lattice_eq_span_basis (p : PeriodDomain) :
    p.lattice = Submodule.span ℤ (Set.range p.basis) := by
  unfold lattice
  congr 2
  funext j
  exact (p.basis_apply j).symm

instance PeriodDomain.lattice_discrete (p : PeriodDomain) : DiscreteTopology p.lattice := by
  rw [lattice_eq_span_basis]
  infer_instance

instance PeriodDomain.lattice_isZLattice (p : PeriodDomain) : IsZLattice ℝ p.lattice := by
  constructor
  rw [lattice_eq_span_basis]
  exact ZSpan.span_top p.basis

instance PeriodDomain.lattice_addSubgroup_discrete (p : PeriodDomain) :
    DiscreteTopology p.lattice.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology p.lattice)

instance PeriodDomain.lattice_isClosed (p : PeriodDomain) :
    IsClosed (p.lattice : Set ComplexPlane₂) := by
  change IsClosed (p.lattice.toAddSubgroup : Set ComplexPlane₂)
  exact AddSubgroup.isClosed_of_discrete (H := p.lattice.toAddSubgroup)

abbrev PeriodDomain.Torus (p : PeriodDomain) :=
  ComplexPlane₂ ⧸ p.lattice

instance PeriodDomain.torus_pathConnected (p : PeriodDomain) : PathConnectedSpace p.Torus :=
  p.lattice.mkQ_surjective.pathConnectedSpace p.lattice.continuous_mkQ

instance PeriodDomain.torus_compact (p : PeriodDomain) : CompactSpace p.Torus := by
  let f := p.lattice.mkQ
  have hf : Continuous f := p.lattice.continuous_mkQ
  have hper : ∀ z w, w ∈ p.lattice → f (z + w) = f z := by
    intro z w hw
    have hw' : f w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
    rw [map_add, hw', add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic p.lattice f hf hper
  have hs : Function.Surjective f := Submodule.Quotient.mk_surjective p.lattice
  exact ⟨by simpa only [Set.range_eq_univ.mpr hs] using hc⟩

abbrev RealPair₂ :=
  (Fin 2 → ℝ) × (Fin 2 → ℝ)

structure FullPeriodMatrix where
  matrix : Matrix (Fin 2) (Fin 2) ℂ
  nondegenerate : Function.Bijective (matrix.map Complex.im).mulVecLin

def FullPeriodMatrix.imaginaryEquiv (p : FullPeriodMatrix) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofBijective (p.matrix.map Complex.im).mulVecLin p.nondegenerate

def FullPeriodMatrix.periodLinear (p : FullPeriodMatrix) : RealPair₂ →ₗ[ℝ] ComplexPlane₂
    where
  toFun x := fun i => (x.1 i : ℂ) + (p.matrix *ᵥ fun j => (x.2 j : ℂ)) i
  map_add' x
    y := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.ofReal_add, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring
  map_smul' a
    x := by
    ext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp only [Complex.real_smul, RingHom.id_apply]
    ring

theorem FullPeriodMatrix.periodLinear_re (p : FullPeriodMatrix) (x : RealPair₂) (i : Fin 2) :
    (p.periodLinear x i).re = x.1 i + ((p.matrix.map Complex.re) *ᵥ x.2) i := by
  simp [periodLinear, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re]

theorem FullPeriodMatrix.periodLinear_im (p : FullPeriodMatrix) (x : RealPair₂) (i : Fin 2) :
    (p.periodLinear x i).im = p.imaginaryEquiv x.2 i := by
  simp [periodLinear, imaginaryEquiv, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im]

theorem FullPeriodMatrix.periodLinear_bijective (p : FullPeriodMatrix) :
    Function.Bijective p.periodLinear := by
  constructor
  · intro x y hxy
    have him : p.imaginaryEquiv x.2 = p.imaginaryEquiv y.2 := by
      ext i
      simpa only [periodLinear_im] using congrArg Complex.im (congrFun hxy i)
    have hs : x.2 = y.2 := p.imaginaryEquiv.injective him
    apply Prod.ext _ hs
    ext i
    have he := congrArg Complex.re (congrFun hxy i)
    simpa only [periodLinear_re, hs, add_left_inj] using he
  · intro z
    let b := p.imaginaryEquiv.symm (fun i => (z i).im)
    let a := (fun i => (z i).re) - (p.matrix.map Complex.re) *ᵥ b
    refine ⟨(a, b), ?_⟩
    ext i
    apply Complex.ext
    · simp only [periodLinear_re, a, Pi.sub_apply, sub_add_cancel]
    · simpa only [periodLinear_im] using congrFun (p.imaginaryEquiv.apply_symm_apply _) i

def FullPeriodMatrix.periodEquiv (p : FullPeriodMatrix) : RealPair₂ ≃ₗ[ℝ] ComplexPlane₂ :=
  LinearEquiv.ofBijective p.periodLinear p.periodLinear_bijective

def FullPeriodMatrix.basis (p : FullPeriodMatrix) :
    Module.Basis (Fin 2 ⊕ Fin 2) ℝ ComplexPlane₂ :=
  ((Pi.basisFun ℝ (Fin 2)).prod (Pi.basisFun ℝ (Fin 2))).map p.periodEquiv

theorem FullPeriodMatrix.basis_inl (p : FullPeriodMatrix) (j : Fin 2) :
    p.basis (Sum.inl j) = Pi.single j 1 := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [basis, periodEquiv, periodLinear, Module.Basis.prod_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem FullPeriodMatrix.basis_inr (p : FullPeriodMatrix) (j : Fin 2) :
    p.basis (Sum.inr j) = fun i => p.matrix i j := by
  ext i
  fin_cases i <;> fin_cases j <;>
    simp [basis, periodEquiv, periodLinear, Module.Basis.prod_apply, Pi.basisFun_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def FullPeriodMatrix.lattice (p : FullPeriodMatrix) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range p.basis)

theorem FullPeriodMatrix.basis_integer_sum (p : FullPeriodMatrix) (c : Fin 2 ⊕ Fin 2 → ℤ) :
    ∑ j, c j • p.basis j =
      (fun i => (c (Sum.inl i) : ℂ)) + p.matrix *ᵥ (fun i => (c (Sum.inr i) : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [Fintype.sum_sum_type, basis_inl, basis_inr, Fin.sum_univ_two, Pi.single_apply,
      zsmul_eq_mul, mul_comm]

theorem FullPeriodMatrix.mem_lattice_iff (p : FullPeriodMatrix) (z : ComplexPlane₂) :
    z ∈ p.lattice ↔
      ∃ m n : Fin 2 → ℤ, z = (fun i => (m i : ℂ)) + p.matrix *ᵥ (fun i => (n i : ℂ)) := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c (Sum.inl i), fun i => c (Sum.inr i), hc.symm.trans (p.basis_integer_sum c)⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨Sum.elim m n, p.basis_integer_sum (Sum.elim m n)⟩

instance FullPeriodMatrix.lattice_discrete (p : FullPeriodMatrix) : DiscreteTopology p.lattice := by
  unfold lattice; infer_instance

instance FullPeriodMatrix.lattice_isZLattice (p : FullPeriodMatrix) : IsZLattice ℝ p.lattice :=
  ⟨ZSpan.span_top p.basis⟩

abbrev FullPeriodMatrix.Torus (p : FullPeriodMatrix) :=
  ComplexPlane₂ ⧸ p.lattice

instance FullPeriodMatrix.torus_pathConnected (p : FullPeriodMatrix) :
    PathConnectedSpace p.Torus :=
  p.lattice.mkQ_surjective.pathConnectedSpace p.lattice.continuous_mkQ

instance FullPeriodMatrix.torus_compact (p : FullPeriodMatrix) : CompactSpace p.Torus := by
  have hper : ∀ z w, w ∈ p.lattice → p.lattice.mkQ (z + w) = p.lattice.mkQ z := by
    intro z w hw
    have hw' : p.lattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero p.lattice).mpr hw
    rw [map_add, hw', add_zero]
  have hc :=
    IsZLattice.isCompact_range_of_periodic p.lattice p.lattice.mkQ p.lattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr p.lattice.mkQ_surjective] using hc⟩

def columnLattice (P : Matrix (Fin 2) (Fin 4) ℂ) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range P.col)

theorem column_mul_mem (P : Matrix (Fin 2) (Fin 4) ℂ) (A : LatticeMatrix) (j : Fin 4) :
    (P * A.map (Int.castRingHom ℂ)).col j ∈ columnLattice P := by
  have he : (P * A.map (Int.castRingHom ℂ)).col j = ∑ k, A k j • P.col k := by
    ext i
    simp [Matrix.mul_apply, Matrix.col, Matrix.transpose_apply, zsmul_eq_mul, mul_comm]
  rw [he]
  exact
    Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem columnLattice_mul_le (P : Matrix (Fin 2) (Fin 4) ℂ) (A : LatticeMatrix) :
    columnLattice (P * A.map (Int.castRingHom ℂ)) ≤ columnLattice P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact column_mul_mem P A j

theorem columnLattice_mul_eq (P : Matrix (Fin 2) (Fin 4) ℂ) (A B : LatticeMatrix)
    (hAB : A * B = 1) : columnLattice (P * A.map (Int.castRingHom ℂ)) = columnLattice P := by
  apply le_antisymm (columnLattice_mul_le P A)
  have hP : (P * A.map (Int.castRingHom ℂ)) * B.map (Int.castRingHom ℂ) = P := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, hAB]
    simp
  have h := columnLattice_mul_le (P * A.map (Int.castRingHom ℂ)) B
  rwa [hP] at h

theorem map_columnLattice (P : Matrix (Fin 2) (Fin 4) ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (columnLattice P).map (R.mulVecLin.restrictScalars ℤ) = columnLattice (R * P) := by
  rw [columnLattice, columnLattice, Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

def PeriodDomain.step₁ (p : PeriodDomain) : PeriodDomain :=
  ⟨p.val.step₁, p.val.step₁_admissible p.property⟩

def PeriodDomain.step₂ (p : PeriodDomain) : PeriodDomain :=
  ⟨p.val.step₂, p.val.step₂_admissible p.property⟩

def PeriodDomain.R₁Equiv (p : PeriodDomain) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) p.val.R₁
      (isUnit_iff_ne_zero.mpr
        (by
          rw [PeriodPoint.det_R₁]
          exact
            div_ne_zero (by norm_num) (p.val.τ_ne_zero p.property.1)))).toContinuousLinearEquiv

def PeriodDomain.R₂Equiv (p : PeriodDomain) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) p.val.R₂
      (isUnit_iff_ne_zero.mpr
        (by
          rw [PeriodPoint.det_R₂]
          exact div_ne_zero one_ne_zero (p.val.τ_ne_zero p.property.1)))).toContinuousLinearEquiv

theorem PeriodDomain.R₁Equiv_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    p.R₁Equiv z = p.val.R₁ *ᵥ z := by simp [R₁Equiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem PeriodDomain.R₂Equiv_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    p.R₂Equiv z = p.val.R₂ *ᵥ z := by simp [R₂Equiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem PeriodDomain.R₁Equiv_map_lattice (p : PeriodDomain) :
    p.lattice.map (p.R₁Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap = p.step₁.lattice := by
  have he :
    (p.R₁Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.R₁.mulVecLin.restrictScalars ℤ := by exact LinearMap.ext fun z => R₁Equiv_apply p z
  change (columnLattice p.val.matrix).map _ = columnLattice p.val.step₁.matrix
  rw [he, map_columnLattice, p.val.step₁_matrix (p.val.τ_ne_zero p.property.1)]
  exact (columnLattice_mul_eq _ T₁.transpose A₁ (by decide)).symm

theorem PeriodDomain.R₂Equiv_map_lattice (p : PeriodDomain) :
    p.lattice.map (p.R₂Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap = p.step₂.lattice := by
  have he :
    (p.R₂Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.R₂.mulVecLin.restrictScalars ℤ := by exact LinearMap.ext fun z => R₂Equiv_apply p z
  change (columnLattice p.val.matrix).map _ = columnLattice p.val.step₂.matrix
  rw [he, map_columnLattice, p.val.step₂_matrix (p.val.τ_ne_zero p.property.1)]
  exact (columnLattice_mul_eq _ T₂.transpose A₂ (by decide)).symm

def PeriodPoint.leftBlock (p : PeriodPoint) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * p.μ, p.τ; p.β, p.μ]

theorem PeriodPoint.leftBlock_apply (p : PeriodPoint) (i j : Fin 2) :
    p.leftBlock i j = p.matrix i (Fin.castAdd 2 j) := by fin_cases i <;> fin_cases j <;> rfl

theorem PeriodPoint.matrix_rightBlock (p : PeriodPoint) (i j : Fin 2) :
    p.matrix i (Fin.natAdd 2 j) = (Pi.single j (1 : ℂ) : ComplexPlane₂) i := by
  fin_cases i <;> fin_cases j <;> simp [PeriodPoint.matrix]

theorem PeriodDomain.fullPeriodLattice_eq (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) : q.lattice = p.lattice := by
  have hrange : Set.range q.basis = Set.range (fun j i => p.val.matrix i j) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | inl j =>
        refine ⟨Fin.natAdd 2 j, ?_⟩
        ext i
        rw [q.basis_inl]
        exact p.val.matrix_rightBlock i j
      | inr j =>
        refine ⟨Fin.castAdd 2 j, ?_⟩
        ext i
        rw [q.basis_inr, h]
        exact (p.val.leftBlock_apply i j).symm
    · rintro ⟨j, rfl⟩
      fin_cases j
      · refine ⟨Sum.inr 0, ?_⟩
        rw [q.basis_inr, h]
        ext i
        exact p.val.leftBlock_apply i 0
      · refine ⟨Sum.inr 1, ?_⟩
        rw [q.basis_inr, h]
        ext i
        exact p.val.leftBlock_apply i 1
      · refine ⟨Sum.inl 0, ?_⟩
        rw [q.basis_inl]
        ext i
        exact (p.val.matrix_rightBlock i 0).symm
      · refine ⟨Sum.inl 1, ?_⟩
        rw [q.basis_inl]
        ext i
        exact (p.val.matrix_rightBlock i 1).symm
  exact congrArg (Submodule.span ℤ) hrange

abbrev ToricCharts.CoordinateSpace (d : ℕ) :=
  Fin d → ℂ

def ToricCharts.torus {d : ℕ} : Set (CoordinateSpace d) :=
  {z | ∀ j, z j ≠ 0}

theorem ToricCharts.torus_open {d : ℕ} : IsOpen (torus : Set (CoordinateSpace d)) := by
  unfold torus
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply j) continuous_const

theorem ToricCharts.torus_dense {d : ℕ} : Dense (torus : Set (CoordinateSpace d)) := by
  simpa [torus, Set.pi] using
    (dense_pi (Set.univ : Set (Fin d)) fun _ _ => dense_compl_singleton (0 : ℂ))

def ToricCharts.monomial {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (z : CoordinateSpace d) :
    CoordinateSpace d := fun i => ∏ j, z j ^ A i j

def ToricCharts.domain {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : Set (CoordinateSpace d) :=
  {z | ∀ i j, A i j < 0 → z j ≠ 0}

theorem ToricCharts.domain_open {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : IsOpen (domain A) := by
  unfold domain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : A i j < 0
  · simpa [h] using isOpen_ne_fun (continuous_apply j) continuous_const
  · simp [h]

theorem ToricCharts.torus_subset_domain {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    torus ⊆ domain A := fun _ hz _ j _ => hz j

theorem ToricCharts.monomial_mapsTo_torus {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    Set.MapsTo (monomial A) torus torus := by
  intro z hz i
  exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hz j)

theorem ToricCharts.monomial_contDiffOn {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (n : ℕ∞ω) :
    ContDiffOn ℂ n (monomial A) (domain A) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_prod
  intro j _
  cases h : A i j with
  | ofNat k =>
    simpa only [h, Int.ofNat_eq_natCast, zpow_natCast] using
      (contDiff_apply ℂ ℂ j).contDiffOn.pow k
  | negSucc k =>
    have hn : A i j < 0 := by omega
    intro z hz
    simpa only [h, zpow_negSucc] using
      ((contDiff_apply ℂ ℂ j).contDiffWithinAt.pow (k + 1)).fun_inv (pow_ne_zero _ (hz i j hn))

private theorem ToricCharts.prod_zpow_eq_mo1973_9082 {d : ℕ} (a : ℂ) (ha : a ≠ 0)
    (s : Finset (Fin d)) (k : Fin d → ℤ) : (∏ i ∈ s, a ^ k i) = a ^ ∑ i ∈ s, k i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

theorem ToricCharts.monomial_mul_on_torus {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    {z : CoordinateSpace d} (hz : z ∈ torus) : monomial A (monomial B z) = monomial (A * B) z := by
  funext i
  simp only [monomial, Matrix.mul_apply]
  calc
    (∏ k, (∏ j, z j ^ B k j) ^ A i k) = ∏ k, ∏ j, z j ^ (A i k * B k j) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_mul, mul_comm]
    _ = ∏ j, ∏ k, z j ^ (A i k * B k j) := Finset.prod_comm
    _ = ∏ j, z j ^ ∑ k, A i k * B k j := by
      apply Finset.prod_congr rfl
      intro j _
      exact prod_zpow_eq_mo1973_9082 (z j) (hz j) _ _

@[simp]
theorem ToricCharts.monomial_one {d : ℕ} (z : CoordinateSpace d) : monomial 1 z = z := by
  funext i
  simp [monomial, Matrix.one_apply]

theorem ToricCharts.monomial_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (z w : CoordinateSpace d) : monomial A (z * w) = monomial A z * monomial A w := by
  funext i
  simp [monomial, mul_zpow, Finset.prod_mul_distrib]

@[simp]
theorem ToricCharts.monomial_ones {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : monomial A 1 = 1 := by
  funext i
  simp [monomial]

def ToricCharts.overlap {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) : Set (CoordinateSpace d) :=
  domain A ∩ monomial A ⁻¹' domain B

theorem ToricCharts.overlap_open {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) :
    IsOpen (overlap A B) :=
  (monomial_contDiffOn A 0).continuousOn.isOpen_inter_preimage (domain_open A) (domain_open B)

theorem ToricCharts.torus_subset_overlap {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) :
    torus ⊆ overlap A B := fun _ hz =>
  ⟨torus_subset_domain A hz, torus_subset_domain B (monomial_mapsTo_torus A hz)⟩

theorem ToricCharts.monomial_inverse_on_overlap {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    (hBA : B * A = 1) : Set.EqOn (monomial B ∘ monomial A) id (overlap A B) := by
  have h : Set.EqOn (monomial B ∘ monomial A) id (overlap A B ∩ torus) := by
    intro z hz
    simpa [hBA] using monomial_mul_on_torus B A hz.2
  refine
    h.of_subset_closure ?_ continuousOn_id Set.inter_subset_left
      (torus_dense.open_subset_closure_inter (overlap_open A B))
  exact
    (monomial_contDiffOn B 0).continuousOn.comp
      ((monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left) (fun _ hz => hz.2)

def ToricCharts.changeOfCoordinates {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (hAB : A * B = 1)
    (hBA : B * A = 1) : OpenPartialHomeomorph (CoordinateSpace d) (CoordinateSpace d)
    where
  toFun := monomial A
  invFun := monomial B
  source := overlap A B
  target := overlap B A
  map_source' z
    hz :=
    ⟨hz.2, by
      change (monomial B ∘ monomial A) z ∈ domain A
      rw [monomial_inverse_on_overlap A B hBA hz]
      exact hz.1⟩
  map_target' z
    hz :=
    ⟨hz.2, by
      change (monomial A ∘ monomial B) z ∈ domain B
      rw [monomial_inverse_on_overlap B A hAB hz]
      exact hz.1⟩
  left_inv' := monomial_inverse_on_overlap A B hBA
  right_inv' := monomial_inverse_on_overlap B A hAB
  open_source := overlap_open A B
  open_target := overlap_open B A
  continuousOn_toFun := (monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left
  continuousOn_invFun := (monomial_contDiffOn B 0).continuousOn.mono Set.inter_subset_left

theorem ToricCharts.changeOfCoordinates_holomorphic {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ContDiffOn ℂ ω (changeOfCoordinates A B hAB hBA) (changeOfCoordinates A B hAB hBA).source :=
  (monomial_contDiffOn A ω).mono Set.inter_subset_left

theorem ToricCharts.changeOfCoordinates_symm_holomorphic {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ContDiffOn ℂ ω (changeOfCoordinates A B hAB hBA).symm
      (changeOfCoordinates A B hAB hBA).target :=
  (monomial_contDiffOn B ω).mono Set.inter_subset_left

def ToricCharts.HeightOne (A : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  ∀ j, ∑ i, A i j = 1

theorem ToricCharts.column_single_of_zero {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    {z : CoordinateSpace 3} (hz : z ∈ domain A) {j : Fin 3} (hj : z j = 0) :
    ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 := by
  have hn (i : Fin 3) : 0 ≤ A i j := by
    by_contra h
    exact hz i j (lt_of_not_ge h) hj
  have hsum := hA j
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.sum_univ_zero,
    add_zero] at hsum
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have hcases : A 0 j = 1 ∨ A 1 j = 1 ∨ A 2 j = 1 := by omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega

theorem ToricCharts.monomial_zero_of_column_single {A : Matrix (Fin 3) (Fin 3) ℤ}
    {z : CoordinateSpace 3} {j k : Fin 3} (hj : z j = 0)
    (hc : ∀ i, A i j = if i = k then 1 else 0) : monomial A z k = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj, hc]

theorem ToricCharts.inverse_mapsTo_domain {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hBA : B * A = 1) : Set.MapsTo (monomial A) (domain A) (domain B) := by
  intro z hz i k hB hzero
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hzj : z j = 0 := eq_zero_of_zpow_eq_zero hj
  have hAj : A k j ≠ 0 := by
    intro he
    simp [he] at hj
  obtain ⟨l, hl⟩ := column_single_of_zero hA hz hzj
  have hkl : k = l := by
    by_contra h
    exact hAj (by simp [hl, h])
  subst l
  have hentry := congrFun (congrFun hBA i) j
  have hnonneg : 0 ≤ B i k := by
    have he : B i k = (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
      simpa [Matrix.mul_apply, hl] using hentry
    rw [he, Matrix.one_apply]
    split_ifs <;> norm_num
  exact (not_lt_of_ge hnonneg) hB

theorem ToricCharts.overlap_eq_domain {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hBA : B * A = 1) : overlap A B = domain A := by
  exact Set.inter_eq_left.mpr (inverse_mapsTo_domain hA hBA)

theorem ToricCharts.domain_composition {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A) :
    overlap A B ⊆ domain (B * A) := by
  intro z hz i j hC hzj
  obtain ⟨k, hk⟩ := column_single_of_zero hA hz.1 hzj
  have hzAk : monomial A z k = 0 := monomial_zero_of_column_single hzj hk
  have hBk : B i k < 0 := by simpa [Matrix.mul_apply, hk] using hC
  exact hz.2 i k hBk hzAk

theorem ToricCharts.monomial_mul_on_overlap {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A) :
    Set.EqOn (monomial B ∘ monomial A) (monomial (B * A)) (overlap A B) := by
  have h : Set.EqOn (monomial B ∘ monomial A) (monomial (B * A)) (overlap A B ∩ torus) :=
    fun _ hz => monomial_mul_on_torus B A hz.2
  refine
    h.of_subset_closure ?_ ?_ Set.inter_subset_left
      (torus_dense.open_subset_closure_inter (overlap_open A B))
  · exact
      (monomial_contDiffOn B 0).continuousOn.comp
        ((monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left) (fun _ hz => hz.2)
  · exact (monomial_contDiffOn (B * A) 0).continuousOn.mono (domain_composition hA)

@[ext]
structure ToricFan.Triangle where
  a : ℤ
  b : ℤ
  upper : Bool
  deriving DecidableEq

instance ToricFan.instLocal1 : Countable Triangle := by
  apply Function.Injective.countable (f := fun s : Triangle => (s.a, s.b, s.upper))
  intro s t h
  simpa only [Prod.mk.injEq, Triangle.ext_iff, and_assoc] using h

def ToricFan.Triangle.rays (s : ToricFan.Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  if s.upper then !![s.a + 1, s.a, s.a + 1; s.b, s.b + 1, s.b + 1; 1, 1, 1]
  else !![s.a, s.a + 1, s.a; s.b, s.b, s.b + 1; 1, 1, 1]

def ToricFan.Triangle.dual (s : ToricFan.Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  if s.upper then !![0, -1, s.b + 1; -1, 0, s.a + 1; 1, 1, -1 - s.a - s.b]
  else !![-1, -1, 1 + s.a + s.b; 1, 0, -s.a; 0, 1, -s.b]

theorem ToricFan.Triangle.dual_rays (s : ToricFan.Triangle) : s.dual * s.rays = 1 := by
  ext i j
  cases h : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [dual, rays, h, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem ToricFan.Triangle.rays_dual (s : ToricFan.Triangle) : s.rays * s.dual = 1 := by
  ext i j
  cases h : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [dual, rays, h, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem ToricFan.Triangle.rays_det (s : ToricFan.Triangle) :
    s.rays.det = if s.upper then -1 else 1 := by
  cases h : s.upper <;> simp [rays, h, Matrix.det_fin_three] <;> ring

@[simp]
theorem ToricFan.Triangle.rays_height (s : ToricFan.Triangle) (j : Fin 3) : s.rays 2 j = 1 := by
  cases h : s.upper <;> fin_cases j <;> simp [rays, h]

def ToricFan.Triangle.transition (s t : ToricFan.Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  t.dual * s.rays

@[simp]
theorem ToricFan.Triangle.transition_self (s : ToricFan.Triangle) : transition s s = 1 :=
  s.dual_rays

theorem ToricFan.Triangle.transition_mul (r s t : ToricFan.Triangle) :
    transition s t * transition r s = transition r t := by
  unfold transition
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc s.rays, rays_dual, Matrix.one_mul]

theorem ToricFan.Triangle.transition_covariance (s t : ToricFan.Triangle) :
    t.rays * transition s t = s.rays := by
  rw [transition, ← Matrix.mul_assoc, rays_dual, Matrix.one_mul]

theorem ToricFan.Triangle.transition_heightOne (s t : ToricFan.Triangle) :
    ToricCharts.HeightOne (transition s t) := by
  intro j
  have h := congrFun (congrFun (transition_covariance s t) 2) j
  simpa [Matrix.mul_apply] using h

def ToricFan.Triangle.chartChange (s t : ToricFan.Triangle) :
    OpenPartialHomeomorph (ToricCharts.CoordinateSpace 3) (ToricCharts.CoordinateSpace 3) :=
  ToricCharts.changeOfCoordinates (transition s t) (transition t s)
    (by rw [transition_mul, transition_self]) (by rw [transition_mul, transition_self])

@[simp]
theorem ToricFan.Triangle.chartChange_source (s t : ToricFan.Triangle) :
    (chartChange s t).source = ToricCharts.domain (transition s t) :=
  ToricCharts.overlap_eq_domain (transition_heightOne s t)
    (by rw [transition_mul, transition_self])

@[simp]
theorem ToricFan.Triangle.chartChange_self_source (s : ToricFan.Triangle) :
    (chartChange s s).source = Set.univ := by
  rw [chartChange_source, transition_self]
  ext z
  simp only [ToricCharts.domain, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i j h
  simp only [Matrix.one_apply] at h
  split_ifs at h <;> omega

@[simp]
theorem ToricFan.Triangle.chartChange_self_apply (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : chartChange s s z = z := by
  change ToricCharts.monomial (transition s s) z = z
  rw [transition_self, ToricCharts.monomial_one]

theorem ToricFan.Triangle.chartChange_cocycle (r s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange r s).source)
    (hsz : chartChange r s z ∈ (chartChange s t).source) :
    z ∈ (chartChange r t).source ∧ chartChange s t (chartChange r s z) = chartChange r t z := by
  rw [chartChange_source] at hz hsz ⊢
  have hm : z ∈ ToricCharts.overlap (transition r s) (transition s t) := ⟨hz, hsz⟩
  constructor
  · simpa only [transition_mul] using ToricCharts.domain_composition (transition_heightOne r s) hm
  · change
      ToricCharts.monomial (transition s t) (ToricCharts.monomial (transition r s) z) =
        ToricCharts.monomial (transition r t) z
    simpa only [Function.comp_apply, transition_mul] using
      ToricCharts.monomial_mul_on_overlap (transition_heightOne r s) hm

theorem ToricFan.Triangle.chartChange_inter (r s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hs : z ∈ (chartChange r s).source)
    (ht : z ∈ (chartChange r t).source) : chartChange r s z ∈ (chartChange s t).source := by
  have hi : chartChange r s z ∈ (chartChange s r).source := (chartChange r s).map_source hs
  have hinv : chartChange s r (chartChange r s z) = z := (chartChange r s).left_inv hs
  exact (chartChange_cocycle s r t hi (by rwa [hinv])).1

theorem ToricFan.Triangle.chartChange_holomorphic (s t : ToricFan.Triangle) :
    ContDiffOn ℂ ω (chartChange s t) (chartChange s t).source :=
  ToricCharts.changeOfCoordinates_holomorphic _ _ _ _

def ToricFan.Triangle.time (z : ToricCharts.CoordinateSpace 3) : ℂ :=
  z 0 * z 1 * z 2

theorem ToricFan.Triangle.time_holomorphic : ContDiff ℂ ω time := by
  exact ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).mul (contDiff_apply ℂ ℂ 2)

theorem ToricFan.Triangle.monomial_rays_height (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : ToricCharts.monomial s.rays z 2 = time z := by
  simp [ToricCharts.monomial, rays_height, Fin.prod_univ_succ, time, mul_assoc]

theorem ToricFan.Triangle.chartChange_preserves_time (s t : ToricFan.Triangle) :
    Set.EqOn (time ∘ chartChange s t) time (chartChange s t).source := by
  have h :
    Set.EqOn (time ∘ chartChange s t) time ((chartChange s t).source ∩ ToricCharts.torus) := by
    intro z hz
    change time (ToricCharts.monomial (transition s t) z) = time z
    have he := congrFun (ToricCharts.monomial_mul_on_torus t.rays (transition s t) hz.2) 2
    simpa only [transition_covariance, monomial_rays_height] using he
  refine
    h.of_subset_closure ?_ time_holomorphic.continuous.continuousOn Set.inter_subset_left
      (ToricCharts.torus_dense.open_subset_closure_inter (chartChange s t).open_source)
  exact time_holomorphic.continuous.comp_continuousOn (chartChange s t).continuousOn

theorem ToricFan.Triangle.central_fibre (z : ToricCharts.CoordinateSpace 3) :
    time z = 0 ↔ z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0 := by simp [time, mul_eq_zero, or_assoc]

abbrev ToricSpace.gluingCore : TopCat.GlueData.MkCore
    where
  J := ToricFan.Triangle
  U := fun _ => TopCat.of (ToricCharts.CoordinateSpace 3)
  V s
    t :=
    ⟨(ToricFan.Triangle.chartChange s t).source, (ToricFan.Triangle.chartChange s t).open_source⟩
  t s
    t :=
    TopCat.ofHom
      { toFun := fun z =>
          ⟨ToricFan.Triangle.chartChange s t z,
            (ToricFan.Triangle.chartChange s t).map_source z.2⟩
        continuous_toFun :=
          (ToricFan.Triangle.chartChange s t).continuousOn.domRestrict.subtype_mk _ }
  V_id
    s := by
    apply TopologicalSpace.Opens.ext
    exact ToricFan.Triangle.chartChange_self_source s
  t_id
    s := by
    funext z
    exact Subtype.ext (ToricFan.Triangle.chartChange_self_apply s z.1)
  t_inter := by
    intro r s t z hz
    exact ToricFan.Triangle.chartChange_inter r s t z.2 hz
  cocycle r s t z
    hz :=
    (ToricFan.Triangle.chartChange_cocycle r s t z.2
        (ToricFan.Triangle.chartChange_inter r s t z.2 hz)).2

abbrev ToricSpace.gluing : TopCat.GlueData :=
  TopCat.GlueData.mk' gluingCore

abbrev ToricSpace.Space :=
  gluing.toGlueData.glued

def ToricSpace.inclusion (s : ToricFan.Triangle) : ToricCharts.CoordinateSpace 3 → Space :=
  gluing.toGlueData.ι s

theorem ToricSpace.inclusion_openEmbedding (s : ToricFan.Triangle) :
    Topology.IsOpenEmbedding (ToricSpace.inclusion s) :=
  gluing.ι_isOpenEmbedding s

theorem ToricSpace.inclusion_jointly_surjective (x : Space) :
    ∃ s z, ToricSpace.inclusion s z = x :=
  gluing.ι_jointly_surjective x

theorem ToricSpace.inclusion_eq_iff (s t : ToricFan.Triangle)
    (z w : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z = ToricSpace.inclusion t w ↔
      z ∈ (ToricFan.Triangle.chartChange s t).source ∧ ToricFan.Triangle.chartChange s t z = w := by
  refine (gluing.ι_eq_iff_rel s t z w).trans ?_
  constructor
  · rintro ⟨⟨v, hv⟩, h1, h2⟩
    change v = z at h1
    change ToricFan.Triangle.chartChange s t v = w at h2
    subst v
    exact ⟨hv, h2⟩
  · rintro ⟨hz, he⟩
    exact ⟨⟨z, hz⟩, rfl, he⟩

def ToricSpace.parametrization (s : ToricFan.Triangle) :
    OpenPartialHomeomorph (ToricCharts.CoordinateSpace 3) Space :=
  (inclusion_openEmbedding s).toOpenPartialHomeomorph (ToricSpace.inclusion s)

@[simp]
theorem ToricSpace.parametrization_target (s : ToricFan.Triangle) :
    (parametrization s).target = Set.range (ToricSpace.inclusion s) := by simp [parametrization]

theorem ToricSpace.parametrization_transition (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3}
    (hz : ToricSpace.inclusion s z ∈ Set.range (ToricSpace.inclusion t)) :
    z ∈ (ToricFan.Triangle.chartChange s t).source ∧
      (parametrization t).symm (ToricSpace.inclusion s z) = ToricFan.Triangle.chartChange s t z :=
  by
  obtain ⟨w, hw⟩ := hz
  have he := (inclusion_eq_iff s t z w).mp hw.symm
  refine ⟨he.1, ?_⟩
  rw [← hw]
  exact ((inclusion_openEmbedding t).toOpenPartialHomeomorph_left_inv).trans he.2.symm

def ToricSpace.preferredTriangle (x : Space) : ToricFan.Triangle :=
  (inclusion_jointly_surjective x).choose

theorem ToricSpace.preferred_mem (x : Space) :
    x ∈ Set.range (ToricSpace.inclusion (preferredTriangle x)) :=
  (inclusion_jointly_surjective x).choose_spec

instance ToricSpace.chartedSpace : ChartedSpace (ToricCharts.CoordinateSpace 3) Space
    where
  atlas := Set.range (fun s : ToricFan.Triangle => (parametrization s).symm)
  chartAt x := (parametrization (preferredTriangle x)).symm
  mem_chart_source
    x := by
    change x ∈ (parametrization (preferredTriangle x)).target
    rw [parametrization_target]
    exact preferred_mem x
  chart_mem_atlas x := Set.mem_range_self _

theorem ToricSpace.transition_holomorphic (s t : ToricFan.Triangle) :
    ContDiffOn ℂ ω ((parametrization s).trans (parametrization t).symm)
      ((parametrization s).trans (parametrization t).symm).source := by
  have hparam (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    parametrization s z = ToricSpace.inclusion s z := rfl
  have h :
    ∀ z ∈ ((parametrization s).trans (parametrization t).symm).source,
      z ∈ (ToricFan.Triangle.chartChange s t).source ∧
        ((parametrization s).trans (parametrization t).symm) z =
          ToricFan.Triangle.chartChange s t z := by
    intro z hz
    exact parametrization_transition s t (by simpa [hparam] using hz.2)
  exact
    ((ToricFan.Triangle.chartChange_holomorphic s t).mono (fun z hz => (h z hz).1)).congr
      (fun z hz => (h z hz).2)

instance ToricSpace.isManifold :
    IsManifold (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω Space := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨s, rfl⟩ := he
  obtain ⟨t, rfl⟩ := he'
  simpa using transition_holomorphic s t

instance ToricSpace.secondCountableTopology : SecondCountableTopology Space := by
  let U : ToricFan.Triangle → Set Space := fun s => Set.range (ToricSpace.inclusion s)
  let (s : ToricFan.Triangle) : SecondCountableTopology (U s) :=
    (inclusion_openEmbedding s).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply
    TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
      (fun s => (inclusion_openEmbedding s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_range_self z⟩

def ToricSpace.time (x : Space) : ℂ :=
  ToricFan.Triangle.time ((parametrization (preferredTriangle x)).symm x)

@[simp]
theorem ToricSpace.time_inclusion (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    time (ToricSpace.inclusion s z) = ToricFan.Triangle.time z := by
  change
    ToricFan.Triangle.time
        ((parametrization (preferredTriangle (ToricSpace.inclusion s z))).symm
          (ToricSpace.inclusion s z)) =
      ToricFan.Triangle.time z
  have h :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  rw [h.2]
  exact ToricFan.Triangle.chartChange_preserves_time _ _ h.1

theorem ToricSpace.time_comp_parametrization (s : ToricFan.Triangle) :
    time ∘ parametrization s = ToricFan.Triangle.time := by
  funext z
  exact time_inclusion s z

theorem ToricSpace.time_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) (modelWithCornersSelf ℂ ℂ)
      ω time := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart :
    chartAt (ToricCharts.CoordinateSpace 3) x = (parametrization (preferredTriangle x)).symm :=
    rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, time_comp_parametrization] using
    ToricFan.Triangle.time_holomorphic.contMDiff.contMDiffAt.contMDiffWithinAt (s := Set.univ)
      (x := (parametrization (preferredTriangle x)).symm x)

def ToricSpace.referenceTriangle : ToricFan.Triangle :=
  ⟨0, 0, Bool.false⟩

def ToricSpace.openTorus : Set Space :=
  ToricSpace.inclusion referenceTriangle '' ToricCharts.torus

theorem ToricSpace.inclusion_torus_subset (s : ToricFan.Triangle) :
    ToricSpace.inclusion s '' ToricCharts.torus ⊆ openTorus := by
  rintro _ ⟨z, hz, rfl⟩
  refine
    ⟨ToricFan.Triangle.chartChange s referenceTriangle z, ToricCharts.monomial_mapsTo_torus _ hz,
      ?_⟩
  exact
    ((inclusion_eq_iff s referenceTriangle z _).mpr
        ⟨ToricCharts.torus_subset_overlap _ _ hz, rfl⟩).symm

theorem ToricSpace.mem_openTorus_iff (x : Space) : x ∈ openTorus ↔ time x ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [time_inclusion]
    exact mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  · intro hx
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    have hz : z ∈ ToricCharts.torus := by
      have h : (z 0 ≠ 0 ∧ z 1 ≠ 0) ∧ z 2 ≠ 0 := by
        simpa only [time_inclusion, ToricFan.Triangle.time, mul_ne_zero_iff] using hx
      intro i
      fin_cases i
      · exact h.1.1
      · exact h.1.2
      · exact h.2
    exact inclusion_torus_subset s ⟨z, hz, rfl⟩

theorem ToricSpace.openTorus_isOpen : IsOpen openTorus := by
  have he : openTorus = {x | time x ≠ 0} := Set.ext mem_openTorus_iff
  rw [he]
  exact isOpen_ne_fun time_holomorphic.continuous continuous_const

theorem ToricSpace.openTorus_dense : Dense openTorus := by
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  apply closure_mono (inclusion_torus_subset s)
  exact
    mem_closure_image (inclusion_openEmbedding s).continuous.continuousAt
      (ToricCharts.torus_dense z)

theorem ToricSpace.inclusion_holomorphic (s : ToricFan.Triangle) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (ToricSpace.inclusion s) := by
  have he :
    (parametrization s).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω Space :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self s)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (ToricSpace.inclusion s)
      Set.univ at h
  exact contMDiffOn_univ.mp h

def ToricSpace.descend {Y : Type*} (f : ToricFan.Triangle → ToricCharts.CoordinateSpace 3 → Y)
    (x : Space) : Y :=
  f (preferredTriangle x) ((parametrization (preferredTriangle x)).symm x)

theorem ToricSpace.descend_inclusion {Y : Type*}
    (f : ToricFan.Triangle → ToricCharts.CoordinateSpace 3 → Y)
    (h :
      ∀ s t z,
        z ∈ (ToricFan.Triangle.chartChange s t).source →
          f t (ToricFan.Triangle.chartChange s t z) = f s z)
    (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    descend f (ToricSpace.inclusion s z) = f s z := by
  change
    f (preferredTriangle (ToricSpace.inclusion s z))
        ((parametrization (preferredTriangle (ToricSpace.inclusion s z))).symm
          (ToricSpace.inclusion s z)) =
      f s z
  have he :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  rw [he.2]
  exact h _ _ _ he.1

theorem ToricSpace.descend_holomorphic {F H Y : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y] (I : ModelWithCorners ℂ F H)
    (f : ToricFan.Triangle → ToricCharts.CoordinateSpace 3 → Y)
    (h :
      ∀ s t z,
        z ∈ (ToricFan.Triangle.chartChange s t).source →
          f t (ToricFan.Triangle.chartChange s t z) = f s z)
    (hf : ∀ s, ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω (f s)) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω (descend f) := by
  have hcomp (s : ToricFan.Triangle) : descend f ∘ parametrization s = f s := by
    funext z
    exact descend_inclusion f h s z
  intro x
  rw [contMDiffAt_iff_source]
  have hchart :
    chartAt (ToricCharts.CoordinateSpace 3) x = (parametrization (preferredTriangle x)).symm :=
    rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, hcomp] using
    (hf (preferredTriangle x)).contMDiffAt.contMDiffWithinAt (s := Set.univ) (x :=
      (parametrization (preferredTriangle x)).symm x)

theorem ToricSpace.contMDiffOn_of_comp_inclusion {F H Y : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    (I : ModelWithCorners ℂ F H) (f : Space → Y) {U : Set Space} (hU : IsOpen U)
    (hf :
      ∀ s,
        ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω
          (f ∘ ToricSpace.inclusion s) (ToricSpace.inclusion s ⁻¹' U)) :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω f U := by
  have hparam (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    parametrization s z = ToricSpace.inclusion s z := rfl
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have he :
    ToricSpace.inclusion (preferredTriangle x) ((parametrization (preferredTriangle x)).symm x) =
      x :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (ToricSpace.inclusion (preferredTriangle x)) (inclusion_openEmbedding _) (preferred_mem x)
  have hm :
    (parametrization (preferredTriangle x)).symm x ∈
      ToricSpace.inclusion (preferredTriangle x) ⁻¹' U := by
    change ToricSpace.inclusion _ _ ∈ U
    rwa [he]
  have hlocal :=
    (hf (preferredTriangle x)).contMDiffAt
      ((hU.preimage (inclusion_openEmbedding _).continuous).mem_nhds hm)
  have hchart :
    chartAt (ToricCharts.CoordinateSpace 3) x = (parametrization (preferredTriangle x)).symm :=
    rfl
  simpa [hparam, extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    hlocal.contMDiffWithinAt (s := Set.univ)

def ToricSeparation.stripIndex (s : ToricFan.Triangle) : Fin 3 → ℤ :=
  ![s.a, s.b, s.a + s.b + if s.upper then 1 else 0]

def ToricSeparation.pencil (k : Fin 3) (x : Fin 3 → ℤ) : ℤ :=
  ![x 0, x 1, x 0 + x 1] k

def ToricSeparation.sign (a b : ℤ) : ℤ :=
  if a < b then -1 else if b < a then 1 else 0

def ToricSeparation.stripValue (a b x : ℤ) : ℤ :=
  sign a b * (2 * x - a - b - 1)

theorem ToricSeparation.sign_swap (a b : ℤ) : sign b a = -sign a b := by
  unfold sign
  split_ifs <;> omega

theorem ToricSeparation.stripValue_nonneg {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1) :
    0 ≤ stripValue a b x := by
  unfold stripValue sign
  split_ifs <;> omega

theorem ToricSeparation.stripValue_zero_bounds {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1)
    (hzero : stripValue a b x = 0) : b ≤ x ∧ x ≤ b + 1 := by
  unfold stripValue sign at hzero
  split_ifs at hzero <;> omega

theorem ToricSeparation.ray_strip_bounds (s : ToricFan.Triangle) (j k : Fin 3) :
    stripIndex s k ≤ pencil k (fun i => s.rays i j) ∧
      pencil k (fun i => s.rays i j) ≤ stripIndex s k + 1 := by
  cases h : s.upper <;> fin_cases j <;> fin_cases k <;>
      simp [stripIndex, pencil, ToricFan.Triangle.rays, h] <;>
    omega

theorem ToricSeparation.transition_nonneg_of_bounds (s t : ToricFan.Triangle) (j : Fin 3)
    (h :
      ∀ k,
        stripIndex t k ≤ pencil k (fun i => s.rays i j) ∧
          pencil k (fun i => s.rays i j) ≤ stripIndex t k + 1) :
    ∀ i, 0 ≤ ToricFan.Triangle.transition s t i j := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  intro i
  cases ht : t.upper <;> fin_cases i <;>
        simp [ToricFan.Triangle.transition, ToricFan.Triangle.dual, ht, Matrix.mul_apply,
          Fin.sum_univ_succ] <;>
      simp [stripIndex, pencil, ht] at h0 h1 h2 <;>
    omega

def ToricSeparation.character (s t : ToricFan.Triangle) : Fin 3 → ℤ :=
  let e : Fin 3 → ℤ := fun k => sign (stripIndex s k) (stripIndex t k)
  ![2 * (e 0 + e 2), 2 * (e 1 + e 2),
    -(e 0 * (stripIndex s 0 + stripIndex t 0 + 1) + e 1 * (stripIndex s 1 + stripIndex t 1 + 1) +
        e 2 * (stripIndex s 2 + stripIndex t 2 + 1))]

theorem ToricSeparation.character_swap (s t : ToricFan.Triangle) :
    character t s = -character s t := by
  have he (k : Fin 3) :
    sign (stripIndex t k) (stripIndex s k) = -sign (stripIndex s k) (stripIndex t k) :=
    sign_swap _ _
  unfold character
  simp only [he]
  ext i
  fin_cases i <;> dsimp <;> ring

def ToricSeparation.exponents (s t : ToricFan.Triangle) : Fin 3 → ℤ :=
  character s t ᵥ* s.rays

theorem ToricSeparation.exponents_eq_sum (s t : ToricFan.Triangle) (j : Fin 3) :
    exponents s t j =
      ∑ k, stripValue (stripIndex s k) (stripIndex t k) (pencil k (fun i => s.rays i j)) := by
  simp [exponents, character, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, stripValue, pencil]
  ring

theorem ToricSeparation.exponents_nonneg (s t : ToricFan.Triangle) (j : Fin 3) :
    0 ≤ exponents s t j := by
  rw [exponents_eq_sum]
  exact Finset.sum_nonneg fun k _ => stripValue_nonneg (ray_strip_bounds s j k)

theorem ToricSeparation.transition_nonneg_of_exponent_zero (s t : ToricFan.Triangle) (j : Fin 3)
    (hzero : exponents s t j = 0) : ∀ i, 0 ≤ ToricFan.Triangle.transition s t i j := by
  apply transition_nonneg_of_bounds s t j
  intro k
  apply stripValue_zero_bounds (ray_strip_bounds s j k)
  rw [exponents_eq_sum] at hzero
  exact
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => stripValue_nonneg (ray_strip_bounds s j k))).mp
      hzero k (Finset.mem_univ k)

theorem ToricSeparation.exponents_pos_of_transition_neg (s t : ToricFan.Triangle) (i j : Fin 3)
    (hneg : ToricFan.Triangle.transition s t i j < 0) : 0 < exponents s t j := by
  have hn := exponents_nonneg s t j
  by_contra h
  have hz : exponents s t j = 0 := by omega
  exact (not_lt_of_ge (transition_nonneg_of_exponent_zero s t j hz i)) hneg

theorem ToricSeparation.exponents_transition (s t : ToricFan.Triangle) :
    exponents t s ᵥ* ToricFan.Triangle.transition s t = -exponents s t := by
  rw [exponents, character_swap, Matrix.vecMul_vecMul, ToricFan.Triangle.transition_covariance]
  simp [exponents, Matrix.neg_vecMul]

theorem ToricSeparation.exponents_cancel (s t : ToricFan.Triangle) (j : Fin 3) :
    exponents s t j + ∑ i, exponents t s i * ToricFan.Triangle.transition s t i j = 0 := by
  have h := congrFun (exponents_transition s t) j
  change (∑ i, exponents t s i * ToricFan.Triangle.transition s t i j) = -exponents s t j at h
  omega

def ToricCharts.character (a : Fin 3 → ℤ) (z : CoordinateSpace 3) : ℂ :=
  ∏ j, z j ^ a j

theorem ToricCharts.character_contDiff (a : Fin 3 → ℤ) (ha : ∀ j, 0 ≤ a j) (n : ℕ∞ω) :
    ContDiff ℂ n (character a) := by
  apply contDiff_prod
  intro j _
  have he :
    (fun z : CoordinateSpace 3 => z j ^ a j) = (fun z : CoordinateSpace 3 => z j ^ (a j).toNat) :=
    by
    funext z
    conv_lhs => rw [← Int.toNat_of_nonneg (ha j), zpow_natCast]
  rw [he]
  exact (contDiff_apply ℂ ℂ j).pow _

theorem ToricCharts.characters_mul_on_torus (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (h : ∀ j, a j + ∑ i, b i * A i j = 0) {z : CoordinateSpace 3} (hz : z ∈ torus) :
    character a z * character b (monomial A z) = 1 := by
  have he := congrFun (monomial_mul_on_torus (fun _ j : Fin 3 => b j) A hz) 0
  change character b (monomial A z) = ∏ j, z j ^ ∑ i, b i * A i j at he
  rw [he]
  unfold character
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ j, z j ^ a j * z j ^ ∑ i, b i * A i j) = ∏ _j : Fin 3, (1 : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_add₀ (hz j), h j, zpow_zero]
    _ = 1 := by simp

theorem ToricCharts.characters_mul_on_domain (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (h : ∀ j, a j + ∑ i, b i * A i j = 0) :
    Set.EqOn (fun z => character a z * character b (monomial A z)) (fun _ => 1) (domain A) := by
  have he :
    Set.EqOn (fun z => character a z * character b (monomial A z)) (fun _ => 1)
      (domain A ∩ torus) :=
    fun _ hz => characters_mul_on_torus A a b h hz.2
  refine
    he.of_subset_closure ?_ continuousOn_const Set.inter_subset_left
      (torus_dense.open_subset_closure_inter (domain_open A))
  exact
    (character_contDiff a ha 0).continuous.continuousOn.mul
      ((character_contDiff b hb 0).continuous.comp_continuousOn
        (monomial_contDiffOn A 0).continuousOn)

def ToricCharts.overlapGraph (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Set (CoordinateSpace 3 × CoordinateSpace 3) :=
  {p | p.1 ∈ domain A ∧ monomial A p.1 = p.2}

theorem ToricCharts.overlapGraph_closed (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hcancel : ∀ j, a j + ∑ i, b i * A i j = 0)
    (hpos : ∀ i j, A i j < 0 → 0 < a j) : IsClosed (overlapGraph A) := by
  let P : CoordinateSpace 3 × CoordinateSpace 3 → ℂ := fun p => character a p.1 * character b p.2
  have hP : Continuous P :=
    ((character_contDiff a ha 0).continuous.comp continuous_fst).mul
      ((character_contDiff b hb 0).continuous.comp continuous_snd)
  have hsubset : overlapGraph A ⊆ {p | P p = 1} := by
    intro p hp
    change character a p.1 * character b p.2 = 1
    rw [← hp.2]
    exact characters_mul_on_domain A a b ha hb hcancel hp.1
  apply isClosed_of_closure_subset
  intro p hp
  have hPeq : P p = 1 := closure_minimal hsubset (isClosed_eq hP continuous_const) hp
  have hD : p.1 ∈ domain A := by
    intro i j hij hz
    have hchar : character a p.1 = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz, zero_zpow _ (ne_of_gt (hpos i j hij))]
    change character a p.1 * character b p.2 = 1 at hPeq
    simp [hchar] at hPeq
  refine ⟨hD, ?_⟩
  let : (𝓝[overlapGraph A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hf : ContinuousAt (fun q : CoordinateSpace 3 × CoordinateSpace 3 => monomial A q.1) p :=
    ((monomial_contDiffOn A 0).continuousOn.continuousAt ((domain_open A).mem_nhds hD)).comp
      continuous_fst.continuousAt
  have he :
    (fun q : CoordinateSpace 3 × CoordinateSpace 3 => monomial A q.1) =ᶠ[𝓝[overlapGraph A] p]
      Prod.snd := by
    filter_upwards [self_mem_nhdsWithin (s := overlapGraph A) (a := p)] with q hq
    exact hq.2
  exact
    tendsto_nhds_unique hf.continuousWithinAt
      (continuous_snd.continuousAt.continuousWithinAt.congr' he.symm)

theorem ToricSpace.chart_overlap_graph_closed (s t : ToricFan.Triangle) :
    IsClosed (ToricCharts.overlapGraph (ToricFan.Triangle.transition s t)) :=
  ToricCharts.overlapGraph_closed (ToricFan.Triangle.transition s t)
    (ToricSeparation.exponents s t) (ToricSeparation.exponents t s)
    (ToricSeparation.exponents_nonneg s t) (ToricSeparation.exponents_nonneg t s)
    (ToricSeparation.exponents_cancel s t) (ToricSeparation.exponents_pos_of_transition_neg s t)

instance ToricSpace.t2Space : T2Space Space := by
  constructor
  intro x y hxy
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨t, w, rfl⟩ := inclusion_jointly_surjective y
  have hn : (z, w) ∈ (ToricCharts.overlapGraph (ToricFan.Triangle.transition s t))ᶜ := by
    intro h
    apply hxy
    exact (inclusion_eq_iff s t z w).mpr ⟨by simpa using h.1, h.2⟩
  obtain ⟨U, V, hU, hV, hz, hw, hUV⟩ :=
    isOpen_prod_iff.mp (chart_overlap_graph_closed s t).isOpen_compl z w hn
  refine
    ⟨ToricSpace.inclusion s '' U, ToricSpace.inclusion t '' V,
      (inclusion_openEmbedding s).isOpenMap _ hU, (inclusion_openEmbedding t).isOpenMap _ hV,
      Set.mem_image_of_mem _ hz, Set.mem_image_of_mem _ hw, ?_⟩
  apply Set.disjoint_left.mpr
  rintro q ⟨u, hu, hsu⟩ ⟨v, hv, htv⟩
  have he := (inclusion_eq_iff s t u v).mp (hsu.trans htv.symm)
  exact hUV (show (u, v) ∈ U ×ˢ V from ⟨hu, hv⟩) ⟨by simpa using he.1, he.2⟩

def ToricFan.Triangle.shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) : ToricFan.Triangle :=
  ⟨s.a + v 0, s.b + v 1, s.upper⟩

@[simp]
theorem ToricFan.Triangle.shift_zero (s : ToricFan.Triangle) : s.shift 0 = s := by
  ext <;> simp [shift]

theorem ToricFan.Triangle.shift_add (s : ToricFan.Triangle) (v w : Fin 2 → ℤ) :
    (s.shift v).shift w = s.shift (v + w) := by ext <;> simp [shift, add_assoc]

def ToricFan.Triangle.shear (v : Fin 2 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, v 0; 0, 1, v 1; 0, 0, 1]

@[simp]
theorem ToricFan.Triangle.shear_zero : shear 0 = 1 := by decide

theorem ToricFan.Triangle.shear_add (v w : Fin 2 → ℤ) : shear v * shear w = shear (v + w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

theorem ToricFan.Triangle.rays_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).rays = shear v * s.rays := by
  ext i j
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [rays, shift, shear, hs, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem ToricFan.Triangle.dual_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).dual = s.dual * shear (-v) := by
  ext i j
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [dual, shift, shear, hs, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

theorem ToricFan.Triangle.transition_shift (s t : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    transition (s.shift v) (t.shift v) = transition s t := by
  rw [transition, dual_shift, rays_shift, Matrix.mul_assoc, ← Matrix.mul_assoc (shear (-v)),
    shear_add]
  simp [transition]

theorem ToricFan.Triangle.chartChange_shift_source (s t : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    (chartChange (s.shift v) (t.shift v)).source = (chartChange s t).source := by
  simp [transition_shift]

theorem ToricFan.Triangle.chartChange_shift_apply (s t : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (z : ToricCharts.CoordinateSpace 3) :
    chartChange (s.shift v) (t.shift v) z = chartChange s t z := by
  change
    ToricCharts.monomial (transition (s.shift v) (t.shift v)) z =
      ToricCharts.monomial (transition s t) z
  rw [transition_shift]

theorem ToricSpace.translation_compatible (v : Fin 2 → ℤ) (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion (t.shift v) (ToricFan.Triangle.chartChange s t z) =
      ToricSpace.inclusion (s.shift v) z := by
  apply ((inclusion_eq_iff (s.shift v) (t.shift v) z _).mpr ?_).symm
  exact
    ⟨by simpa only [ToricFan.Triangle.chartChange_shift_source] using hz,
      ToricFan.Triangle.chartChange_shift_apply s t v z⟩

def ToricSpace.translate (v : Fin 2 → ℤ) : Space → Space :=
  descend (fun s z => ToricSpace.inclusion (s.shift v) z)

@[simp]
theorem ToricSpace.translate_inclusion (v : Fin 2 → ℤ) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.translate v (ToricSpace.inclusion s z) = ToricSpace.inclusion (s.shift v) z :=
  descend_inclusion _ (translation_compatible v) s z

theorem ToricSpace.translate_holomorphic (v : Fin 2 → ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (ToricSpace.translate v) :=
  descend_holomorphic _ _ (translation_compatible v) (fun s => inclusion_holomorphic (s.shift v))

@[simp]
theorem ToricSpace.translate_zero (x : Space) : ToricSpace.translate 0 x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

theorem ToricSpace.translate_add (v w : Fin 2 → ℤ) (x : Space) :
    ToricSpace.translate v (ToricSpace.translate w x) = ToricSpace.translate (v + w) x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [ToricFan.Triangle.shift_add, add_comm v w]

def ToricSpace.translationHomeomorph (v : Fin 2 → ℤ) : Space ≃ₜ Space
    where
  toFun := ToricSpace.translate v
  invFun := ToricSpace.translate (-v)
  left_inv x := by rw [ToricSpace.translate_add]; simp
  right_inv x := by rw [ToricSpace.translate_add]; simp
  continuous_toFun := (translate_holomorphic v).continuous
  continuous_invFun := (translate_holomorphic (-v)).continuous

@[simp]
theorem ToricSpace.time_translate (v : Fin 2 → ℤ) (x : Space) :
    time (ToricSpace.translate v x) = time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

abbrev ToricSpace.ActingTorus :=
  Fin 3 → ℂˣ

def ToricSpace.factors (s : ToricFan.Triangle) (u : ActingTorus) :
    ToricCharts.CoordinateSpace 3 :=
  ToricCharts.monomial s.dual (fun j => (u j : ℂ))

theorem ToricSpace.factors_nonzero (s : ToricFan.Triangle) (u : ActingTorus) (j : Fin 3) :
    factors s u j ≠ 0 :=
  ToricCharts.monomial_mapsTo_torus _ (fun i => (u i).ne_zero) j

def ToricSpace.scale (s : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) : ToricCharts.CoordinateSpace 3 :=
  factors s u * z

theorem ToricSpace.scale_holomorphic (s : ToricFan.Triangle) (u : ActingTorus) :
    ContDiff ℂ ω (scale s u) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_const.mul (contDiff_apply ℂ ℂ j)

theorem ToricSpace.scale_mem_source (s t : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) :
    scale s u z ∈ (ToricFan.Triangle.chartChange s t).source ↔
      z ∈ (ToricFan.Triangle.chartChange s t).source := by
  simp [ToricFan.Triangle.chartChange_source, ToricCharts.domain, scale, factors_nonzero]

theorem ToricSpace.transition_factors (s t : ToricFan.Triangle) (u : ActingTorus) :
    ToricCharts.monomial (ToricFan.Triangle.transition s t) (factors s u) = factors t u := by
  have he : ToricFan.Triangle.transition s t * s.dual = t.dual := by
    rw [ToricFan.Triangle.transition, Matrix.mul_assoc, ToricFan.Triangle.rays_dual,
      Matrix.mul_one]
  change
    ToricCharts.monomial (ToricFan.Triangle.transition s t)
        (ToricCharts.monomial s.dual (fun j => (u j : ℂ))) =
      _
  rw [ToricCharts.monomial_mul_on_torus _ _ (fun j => (u j).ne_zero), he]
  rfl

theorem ToricSpace.scale_transition (s t : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.chartChange s t (scale s u z) =
      scale t u (ToricFan.Triangle.chartChange s t z) := by
  change
    ToricCharts.monomial (ToricFan.Triangle.transition s t) (factors s u * z) =
      factors t u * ToricCharts.monomial (ToricFan.Triangle.transition s t) z
  rw [ToricCharts.monomial_mul, transition_factors]

theorem ToricSpace.action_compatible (u : ActingTorus) (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion t (scale t u (ToricFan.Triangle.chartChange s t z)) =
      ToricSpace.inclusion s (scale s u z) := by
  exact
    ((inclusion_eq_iff s t _ _).mpr
        ⟨(scale_mem_source s t u z).mpr hz, scale_transition s t u z⟩).symm

def ToricSpace.torusAction (u : ActingTorus) : Space → Space :=
  descend (fun s z => ToricSpace.inclusion s (scale s u z))

@[simp]
theorem ToricSpace.torusAction_inclusion (u : ActingTorus) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    torusAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s (scale s u z) :=
  descend_inclusion _ (action_compatible u) s z

theorem ToricSpace.torusAction_holomorphic (u : ActingTorus) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (torusAction u) :=
  descend_holomorphic _ _ (action_compatible u)
    (fun s => (inclusion_holomorphic s).comp (scale_holomorphic s u).contMDiff)

@[simp]
theorem ToricSpace.factors_one (s : ToricFan.Triangle) : factors s 1 = 1 := by
  change ToricCharts.monomial s.dual 1 = 1
  exact ToricCharts.monomial_ones _

theorem ToricSpace.factors_mul (s : ToricFan.Triangle) (u v : ActingTorus) :
    factors s (u * v) = factors s u * factors s v := by
  change ToricCharts.monomial s.dual ((fun j => (u j : ℂ)) * (fun j => (v j : ℂ))) = _
  exact ToricCharts.monomial_mul _ _ _

@[simp]
theorem ToricSpace.scale_one (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    scale s 1 z = z := by simp [scale]

theorem ToricSpace.scale_mul (s : ToricFan.Triangle) (u v : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) : scale s u (scale s v z) = scale s (u * v) z := by
  simp [scale, factors_mul, mul_assoc]

@[simp]
theorem ToricSpace.torusAction_one (x : Space) : torusAction 1 x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

theorem ToricSpace.torusAction_mul (u v : ActingTorus) (x : Space) :
    torusAction u (torusAction v x) = torusAction (u * v) x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [scale_mul]

def ToricSpace.torusHomeomorph (u : ActingTorus) : Space ≃ₜ Space
    where
  toFun := torusAction u
  invFun := torusAction u⁻¹
  left_inv x := by rw [torusAction_mul]; simp
  right_inv x := by rw [torusAction_mul]; simp
  continuous_toFun := (torusAction_holomorphic u).continuous
  continuous_invFun := (torusAction_holomorphic u⁻¹).continuous

theorem ToricSpace.time_factors (s : ToricFan.Triangle) (u : ActingTorus) :
    ToricFan.Triangle.time (factors s u) = u 2 := by
  have he := congrFun (ToricCharts.monomial_mul_on_torus s.rays s.dual (fun j => (u j).ne_zero)) 2
  simpa only [factors, ToricFan.Triangle.rays_dual, ToricCharts.monomial_one,
    ToricFan.Triangle.monomial_rays_height] using he

theorem ToricSpace.time_scale (s : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.time (scale s u z) = (u 2 : ℂ) * ToricFan.Triangle.time z := by
  rw [← time_factors s u]
  simp [ToricFan.Triangle.time, scale]
  ring

theorem ToricSpace.time_torusAction (u : ActingTorus) (x : Space) :
    time (torusAction u x) = (u 2 : ℂ) * time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [time_scale]

def ToricSpace.fibreMultiplier (u : Fin 2 → ℂˣ) : ActingTorus :=
  ![u 0, u 1, 1]

@[simp]
theorem ToricSpace.time_fibreMultiplier (u : Fin 2 → ℂˣ) (x : Space) :
    time (torusAction (fibreMultiplier u) x) = time x := by
  simp [time_torusAction, fibreMultiplier]

theorem ToricSpace.shear_fibreMultiplier (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) :
    ToricCharts.monomial (ToricFan.Triangle.shear v) (fun j => (fibreMultiplier u j : ℂ)) =
      (fun j => (fibreMultiplier u j : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [ToricCharts.monomial, ToricFan.Triangle.shear, fibreMultiplier, Fin.prod_univ_succ]

theorem ToricSpace.factors_shift_fibreMultiplier (s : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (u : Fin 2 → ℂˣ) : factors (s.shift v) (fibreMultiplier u) = factors s (fibreMultiplier u) := by
  unfold factors
  rw [ToricFan.Triangle.dual_shift, ←
    ToricCharts.monomial_mul_on_torus s.dual (ToricFan.Triangle.shear (-v))
      (fun j => (fibreMultiplier u j).ne_zero),
    shear_fibreMultiplier]

theorem ToricSpace.fibreMultiplier_translate (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) (x : Space) :
    torusAction (fibreMultiplier u) (ToricSpace.translate v x) =
      ToricSpace.translate v (torusAction (fibreMultiplier u) x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [scale, factors_shift_fibreMultiplier]

@[simp]
theorem ToricSpace.fibreMultiplier_one : fibreMultiplier 1 = 1 := by
  ext i
  fin_cases i <;> simp [fibreMultiplier]

theorem ToricSpace.fibreMultiplier_mul (u v : Fin 2 → ℂˣ) :
    fibreMultiplier (u * v) = fibreMultiplier u * fibreMultiplier v := by
  ext i
  fin_cases i <;> simp [fibreMultiplier]

def ToricSpace.variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) : Space :=
  torusAction (fibreMultiplier (u (time x))) x

@[simp]
theorem ToricSpace.variableMultiplier_inclusion (u : ℂ → Fin 2 → ℂˣ) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    variableMultiplier u (ToricSpace.inclusion s z) =
      ToricSpace.inclusion s (scale s (fibreMultiplier (u (ToricFan.Triangle.time z))) z) := by
  simp [variableMultiplier]

@[simp]
theorem ToricSpace.time_variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) :
    time (variableMultiplier u x) = time x := by simp [variableMultiplier]

@[simp]
theorem ToricSpace.variableMultiplier_one (x : Space) : variableMultiplier (fun _ => 1) x = x := by
  simp [variableMultiplier]

theorem ToricSpace.variableMultiplier_mul (u v : ℂ → Fin 2 → ℂˣ) (x : Space) :
    variableMultiplier u (variableMultiplier v x) = variableMultiplier (fun t => u t * v t) x := by
  simp only [variableMultiplier, time_fibreMultiplier, torusAction_mul, fibreMultiplier_mul]

theorem ToricSpace.variableMultiplier_translate (u : ℂ → Fin 2 → ℂˣ) (v : Fin 2 → ℤ) (x : Space) :
    variableMultiplier u (ToricSpace.translate v x) =
      ToricSpace.translate v (variableMultiplier u x) := by
  simp [variableMultiplier, fibreMultiplier_translate]

theorem ToricSpace.varying_scale_holomorphic (s : ToricFan.Triangle) (u : ℂ → Fin 2 → ℂˣ)
    {D : Set ℂ} (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContDiffOn ℂ ω (fun z => scale s (fibreMultiplier (u (ToricFan.Triangle.time z))) z)
      (ToricFan.Triangle.time ⁻¹' D) := by
  have hval :
    ContDiffOn ℂ ω
      (fun z : ToricCharts.CoordinateSpace 3 => fun j =>
        (fibreMultiplier (u (ToricFan.Triangle.time z)) j : ℂ))
      (ToricFan.Triangle.time ⁻¹' D) := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact (hu 0).comp ToricFan.Triangle.time_holomorphic.contDiffOn (fun _ hz => hz)
    · exact (hu 1).comp ToricFan.Triangle.time_holomorphic.contDiffOn (fun _ hz => hz)
    · exact contDiffOn_const
  have hfactors :
    ContDiffOn ℂ ω
      (fun z : ToricCharts.CoordinateSpace 3 =>
        factors s (fibreMultiplier (u (ToricFan.Triangle.time z))))
      (ToricFan.Triangle.time ⁻¹' D) :=
    (ToricCharts.monomial_contDiffOn s.dual ω).comp hval
      (fun z _ =>
        ToricCharts.torus_subset_domain _
          (fun j => (fibreMultiplier (u (ToricFan.Triangle.time z)) j).ne_zero))
  exact hfactors.mul contDiffOn_id

theorem ToricSpace.variableMultiplier_holomorphic (u : ℂ → Fin 2 → ℂˣ) {D : Set ℂ} (hD : IsOpen D)
    (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (variableMultiplier u)
      (time ⁻¹' D) := by
  apply contMDiffOn_of_comp_inclusion _ _ (hD.preimage time_holomorphic.continuous)
  intro s
  have he :
    (variableMultiplier u ∘ ToricSpace.inclusion s) =
      (ToricSpace.inclusion s ∘ fun z =>
        scale s (fibreMultiplier (u (ToricFan.Triangle.time z))) z) := by
    funext z
    exact variableMultiplier_inclusion u s z
  rw [he]
  have hpre : ToricSpace.inclusion s ⁻¹' (time ⁻¹' D) = ToricFan.Triangle.time ⁻¹' D := by
    ext z
    simp
  rw [hpre]
  exact (inclusion_holomorphic s).comp_contMDiffOn (varying_scale_holomorphic s u hu).contMDiffOn

def ToricSpace.cuspVector (v : Fin 2 → ℤ) : Fin 2 → ℤ :=
  ![v 1, -v 0]

@[simp]
theorem ToricSpace.cuspVector_zero : cuspVector 0 = 0 := by ext i; fin_cases i <;> rfl

theorem ToricSpace.cuspVector_add (v w : Fin 2 → ℤ) :
    cuspVector (v + w) = cuspVector v + cuspVector w := by
  ext i
  fin_cases i <;> simp [cuspVector, add_comm]

def ToricSpace.exponentialMultiplier (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) :
    Fin 2 → ℂˣ := fun j =>
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (v i : ℂ))) j))
    (Complex.exp_ne_zero _)

@[simp]
theorem ToricSpace.exponentialMultiplier_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    exponentialMultiplier C 0 t = 1 := by
  ext j
  simp [exponentialMultiplier, Matrix.mulVec, dotProduct]

theorem ToricSpace.exponentialMultiplier_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (t : ℂ) :
    exponentialMultiplier C (v + w) t =
      exponentialMultiplier C v t * exponentialMultiplier C w t := by
  have he : (fun i => ((v + w) i : ℂ)) = (fun i => (v i : ℂ)) + (fun i => (w i : ℂ)) := by
    ext i
    simp
  ext j
  change
    Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => ((v + w) i : ℂ))) j) =
      Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (v i : ℂ))) j) *
        Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (w i : ℂ))) j)
  rw [he, Matrix.mulVec_add]
  simp only [Pi.add_apply, mul_add, Complex.exp_add]

theorem ToricSpace.exponentialMultiplier_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {D : Set ℂ} (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D) (j : Fin 2) :
    ContDiffOn ℂ ω (fun t => (exponentialMultiplier C v t j : ℂ)) D := by
  apply ContDiffOn.cexp
  apply contDiffOn_const.mul
  change ContDiffOn ℂ ω (fun t => ∑ i, C t j i * (v i : ℂ)) D
  apply ContDiffOn.sum
  intro i _
  exact (hC j i).mul contDiffOn_const

def ToricSpace.twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    Space :=
  variableMultiplier (exponentialMultiplier C v) (ToricSpace.translate (cuspVector v) x)

@[simp]
theorem ToricSpace.time_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : Space) : time (twistedTranslate C v x) = time x := by simp [twistedTranslate]

@[simp]
theorem ToricSpace.twistedTranslate_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : Space) :
    twistedTranslate C 0 x = x := by
  have he : exponentialMultiplier C 0 = (fun _ => 1) := funext (exponentialMultiplier_zero C)
  simp [twistedTranslate, he]

theorem ToricSpace.twistedTranslate_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (x : Space) : twistedTranslate C v (twistedTranslate C w x) = twistedTranslate C (v + w) x := by
  simp only [twistedTranslate]
  rw [← variableMultiplier_translate, ToricSpace.translate_add, variableMultiplier_mul]
  have he :
    (fun t => exponentialMultiplier C v t * exponentialMultiplier C w t) =
      exponentialMultiplier C (v + w) :=
    funext fun t => (exponentialMultiplier_add C v w t).symm
  rw [he, cuspVector_add]

theorem ToricSpace.twistedTranslate_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {D : Set ℂ} (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D) :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (twistedTranslate C v)
      (time ⁻¹' D) := by
  exact
    (variableMultiplier_holomorphic _ hD (exponentialMultiplier_holomorphic C v hC)).comp
      (translate_holomorphic (cuspVector v)).contMDiffOn (fun x hx => by simpa using hx)

def ToricSpace.tubeOpen (D : TopologicalSpace.Opens ℂ) : TopologicalSpace.Opens Space :=
  ⟨time ⁻¹' (D : Set ℂ), D.isOpen.preimage time_holomorphic.continuous⟩

abbrev ToricSpace.Tube (D : TopologicalSpace.Opens ℂ) :=
  tubeOpen D

def ToricSpace.tubeTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (D : TopologicalSpace.Opens ℂ)
    (v : Fin 2 → ℤ) (x : Tube D) : Tube D :=
  ⟨twistedTranslate C v x, by
    change time (twistedTranslate C v x) ∈ D
    rw [time_twistedTranslate]
    exact x.2⟩

@[instance_reducible]
def ToricSpace.tubeAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (D : TopologicalSpace.Opens ℂ) :
    MulAction (Multiplicative (Fin 2 → ℤ)) (Tube D)
    where
  smul v x := tubeTranslate C D v.toAdd x
  one_smul x := Subtype.ext (twistedTranslate_zero C x)
  mul_smul v w x := Subtype.ext (twistedTranslate_add C v.toAdd w.toAdd x).symm

theorem ToricSpace.tubeTranslate_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (D : Set ℂ)) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (tubeTranslate C D v) := by
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun y : Tube D => (tubeTranslate C D v y : Space)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (tubeTranslate C D v) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  change
    ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun y : Tube D => twistedTranslate C v (y : Space)) x
  apply (contMDiffAt_subtype_iff (U := tubeOpen D) (f := twistedTranslate C v)).mpr
  exact
    (twistedTranslate_holomorphic C v D.isOpen hC).contMDiffAt ((tubeOpen D).isOpen.mem_nhds x.2)

def ToricSpace.torusCoordinates (x : Space) : ToricCharts.CoordinateSpace 3 :=
  ToricCharts.monomial (preferredTriangle x).rays ((parametrization (preferredTriangle x)).symm x)

theorem ToricSpace.torusCoordinates_inclusion (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus) :
    torusCoordinates (ToricSpace.inclusion s z) = ToricCharts.monomial s.rays z := by
  have he :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  unfold torusCoordinates
  rw [he.2]
  change
    ToricCharts.monomial (preferredTriangle (ToricSpace.inclusion s z)).rays
        (ToricCharts.monomial
          (ToricFan.Triangle.transition s (preferredTriangle (ToricSpace.inclusion s z))) z) =
      _
  rw [ToricCharts.monomial_mul_on_torus _ _ hz, ToricFan.Triangle.transition_covariance]

@[simp]
theorem ToricSpace.torusCoordinates_time (x : Space) : torusCoordinates x 2 = time x :=
  ToricFan.Triangle.monomial_rays_height _ _

theorem ToricSpace.torusCoordinates_nonzero {x : Space} (hx : x ∈ openTorus) (i : Fin 3) :
    torusCoordinates x i ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [torusCoordinates_inclusion _ hz]
  exact ToricCharts.monomial_mapsTo_torus _ hz i

theorem ToricSpace.inclusion_preimage_openTorus (s : ToricFan.Triangle) :
    ToricSpace.inclusion s ⁻¹' openTorus = ToricCharts.torus := by
  ext z
  simp [mem_openTorus_iff, ToricFan.Triangle.time, ToricCharts.torus, Fin.forall_fin_succ,
    and_assoc]

theorem ToricSpace.torusCoordinates_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω torusCoordinates openTorus := by
  apply contMDiffOn_of_comp_inclusion _ _ openTorus_isOpen
  intro s
  rw [inclusion_preimage_openTorus]
  exact
    ((ToricCharts.monomial_contDiffOn s.rays ω).mono
          (ToricCharts.torus_subset_domain _)).contMDiffOn.congr
      (fun z hz => torusCoordinates_inclusion s hz)

theorem ToricSpace.torusCoordinates_translate (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (ToricSpace.translate v x) =
      ToricCharts.monomial (ToricFan.Triangle.shear v) (torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [translate_inclusion, torusCoordinates_inclusion _ hz, torusCoordinates_inclusion _ hz,
    ToricFan.Triangle.rays_shift]
  exact (ToricCharts.monomial_mul_on_torus _ _ hz).symm

theorem ToricSpace.monomial_rays_factors (s : ToricFan.Triangle) (u : ActingTorus) :
    ToricCharts.monomial s.rays (factors s u) = (fun j => (u j : ℂ)) := by
  rw [factors, ToricCharts.monomial_mul_on_torus _ _ (fun j => (u j).ne_zero),
    ToricFan.Triangle.rays_dual, ToricCharts.monomial_one]

theorem ToricSpace.torusCoordinates_action (u : ActingTorus) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (torusAction u x) = (fun j => (u j : ℂ)) * torusCoordinates x := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hs : scale referenceTriangle u z ∈ ToricCharts.torus := fun j =>
    mul_ne_zero (factors_nonzero _ _ j) (hz j)
  rw [torusAction_inclusion, torusCoordinates_inclusion _ hs, torusCoordinates_inclusion _ hz]
  rw [scale, ToricCharts.monomial_mul, monomial_rays_factors]

theorem ToricSpace.torusCoordinates_variableMultiplier (u : ℂ → Fin 2 → ℂˣ) {x : Space}
    (hx : x ∈ openTorus) :
    torusCoordinates (variableMultiplier u x) =
      (fun j => (fibreMultiplier (u (time x)) j : ℂ)) * torusCoordinates x :=
  torusCoordinates_action _ hx

theorem ToricSpace.torusCoordinates_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (twistedTranslate C v x) =
      (fun j => (fibreMultiplier (exponentialMultiplier C v (time x)) j : ℂ)) *
        ToricCharts.monomial (ToricFan.Triangle.shear (cuspVector v)) (torusCoordinates x) := by
  have ht : ToricSpace.translate (cuspVector v) x ∈ openTorus := by
    simpa only [mem_openTorus_iff, time_translate] using hx
  rw [twistedTranslate, torusCoordinates_variableMultiplier _ ht, time_translate,
    torusCoordinates_translate _ hx]

theorem ToricSpace.torusCoordinates_twistedTranslate_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    torusCoordinates (twistedTranslate C v x) i.castSucc =
      (exponentialMultiplier C v (time x) i : ℂ) * (time x) ^ cuspVector v i *
        torusCoordinates x i.castSucc := by
  rw [torusCoordinates_twistedTranslate C v hx]
  fin_cases i <;>
    simp [ToricCharts.monomial, ToricFan.Triangle.shear, fibreMultiplier, Fin.prod_univ_succ,
      mul_comm, mul_left_comm, mul_assoc]

def ToricSpace.logNorm (z : ToricCharts.CoordinateSpace 3) : Fin 3 → ℝ := fun i => Real.log ‖z i‖

theorem ToricSpace.logNorm_monomial (A : Matrix (Fin 3) (Fin 3) ℤ)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus) :
    logNorm (ToricCharts.monomial A z) = A.map (Int.castRingHom ℝ) *ᵥ logNorm z := by
  ext i
  change Real.log ‖∏ j, z j ^ A i j‖ = ∑ j, (A i j : ℝ) * Real.log ‖z j‖
  rw [norm_prod, Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz j)))]
  simp [norm_zpow, Real.log_zpow]

def ToricSpace.logCoordinates (x : Space) : Fin 3 → ℝ :=
  logNorm (torusCoordinates x)

theorem ToricSpace.logCoordinates_inclusion (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus) :
    logCoordinates (ToricSpace.inclusion s z) = s.rays.map (Int.castRingHom ℝ) *ᵥ logNorm z := by
  rw [logCoordinates, torusCoordinates_inclusion s hz, logNorm_monomial _ hz]

@[simp]
theorem ToricSpace.logCoordinates_time (x : Space) : logCoordinates x 2 = Real.log ‖time x‖ := by
  simp [logCoordinates, logNorm]

theorem ToricSpace.logNorm_sum (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) : ∑ j, logNorm z j = Real.log ‖ToricFan.Triangle.time z‖ := by
  have he := congrFun (logCoordinates_inclusion s hz) 2
  simpa [Matrix.mulVec, dotProduct, logCoordinates_time] using he.symm

def ToricSpace.driftMatrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => -2 * Real.pi * (C t i j).im

theorem ToricSpace.exponentialMultiplier_log_norm (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    Real.log ‖(exponentialMultiplier C v t i : ℂ)‖ =
      (driftMatrix C t *ᵥ (fun j => (v j : ℝ))) i := by
  simp [exponentialMultiplier, Complex.norm_exp, driftMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

theorem ToricSpace.logCoordinates_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    logCoordinates (twistedTranslate C v x) i.castSucc =
      logCoordinates x i.castSucc + Real.log ‖time x‖ * (cuspVector v i : ℝ) +
        (driftMatrix C (time x) *ᵥ (fun j => (v j : ℝ))) i := by
  have ht : time x ≠ 0 := (mem_openTorus_iff x).mp hx
  have hu : ‖(exponentialMultiplier C v (time x) i : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (exponentialMultiplier C v (time x) i).ne_zero
  have hp : ‖(time x) ^ cuspVector v i‖ ≠ 0 := norm_ne_zero_iff.mpr (zpow_ne_zero _ ht)
  have hz : ‖torusCoordinates x i.castSucc‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (torusCoordinates_nonzero hx _)
  simp only [logCoordinates, logNorm, torusCoordinates_twistedTranslate_apply C v hx, norm_mul]
  rw [Real.log_mul (mul_ne_zero hu hp) hz, Real.log_mul hu hp, exponentialMultiplier_log_norm,
    norm_zpow, Real.log_zpow]
  ring

def ToricSpace.position (x : Space) : Fin 2 → ℝ := fun i =>
  logCoordinates x i.castSucc / Real.log ‖time x‖

theorem ToricSpace.position_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) (i : Fin 2) :
    position (twistedTranslate C v x) i =
      position x i + (cuspVector v i : ℝ) +
        (driftMatrix C (time x) *ᵥ (fun j => (v j : ℝ))) i / Real.log ‖time x‖ := by
  simp only [position, time_twistedTranslate, logCoordinates_twistedTranslate C v hx]
  field_simp

def ToricSpace.latticeReal (v : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (v i : ℝ)

theorem ToricSpace.norm_latticeReal (v : Fin 2 → ℤ) : ‖latticeReal v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact (Int.norm_cast_real (v i)).le.trans (norm_le_pi_norm v i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← Int.norm_cast_real (v i)]
    exact norm_le_pi_norm (latticeReal v) i

theorem ToricSpace.lattice_bounded_finite (R : ℝ) :
    {v : Fin 2 → ℤ | ‖latticeReal v‖ ≤ R}.Finite := by
  have he : {v : Fin 2 → ℤ | ‖latticeReal v‖ ≤ R} = Metric.closedBall 0 R := by
    ext v
    simp [norm_latticeReal, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact (ProperSpace.isCompact_closedBall _ _).finite_of_discrete

def ToricSpace.entryNorm (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ‖fun i : Fin 2 => fun j : Fin 2 => A i j‖

theorem ToricSpace.entryNorm_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ entryNorm A :=
  norm_nonneg _

theorem ToricSpace.norm_cuspVector (v : Fin 2 → ℤ) :
    ‖latticeReal (cuspVector v)‖ = ‖latticeReal v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm (latticeReal v) 1
    · simpa [latticeReal, cuspVector] using norm_le_pi_norm (latticeReal v) 0
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [latticeReal, cuspVector] using norm_le_pi_norm (latticeReal (cuspVector v)) 1
    · exact norm_le_pi_norm (latticeReal (cuspVector v)) 0

theorem ToricSpace.norm_matrix_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    ‖A *ᵥ v‖ ≤ 2 * entryNorm A * ‖v‖ := by
  have hA := entryNorm_nonneg A
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, entryNorm A * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact
        mul_le_mul
          ((norm_le_pi_norm (A i) j).trans
            (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 => A k l) i))
          (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * entryNorm A * ‖v‖ := by simp; ring

theorem ToricSpace.position_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) :
    position (twistedTranslate C v x) - position x =
      latticeReal (cuspVector v) +
        (Real.log ‖time x‖)⁻¹ • (driftMatrix C (time x) *ᵥ latticeReal v) := by
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [position_twistedTranslate C v hx ht]
  simp only [latticeReal, div_eq_mul_inv, Matrix.mulVec, dotProduct]
  ring

theorem ToricSpace.lattice_bound_of_small_drift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ‖latticeReal v‖ ≤ 2 * ‖position (twistedTranslate C v x) - position x‖ := by
  let e := (Real.log ‖time x‖)⁻¹ • (driftMatrix C (time x) *ᵥ latticeReal v)
  have hneg : 0 < -Real.log ‖time x‖ := neg_pos.mpr ht
  have he : ‖e‖ ≤ ‖latticeReal v‖ / 2 := by
    calc
      ‖e‖ = (-Real.log ‖time x‖)⁻¹ * ‖driftMatrix C (time x) *ᵥ latticeReal v‖ := by
        simp only [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_neg ht]
      _ ≤ (-Real.log ‖time x‖)⁻¹ * (2 * entryNorm (driftMatrix C (time x)) * ‖latticeReal v‖) :=
        (mul_le_mul_of_nonneg_left (norm_matrix_mulVec_le _ _) (by positivity))
      _ ≤ (-Real.log ‖time x‖)⁻¹ * (2 * (-Real.log ‖time x‖ / 4) * ‖latticeReal v‖) := by gcongr
      _ = ‖latticeReal v‖ / 2 := by field_simp [ht.ne]; ring
  have htriangle := norm_add_le (latticeReal (cuspVector v) + e) (-e)
  have hnorm :
    ‖latticeReal (cuspVector v) + e‖ = ‖position (twistedTranslate C v x) - position x‖ := by
    rw [position_displacement C v hx ht.ne]
  simp only [add_neg_cancel_right, norm_neg, norm_cuspVector] at htriangle
  rw [hnorm] at htriangle
  linarith

def ToricSpace.barycentric (z : ToricCharts.CoordinateSpace 3) : Fin 3 → ℝ := fun j =>
  logNorm z j / Real.log ‖ToricFan.Triangle.time z‖

theorem ToricSpace.barycentric_sum (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) (ht : Real.log ‖ToricFan.Triangle.time z‖ ≠ 0) :
    ∑ j, barycentric z j = 1 := by
  simp only [barycentric, ← Finset.sum_div, logNorm_sum s hz, div_self ht]

theorem ToricSpace.position_inclusion (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) (i : Fin 2) :
    position (ToricSpace.inclusion s z) i = ∑ j, (s.rays i.castSucc j : ℝ) * barycentric z j := by
  simp only [position, time_inclusion, logCoordinates_inclusion s hz, Matrix.mulVec, dotProduct,
    barycentric, Finset.sum_div, mul_div_assoc]
  rfl

def ToricSpace.chartSize (s : ToricFan.Triangle) : ℝ :=
  ‖(s.a : ℝ)‖ + ‖(s.b : ℝ)‖ + 1

theorem ToricSpace.chartSize_pos (s : ToricFan.Triangle) : 0 < chartSize s := by
  unfold chartSize
  positivity

theorem ToricSpace.ray_norm_le_chartSize (s : ToricFan.Triangle) (i : Fin 2) (j : Fin 3) :
    ‖(s.rays i.castSucc j : ℝ)‖ ≤ chartSize s := by
  have ha : ‖(s.a : ℝ)‖ ≤ chartSize s := by unfold chartSize; linarith [norm_nonneg (s.b : ℝ)]
  have hb : ‖(s.b : ℝ)‖ ≤ chartSize s := by unfold chartSize; linarith [norm_nonneg (s.a : ℝ)]
  have ha' : ‖(s.a : ℝ) + 1‖ ≤ chartSize s := (norm_add_le _ _).trans (by simp [chartSize])
  have hb' : ‖(s.b : ℝ) + 1‖ ≤ chartSize s := (norm_add_le _ _).trans (by simp [chartSize])
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    first
    | simpa [ToricFan.Triangle.rays, hs] using ha
    | simpa [ToricFan.Triangle.rays, hs] using hb
    | simpa [ToricFan.Triangle.rays, hs] using ha'
    | simpa [ToricFan.Triangle.rays, hs] using hb'

theorem ToricSpace.barycentric_lower_bound {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖ToricFan.Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) (j : Fin 3) :
    -(Real.log S / (-Real.log ε)) ≤ barycentric z j := by
  have hn : ToricFan.Triangle.time z ≠ 0 := mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  have hlogε : Real.log ε < 0 := Real.log_neg hε hε1
  have hlogt : Real.log ‖ToricFan.Triangle.time z‖ < Real.log ε :=
    Real.log_lt_log (norm_pos_iff.mpr hn) ht
  have hη : 0 ≤ Real.log S / (-Real.log ε) :=
    div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr hlogε.le)
  have hlogz : Real.log ‖z j‖ ≤ Real.log S := Real.log_le_log (norm_pos_iff.mpr (hz j)) (hzS j)
  have hmul := mul_le_mul_of_nonpos_left hlogt.le (neg_nonpos.mpr hη)
  have he : -(Real.log S / (-Real.log ε)) * Real.log ε = Real.log S := by field_simp [hlogε.ne]
  rw [he] at hmul
  exact (le_div_iff_of_neg (hlogt.trans hlogε)).mpr (hlogz.trans hmul)

theorem ToricSpace.barycentric_norm_bound {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖ToricFan.Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) (j : Fin 3) :
    ‖barycentric z j‖ ≤ 1 + 2 * (Real.log S / (-Real.log ε)) := by
  let η := Real.log S / (-Real.log ε)
  have hη : 0 ≤ η := div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr (Real.log_neg hε hε1).le)
  have hlow (k : Fin 3) : -η ≤ barycentric z k := barycentric_lower_bound hz hS hε hε1 ht hzS k
  have hn : ToricFan.Triangle.time z ≠ 0 := mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  have hs :=
    barycentric_sum referenceTriangle hz (Real.log_neg (norm_pos_iff.mpr hn) (ht.trans hε1)).ne
  have hsum : ∑ k : Fin 3, (barycentric z k + η) = 1 + 3 * η := by
    rw [Finset.sum_add_distrib, hs]
    simp
  have hu :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 3 => barycentric z k + η)
      (fun k _ => by linarith [hlow k]) (Finset.mem_univ j)
  rw [hsum] at hu
  change ‖barycentric z j‖ ≤ 1 + 2 * η
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hlow j]

def ToricSpace.positionBound (s : ToricFan.Triangle) (S ε : ℝ) : ℝ :=
  3 * chartSize s * (1 + 2 * (Real.log S / (-Real.log ε)))

theorem ToricSpace.position_norm_bound (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖ToricFan.Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) :
    ‖position (ToricSpace.inclusion s z)‖ ≤ positionBound s S ε := by
  have hη : 0 ≤ Real.log S / (-Real.log ε) :=
    div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr (Real.log_neg hε hε1).le)
  have hsize := chartSize_pos s
  apply (pi_norm_le_iff_of_nonneg (by unfold positionBound; positivity)).mpr
  intro i
  rw [position_inclusion s hz]
  calc
    ‖∑ j, (s.rays i.castSucc j : ℝ) * barycentric z j‖ ≤
        ∑ j, ‖(s.rays i.castSucc j : ℝ) * barycentric z j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, chartSize s * (1 + 2 * (Real.log S / (-Real.log ε))) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact
        mul_le_mul (ray_norm_le_chartSize s i j) (barycentric_norm_bound hz hS hε hε1 ht hzS j)
          (norm_nonneg _) (chartSize_pos s).le
    _ = positionBound s S ε := by simp [positionBound]; ring

def ToricSpace.SmallDrift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : Prop :=
  ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ε → entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4

def ToricSpace.chartNeighbourhood (s : ToricFan.Triangle) (n : ℕ) (ε : ℝ) : Set Space :=
  ToricSpace.inclusion s ''
    {z : ToricCharts.CoordinateSpace 3 |
      (∀ j, ‖z j‖ < (n : ℝ) + 2) ∧ ‖ToricFan.Triangle.time z‖ < ε}

theorem ToricSpace.chartNeighbourhood_open (s : ToricFan.Triangle) (n : ℕ) (ε : ℝ) :
    IsOpen (chartNeighbourhood s n ε) := by
  apply (inclusion_openEmbedding s).isOpenMap
  have hc : IsOpen {z : ToricCharts.CoordinateSpace 3 | ∀ j, ‖z j‖ < (n : ℝ) + 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply j).norm continuous_const
  exact hc.inter (isOpen_lt ToricFan.Triangle.time_holomorphic.continuous.norm continuous_const)

theorem ToricSpace.chartNeighbourhood_time {s : ToricFan.Triangle} {n : ℕ} {ε : ℝ} {x : Space}
    (hx : x ∈ chartNeighbourhood s n ε) : ‖time x‖ < ε := by
  obtain ⟨z, hz, rfl⟩ := hx
  simpa only [time_inclusion] using hz.2

theorem ToricSpace.chartNeighbourhood_cover {ε : ℝ} {x : Space} (hx : ‖time x‖ < ε) :
    ∃ s n, x ∈ chartNeighbourhood s n ε := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  refine ⟨s, n, z, ⟨?_, by simpa using hx⟩, rfl⟩
  intro j
  have h := norm_le_pi_norm z j
  linarith

def ToricSpace.chartTranslates (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s t : ToricFan.Triangle) (n m : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (chartNeighbourhood s n ε ∩ twistedTranslate C v ⁻¹' chartNeighbourhood t m ε).Nonempty}

theorem ToricSpace.chartTranslates_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (s t : ToricFan.Triangle) (n m : ℕ) :
    (chartTranslates C ε s t n m).Finite := by
  apply
    (lattice_bounded_finite
        (2 * (positionBound s ((n : ℝ) + 2) ε + positionBound t ((m : ℝ) + 2) ε))).subset
  intro v hv
  have hcont : ContinuousOn (twistedTranslate C v) (chartNeighbourhood s n ε) :=
    (twistedTranslate_holomorphic C v Metric.isOpen_ball hC).continuousOn.mono
      (by
        intro x hx
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using
          chartNeighbourhood_time hx)
  have hV :=
    hcont.isOpen_inter_preimage (chartNeighbourhood_open s n ε) (chartNeighbourhood_open t m ε)
  obtain ⟨p, hpT, hpV⟩ := openTorus_dense.exists_mem_open hV hv
  obtain ⟨z, hz, rfl⟩ := hpV.1
  have hzT : z ∈ ToricCharts.torus := by
    rw [← inclusion_preimage_openTorus s]
    exact hpT
  obtain ⟨w, hw, hew⟩ := hpV.2
  have hwT : w ∈ ToricCharts.torus := by
    rw [← inclusion_preimage_openTorus t]
    change ToricSpace.inclusion t w ∈ openTorus
    rw [hew, mem_openTorus_iff, time_twistedTranslate]
    exact (mem_openTorus_iff _).mp hpT
  have ht : 0 < ‖time (ToricSpace.inclusion s z)‖ :=
    norm_pos_iff.mpr ((mem_openTorus_iff _).mp hpT)
  have htime : ‖time (ToricSpace.inclusion s z)‖ < ε := by simpa only [time_inclusion] using hz.2
  have hvbound :=
    lattice_bound_of_small_drift C v hpT (Real.log_neg ht (htime.trans hε1)) (hR _ ht htime)
  have hpbound :=
    position_norm_bound s hzT
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith : (1 : ℝ) ≤ n + 2) hε hε1 hz.2
      (fun j => (hz.1 j).le)
  have hqbound :=
    position_norm_bound t hwT
      (by have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith : (1 : ℝ) ≤ m + 2) hε hε1 hw.2
      (fun j => (hw.1 j).le)
  rw [hew] at hqbound
  have hd :=
    norm_sub_le (position (twistedTranslate C v (ToricSpace.inclusion s z)))
      (position (ToricSpace.inclusion s z))
  change ‖latticeReal v‖ ≤ _
  linarith

theorem ToricSpace.compact_translates_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {K : Set Space} (hK : IsCompact K) (hKt : ∀ x ∈ K, ‖time x‖ < ε) :
    {v : Fin 2 → ℤ | (twistedTranslate C v '' K ∩ K).Nonempty}.Finite := by
  let U : ToricFan.Triangle × ℕ → Set Space := fun i => chartNeighbourhood i.1 i.2 ε
  have hcover : K ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨s, n, hn⟩ := chartNeighbourhood_cover (hKt x hx)
    exact Set.mem_iUnion.mpr ⟨(s, n), hn⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover U (fun i => chartNeighbourhood_open _ _ _) hcover
  have hfinite : (⋃ i ∈ I, ⋃ j ∈ I, chartTranslates C ε i.1 j.1 i.2 j.2).Finite :=
    I.finite_toSet.biUnion fun i _ =>
      I.finite_toSet.biUnion fun j _ => chartTranslates_finite C hε hε1 hC hR i.1 j.1 i.2 j.2
  apply hfinite.subset
  rintro v ⟨q, ⟨p, hp, hpq⟩, hq⟩
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp (hI hp)
  obtain ⟨j, hj, hqj⟩ := Set.mem_iUnion₂.mp (hI hq)
  apply Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  apply Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
  exact ⟨p, hpi, by simpa only [Set.mem_preimage, hpq] using hqj⟩

theorem ToricSpace.SmallDrift.mono {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {ε δ : ℝ}
    (h : ToricSpace.SmallDrift C ε) (hδε : δ ≤ ε) : ToricSpace.SmallDrift C δ := fun t ht hδ =>
  h t ht (hδ.trans_le hδε)

theorem ToricSpace.exists_smallDrift_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hC : ∀ i j, ContinuousAt (fun t => C t i j) 0) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ SmallDrift C ε := by
  have hentries :
    ContinuousAt (fun t : ℂ => fun i : Fin 2 => fun j : Fin 2 => driftMatrix C t i j) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hC i j))
  have hnorm : ContinuousAt (fun t => entryNorm (driftMatrix C t)) 0 := hentries.norm
  let M := entryNorm (driftMatrix C 0) + 1
  have hM : entryNorm (driftMatrix C 0) < M := by dsimp [M]; linarith
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), entryNorm (driftMatrix C t) < M := hnorm (gt_mem_nhds hM)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε := Min.min δ (Min.min (1 / 2) (Real.exp (-4 * M)))
  have hε : 0 < ε := lt_min hδ (lt_min (by norm_num) (Real.exp_pos _))
  refine ⟨ε, hε, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num), ?_⟩
  intro t ht htε
  have htδ : Dist.dist t 0 < δ := by
    simpa only [dist_zero_right] using htε.trans_le (min_le_left _ _)
  have hbound := hδbound htδ
  have hlog : Real.log ‖t‖ ≤ -4 * M := by
    have hsmall : ‖t‖ ≤ Real.exp (-4 * M) :=
      htε.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [Real.log_exp] using Real.log_le_log ht hsmall
  linarith

theorem quotientCoveringMap_of_localHomeomorph {X Y G : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Group G] [MulAction G X] [ContinuousConstSMul G X] [IsCancelSMul G X]
    {q : X → Y} (hq : IsLocalHomeomorph q) (hs : Function.Surjective q)
    (ho : ∀ x y, q x = q y ↔ x ∈ MulAction.orbit G y) : IsQuotientCoveringMap q G
    where
  toIsQuotientMap := hq.isOpenMap.isQuotientMap hq.continuous hs
  continuous_const_smul := ContinuousConstSMul.continuous_const_smul
  apply_eq_iff_mem_orbit := ho _ _
  disjoint
    x := by
    let e := hq.localInverseAt x
    refine ⟨e.target, e.open_target.mem_nhds hq.self_mem_localInverseAt_target, ?_⟩
    rintro g ⟨z, ⟨w, hw, rfl⟩, hgw⟩
    have heq : q (g • w) = q w := (ho _ _).mpr ⟨g, rfl⟩
    have heq' : g • w = (1 : G) • w := by
      simpa only [one_smul] using hq.injOn_localInverseAt_target hgw hw heq
    exact IsCancelSMul.right_cancel _ _ w heq'

theorem localHomeomorph_prod_id {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X]
    [TopologicalSpace Y] {q : X → Y} (hq : IsLocalHomeomorph q) :
    IsLocalHomeomorph (fun z : B × X => (z.1, q z.2)) := by
  intro x
  obtain ⟨e, he, hqe⟩ := hq x.2
  refine ⟨(OpenPartialHomeomorph.refl B).prod e, ⟨Set.mem_univ _, he⟩, ?_⟩
  funext y
  exact congrArg (Prod.mk y.1) (congrFun hqe y.2)

abbrev CuspQuotient.LatticeGroup :=
  Multiplicative (Fin 2 → ℤ)

def CuspQuotient.disc (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 ε, Metric.isOpen_ball⟩

instance CuspQuotient.tube_locallyCompactSpace (ε : ℝ) :
    LocallyCompactSpace (ToricSpace.Tube (disc ε)) :=
  ChartedSpace.locallyCompactSpace (ToricCharts.CoordinateSpace 3) (ToricSpace.Tube (disc ε))

theorem CuspQuotient.continuous_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    letI := ToricSpace.tubeAction C (disc ε)
    ContinuousConstSMul LatticeGroup (ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  exact ⟨fun v => (ToricSpace.tubeTranslate_holomorphic C (disc ε) v.toAdd hC).continuous⟩

theorem CuspQuotient.proper_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := ToricSpace.tubeAction C (disc ε)
    ProperlyDiscontinuousSMul LatticeGroup (ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  constructor
  intro K L hK hL
  let K' : Set ToricSpace.Space := Subtype.val '' (K ∪ L)
  have hK' : IsCompact K' := (hK.union hL).image continuous_subtype_val
  have hKt : ∀ x ∈ K', ‖ToricSpace.time x‖ < ε := by
    rintro _ ⟨x, _, rfl⟩
    have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hfinite := ToricSpace.compact_translates_finite C hε hε1 hC hR hK' hKt
  have hinj : Function.Injective (fun g : LatticeGroup => g.toAdd) := fun _ _ h =>
    congrArg Multiplicative.ofAdd h
  apply (hfinite.preimage hinj.injOn).subset
  rintro g ⟨q, ⟨p, hp, hpq⟩, hq⟩
  refine
    ⟨(q : ToricSpace.Space), ⟨(p : ToricSpace.Space), ⟨p, Or.inl hp, rfl⟩, ?_⟩,
      ⟨q, Or.inr hq, rfl⟩⟩
  exact congrArg Subtype.val hpq

theorem CuspQuotient.free_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := ToricSpace.tubeAction C (disc ε)
    IsCancelSMul LatticeGroup (ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  let := proper_action C ε hε hε1 hC hR
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hg
  let H := MulAction.stabilizer LatticeGroup x
  let : Finite H := ProperlyDiscontinuousSMul.finite_stabilizer x
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite (⟨g, hg⟩ : H)).exists_pow_eq_one
  have he : g ^ n = 1 := congrArg Subtype.val hpow
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, he⟩).eq_one'

def CuspQuotient.relation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Setoid (ToricSpace.Tube (disc ε)) :=
  letI := ToricSpace.tubeAction C (disc ε)
  MulAction.orbitRel LatticeGroup (ToricSpace.Tube (disc ε))

abbrev CuspQuotient.QuotientSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  Quotient (relation C ε)

def CuspQuotient.quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    ToricSpace.Tube (disc ε) → QuotientSpace C ε :=
  Quotient.mk (relation C ε)

theorem CuspQuotient.quotientMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (quotientMap C ε) :=
  continuous_quotient_mk'

@[simp]
theorem CuspQuotient.quotientMap_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Tube (disc ε)) :
    quotientMap C ε (ToricSpace.tubeTranslate C (disc ε) v x) = quotientMap C ε x := by
  let := ToricSpace.tubeAction C (disc ε)
  exact MulAction.orbitRel.Quotient.quotient_smul_eq (g := Multiplicative.ofAdd v) (a := x)

def CuspQuotient.projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : QuotientSpace C ε → ℂ :=
  Quotient.lift (fun x : ToricSpace.Tube (disc ε) => ToricSpace.time (x : ToricSpace.Space))
    (by
      let := ToricSpace.tubeAction C (disc ε)
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact ToricSpace.time_twistedTranslate C g.toAdd y)

@[simp]
theorem CuspQuotient.projection_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : ToricSpace.Tube (disc ε)) :
    projection C ε (quotientMap C ε x) = ToricSpace.time (x : ToricSpace.Space) :=
  rfl

theorem CuspQuotient.projection_mem_disc (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : QuotientSpace C ε) : projection C ε x ∈ disc ε := by
  induction x using Quotient.inductionOn with
  | h x => exact x.2

def CuspQuotient.baseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (x : QuotientSpace C ε) :
    disc ε :=
  ⟨projection C ε x, projection_mem_disc C ε x⟩

theorem CuspQuotient.projection_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (projection C ε) :=
  (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val).quotient_lift _

theorem CuspQuotient.baseMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (baseMap C ε) :=
  (projection_continuous C ε).subtype_mk _

theorem CuspQuotient.quotientMap_covering (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := ToricSpace.tubeAction C (disc ε)
    IsQuotientCoveringMap (quotientMap C ε) LatticeGroup := by
  let := ToricSpace.tubeAction C (disc ε)
  let := continuous_action C ε hC
  let := proper_action C ε hε hε1 hC hR
  let := free_action C ε hε hε1 hC hR
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem CuspQuotient.quotient_t2Space (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : T2Space (QuotientSpace C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  let := continuous_action C ε hC
  let := proper_action C ε hε hε1 hC hR
  change T2Space (Quotient (MulAction.orbitRel LatticeGroup (ToricSpace.Tube (disc ε))))
  infer_instance

@[instance_reducible]
def CuspQuotient.chartedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    ChartedSpace (ToricCharts.CoordinateSpace 3) (QuotientSpace C ε) :=
  letI := ToricSpace.tubeAction C (disc ε)
  CoveringQuotient.chartedSpace (E := ToricCharts.CoordinateSpace 3)
    (quotientMap_covering C ε hε hε1 hC hR)

theorem CuspQuotient.isManifold (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    IsManifold (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (QuotientSpace C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  exact
    CoveringQuotient.isManifold (E := ToricCharts.CoordinateSpace 3)
      (quotientMap_covering C ε hε hε1 hC hR) ω
      (fun v => ToricSpace.tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

theorem CuspQuotient.quotientMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (quotientMap C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  exact
    CoveringQuotient.contMDiff_project (E := ToricCharts.CoordinateSpace 3)
      (quotientMap_covering C ε hε hε1 hC hR) ω
      (fun v => ToricSpace.tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

theorem CuspQuotient.exists_admissible_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ}
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < r ∧
          ε < 1 ∧
            ToricSpace.SmallDrift C ε ∧
              ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε) := by
  have hC0 : ∀ i j, ContinuousAt (fun z => C z i j) 0 := by
    intro i j
    exact (hC i j).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  obtain ⟨δ, hδ, hδ1, hR⟩ := ToricSpace.exists_smallDrift_radius C hC0
  refine
    ⟨Min.min δ (r / 2), lt_min hδ (half_pos hr), (min_le_right _ _).trans_lt (half_lt_self hr),
      (min_le_left _ _).trans_lt hδ1, hR.mono (min_le_left _ _), ?_⟩
  intro i j
  exact (hC i j).mono (Metric.ball_subset_ball ((min_le_right _ _).trans (half_le_self hr.le)))

def CuspUniformization.exponential (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * z)

theorem CuspUniformization.exponential_factor_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  exact
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

@[simp]
theorem CuspUniformization.exponential_ne_zero (z : ℂ) : exponential z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem CuspUniformization.exponential_zero : exponential 0 = 1 := by simp [exponential]

theorem CuspUniformization.exponential_add (z w : ℂ) :
    exponential (z + w) = exponential z * exponential w := by
  simp only [exponential, mul_add, Complex.exp_add]

@[simp]
theorem CuspUniformization.exponential_int (n : ℤ) : exponential n = 1 := by
  simpa only [exponential, mul_comm] using Complex.exp_int_mul_two_pi_mul_I n

theorem CuspUniformization.exponential_eq_iff (z w : ℂ) :
    exponential z = exponential w ↔ ∃ n : ℤ, z = w + n := by
  rw [exponential, exponential, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, mul_left_cancel₀ exponential_factor_ne_zero ?_⟩
    calc
      (2 * Real.pi * Complex.I : ℂ) * z = _ := hn
      _ = (2 * Real.pi * Complex.I : ℂ) * (w + n) := by ring
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

def CuspUniformization.logarithm (t : ℂ) : ℂ :=
  Complex.log t / (2 * Real.pi * Complex.I)

theorem CuspUniformization.exponential_logarithm {t : ℂ} (ht : t ≠ 0) :
    exponential (logarithm t) = t := by
  rw [exponential, logarithm, mul_div_cancel₀ _ exponential_factor_ne_zero]
  exact Complex.exp_log ht

theorem CuspUniformization.exponential_holomorphic : ContDiff ℂ ω exponential :=
  (contDiff_const.mul contDiff_id).cexp

theorem CuspUniformization.log_norm_exponential (s : ℂ) :
    Real.log ‖exponential s‖ = -2 * Real.pi * s.im := by
  simp [exponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

def CuspUniformization.torusPoint (w : ToricCharts.CoordinateSpace 3) : ToricSpace.Space :=
  ToricSpace.inclusion ToricSpace.referenceTriangle
    (ToricCharts.monomial ToricSpace.referenceTriangle.dual w)

theorem CuspUniformization.torusPoint_mem {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) : torusPoint w ∈ ToricSpace.openTorus :=
  ToricSpace.inclusion_torus_subset _ ⟨_, ToricCharts.monomial_mapsTo_torus _ hw, rfl⟩

theorem CuspUniformization.torusCoordinates_torusPoint {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) : ToricSpace.torusCoordinates (torusPoint w) = w := by
  rw [torusPoint,
    ToricSpace.torusCoordinates_inclusion _ (ToricCharts.monomial_mapsTo_torus _ hw),
    ToricCharts.monomial_mul_on_torus _ _ hw, ToricFan.Triangle.rays_dual,
    ToricCharts.monomial_one]

theorem CuspUniformization.torusPoint_torusCoordinates {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) : torusPoint (ToricSpace.torusCoordinates x) = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [ToricSpace.torusCoordinates_inclusion _ hz, torusPoint,
    ToricCharts.monomial_mul_on_torus _ _ hz, ToricFan.Triangle.dual_rays,
    ToricCharts.monomial_one]

theorem CuspUniformization.torusCoordinates_injective :
    Set.InjOn ToricSpace.torusCoordinates ToricSpace.openTorus := by
  intro x hx y hy he
  rw [← torusPoint_torusCoordinates hx, ← torusPoint_torusCoordinates hy, he]

def CuspUniformization.exponentialCoordinates (t : ℂ) (z : ComplexPlane₂) :
    ToricCharts.CoordinateSpace 3 :=
  ![exponential (z 0), exponential (z 1), t]

theorem CuspUniformization.exponentialCoordinates_mem {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    exponentialCoordinates t z ∈ ToricCharts.torus := by
  intro i
  fin_cases i
  · exact exponential_ne_zero _
  · exact exponential_ne_zero _
  · exact ht

theorem CuspUniformization.exponentialCoordinates_holomorphic (t : ℂ) :
    ContDiff ℂ ω (exponentialCoordinates t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ 0)
  · exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ 1)
  · exact contDiff_const

def CuspUniformization.exponentialPoint (t : ℂ) : ComplexPlane₂ → ToricSpace.Space :=
  torusPoint ∘ exponentialCoordinates t

theorem CuspUniformization.exponentialPoint_mem {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    exponentialPoint t z ∈ ToricSpace.openTorus :=
  torusPoint_mem (exponentialCoordinates_mem ht z)

theorem CuspUniformization.torusCoordinates_exponentialPoint {t : ℂ} (ht : t ≠ 0)
    (z : ComplexPlane₂) :
    ToricSpace.torusCoordinates (exponentialPoint t z) = exponentialCoordinates t z :=
  torusCoordinates_torusPoint (exponentialCoordinates_mem ht z)

theorem CuspUniformization.time_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    ToricSpace.time (exponentialPoint t z) = t := by
  simpa [exponentialCoordinates] using congrFun (torusCoordinates_exponentialPoint ht z) 2

theorem CuspUniformization.exponentialPoint_holomorphic {t : ℂ} (ht : t ≠ 0) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (exponentialPoint t) := by
  apply (ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp
  apply ContDiff.contMDiff
  apply contDiffOn_univ.mp
  exact
    (ToricCharts.monomial_contDiffOn ToricSpace.referenceTriangle.dual ω).comp
      (exponentialCoordinates_holomorphic t).contDiffOn
      (fun z _ => ToricCharts.torus_subset_domain _ (exponentialCoordinates_mem ht z))

theorem CuspUniformization.exponentialPoint_surjective_fibre {t : ℂ} (ht : t ≠ 0)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = t) :
    ∃ z : ComplexPlane₂, exponentialPoint t z = x := by
  have hxT : x ∈ ToricSpace.openTorus := (ToricSpace.mem_openTorus_iff _).mpr (hx ▸ ht)
  let z : ComplexPlane₂ := fun i => logarithm (ToricSpace.torusCoordinates x i.castSucc)
  refine ⟨z, torusCoordinates_injective (exponentialPoint_mem ht z) hxT ?_⟩
  rw [torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i
  · exact exponential_logarithm (ToricSpace.torusCoordinates_nonzero hxT 0)
  · exact exponential_logarithm (ToricSpace.torusCoordinates_nonzero hxT 1)
  · simpa [exponentialCoordinates] using hx.symm

theorem CuspUniformization.exponentialPoint_eq_iff {t : ℂ} (ht : t ≠ 0) (z w : ComplexPlane₂) :
    exponentialPoint t z = exponentialPoint t w ↔ ∃ m : Fin 2 → ℤ, z = w + (fun i => (m i : ℂ)) :=
  by
  constructor
  · intro he
    have hec := congrArg ToricSpace.torusCoordinates he
    rw [torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht] at hec
    have hi (i : Fin 2) : ∃ n : ℤ, z i = w i + n := by
      apply (exponential_eq_iff _ _).mp
      have hi := congrFun hec i.castSucc
      fin_cases i <;> exact hi
    choose m hm using hi
    exact ⟨m, funext hm⟩
  · rintro ⟨m, rfl⟩
    apply torusCoordinates_injective (exponentialPoint_mem ht _) (exponentialPoint_mem ht _)
    rw [torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht]
    ext i
    fin_cases i
    · exact (exponential_eq_iff _ _).mpr ⟨m 0, rfl⟩
    · exact (exponential_eq_iff _ _).mpr ⟨m 1, rfl⟩
    · rfl

theorem CuspUniformization.torusPoint_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω torusPoint ToricCharts.torus :=
  (ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp_contMDiffOn
    ((ToricCharts.monomial_contDiffOn ToricSpace.referenceTriangle.dual ω).mono
        (ToricCharts.torus_subset_domain _)).contMDiffOn

def CuspUniformization.torusChart :
    OpenPartialHomeomorph ToricSpace.Space (ToricCharts.CoordinateSpace 3)
    where
  toFun := ToricSpace.torusCoordinates
  invFun := torusPoint
  source := ToricSpace.openTorus
  target := ToricCharts.torus
  map_source' _ hx := ToricSpace.torusCoordinates_nonzero hx
  map_target' _ hw := torusPoint_mem hw
  left_inv' _ hx := torusPoint_torusCoordinates hx
  right_inv' _ hw := torusCoordinates_torusPoint hw
  open_source := ToricSpace.openTorus_isOpen
  open_target := ToricCharts.torus_open
  continuousOn_toFun := ToricSpace.torusCoordinates_holomorphic.continuousOn
  continuousOn_invFun := torusPoint_holomorphic.continuousOn

abbrev ToricFan.Triangle.RealCoordinates :=
  Fin 3 → ℝ

def ToricFan.Triangle.coordinates (s : ToricFan.Triangle) :
    RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (s.dual.map (Int.castRingHom ℝ)).mulVecLin

def ToricFan.Triangle.generate (s : ToricFan.Triangle) : RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (s.rays.map (Int.castRingHom ℝ)).mulVecLin

theorem ToricFan.Triangle.coordinates_lower (a b : ℤ) (x : RealCoordinates) :
    coordinates ⟨a, b, Bool.false⟩ x =
      ![(1 + (a : ℝ) + b) * x 2 - x 0 - x 1, x 0 - a * x 2, x 1 - b * x 2] := by
  ext i
  fin_cases i <;> simp [coordinates, dual, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem ToricFan.Triangle.coordinates_upper (a b : ℤ) (x : RealCoordinates) :
    coordinates ⟨a, b, Bool.true⟩ x =
      ![((b : ℝ) + 1) * x 2 - x 1, ((a : ℝ) + 1) * x 2 - x 0,
        x 0 + x 1 - (1 + (a : ℝ) + b) * x 2] := by
  ext i
  fin_cases i <;> simp [coordinates, dual, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

theorem ToricFan.Triangle.coordinates_generate (s : ToricFan.Triangle) (x : RealCoordinates) :
    s.coordinates (s.generate x) = x := by
  change (s.dual.map (Int.castRingHom ℝ)) *ᵥ ((s.rays.map (Int.castRingHom ℝ)) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, dual_rays]
  simp

def ToricFan.Triangle.cone (s : ToricFan.Triangle) : ConvexCone ℝ RealCoordinates
    where
  carrier := {x | ∀ i, 0 ≤ s.coordinates x i}
  smul_mem' := by
    intro c hc x hx i
    simpa using mul_nonneg hc.le (hx i)
  add_mem' := by
    intro x hx y hy i
    simpa using add_nonneg (hx i) (hy i)

@[simp]
theorem ToricFan.Triangle.mem_cone (s : ToricFan.Triangle) (x : RealCoordinates) :
    x ∈ s.cone ↔ ∀ i, 0 ≤ s.coordinates x i :=
  Iff.rfl

def ToricSpace.realCuspVector : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)
    where
  toFun v := ![v 1, -v 0]
  map_add' v w := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp

theorem ToricSpace.realCuspVector_latticeReal (v : Fin 2 → ℤ) :
    realCuspVector (latticeReal v) = latticeReal (cuspVector v) := by
  ext i
  fin_cases i <;> simp [realCuspVector, latticeReal, cuspVector]

theorem ToricSpace.realCuspVector_norm (v : Fin 2 → ℝ) : ‖realCuspVector v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · simpa [realCuspVector] using norm_le_pi_norm v 0
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [realCuspVector] using norm_le_pi_norm (realCuspVector v) 1
    · exact norm_le_pi_norm (realCuspVector v) 0

def ToricSpace.displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  realCuspVector + (Real.log ‖t‖)⁻¹ • (driftMatrix C t).mulVecLin

theorem ToricSpace.displacement_error_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖displacement C t v - realCuspVector v‖ ≤ ‖v‖ / 2 := by
  have hneg : 0 < -Real.log ‖t‖ := neg_pos.mpr ht
  have he : displacement C t v - realCuspVector v = (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ v) := by
    simp [displacement]
  rw [he]
  calc
    ‖(Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ v)‖ = (-Real.log ‖t‖)⁻¹ * ‖driftMatrix C t *ᵥ v‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_neg ht]
    _ ≤ (-Real.log ‖t‖)⁻¹ * (2 * entryNorm (driftMatrix C t) * ‖v‖) :=
      (mul_le_mul_of_nonneg_left (norm_matrix_mulVec_le _ _) (by positivity))
    _ ≤ (-Real.log ‖t‖)⁻¹ * (2 * (-Real.log ‖t‖ / 4) * ‖v‖) := by gcongr
    _ = ‖v‖ / 2 := by field_simp [ht.ne]; ring

theorem ToricSpace.displacement_lower_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖v‖ ≤ 2 * ‖displacement C t v‖ := by
  have he := displacement_error_bound C ht hR v
  have htri := norm_sub_le (displacement C t v) (displacement C t v - realCuspVector v)
  rw [sub_sub_cancel, realCuspVector_norm] at htri
  linarith

theorem ToricSpace.displacement_upper_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖displacement C t v‖ ≤ 3 / 2 * ‖v‖ := by
  have he := displacement_error_bound C ht hR v
  have htri := norm_add_le (realCuspVector v) (displacement C t v - realCuspVector v)
  rw [add_sub_cancel, realCuspVector_norm] at htri
  linarith

theorem ToricSpace.displacement_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    Function.Bijective (displacement C t) := by
  have hinj : Function.Injective (displacement C t) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hb := displacement_lower_bound C ht hR v
    rw [hv, norm_zero, MulZeroClass.mul_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem ToricSpace.exists_integer_rounding (u : Fin 2 → ℝ) :
    ∃ v : Fin 2 → ℤ, ‖u + latticeReal v‖ ≤ 1 := by
  refine ⟨fun i => -⌊u i⌋, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  simp only [Pi.add_apply, latticeReal, Int.cast_neg, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [Int.floor_le (u i), Int.lt_floor_add_one (u i)]

theorem ToricSpace.position_twistedTranslate_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) :
    position (twistedTranslate C v x) = position x + displacement C (time x) (latticeReal v) := by
  have he := position_displacement C v hx ht
  rw [← realCuspVector_latticeReal] at he
  change
    position (twistedTranslate C v x) - position x = displacement C (time x) (latticeReal v) at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem ToricSpace.exists_bounded_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {x : Space}
    (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ∃ v : Fin 2 → ℤ, ‖position (twistedTranslate C v x)‖ ≤ 2 := by
  obtain ⟨u, hu⟩ := (displacement_bijective C ht hR).surjective (position x)
  obtain ⟨v, hv⟩ := exists_integer_rounding u
  refine ⟨v, ?_⟩
  rw [position_twistedTranslate_displacement C v hx ht.ne, ← hu, ← map_add]
  exact (displacement_upper_bound C ht hR _).trans (by nlinarith)

theorem ToricSpace.exists_torus_chart (s : ToricFan.Triangle) {x : Space} (hx : x ∈ openTorus) :
    ∃ z ∈ ToricCharts.torus, ToricSpace.inclusion s z = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine
    ⟨ToricFan.Triangle.chartChange referenceTriangle s z, ToricCharts.monomial_mapsTo_torus _ hz,
      ?_⟩
  exact
    ((inclusion_eq_iff referenceTriangle s z _).mpr
        ⟨ToricCharts.torus_subset_overlap _ _ hz, rfl⟩).symm

def ToricSpace.positionPoint (y : Fin 2 → ℝ) : ToricFan.Triangle.RealCoordinates :=
  ![y 0, y 1, 1]

theorem ToricSpace.generate_barycentric (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus)
    (ht : Real.log ‖ToricFan.Triangle.time z‖ ≠ 0) :
    s.generate (barycentric z) = positionPoint (position (ToricSpace.inclusion s z)) := by
  ext i
  fin_cases i
  · exact (position_inclusion s hz 0).symm
  · exact (position_inclusion s hz 1).symm
  · simpa [ToricFan.Triangle.generate, Matrix.mulVec, dotProduct, positionPoint] using
      barycentric_sum s hz ht

theorem ToricSpace.unit_chart_of_position_mem_cone (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus)
    (ht : Real.log ‖ToricFan.Triangle.time z‖ < 0)
    (hp : positionPoint (position (ToricSpace.inclusion s z)) ∈ s.cone) : ‖z‖ ≤ 1 := by
  rw [← generate_barycentric s hz ht.ne, ToricFan.Triangle.mem_cone,
    ToricFan.Triangle.coordinates_generate] at hp
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  apply (Real.log_nonpos_iff (norm_nonneg _)).mp
  have hj := (le_div_iff_of_neg ht).mp (hp j)
  simpa [barycentric, logNorm] using hj

def ToricSpace.boundedTriangles : Set ToricFan.Triangle :=
  {s | (-3 ≤ s.a ∧ s.a ≤ 3) ∧ (-3 ≤ s.b ∧ s.b ≤ 3)}

theorem ToricSpace.boundedTriangles_finite : boundedTriangles.Finite := by
  have hf :=
    (Set.finite_Icc (-3 : ℤ) 3).prod
      ((Set.finite_Icc (-3 : ℤ) 3).prod (Set.finite_univ (α := Bool)))
  have hi : Function.Injective (fun s : ToricFan.Triangle => (s.a, s.b, s.upper)) := by
    intro s t h
    simpa only [Prod.mk.injEq, ToricFan.Triangle.ext_iff, and_assoc] using h
  apply (hf.preimage hi.injOn).subset
  intro s hs
  exact ⟨hs.1, hs.2, Set.mem_univ _⟩

theorem ToricSpace.exists_bounded_cone (y : Fin 2 → ℝ) (hy : ‖y‖ ≤ 2) :
    ∃ s ∈ boundedTriangles, positionPoint y ∈ s.cone := by
  let a := ⌊y 0⌋
  let b := ⌊y 1⌋
  have ha : (a : ℝ) ≤ y 0 := Int.floor_le _
  have hb : (b : ℝ) ≤ y 1 := Int.floor_le _
  have ha' : y 0 < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hb' : y 1 < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hy0 : -(2 : ℝ) ≤ y 0 ∧ y 0 ≤ 2 :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 0).trans hy)
  have hy1 : -(2 : ℝ) ≤ y 1 ∧ y 1 ≤ 2 :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 1).trans hy)
  have haI : (-3 : ℤ) ≤ a ∧ a ≤ 3 := by
    constructor
    · exact_mod_cast (show (-3 : ℝ) ≤ (a : ℝ) by linarith)
    · exact_mod_cast (show (a : ℝ) ≤ 3 by linarith)
  have hbI : (-3 : ℤ) ≤ b ∧ b ≤ 3 := by
    constructor
    · exact_mod_cast (show (-3 : ℝ) ≤ (b : ℝ) by linarith)
    · exact_mod_cast (show (b : ℝ) ≤ 3 by linarith)
  by_cases hsum : y 0 + y 1 ≤ 1 + (a : ℝ) + b
  · refine ⟨⟨a, b, Bool.false⟩, ⟨haI, hbI⟩, ?_⟩
    rw [ToricFan.Triangle.mem_cone, ToricFan.Triangle.coordinates_lower]
    intro i
    fin_cases i <;> dsimp [positionPoint] <;> linarith
  · refine ⟨⟨a, b, Bool.true⟩, ⟨haI, hbI⟩, ?_⟩
    rw [ToricFan.Triangle.mem_cone, ToricFan.Triangle.coordinates_upper]
    intro i
    fin_cases i <;> dsimp [positionPoint] <;> linarith

theorem ToricSpace.exists_unit_chart_of_bounded_position {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0) (hp : ‖position x‖ ≤ 2) :
    ∃ s ∈ boundedTriangles,
      ∃ z ∈ Metric.closedBall (0 : ToricCharts.CoordinateSpace 3) 1,
        ToricSpace.inclusion s z = x := by
  obtain ⟨s, hs, hp⟩ := exists_bounded_cone (position x) hp
  obtain ⟨z, hz, rfl⟩ := exists_torus_chart s hx
  refine ⟨s, hs, z, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact unit_chart_of_position_mem_cone s hz (by simpa using ht) hp

theorem ToricSpace.exists_bounded_chart_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {x : Space}
    (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ∃ v : Fin 2 → ℤ,
      ∃ s ∈ boundedTriangles,
        ∃ z ∈ Metric.closedBall (0 : ToricCharts.CoordinateSpace 3) 1,
          ToricSpace.inclusion s z = twistedTranslate C v x := by
  obtain ⟨v, hv⟩ := exists_bounded_translate C hx ht hR
  refine ⟨v, ?_⟩
  apply exists_unit_chart_of_bounded_position _ (by simpa using ht) hv
  simpa only [mem_openTorus_iff, time_twistedTranslate] using hx

def CuspUniformization.logarithmicPeriod (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  s • B₀.map (Int.castRingHom ℂ) + C (exponential s)

theorem CuspUniformization.logarithmicPeriod_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    (logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i =
      s * (ToricSpace.cuspVector v i : ℂ) + (C (exponential s) *ᵥ (fun j => (v j : ℂ))) i := by
  fin_cases i <;>
      simp [logarithmicPeriod, B₀, ToricSpace.cuspVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, smul_eq_mul] <;>
    ring

theorem CuspUniformization.imaginary_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ ≠ 0) (v : Fin 2 → ℝ) :
    Real.log ‖exponential s‖ • ToricSpace.displacement C (exponential s) v =
      (-2 * Real.pi) • ((logarithmicPeriod C s).map Complex.im *ᵥ v) := by
  change
    Real.log ‖exponential s‖ •
        (ToricSpace.realCuspVector v +
          (Real.log ‖exponential s‖)⁻¹ • (ToricSpace.driftMatrix C (exponential s) *ᵥ v)) =
      _
  rw [smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul]
  ext i
  fin_cases i <;>
      simp [logarithmicPeriod, B₀, ToricSpace.realCuspVector, ToricSpace.driftMatrix, smul_eq_mul,
        log_norm_exponential] <;>
    ring

theorem CuspUniformization.logarithmicPeriod_nondegenerate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (ht : Real.log ‖exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Function.Bijective ((logarithmicPeriod C s).map Complex.im).mulVecLin := by
  have hinj : Function.Injective ((logarithmicPeriod C s).map Complex.im).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he := imaginary_displacement C s ht.ne v
    change (logarithmicPeriod C s).map Complex.im *ᵥ v = 0 at hv
    rw [hv, smul_zero] at he
    have hd : ToricSpace.displacement C (exponential s) v = 0 :=
      (smul_eq_zero.mp he).resolve_left ht.ne
    exact (ToricSpace.displacement_bijective C ht hR).injective (hd.trans (map_zero _).symm)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

def CuspUniformization.periodData (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    FullPeriodMatrix :=
  ⟨logarithmicPeriod C s, logarithmicPeriod_nondegenerate C s ht hR⟩

theorem CuspUniformization.exponential_logarithmicPeriod (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (v : Fin 2 → ℤ) (i : Fin 2) :
    exponential ((logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i) =
      (ToricSpace.exponentialMultiplier C v (exponential s) i : ℂ) *
        exponential s ^ ToricSpace.cuspVector v i := by
  rw [logarithmicPeriod_apply, exponential_add]
  have he :
    exponential (s * (ToricSpace.cuspVector v i : ℂ)) =
      exponential s ^ ToricSpace.cuspVector v i := by
    unfold exponential
    rw [show
        (2 * Real.pi * Complex.I : ℂ) * (s * (ToricSpace.cuspVector v i : ℂ)) =
          (ToricSpace.cuspVector v i : ℂ) * (2 * Real.pi * Complex.I * s)
        by ring,
      Complex.exp_int_mul]
  rw [he]
  exact mul_comm _ _

theorem CuspUniformization.twistedTranslate_exponentialPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (v : Fin 2 → ℤ) (z : ComplexPlane₂) :
    ToricSpace.twistedTranslate C v (exponentialPoint (exponential s) z) =
      exponentialPoint (exponential s) (z + logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) := by
  have ht := exponential_ne_zero s
  have hx := exponentialPoint_mem ht z
  have hx' :
    ToricSpace.twistedTranslate C v (exponentialPoint (exponential s) z) ∈ ToricSpace.openTorus :=
    by simpa only [ToricSpace.mem_openTorus_iff, ToricSpace.time_twistedTranslate] using hx
  apply torusCoordinates_injective hx' (exponentialPoint_mem ht _)
  have hi (i : Fin 2) :
    ToricSpace.torusCoordinates
        (ToricSpace.twistedTranslate C v (exponentialPoint (exponential s) z)) i.castSucc =
      exponential (z i + (logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i) := by
    rw [ToricSpace.torusCoordinates_twistedTranslate_apply C v hx, time_exponentialPoint ht]
    have hz :
      ToricSpace.torusCoordinates (exponentialPoint (exponential s) z) i.castSucc =
        exponential (z i) := by
      rw [torusCoordinates_exponentialPoint ht]
      fin_cases i <;> rfl
    rw [hz, exponential_add, exponential_logarithmicPeriod]
    ring
  rw [torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i
  · exact hi 0
  · exact hi 1
  · simp [exponentialCoordinates, ToricSpace.time_twistedTranslate, time_exponentialPoint ht]

def CuspQuotient.compactRepresentatives (η : ℝ) : Set ToricSpace.Space :=
  ⋃ s ∈ ToricSpace.boundedTriangles,
    ToricSpace.inclusion s ''
      (Metric.closedBall (0 : ToricCharts.CoordinateSpace 3) 1 ∩
        ToricFan.Triangle.time ⁻¹' Metric.closedBall 0 η)

theorem CuspQuotient.compactRepresentatives_compact (η : ℝ) :
    IsCompact (compactRepresentatives η) := by
  apply ToricSpace.boundedTriangles_finite.isCompact_biUnion
  intro s _
  exact
    ((ProperSpace.isCompact_closedBall _ _).inter_right
          (Metric.isClosed_closedBall.preimage
            ToricFan.Triangle.time_holomorphic.continuous)).image
      (ToricSpace.inclusion_openEmbedding s).continuous

theorem CuspQuotient.compactRepresentatives_time {η : ℝ} {x : ToricSpace.Space}
    (hx : x ∈ compactRepresentatives η) : ‖ToricSpace.time x‖ ≤ η := by
  obtain ⟨s, _, z, hz, rfl⟩ := Set.mem_iUnion₂.mp hx
  simpa only [ToricSpace.time_inclusion, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right] using hz.2

def CuspQuotient.tubeRepresentatives (ε η : ℝ) : Set (ToricSpace.Tube (disc ε)) :=
  Subtype.val ⁻¹' compactRepresentatives η

theorem CuspQuotient.tubeRepresentatives_compact {ε η : ℝ} (hηε : η < ε) :
    IsCompact (tubeRepresentatives ε η) := by
  apply
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (compactRepresentatives_compact η)
  intro x hx
  have hxt : x ∈ ToricSpace.tubeOpen (disc ε) := by
    change ToricSpace.time x ∈ Metric.ball 0 ε
    simpa only [Metric.mem_ball, dist_zero_right] using
      (compactRepresentatives_time hx).trans_lt hηε
  exact ⟨⟨x, hxt⟩, rfl⟩

def CuspQuotient.quotientRepresentatives (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (η : ℝ) :
    Set (QuotientSpace C ε) :=
  quotientMap C ε '' tubeRepresentatives ε η

theorem CuspQuotient.quotientRepresentatives_compact (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    {η : ℝ} (hηε : η < ε) : IsCompact (quotientRepresentatives C ε η) :=
  (tubeRepresentatives_compact hηε).image (quotientMap_continuous C ε)

theorem CuspQuotient.torus_mem_quotientRepresentatives (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift C ε) {η : ℝ} {x : ToricSpace.Tube (disc ε)}
    (hx : (x : ToricSpace.Space) ∈ ToricSpace.openTorus)
    (hxη : ‖ToricSpace.time (x : ToricSpace.Space)‖ ≤ η) :
    quotientMap C ε x ∈ quotientRepresentatives C ε η := by
  have hxt : ‖ToricSpace.time (x : ToricSpace.Space)‖ < ε := by
    have hxε : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hxε
  have ht : 0 < ‖ToricSpace.time (x : ToricSpace.Space)‖ :=
    norm_pos_iff.mpr ((ToricSpace.mem_openTorus_iff _).mp hx)
  obtain ⟨v, s, hs, z, hz, he⟩ :=
    ToricSpace.exists_bounded_chart_translate C hx (Real.log_neg ht (hxt.trans hε1)) (hR _ ht hxt)
  refine ⟨ToricSpace.tubeTranslate C (disc ε) v x, ?_, quotientMap_translate C ε v x⟩
  change ToricSpace.twistedTranslate C v (x : ToricSpace.Space) ∈ compactRepresentatives η
  refine Set.mem_iUnion₂.mpr ⟨s, hs, z, ⟨hz, ?_⟩, he⟩
  change ToricFan.Triangle.time z ∈ Metric.closedBall 0 η
  rw [← ToricSpace.time_inclusion s z, he, ToricSpace.time_twistedTranslate,
    Metric.mem_closedBall, dist_zero_right]
  exact hxη

theorem CuspQuotient.tube_torus_dense (ε : ℝ) :
    Dense
      ((Subtype.val : ToricSpace.Tube (disc ε) → ToricSpace.Space) ⁻¹' ToricSpace.openTorus) :=
  ToricSpace.openTorus_dense.preimage
    (ToricSpace.tubeOpen (disc ε)).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

theorem CuspQuotient.mem_quotientRepresentatives (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {η : ℝ} (hη : 0 < η) (hηε : η < ε)
    {x : ToricSpace.Tube (disc ε)} (hxη : ‖ToricSpace.time (x : ToricSpace.Space)‖ ≤ η) :
    quotientMap C ε x ∈ quotientRepresentatives C ε η := by
  let := quotient_t2Space C ε hε hε1 hC hR
  by_cases hx : (x : ToricSpace.Space) ∈ ToricSpace.openTorus
  · exact torus_mem_quotientRepresentatives C ε hε1 hR hx hxη
  have hzero : ToricSpace.time (x : ToricSpace.Space) = 0 := by
    simpa only [ToricSpace.mem_openTorus_iff, Classical.not_not] using hx
  let A := quotientMap C ε ⁻¹' quotientRepresentatives C ε η
  have hA : IsClosed A :=
    (quotientRepresentatives_compact C ε hηε).isClosed.preimage (quotientMap_continuous C ε)
  let U : Set (ToricSpace.Tube (disc ε)) := {p | ‖ToricSpace.time (p : ToricSpace.Space)‖ < η}
  have hU : IsOpen U :=
    isOpen_lt (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val).norm
      continuous_const
  by_contra hn
  have hxU : x ∈ U := by simpa [U, hzero] using hη
  obtain ⟨p, hp, hpU, hpA⟩ :=
    (tube_torus_dense ε).exists_mem_open (hU.inter hA.isOpen_compl) ⟨x, hxU, hn⟩
  exact hpA (torus_mem_quotientRepresentatives C ε hε1 hR hp hpU.le)

theorem CuspQuotient.closedDisc_preimage_compact (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {η : ℝ} (hη : 0 < η) (hηε : η < ε) :
    IsCompact (projection C ε ⁻¹' Metric.closedBall 0 η) := by
  have he : projection C ε ⁻¹' Metric.closedBall 0 η = quotientRepresentatives C ε η := by
    ext q
    constructor
    · induction q using Quotient.inductionOn with
      | h x =>
        intro hx
        exact
          mem_quotientRepresentatives C ε hε hε1 hC hR hη hηε
            (by
              simpa only [Set.mem_preimage, projection, Quotient.lift_mk, Metric.mem_closedBall,
                dist_zero_right] using hx)
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, projection_quotientMap, Metric.mem_closedBall,
        dist_zero_right] using compactRepresentatives_time hx
  rw [he]
  exact quotientRepresentatives_compact C ε hηε

theorem CuspQuotient.baseMap_proper (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (baseMap C ε) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨baseMap_continuous C ε, ?_⟩
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨t, ht, hmax⟩ := hK.exists_isMaxOn hne continuous_subtype_val.norm.continuousOn
  have htε : ‖(t : ℂ)‖ < ε := by
    have htball : (t : ℂ) ∈ Metric.ball 0 ε := t.2
    simpa only [Metric.mem_ball, dist_zero_right] using htball
  obtain ⟨η, htη, hηε⟩ := exists_between htε
  have hη : 0 < η := (norm_nonneg _).trans_lt htη
  apply
    (closedDisc_preimage_compact C ε hε hε1 hC hR hη hηε).of_isClosed_subset
      (hK.isClosed.preimage (baseMap_continuous C ε))
  intro q hq
  have hb : ‖projection C ε q‖ ≤ ‖(t : ℂ)‖ := hmax hq
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hb.trans htη.le

def CuspQuotient.affineTube (ε : ℝ) : Set (ToricCharts.CoordinateSpace 3) :=
  {z | ‖ToricFan.Triangle.time z‖ < ε}

theorem CuspQuotient.affineTube_starConvex (ε : ℝ) : StarConvex ℝ 0 (affineTube ε) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  change ‖ToricFan.Triangle.time (b • z)‖ < ε
  have he : ‖ToricFan.Triangle.time (b • z)‖ = b ^ 3 * ‖ToricFan.Triangle.time z‖ := by
    simp only [ToricFan.Triangle.time, Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hb]
    ring
  rw [he]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hb hb1)).trans_lt hz

theorem CuspQuotient.affineTube_connected {ε : ℝ} (hε : 0 < ε) : IsConnected (affineTube ε) :=
  ((affineTube_starConvex ε).isPathConnected
      (by simpa [affineTube, ToricFan.Triangle.time] using hε)).isConnected

theorem CuspQuotient.tube_eq_union (ε : ℝ) :
    (ToricSpace.tubeOpen (disc ε) : Set ToricSpace.Space) =
      ⋃ s : ToricFan.Triangle, ToricSpace.inclusion s '' affineTube ε := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
    refine Set.mem_iUnion.mpr ⟨s, z, ?_, rfl⟩
    have he : ToricSpace.time (ToricSpace.inclusion s z) ∈ Metric.ball 0 ε := hx
    simpa only [affineTube, Set.mem_ofPred_eq, ToricSpace.time_inclusion, Metric.mem_ball,
      dist_zero_right] using he
  · intro hx
    obtain ⟨s, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    change ToricSpace.time (ToricSpace.inclusion s z) ∈ Metric.ball 0 ε
    simpa only [affineTube, Set.mem_ofPred_eq, ToricSpace.time_inclusion, Metric.mem_ball,
      dist_zero_right] using hz

theorem CuspQuotient.tube_charts_common_point {ε : ℝ} (hε : 0 < ε) :
    (⋂ s : ToricFan.Triangle, ToricSpace.inclusion s '' affineTube ε).Nonempty := by
  let x := ToricSpace.inclusion ToricSpace.referenceTriangle ![((ε / 2 : ℝ) : ℂ), 1, 1]
  have hxT : x ∈ ToricSpace.openTorus := by
    apply ToricSpace.inclusion_torus_subset ToricSpace.referenceTriangle
    refine ⟨_, ?_, rfl⟩
    intro i
    fin_cases i
    · change ((ε / 2 : ℝ) : ℂ) ≠ 0
      exact_mod_cast (half_pos hε).ne'
    · exact one_ne_zero
    · exact one_ne_zero
  have hxt : ‖ToricSpace.time x‖ < ε := by
    simpa [x, ToricFan.Triangle.time, abs_of_pos hε] using half_lt_self hε
  refine ⟨x, Set.mem_iInter.mpr fun s => ?_⟩
  obtain ⟨z, _, he⟩ := ToricSpace.exists_torus_chart s hxT
  refine ⟨z, ?_, he⟩
  change ‖ToricFan.Triangle.time z‖ < ε
  rw [← ToricSpace.time_inclusion s z, he]
  exact hxt

theorem CuspQuotient.tube_connected {ε : ℝ} (hε : 0 < ε) :
    ConnectedSpace (ToricSpace.Tube (disc ε)) := by
  apply isConnected_iff_connectedSpace.mp
  have hpre : IsPreconnected (⋃ s : ToricFan.Triangle, ToricSpace.inclusion s '' affineTube ε) :=
    isPreconnected_iUnion (tube_charts_common_point hε)
      (fun s =>
        (affineTube_connected hε).isPreconnected.image _
          (ToricSpace.inclusion_openEmbedding s).continuous.continuousOn)
  rw [← tube_eq_union] at hpre
  refine ⟨⟨ToricSpace.inclusion ToricSpace.referenceTriangle 0, ?_⟩, hpre⟩
  change ToricSpace.time (ToricSpace.inclusion ToricSpace.referenceTriangle 0) ∈ Metric.ball 0 ε
  simpa [ToricFan.Triangle.time] using hε

theorem CuspQuotient.quotient_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    ConnectedSpace (QuotientSpace C ε) := by
  let := tube_connected hε
  infer_instance

theorem CuspQuotient.quotient_secondCountable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : SecondCountableTopology (QuotientSpace C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  have hq := quotientMap_covering C ε hε hε1 hC hR
  exact hq.toIsQuotientMap.secondCountableTopology hq.isCoveringMap.isOpenMap

def CuspQuotient.centralAffine : Set (ToricCharts.CoordinateSpace 3) :=
  {z | ToricFan.Triangle.time z = 0}

def CuspQuotient.centralOrigin : centralAffine :=
  ⟨0, by simp [centralAffine, ToricFan.Triangle.time]⟩

theorem CuspQuotient.centralAffine_starConvex : StarConvex ℝ 0 centralAffine := by
  intro z hz a b _ _ _
  simp only [smul_zero, zero_add]
  change ToricFan.Triangle.time (b • z) = 0
  obtain h | h | h := (ToricFan.Triangle.central_fibre z).mp hz
  all_goals simp [ToricFan.Triangle.time, Pi.smul_apply, h]

instance CuspQuotient.centralAffine_connected : ConnectedSpace centralAffine :=
  isConnected_iff_connectedSpace.mp
    ((centralAffine_starConvex.isPathConnected centralOrigin.2).isConnected)

def CuspQuotient.centralLift (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) (z : centralAffine) :
    ToricSpace.Tube (disc ε) :=
  ⟨ToricSpace.inclusion s z,
    by
    change ToricSpace.time (ToricSpace.inclusion s z) ∈ Metric.ball 0 ε
    rw [ToricSpace.time_inclusion, z.2]
    simpa using hε⟩

theorem CuspQuotient.centralLift_continuous (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) :
    Continuous (centralLift ε hε s) :=
  ((ToricSpace.inclusion_openEmbedding s).continuous.comp continuous_subtype_val).subtype_mk _

def CuspQuotient.centralChartMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (s : ToricFan.Triangle) : centralAffine → QuotientSpace C ε :=
  quotientMap C ε ∘ centralLift ε hε s

theorem CuspQuotient.centralChartMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) : Continuous (centralChartMap C ε hε s) :=
  (quotientMap_continuous C ε).comp (centralLift_continuous ε hε s)

theorem CuspQuotient.centralChartMap_range_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) : IsConnected (Set.range (centralChartMap C ε hε s)) :=
  isConnected_range (centralChartMap_continuous C ε hε s)

@[simp]
theorem CuspQuotient.projection_centralChartMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) (z : centralAffine) :
    projection C ε (centralChartMap C ε hε s z) = 0 := by
  change ToricSpace.time (ToricSpace.inclusion s z) = 0
  rw [ToricSpace.time_inclusion, z.2]

theorem CuspQuotient.centralChartMap_origin_shift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    centralChartMap C ε hε (s.shift (ToricSpace.cuspVector v)) centralOrigin =
      centralChartMap C ε hε s centralOrigin := by
  have he :
    ToricSpace.tubeTranslate C (disc ε) v (centralLift ε hε s centralOrigin) =
      centralLift ε hε (s.shift (ToricSpace.cuspVector v)) centralOrigin := by
    apply Subtype.ext
    simp [ToricSpace.tubeTranslate, centralLift, centralOrigin, ToricSpace.twistedTranslate,
      ToricSpace.variableMultiplier, ToricSpace.translate_inclusion,
      ToricSpace.torusAction_inclusion, ToricSpace.scale]
  exact
    (congrArg (quotientMap C ε) he).symm.trans
      (quotientMap_translate C ε v (centralLift ε hε s centralOrigin))

theorem CuspQuotient.centralChartMap_origin_reference (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) :
    centralChartMap C ε hε s centralOrigin =
      centralChartMap C ε hε ⟨0, 0, s.upper⟩ centralOrigin := by
  let v : Fin 2 → ℤ := ![-s.b, s.a]
  have he : (⟨0, 0, s.upper⟩ : ToricFan.Triangle).shift (ToricSpace.cuspVector v) = s := by
    ext <;> simp [ToricFan.Triangle.shift, ToricSpace.cuspVector, v]
  simpa only [he] using centralChartMap_origin_shift C ε hε ⟨0, 0, s.upper⟩ v

theorem CuspQuotient.reference_central_overlap :
    ToricSpace.inclusion (⟨0, 0, Bool.false⟩ : ToricFan.Triangle) ![1, 0, 0] =
      ToricSpace.inclusion (⟨0, 0, Bool.true⟩ : ToricFan.Triangle) ![0, 0, 1] := by
  have hA :
    ToricFan.Triangle.transition ⟨0, 0, Bool.false⟩ ⟨0, 0, Bool.true⟩ =
      !![1, 1, 0; 1, 0, 1; -1, 0, 0] := by decide
  apply (ToricSpace.inclusion_eq_iff _ _ _ _).mpr
  constructor
  · rw [ToricFan.Triangle.chartChange_source]
    intro i j hij
    rw [hA] at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    norm_num
  · change ToricCharts.monomial (ToricFan.Triangle.transition _ _) _ = _
    rw [hA]
    ext i
    fin_cases i <;> norm_num [ToricCharts.monomial, Fin.prod_univ_succ]

theorem CuspQuotient.reference_centralChartMap_overlap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (Set.range (centralChartMap C ε hε ⟨0, 0, Bool.false⟩) ∩
        Set.range (centralChartMap C ε hε ⟨0, 0, Bool.true⟩)).Nonempty := by
  let z : centralAffine := ⟨![1, 0, 0], by simp [centralAffine, ToricFan.Triangle.time]⟩
  let w : centralAffine := ⟨![0, 0, 1], by simp [centralAffine, ToricFan.Triangle.time]⟩
  refine ⟨centralChartMap C ε hε ⟨0, 0, Bool.false⟩ z, Set.mem_range_self z, w, ?_⟩
  apply congrArg (quotientMap C ε)
  exact Subtype.ext reference_central_overlap.symm

theorem CuspQuotient.central_fibre_eq_union (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    projection C ε ⁻¹' {0} = ⋃ s : ToricFan.Triangle, Set.range (centralChartMap C ε hε s) := by
  ext q
  constructor
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have hx0 : ToricSpace.time (x : ToricSpace.Space) = 0 := hx
      obtain ⟨s, z, he⟩ := ToricSpace.inclusion_jointly_surjective (x : ToricSpace.Space)
      have hz : z ∈ centralAffine := by
        change ToricFan.Triangle.time z = 0
        rw [← ToricSpace.time_inclusion s z, he, hx0]
      refine Set.mem_iUnion.mpr ⟨s, ⟨z, hz⟩, ?_⟩
      apply congrArg (quotientMap C ε)
      exact Subtype.ext he
  · intro hq
    obtain ⟨s, z, rfl⟩ := Set.mem_iUnion.mp hq
    exact projection_centralChartMap C ε hε s z

theorem CuspQuotient.central_fibre_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : IsConnected (projection C ε ⁻¹' {0}) := by
  let U := fun s : ToricFan.Triangle => Set.range (centralChartMap C ε hε s)
  let R := U ⟨0, 0, Bool.false⟩ ∪ U ⟨0, 0, Bool.true⟩
  have hU (s : ToricFan.Triangle) : IsPreconnected (U s) :=
    (centralChartMap_range_connected C ε hε s).isPreconnected
  have hR : IsPreconnected R :=
    IsPreconnected.union' (reference_centralChartMap_overlap C ε hε) (hU _) (hU _)
  have horigin (s : ToricFan.Triangle) : centralChartMap C ε hε s centralOrigin ∈ R := by
    rw [centralChartMap_origin_reference]
    cases hs : s.upper
    · exact Or.inl (Set.mem_range_self _)
    · exact Or.inr (Set.mem_range_self _)
  have hcommon : (⋂ s : ToricFan.Triangle, R ∪ U s).Nonempty := by
    refine
      ⟨centralChartMap C ε hε ⟨0, 0, Bool.false⟩ centralOrigin, Set.mem_iInter.mpr fun s => ?_⟩
    exact Or.inl (Or.inl (Set.mem_range_self _))
  have hpre : IsPreconnected (⋃ s : ToricFan.Triangle, R ∪ U s) :=
    isPreconnected_iUnion hcommon
      (fun s =>
        IsPreconnected.union'
          ⟨centralChartMap C ε hε s centralOrigin, horigin s, Set.mem_range_self _⟩ hR (hU s))
  have he : (⋃ s : ToricFan.Triangle, R ∪ U s) = ⋃ s : ToricFan.Triangle, U s := by
    apply subset_antisymm
    · intro q hq
      obtain ⟨s, hq⟩ := Set.mem_iUnion.mp hq
      rcases hq with (hq | hq) | hq
      · exact Set.mem_iUnion.mpr ⟨⟨0, 0, Bool.false⟩, hq⟩
      · exact Set.mem_iUnion.mpr ⟨⟨0, 0, Bool.true⟩, hq⟩
      · exact Set.mem_iUnion.mpr ⟨s, hq⟩
    · intro q hq
      obtain ⟨s, hq⟩ := Set.mem_iUnion.mp hq
      exact Set.mem_iUnion.mpr ⟨s, Or.inr hq⟩
  rw [he] at hpre
  rw [central_fibre_eq_union C ε hε]
  exact
    ⟨⟨centralChartMap C ε hε ⟨0, 0, Bool.false⟩ centralOrigin,
        Set.mem_iUnion.mpr ⟨⟨0, 0, Bool.false⟩, Set.mem_range_self _⟩⟩,
      hpre⟩

def CuspUniformization.exponentialLift (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (z : ComplexPlane₂) : ToricSpace.Tube (CuspQuotient.disc ε) :=
  ⟨exponentialPoint (exponential s) z,
    by
    change ToricSpace.time (exponentialPoint (exponential s) z) ∈ Metric.ball 0 ε
    simpa only [time_exponentialPoint (exponential_ne_zero s), Metric.mem_ball,
      dist_zero_right] using hs⟩

theorem CuspUniformization.exponentialLift_continuous (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) :
    Continuous (exponentialLift ε s hs) :=
  (exponentialPoint_holomorphic (exponential_ne_zero s)).continuous.subtype_mk _

theorem CuspUniformization.exponentialLift_holomorphic (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (exponentialLift ε s hs) := by
  intro z
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun w => (exponentialLift ε s hs w : ToricSpace.Space)) z ↔
      ContMDiffAt (modelWithCornersSelf ℂ ComplexPlane₂)
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (exponentialLift ε s hs) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (exponentialPoint_holomorphic (exponential_ne_zero s) z)

def CuspUniformization.fibreCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) : ComplexPlane₂ → CuspQuotient.QuotientSpace C ε :=
  CuspQuotient.quotientMap C ε ∘ exponentialLift ε s hs

theorem CuspUniformization.fibreCover_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) : Continuous (fibreCover C ε s hs) :=
  (CuspQuotient.quotientMap_continuous C ε).comp (exponentialLift_continuous ε s hs)

@[simp]
theorem CuspUniformization.projection_fibreCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) (z : ComplexPlane₂) :
    CuspQuotient.projection C ε (fibreCover C ε s hs z) = exponential s :=
  time_exponentialPoint (exponential_ne_zero s) z

theorem CuspUniformization.fibreCover_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (z w : ComplexPlane₂) :
    fibreCover C ε s hs z = fibreCover C ε s hs w ↔ z - w ∈ (periodData C s hlog hRp).lattice := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  constructor
  · intro he
    have horb := Quotient.exact he
    change
      exponentialLift ε s hs z ∈
        MulAction.orbit CuspQuotient.LatticeGroup (exponentialLift ε s hs w) at horb
    obtain ⟨g, hg⟩ := horb
    have hp :
      exponentialPoint (exponential s) z =
        exponentialPoint (exponential s)
          (w + logarithmicPeriod C s *ᵥ (fun j => (g.toAdd j : ℂ))) :=
      (congrArg Subtype.val hg).symm.trans (twistedTranslate_exponentialPoint C s g.toAdd w)
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mp hp
    apply (FullPeriodMatrix.mem_lattice_iff _ _).mpr
    refine ⟨m, g.toAdd, ?_⟩
    change z - w = (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (g.toAdd j : ℂ))
    rw [hm]
    abel
  · intro he
    obtain ⟨m, n, hmn⟩ := (FullPeriodMatrix.mem_lattice_iff _ _).mp he
    have hp :
      exponentialPoint (exponential s) z =
        exponentialPoint (exponential s) (w + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) := by
      apply (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mpr
      refine ⟨m, ?_⟩
      have he := sub_eq_iff_eq_add.mp hmn
      change z = (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ)) + w at he
      rw [he]
      abel
    have hl :
      exponentialLift ε s hs z =
        ToricSpace.tubeTranslate C (CuspQuotient.disc ε) n (exponentialLift ε s hs w) :=
      Subtype.ext (hp.trans (twistedTranslate_exponentialPoint C s n w).symm)
    change
      CuspQuotient.quotientMap C ε (exponentialLift ε s hs z) =
        CuspQuotient.quotientMap C ε (exponentialLift ε s hs w)
    rw [hl, CuspQuotient.quotientMap_translate]

def CuspUniformization.fibreMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    (periodData C s hlog hRp).Torus → CuspQuotient.QuotientSpace C ε :=
  Quotient.lift (fibreCover C ε s hs)
    (by
      intro z w hzw
      apply (fibreCover_eq_iff C ε s hs hlog hRp z w).mpr
      exact (Submodule.Quotient.eq _).mp (Quotient.sound hzw))

theorem CuspUniformization.fibreMap_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Function.Injective (fibreMap C ε s hs hlog hRp) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h z =>
    induction y using Quotient.inductionOn with
    | h w =>
      intro he
      exact (Submodule.Quotient.eq _).mpr ((fibreCover_eq_iff C ε s hs hlog hRp z w).mp he)

theorem CuspUniformization.fibreMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Continuous (fibreMap C ε s hs hlog hRp) :=
  (fibreCover_continuous C ε s hs).quotient_lift _

@[simp]
theorem CuspUniformization.projection_fibreMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (x : (periodData C s hlog hRp).Torus) :
    CuspQuotient.projection C ε (fibreMap C ε s hs hlog hRp x) = exponential s := by
  induction x using Quotient.inductionOn with
  | h z => exact projection_fibreCover C ε s hs z

theorem CuspUniformization.fibreMap_range (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Set.range (fibreMap C ε s hs hlog hRp) = CuspQuotient.projection C ε ⁻¹' {exponential s} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact projection_fibreMap C ε s hs hlog hRp x
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have ht : ToricSpace.time (x : ToricSpace.Space) = exponential s := hx
      obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre (exponential_ne_zero s) ht
      refine ⟨(periodData C s hlog hRp).lattice.mkQ z, ?_⟩
      apply congrArg (CuspQuotient.quotientMap C ε)
      exact Subtype.ext hz

theorem CuspUniformization.fibreMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (fibreMap C ε s hs hlog hRp) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply DiscreteQuotient.contMDiff_of_comp_mkQ
  exact
    (CuspQuotient.quotientMap_holomorphic C ε hε hε1 hC hR).comp
      (exponentialLift_holomorphic ε s hs)

def CuspUniformization.fibreMapToFibre (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (x : (periodData C s hlog hRp).Torus) : CuspQuotient.projection C ε ⁻¹' {exponential s} :=
  ⟨fibreMap C ε s hs hlog hRp x, projection_fibreMap C ε s hs hlog hRp x⟩

theorem CuspUniformization.fibreMapToFibre_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    Function.Bijective (fibreMapToFibre C ε s hs hlog hRp) := by
  constructor
  · intro x y he
    exact fibreMap_injective C ε s hs hlog hRp (congrArg Subtype.val he)
  · intro q
    have hq : (q : CuspQuotient.QuotientSpace C ε) ∈ Set.range (fibreMap C ε s hs hlog hRp) := by
      rw [fibreMap_range]
      exact q.2
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, Subtype.ext hx⟩

def CuspUniformization.fibreHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (periodData C s hlog hRp).Torus ≃ₜ CuspQuotient.projection C ε ⁻¹' {exponential s} := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  let e :=
    Equiv.ofBijective (fibreMapToFibre C ε s hs hlog hRp)
      (fibreMapToFibre_bijective C ε s hs hlog hRp)
  exact
    Continuous.homeoOfEquivCompactToT2 (f := e)
      ((fibreMap_continuous C ε s hs hlog hRp).subtype_mk _)

theorem CuspUniformization.fibreMap_isEmbedding (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Topology.IsEmbedding (fibreMap C ε s hs hlog hRp) := by
  exact
    Topology.IsEmbedding.subtypeVal.comp
      (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR).isEmbedding

theorem CuspUniformization.nonzero_fibre_torus (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∃ p : FullPeriodMatrix,
      ∃ f : p.Torus → CuspQuotient.QuotientSpace C ε,
        ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
            (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω f ∧
          Topology.IsEmbedding f ∧ Set.range f = CuspQuotient.projection C ε ⁻¹' { t } := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let s := logarithm t
  have hst : exponential s = t := exponential_logarithm ht0
  have hs : ‖exponential s‖ < ε := by simpa only [hst] using ht
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans hε1)
  have hRp := hR _ hpos hs
  refine
    ⟨periodData C s hlog hRp, fibreMap C ε s hs hlog hRp,
      fibreMap_holomorphic C ε s hs hlog hRp hε hε1 hC hR,
      fibreMap_isEmbedding C ε s hs hlog hRp hε hε1 hC hR, ?_⟩
  simpa only [hst] using fibreMap_range C ε s hs hlog hRp

theorem CuspUniformization.nonzero_fibre_pathConnected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    IsPathConnected (CuspQuotient.projection C ε ⁻¹' { t }) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  obtain ⟨p, f, hf, _, he⟩ := nonzero_fibre_torus C ε hε hε1 hC hR ht0 ht
  rw [← he]
  exact isPathConnected_range hf.continuous

theorem CuspUniformization.fibre_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (t : CuspQuotient.disc ε) :
    IsConnected (CuspQuotient.projection C ε ⁻¹' {(t : ℂ)}) := by
  by_cases ht0 : (t : ℂ) = 0
  · rw [ht0]
    exact CuspQuotient.central_fibre_connected C ε hε
  · have ht : ‖(t : ℂ)‖ < ε := by
      have htball : (t : ℂ) ∈ Metric.ball 0 ε := t.2
      simpa only [Metric.mem_ball, dist_zero_right] using htball
    exact (nonzero_fibre_pathConnected C ε hε hε1 hC hR ht0 ht).isConnected

def CuspUniformization.exponentialPair (z : ComplexPlane₂) : ComplexPlane₂ := fun i =>
  exponential (z i)

theorem CuspUniformization.exponential_hasDerivAt (z : ℂ) :
    HasDerivAt exponential (exponential z * (2 * Real.pi * Complex.I)) z := by
  change
    HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * w))
      (Complex.exp (2 * Real.pi * Complex.I * z) * (2 * Real.pi * Complex.I)) z
  convert! ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).cexp using 1
  simp

def CuspUniformization.exponentialPairDerivative (z : ComplexPlane₂) :
    ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  ContinuousLinearEquiv.piCongrRight fun i =>
    ContinuousLinearEquiv.unitsEquivAut ℂ
      (Units.mk0 (exponential (z i) * (2 * Real.pi * Complex.I))
        (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))

theorem CuspUniformization.exponentialPair_hasFDerivAt (z : ComplexPlane₂) :
    HasFDerivAt exponentialPair (exponentialPairDerivative z : ComplexPlane₂ →L[ℂ] ComplexPlane₂)
      z := by
  apply hasFDerivAt_pi''
  intro i
  convert!
    ((exponential_hasDerivAt (z i)).hasFDerivAt_equiv
          (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero)).comp
      z (hasFDerivAt_apply (𝕜 := ℂ) i z) using
    1

def SpecialPeriods.cuspCorrection (μ b h : ℂ → ℂ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![6 * μ t, h t; b t - h t, μ t]

theorem SpecialPeriods.cuspCorrection_holomorphicOn {μ b h : ℂ → ℂ} {U : Set ℂ}
    (hμ : ContDiffOn ℂ ω μ U) (hb : ContDiffOn ℂ ω b U) (hh : ContDiffOn ℂ ω h U) (i j : Fin 2) :
    ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) U := by
  fin_cases i <;> fin_cases j
  · exact contDiffOn_const.mul hμ
  · exact hh
  · exact hb.sub hh
  · exact hμ

theorem SpecialPeriods.exists_cuspCorrection_admissible_radius {μ b h : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hμ : ContDiffOn ℂ ω μ (Metric.ball 0 r))
    (hb : ContDiffOn ℂ ω b (Metric.ball 0 r)) (hh : ContDiffOn ℂ ω h (Metric.ball 0 r)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < r ∧
          ε < 1 ∧
            ToricSpace.SmallDrift (cuspCorrection μ b h) ε ∧
              ∀ i j, ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 ε) :=
  CuspQuotient.exists_admissible_radius (cuspCorrection μ b h) hr
    (cuspCorrection_holomorphicOn hμ hb hh)

theorem SpecialPeriods.exists_cuspCorrection_admissible_radius_of_analyticAt {μ b h : ℂ → ℂ}
    (hμ : AnalyticAt ℂ μ 0) (hb : AnalyticAt ℂ b 0) (hh : AnalyticAt ℂ h 0) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < 1 ∧
          ToricSpace.SmallDrift (cuspCorrection μ b h) ε ∧
            ∀ i j, ContDiffOn ℂ ω (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 ε) := by
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp
      (hμ.eventually_analyticAt.and (hb.eventually_analyticAt.and hh.eventually_analyticAt))
  have hμr : ContDiffOn ℂ ω μ (Metric.ball 0 r) := fun t ht =>
    (hball ht).1.contDiffAt.contDiffWithinAt
  have hbr : ContDiffOn ℂ ω b (Metric.ball 0 r) := fun t ht =>
    (hball ht).2.1.contDiffAt.contDiffWithinAt
  have hhr : ContDiffOn ℂ ω h (Metric.ball 0 r) := fun t ht =>
    (hball ht).2.2.contDiffAt.contDiffWithinAt
  obtain ⟨ε, hε, _, hε1, hR, hC⟩ := exists_cuspCorrection_admissible_radius hr hμr hbr hhr
  exact ⟨ε, hε, hε1, hR, hC⟩

def SpecialPeriods.cuspPeriodPoint (μ b h : ℂ → ℂ) (s : ℂ) : PeriodPoint :=
  ⟨s + h (CuspUniformization.exponential s), μ (CuspUniformization.exponential s),
    b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)⟩

theorem SpecialPeriods.cuspPeriodPoint_leftBlock (μ b h : ℂ → ℂ) (s : ℂ) :
    (cuspPeriodPoint μ b h s).leftBlock =
      CuspUniformization.logarithmicPeriod (cuspCorrection μ b h) s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspPeriodPoint, PeriodPoint.leftBlock, CuspUniformization.logarithmicPeriod,
      cuspCorrection, B₀, smul_eq_mul]
  ring

theorem SpecialPeriods.correction_im_bound_of_smallDrift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (i j : Fin 2) : |(C (CuspUniformization.exponential s) i j).im| ≤ s.im / 4 := by
  have hentry :
    ‖ToricSpace.driftMatrix C (CuspUniformization.exponential s) i j‖ ≤
      -Real.log ‖CuspUniformization.exponential s‖ / 4 :=
    ((norm_le_pi_norm (ToricSpace.driftMatrix C (CuspUniformization.exponential s) i) j).trans
          (norm_le_pi_norm
            (fun k : Fin 2 => fun l : Fin 2 =>
              ToricSpace.driftMatrix C (CuspUniformization.exponential s) k l)
            i)).trans
      hR
  have hscaled :
    (2 * Real.pi) * |(C (CuspUniformization.exponential s) i j).im| ≤
      (2 * Real.pi) * (s.im / 4) := by
    simpa [ToricSpace.driftMatrix, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
      CuspUniformization.log_norm_exponential, neg_mul, mul_div_assoc] using hentry
  exact le_of_mul_le_mul_left hscaled (by positivity : 0 < 2 * Real.pi)

theorem SpecialPeriods.cuspPeriodPoint_admissible (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (cuspCorrection μ b h) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4) :
    (cuspPeriodPoint μ b h s).Admissible := by
  have hs : 0 < s.im := by
    rw [CuspUniformization.log_norm_exponential] at hlog
    have hp := Real.pi_pos
    nlinarith
  have hh := (abs_le.mp (correction_im_bound_of_smallDrift (cuspCorrection μ b h) s hR 0 1)).1
  have hbh := (abs_le.mp (correction_im_bound_of_smallDrift (cuspCorrection μ b h) s hR 1 0)).2
  change -(s.im / 4) ≤ (h (CuspUniformization.exponential s)).im at hh
  change
    (b (CuspUniformization.exponential s) - h (CuspUniformization.exponential s)).im ≤
      s.im / 4 at hbh
  have hτ : 0 < (s + h (CuspUniformization.exponential s)).im := by
    rw [Complex.add_im]
    linarith
  have hβ :
    (b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)).im < 0 := by
    rw [Complex.sub_im] at hbh
    rw [Complex.sub_im, Complex.sub_im]
    linarith
  refine ⟨hτ, ?_⟩
  change
    (b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)).im -
        6 * (μ (CuspUniformization.exponential s)).im ^ 2 /
          (s + h (CuspUniformization.exponential s)).im <
      0
  have hn :
    0 ≤
      6 * (μ (CuspUniformization.exponential s)).im ^ 2 /
        (s + h (CuspUniformization.exponential s)).im :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hτ.le
  linarith

def SpecialPeriods.cuspPeriodDomain (μ b h : ℂ → ℂ) (s : ℂ)
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (cuspCorrection μ b h) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4) :
    PeriodDomain :=
  ⟨cuspPeriodPoint μ b h s, cuspPeriodPoint_admissible μ b h s hlog hR⟩

theorem SpecialPeriods.leftBlock_eq_logarithmicPeriod_of_cusp_expansion (μ b h : ℂ → ℂ)
    (p : PeriodPoint) (s : ℂ) (hτ : p.τ = s + h (CuspUniformization.exponential s))
    (hμ : p.μ = μ (CuspUniformization.exponential s))
    (hβ : p.β = b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s)) :
    p.leftBlock = CuspUniformization.logarithmicPeriod (cuspCorrection μ b h) s := by
  have hp : p = cuspPeriodPoint μ b h s := PeriodPoint.ext hτ hμ hβ
  rw [hp, cuspPeriodPoint_leftBlock]

theorem SpecialPeriods.cusp_period_lattice_eq (μ b h : ℂ → ℂ) (p : PeriodDomain) (s : ℂ)
    (hτ : p.val.τ = s + h (CuspUniformization.exponential s))
    (hμ : p.val.μ = μ (CuspUniformization.exponential s))
    (hβ :
      p.val.β = b (CuspUniformization.exponential s) - s - h (CuspUniformization.exponential s))
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (cuspCorrection μ b h) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4) :
    (CuspUniformization.periodData (cuspCorrection μ b h) s hlog hRp).lattice = p.lattice := by
  apply p.fullPeriodLattice_eq
  exact (leftBlock_eq_logarithmicPeriod_of_cusp_expansion μ b h p.val s hτ hμ hβ).symm

def CuspUniformization.logDomain (ε : ℝ) : TopologicalSpace.Opens (ℂ × ComplexPlane₂) :=
  ⟨(fun p : ℂ × ComplexPlane₂ => exponential p.1) ⁻¹' Metric.ball 0 ε,
    Metric.isOpen_ball.preimage (exponential_holomorphic.continuous.comp continuous_fst)⟩

abbrev CuspUniformization.LogCover (ε : ℝ) :=
  logDomain ε

@[simp]
theorem CuspUniformization.mem_logDomain (ε : ℝ) (p : ℂ × ComplexPlane₂) :
    p ∈ logDomain ε ↔ ‖exponential p.1‖ < ε := by simp [logDomain, Metric.mem_ball]

def CuspUniformization.puncturedTubeOpen (ε : ℝ) :
    TopologicalSpace.Opens (ToricSpace.Tube (CuspQuotient.disc ε)) :=
  ⟨{x | ToricSpace.time (x : ToricSpace.Space) ≠ 0},
    isOpen_ne_fun (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val)
      continuous_const⟩

abbrev CuspUniformization.PuncturedTube (ε : ℝ) :=
  puncturedTubeOpen ε

def CuspUniformization.puncturedQuotientOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    TopologicalSpace.Opens (CuspQuotient.QuotientSpace C ε) :=
  ⟨{x | CuspQuotient.projection C ε x ≠ 0},
    isOpen_ne_fun (CuspQuotient.projection_continuous C ε) continuous_const⟩

abbrev CuspUniformization.PuncturedQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  puncturedQuotientOpen C ε

def CuspUniformization.totalExponentialPoint (p : ℂ × ComplexPlane₂) : ToricSpace.Space :=
  exponentialPoint (exponential p.1) p.2

@[simp]
theorem CuspUniformization.time_totalExponentialPoint (p : ℂ × ComplexPlane₂) :
    ToricSpace.time (totalExponentialPoint p) = exponential p.1 :=
  time_exponentialPoint (exponential_ne_zero p.1) p.2

theorem CuspUniformization.totalExponentialPoint_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω totalExponentialPoint := by
  apply (ToricSpace.inclusion_holomorphic ToricSpace.referenceTriangle).comp
  apply ContDiff.contMDiff
  apply contDiffOn_univ.mp
  apply (ToricCharts.monomial_contDiffOn ToricSpace.referenceTriangle.dual ω).comp
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 0).comp contDiff_snd)
    · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 1).comp contDiff_snd)
    · exact exponential_holomorphic.comp contDiff_fst
  · intro p _
    exact
      ToricCharts.torus_subset_domain _ (exponentialCoordinates_mem (exponential_ne_zero p.1) p.2)

def CuspUniformization.totalExponentialLift (ε : ℝ) (p : LogCover ε) :
    ToricSpace.Tube (CuspQuotient.disc ε) :=
  ⟨totalExponentialPoint p,
    by
    change ToricSpace.time (totalExponentialPoint p) ∈ Metric.ball 0 ε
    rw [time_totalExponentialPoint]
    exact p.2⟩

def CuspUniformization.puncturedExponential (ε : ℝ) (p : LogCover ε) : PuncturedTube ε :=
  ⟨totalExponentialLift ε p,
    by
    change ToricSpace.time (totalExponentialPoint p) ≠ 0
    rw [time_totalExponentialPoint]
    exact exponential_ne_zero _⟩

def CuspUniformization.totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : LogCover ε) : CuspQuotient.QuotientSpace C ε :=
  CuspQuotient.quotientMap C ε (totalExponentialLift ε p)

@[simp]
theorem CuspUniformization.projection_totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : LogCover ε) : CuspQuotient.projection C ε (totalCuspCover C ε p) = exponential p.1.1 :=
  time_totalExponentialPoint p

def CuspUniformization.puncturedCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : LogCover ε) : PuncturedQuotient C ε :=
  ⟨totalCuspCover C ε p,
    by
    change CuspQuotient.projection C ε (totalCuspCover C ε p) ≠ 0
    rw [projection_totalCuspCover]
    exact exponential_ne_zero _⟩

def CuspUniformization.puncturedQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : PuncturedTube ε) : PuncturedQuotient C ε :=
  ⟨CuspQuotient.quotientMap C ε p, p.2⟩

theorem CuspUniformization.totalExponentialLift_holomorphic (ε : ℝ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalExponentialLift ε) := by
  intro p
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun q => (totalExponentialLift ε q : ToricSpace.Space)) p ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalExponentialLift ε) p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (totalExponentialPoint_holomorphic.comp contMDiff_subtype_val p)

theorem CuspUniformization.puncturedExponential_surjective (ε : ℝ) :
    Function.Surjective (puncturedExponential ε) := by
  intro x
  let t : ℂ := ToricSpace.time (x.1 : ToricSpace.Space)
  have ht : t ≠ 0 := x.2
  obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre ht (x := (x.1 : ToricSpace.Space)) rfl
  let p : LogCover ε :=
    ⟨(logarithm t, z), by
      change exponential (logarithm t) ∈ Metric.ball 0 ε
      rw [exponential_logarithm ht]
      exact x.1.2⟩
  refine ⟨p, Subtype.ext (Subtype.ext ?_)⟩
  change exponentialPoint (exponential (logarithm t)) z = (x.1 : ToricSpace.Space)
  rw [exponential_logarithm ht]
  exact hz

theorem CuspUniformization.puncturedQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Surjective (puncturedQuotientMap C ε) := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.1
  have hp : ToricSpace.time (x : ToricSpace.Space) ≠ 0 := by
    have h := q.2
    change CuspQuotient.projection C ε q.1 ≠ 0 at h
    rwa [← hx] at h
  exact ⟨⟨x, hp⟩, Subtype.ext hx⟩

theorem CuspUniformization.puncturedCuspCover_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Surjective (puncturedCuspCover C ε) :=
  (puncturedQuotientMap_surjective C ε).comp (puncturedExponential_surjective ε)

def CuspUniformization.TotalPeriodRelated (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (p q : ℂ × ComplexPlane₂) : Prop :=
  ∃ (k : ℤ) (m n : Fin 2 → ℤ),
    p.1 = q.1 + k ∧
      p.2 = q.2 + (fun i => (m i : ℂ)) + logarithmicPeriod C q.1 *ᵥ (fun i => (n i : ℂ))

theorem CuspUniformization.totalCuspCover_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p q : LogCover ε) : totalCuspCover C ε p = totalCuspCover C ε q ↔ TotalPeriodRelated C p q :=
  by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  constructor
  · intro h
    have hs : exponential p.1.1 = exponential q.1.1 := by
      simpa only [projection_totalCuspCover] using congrArg (CuspQuotient.projection C ε) h
    obtain ⟨k, hk⟩ := (exponential_eq_iff _ _).mp hs
    have horb := Quotient.exact h
    change
      totalExponentialLift ε p ∈
        MulAction.orbit CuspQuotient.LatticeGroup (totalExponentialLift ε q) at horb
    obtain ⟨g, hg⟩ := horb
    have hp :
      exponentialPoint (exponential q.1.1) p.1.2 =
        exponentialPoint (exponential q.1.1)
          (q.1.2 + logarithmicPeriod C q.1.1 *ᵥ (fun i => (g.toAdd i : ℂ))) := by
      have he :=
        (congrArg Subtype.val hg).symm.trans
          (twistedTranslate_exponentialPoint C q.1.1 g.toAdd q.1.2)
      change exponentialPoint (exponential p.1.1) p.1.2 = _ at he
      rwa [hs] at he
    obtain ⟨m, hm⟩ := (exponentialPoint_eq_iff (exponential_ne_zero q.1.1) _ _).mp hp
    refine ⟨k, m, g.toAdd, hk, ?_⟩
    rw [hm]
    abel
  · rintro ⟨k, m, n, hk, hmn⟩
    have hs := (exponential_eq_iff p.1.1 q.1.1).mpr ⟨k, hk⟩
    have hp :
      totalExponentialPoint p = ToricSpace.twistedTranslate C n (totalExponentialPoint q) := by
      change
        exponentialPoint (exponential p.1.1) p.1.2 =
          ToricSpace.twistedTranslate C n (exponentialPoint (exponential q.1.1) q.1.2)
      rw [hs, twistedTranslate_exponentialPoint]
      apply (exponentialPoint_eq_iff (exponential_ne_zero q.1.1) _ _).mpr
      refine ⟨m, ?_⟩
      rw [hmn]
      abel
    have hl :
      totalExponentialLift ε p =
        ToricSpace.tubeTranslate C (CuspQuotient.disc ε) n (totalExponentialLift ε q) :=
      Subtype.ext hp
    change
      CuspQuotient.quotientMap C ε (totalExponentialLift ε p) =
        CuspQuotient.quotientMap C ε (totalExponentialLift ε q)
    rw [hl, CuspQuotient.quotientMap_translate]

theorem CuspUniformization.puncturedCuspCover_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p q : LogCover ε) :
    puncturedCuspCover C ε p = puncturedCuspCover C ε q ↔ TotalPeriodRelated C p q := by
  rw [← totalCuspCover_eq_iff C ε p q]
  exact Subtype.ext_iff

def opensInclusionPartialDiffeomorph {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    (U : TopologicalSpace.Opens M) (hU : Nonempty U) : PartialDiffeomorph I I U M ω := by
  let e := U.openPartialHomeomorphSubtypeCoe hU
  refine
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := ?_ }
  intro x hx
  have hxU : x ∈ U := by simpa [e] using hx
  have he : (Subtype.val ∘ e.symm) =ᶠ[𝓝 x] id := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hy
    exact
      e.right_inv
        (by
          simpa only [e, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy)
  have hs : ContMDiffAt I I ω (Subtype.val ∘ e.symm) x := contMDiffAt_id.congr_of_eventuallyEq he
  have hi : ContMDiffAt I I ω (Subtype.val ∘ e.symm) x ↔ ContMDiffAt I I ω e.symm x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact (hi.mp hs).contMDiffWithinAt

theorem isLocalDiffeomorph_subtypeVal {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    (U : TopologicalSpace.Opens M) : IsLocalDiffeomorph I I ω (Subtype.val : U → M) := by
  intro x
  refine ⟨opensInclusionPartialDiffeomorph I U ⟨x⟩, Set.mem_univ _, ?_⟩
  intro y _
  rfl

theorem isLocalDiffeomorphAt_codRestrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    {x : M} (hf : IsLocalDiffeomorphAt I J ω f x) (V : TopologicalSpace.Opens N)
    (hV : ∀ x, f x ∈ V) : IsLocalDiffeomorphAt I J ω (fun y => (⟨f y, hV y⟩ : V)) x := by
  obtain ⟨Φ, hx, he⟩ := hf
  let eV := opensInclusionPartialDiffeomorph J V ⟨⟨f x, hV x⟩⟩
  let Ψ := Φ.trans eV.symm
  have hxV : Φ x ∈ V := by
    rw [← he hx]
    exact hV x
  have hxV' : Φ x ∈ (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).target := by simpa using hxV
  refine ⟨Ψ, ⟨hx, hxV'⟩, ?_⟩
  intro y hy
  have hyV : Φ y ∈ (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).target := hy.2
  apply Subtype.ext
  change f y = ((V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).symm (Φ y) : N)
  have hv := (V.openPartialHomeomorphSubtypeCoe ⟨⟨f x, hV x⟩⟩).right_inv hyV
  exact (he hy.1).trans hv.symm

theorem isLocalDiffeomorph_codRestrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (V : TopologicalSpace.Opens N) (hV : ∀ x, f x ∈ V) :
    IsLocalDiffeomorph I J ω (fun x => (⟨f x, hV x⟩ : V)) := fun x =>
  isLocalDiffeomorphAt_codRestrictOpens I J (hf x) V hV

theorem isLocalDiffeomorphAt_restrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    {x : M} (hf : IsLocalDiffeomorphAt I J ω f x) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (hUV : Set.MapsTo f (U : Set M) (V : Set N)) (hx : x ∈ U) :
    IsLocalDiffeomorphAt I J ω (fun y : U => (⟨f y, hUV y.2⟩ : V)) ⟨x, hx⟩ := by
  have hU : IsLocalDiffeomorphAt I J ω (fun y : U => f y) ⟨x, hx⟩ :=
    (isLocalDiffeomorph_subtypeVal I U ⟨x, hx⟩).comp (K := J) (P := N) hf
  exact isLocalDiffeomorphAt_codRestrictOpens I J hU V (fun y => hUV y.2)

theorem isLocalDiffeomorph_restrictOpens {E F H K M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace K] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace K N] (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K) {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (U : TopologicalSpace.Opens M)
    (V : TopologicalSpace.Opens N) (hUV : Set.MapsTo f (U : Set M) (V : Set N)) :
    IsLocalDiffeomorph I J ω (fun x : U => (⟨f x, hUV x.2⟩ : V)) := by
  have hU : IsLocalDiffeomorph I J ω (fun x : U => f x) := by
    intro x
    exact (isLocalDiffeomorph_subtypeVal I U x).comp (K := J) (P := N) (hf x)
  exact isLocalDiffeomorph_codRestrictOpens I J hU V (fun x => hUV x.2)

def SpecialPeriods.CuspFamily.logBase (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨CuspUniformization.exponential ⁻¹' Metric.ball 0 ε,
    Metric.isOpen_ball.preimage CuspUniformization.exponential_holomorphic.continuous⟩

abbrev SpecialPeriods.CuspFamily.LogBase (ε : ℝ) :=
  logBase ε

@[simp]
theorem SpecialPeriods.CuspFamily.mem_logBase (ε : ℝ) (s : ℂ) :
    s ∈ logBase ε ↔ ‖CuspUniformization.exponential s‖ < ε := by simp [logBase, Metric.mem_ball]

def SpecialPeriods.CuspFamily.puncturedDisc (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 ε ∩ {t | t ≠ 0},
    Metric.isOpen_ball.inter (isOpen_ne_fun continuous_id continuous_const)⟩

@[simp]
theorem SpecialPeriods.CuspFamily.mem_puncturedDisc (ε : ℝ) (t : ℂ) :
    t ∈ puncturedDisc ε ↔ ‖t‖ < ε ∧ t ≠ 0 := by simp [puncturedDisc, Metric.mem_ball]

def SpecialPeriods.CuspFamily.baseExponential (ε : ℝ) (s : LogBase ε) : puncturedDisc ε :=
  ⟨CuspUniformization.exponential s, s.2, CuspUniformization.exponential_ne_zero s⟩

theorem SpecialPeriods.CuspFamily.baseExponential_surjective (ε : ℝ) :
    Function.Surjective (baseExponential ε) := by
  intro t
  let s : LogBase ε :=
    ⟨CuspUniformization.logarithm t,
      by
      change CuspUniformization.exponential (CuspUniformization.logarithm t) ∈ Metric.ball 0 ε
      rw [CuspUniformization.exponential_logarithm t.2.2]
      exact t.2.1⟩
  exact ⟨s, Subtype.ext (CuspUniformization.exponential_logarithm t.2.2)⟩

theorem SpecialPeriods.CuspFamily.exponential_sub_int (s : ℂ) (k : ℤ) :
    CuspUniformization.exponential (s - k) = CuspUniformization.exponential s := by
  rw [sub_eq_add_neg, ← Int.cast_neg, CuspUniformization.exponential_add,
    CuspUniformization.exponential_int, mul_one]

def SpecialPeriods.CuspFamily.logBaseTranslate (ε : ℝ) (k : ℤ) (s : LogBase ε) : LogBase ε :=
  ⟨(s : ℂ) - k,
    by
    change CuspUniformization.exponential ((s : ℂ) - k) ∈ Metric.ball 0 ε
    rw [exponential_sub_int]
    exact s.2⟩

@[simp]
theorem SpecialPeriods.CuspFamily.logBaseTranslate_coe (ε : ℝ) (k : ℤ) (s : LogBase ε) :
    (logBaseTranslate ε k s : ℂ) = (s : ℂ) - k :=
  rfl

@[instance_reducible]
def SpecialPeriods.CuspFamily.logBaseAction (ε : ℝ) : MulAction (Multiplicative ℤ) (LogBase ε)
    where
  smul g s := logBaseTranslate ε g.toAdd s
  mul_smul g h
    s := by
    apply Subtype.ext
    change (s : ℂ) - ((g.toAdd + h.toAdd : ℤ) : ℂ) = ((s : ℂ) - h.toAdd) - g.toAdd
    push_cast
    abel
  one_smul
    s := by
    apply Subtype.ext
    change (s : ℂ) - ((1 : Multiplicative ℤ).toAdd : ℂ) = (s : ℂ)
    simp only [toAdd_one, Int.cast_zero, sub_zero]

theorem SpecialPeriods.CuspFamily.logBaseTranslate_holomorphic (ε : ℝ) (k : ℤ) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (logBaseTranslate ε k) := by
  intro s
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (Subtype.val ∘ logBaseTranslate ε k) s ↔
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (logBaseTranslate ε k)
        s :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.sub contMDiff_const) s)

theorem SpecialPeriods.CuspFamily.logBase_action_holomorphic (ε : ℝ) :
    letI := logBaseAction ε
    ∀ g : Multiplicative ℤ,
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (fun s : LogBase ε => g • s) := by
  let := logBaseAction ε
  intro g
  exact logBaseTranslate_holomorphic ε g.toAdd

theorem SpecialPeriods.CuspFamily.logBase_continuousConstSMul (ε : ℝ) :
    letI := logBaseAction ε
    ContinuousConstSMul (Multiplicative ℤ) (LogBase ε) := by
  let := logBaseAction ε
  exact ⟨fun g => (logBase_action_holomorphic ε g).continuous⟩

theorem SpecialPeriods.CuspFamily.logBase_free_action (ε : ℝ) :
    letI := logBaseAction ε
    IsCancelSMul (Multiplicative ℤ) (LogBase ε) := by
  let := logBaseAction ε
  constructor
  intro g h s he
  have hc := congrArg (Subtype.val : LogBase ε → ℂ) he
  change (s : ℂ) - g.toAdd = (s : ℂ) - h.toAdd at hc
  apply Multiplicative.toAdd.injective
  exact_mod_cast sub_right_inj.mp hc

@[simp]
theorem SpecialPeriods.CuspFamily.baseExponential_smul (ε : ℝ) (g : Multiplicative ℤ)
    (s : LogBase ε) :
    letI := logBaseAction ε
    baseExponential ε (g • s) = baseExponential ε s := by
  let := logBaseAction ε
  apply Subtype.ext
  exact exponential_sub_int s g.toAdd

theorem SpecialPeriods.CuspFamily.baseExponential_eq_iff_orbit (ε : ℝ) (s t : LogBase ε) :
    letI := logBaseAction ε
    baseExponential ε s = baseExponential ε t ↔ s ∈ MulAction.orbit (Multiplicative ℤ) t := by
  let := logBaseAction ε
  constructor
  · intro h
    obtain ⟨k, hk⟩ :=
      (CuspUniformization.exponential_eq_iff (s : ℂ) t).mp (congrArg Subtype.val h)
    refine ⟨Multiplicative.ofAdd (-k), Subtype.ext ?_⟩
    change (t : ℂ) - ((-k : ℤ) : ℂ) = (s : ℂ)
    rw [hk, Int.cast_neg, sub_neg_eq_add]
  · rintro ⟨g, rfl⟩
    exact baseExponential_smul ε g t

def SpecialPeriods.CuspFamily.scalarExponentialChart (s : ℂ) : OpenPartialHomeomorph ℂ ℂ :=
  CuspUniformization.exponential_holomorphic.contDiffAt.toOpenPartialHomeomorph
    CuspUniformization.exponential
    ((CuspUniformization.exponential_hasDerivAt s).hasFDerivAt_equiv
      (mul_ne_zero (CuspUniformization.exponential_ne_zero s)
        CuspUniformization.exponential_factor_ne_zero))
    (by simp)

theorem SpecialPeriods.CuspFamily.scalarExponentialChart_mem_source (s : ℂ) :
    s ∈ (scalarExponentialChart s).source :=
  CuspUniformization.exponential_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    ((CuspUniformization.exponential_hasDerivAt s).hasFDerivAt_equiv
      (mul_ne_zero (CuspUniformization.exponential_ne_zero s)
        CuspUniformization.exponential_factor_ne_zero))
    (by simp)

theorem SpecialPeriods.CuspFamily.scalarExponentialChart_holomorphic (s : ℂ) :
    ContDiffOn ℂ ω (scalarExponentialChart s) (scalarExponentialChart s).source :=
  CuspUniformization.exponential_holomorphic.contDiffOn

theorem SpecialPeriods.CuspFamily.scalarExponentialChart_symm_holomorphic (s : ℂ) :
    ContDiffOn ℂ ω (scalarExponentialChart s).symm (scalarExponentialChart s).target := by
  intro t ht
  exact
    ((scalarExponentialChart s).contDiffAt_symm ht
        ((CuspUniformization.exponential_hasDerivAt
              ((scalarExponentialChart s).symm t)).hasFDerivAt_equiv
          (mul_ne_zero (CuspUniformization.exponential_ne_zero _)
            CuspUniformization.exponential_factor_ne_zero))
        CuspUniformization.exponential_holomorphic.contDiffAt).contDiffWithinAt

theorem SpecialPeriods.CuspFamily.exponential_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      CuspUniformization.exponential := by
  intro s
  refine
    ⟨{  toPartialEquiv := (scalarExponentialChart s).toPartialEquiv
        open_source := (scalarExponentialChart s).open_source
        open_target := (scalarExponentialChart s).open_target
        contMDiffOn_toFun := (scalarExponentialChart_holomorphic s).contMDiffOn
        contMDiffOn_invFun := (scalarExponentialChart_symm_holomorphic s).contMDiffOn },
      scalarExponentialChart_mem_source s, ?_⟩
  intro t _
  rfl

theorem SpecialPeriods.CuspFamily.baseExponential_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (baseExponential ε) :=
  isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
    exponential_isLocalDiffeomorph (logBase ε) (puncturedDisc ε)
    (fun s hs => ⟨hs, CuspUniformization.exponential_ne_zero s⟩)

theorem SpecialPeriods.CuspFamily.baseExponential_isLocalHomeomorph (ε : ℝ) :
    IsLocalHomeomorph (baseExponential ε) :=
  (baseExponential_isLocalDiffeomorph ε).isLocalHomeomorph

theorem SpecialPeriods.CuspFamily.baseExponential_covering (ε : ℝ) :
    letI := logBaseAction ε
    IsQuotientCoveringMap (baseExponential ε) (Multiplicative ℤ) := by
  let := logBaseAction ε
  let := logBase_continuousConstSMul ε
  let := logBase_free_action ε
  exact
    quotientCoveringMap_of_localHomeomorph (baseExponential_isLocalHomeomorph ε)
      (baseExponential_surjective ε) (baseExponential_eq_iff_orbit ε)

instance SpecialPeriods.CuspFamily.logBaseProductChartedSpace (ε : ℝ) :
    ChartedSpace (ℂ × ComplexPlane₂) (LogBase ε × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (LogBase ε × ComplexPlane₂))

instance SpecialPeriods.CuspFamily.logBaseProductManifold (ε : ℝ) :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (LogBase ε × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := (modelWithCornersSelf ℂ ℂ)) (I' :=
      (modelWithCornersSelf ℂ ComplexPlane₂)) (LogBase ε) ComplexPlane₂

def SpecialPeriods.CuspFamily.logCoverProductEquiv (ε : ℝ) :
    CuspUniformization.LogCover ε ≃ (LogBase ε × ComplexPlane₂)
    where
  toFun p := (⟨p.1.1, p.2⟩, p.1.2)
  invFun p := ⟨((p.1 : ℂ), p.2), p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem SpecialPeriods.CuspFamily.logCoverProductEquiv_snd (ε : ℝ)
    (p : CuspUniformization.LogCover ε) : (logCoverProductEquiv ε p).2 = p.1.2 :=
  rfl

theorem SpecialPeriods.CuspFamily.logCoverProductEquiv_holomorphic (ε : ℝ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (logCoverProductEquiv ε) := by
  have hb :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      (fun p : CuspUniformization.LogCover ε => p.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_subtype_val
  have hb' :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      (fun p : CuspUniformization.LogCover ε => (⟨p.1.1, p.2⟩ : LogBase ε)) := by
    intro p
    have he :
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
          (Subtype.val ∘ fun q : CuspUniformization.LogCover ε => (⟨q.1.1, q.2⟩ : LogBase ε)) p ↔
        ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
          (fun q : CuspUniformization.LogCover ε => (⟨q.1.1, q.2⟩ : LogBase ε)) p :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp (hb p)
  have hz :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun p : CuspUniformization.LogCover ε => p.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_subtype_val
  rw [modelWithCornersSelf_prod]
  exact hb'.prodMk hz

theorem SpecialPeriods.CuspFamily.logCoverProductEquiv_symm_holomorphic (ε : ℝ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (logCoverProductEquiv ε).symm := by
  have hb :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : LogBase ε × ComplexPlane₂ → LogBase ε) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hz :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (Prod.snd : LogBase ε × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hp :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : LogBase ε × ComplexPlane₂ => ((p.1 : ℂ), p.2)) :=
    (contMDiff_subtype_val.comp hb).prodMk_space hz
  intro p
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
        (Subtype.val ∘ (logCoverProductEquiv ε).symm) p ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (logCoverProductEquiv ε).symm p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hp p)

def SpecialPeriods.CuspFamily.logCoverProductBiholomorph (ε : ℝ) :
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (CuspUniformization.LogCover ε)
      (LogBase ε × ComplexPlane₂) ω
    where
  toEquiv := logCoverProductEquiv ε
  contMDiff_toFun := logCoverProductEquiv_holomorphic ε
  contMDiff_invFun := logCoverProductEquiv_symm_holomorphic ε

abbrev RealPlane₄ :=
  Fin 4 → ℝ

def standardLattice : Submodule ℤ RealPlane₄ :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))

instance standardLattice_discrete : DiscreteTopology standardLattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))

instance standardLattice_isZLattice : IsZLattice ℝ standardLattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))))

instance standardLattice_closed : IsClosed (standardLattice : Set RealPlane₄) := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  exact AddSubgroup.isClosed_of_discrete (H := standardLattice.toAddSubgroup)

abbrev RealTorus₄ :=
  RealPlane₄ ⧸ standardLattice

instance realTorus_secondCountable : SecondCountableTopology RealTorus₄ :=
  standardLattice.isQuotientMap_mkQ.secondCountableTopology standardLattice.isOpenMap_mkQ

instance realTorus_pathConnected : PathConnectedSpace RealTorus₄ :=
  standardLattice.mkQ_surjective.pathConnectedSpace standardLattice.continuous_mkQ

instance realTorus_compact : CompactSpace RealTorus₄ := by
  have hper : ∀ z w, w ∈ standardLattice → standardLattice.mkQ (z + w) = standardLattice.mkQ z := by
    intro z w hw
    have hw' : standardLattice.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero standardLattice).mpr hw
    rw [map_add, hw', add_zero]
  have h :=
    IsZLattice.isCompact_range_of_periodic standardLattice standardLattice.mkQ
      standardLattice.continuous_mkQ hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr standardLattice.mkQ_surjective] using h⟩

structure HolomorphicPeriodMap (V B : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] where
  point : B → PeriodDomain
  holomorphic_tau :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω (fun b => (point b).val.τ)
  holomorphic_mu :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω (fun b => (point b).val.μ)
  holomorphic_beta :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω (fun b => (point b).val.β)

def HolomorphicPeriodMap.periodEquiv {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    RealPlane₄ ≃ₗ[ℝ] ComplexPlane₂ :=
  (P.point b).realEquiv.trans complexCoordinates

theorem HolomorphicPeriodMap.periodEquiv_apply {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (v : RealPlane₄) :
    P.periodEquiv b v = complexCoordinates ((P.point b).val.realMatrix *ᵥ v) := by
  simp only [periodEquiv, LinearEquiv.trans_apply, PeriodDomain.realEquiv_apply]

theorem HolomorphicPeriodMap.periodEquiv_symm_apply {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (z : ComplexPlane₂) :
    (P.periodEquiv b).symm z = (P.point b).val.realMatrix⁻¹ *ᵥ complexCoordinates.symm z := by
  simp [periodEquiv, PeriodDomain.realEquiv, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply]

theorem HolomorphicPeriodMap.continuous_realMatrix {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun b => (P.point b).val.realMatrix) := by
  have ht := P.holomorphic_tau.continuous
  have hm := P.holomorphic_mu.continuous
  have hb := P.holomorphic_beta.continuous
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [PeriodPoint.realMatrix] <;> fun_prop

theorem HolomorphicPeriodMap.continuous_realMatrix_inv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun b => (P.point b).val.realMatrix⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  have hd : (P.point b).val.realMatrix.det ≠ 0 :=
    ne_of_lt ((P.point b).val.det_realMatrix_neg (P.point b).property)
  have hinv : ContinuousAt (fun A : Matrix (Fin 4) (Fin 4) ℝ => A⁻¹) (P.point b).val.realMatrix :=
    by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using ContinuousInv₀.continuousAt_inv₀ hd
  exact
    hinv.comp (f := fun b : B => (P.point b).val.realMatrix)
      (P.continuous_realMatrix.continuousAt (x := b))

theorem HolomorphicPeriodMap.continuous_periodEquiv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun x : B × RealPlane₄ => P.periodEquiv x.1 x.2) := by
  simp_rw [periodEquiv_apply]
  exact
    complexCoordinates.toContinuousLinearEquiv.continuous.comp
      ((P.continuous_realMatrix.comp continuous_fst).matrix_mulVec continuous_snd)

theorem HolomorphicPeriodMap.continuous_periodEquiv_symm {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Continuous (fun x : B × ComplexPlane₂ => (P.periodEquiv x.1).symm x.2) := by
  simp_rw [periodEquiv_symm_apply]
  exact
    (P.continuous_realMatrix_inv.comp continuous_fst).matrix_mulVec
      (complexCoordinates.symm.toContinuousLinearEquiv.continuous.comp continuous_snd)

def HolomorphicPeriodMap.realTrivialization {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    (B × ComplexPlane₂) ≃ₜ (B × RealPlane₄)
    where
  toFun x := (x.1, (P.periodEquiv x.1).symm x.2)
  invFun x := (x.1, P.periodEquiv x.1 x.2)
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_fst.prodMk P.continuous_periodEquiv_symm
  continuous_invFun := continuous_fst.prodMk P.continuous_periodEquiv

abbrev HolomorphicPeriodMap.TotalSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (_P : HolomorphicPeriodMap V B) :=
  B × RealTorus₄

def HolomorphicPeriodMap.quotientMap {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    (B × ComplexPlane₂) → P.TotalSpace := fun x =>
  (x.1, standardLattice.mkQ ((P.periodEquiv x.1).symm x.2))

theorem HolomorphicPeriodMap.quotientMap_localHomeomorph {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    IsLocalHomeomorph P.quotientMap := by
  have : DiscreteTopology standardLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology standardLattice)
  have h :=
    (AddSubgroup.isAddQuotientCoveringMap_of_comm standardLattice.toAddSubgroup
        DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph
  exact (localHomeomorph_prod_id (B := B) h).comp P.realTrivialization.isLocalHomeomorph

theorem HolomorphicPeriodMap.quotientMap_surjective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Function.Surjective P.quotientMap := by
  rintro ⟨b, z⟩
  obtain ⟨v, hv⟩ := standardLattice.mkQ_surjective z
  refine ⟨(b, P.periodEquiv b v), ?_⟩
  simpa [quotientMap] using congrArg (Prod.mk b) hv

theorem HolomorphicPeriodMap.periodEquiv_coordinates {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (v : RealPlane₄) :
    P.periodEquiv b v =
      ![6 * (P.point b).val.μ * (v 0) + (P.point b).val.τ * (v 1) + (v 2),
        (P.point b).val.β * (v 0) + (P.point b).val.μ * (v 1) + (v 3)] := by
  rw [periodEquiv_apply]
  ext i : 1
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, dotProduct, Fin.sum_univ_four,
      Complex.mul_re, Complex.mul_im]

theorem HolomorphicPeriodMap.holomorphic_periodEquiv_const {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (v : RealPlane₄) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun b => P.periodEquiv b v) := by
  simp_rw [periodEquiv_coordinates]
  apply contMDiff_pi_space.mpr
  intro i
  fin_cases i
  · exact
      (((contMDiff_const.mul P.holomorphic_mu).mul contMDiff_const).add
            (P.holomorphic_tau.mul contMDiff_const)).add
        contMDiff_const
  · exact
      ((P.holomorphic_beta.mul contMDiff_const).add (P.holomorphic_mu.mul contMDiff_const)).add
        contMDiff_const

theorem HolomorphicPeriodMap.periodEquiv_map_lattice {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) :
    standardLattice.map ((P.periodEquiv b).restrictScalars ℤ).toLinearMap = (P.point b).lattice :=
  by
  rw [standardLattice, Submodule.map_span, PeriodDomain.lattice_eq_span_basis]
  congr 1
  rw [← Set.range_comp]
  congr 1

@[instance_reducible]
def HolomorphicPeriodMap.coveringAction {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    MulAction (Multiplicative standardLattice) (B × ComplexPlane₂)
    where
  smul g x := (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄))
  one_smul
    x := by
    change
      (x.1, x.2 + P.periodEquiv x.1 ((1 : Multiplicative standardLattice).toAdd : RealPlane₄)) = x
    simp
  mul_smul g h
    x := by
    change
      (x.1, x.2 + P.periodEquiv x.1 ((g * h).toAdd : RealPlane₄)) =
        (x.1,
          (x.2 + P.periodEquiv x.1 (h.toAdd : RealPlane₄)) +
            P.periodEquiv x.1 (g.toAdd : RealPlane₄))
    simp [map_add, add_left_comm, add_comm]

theorem HolomorphicPeriodMap.realTrivialization_smul {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    P.realTrivialization (g • x) = (x.1, (P.periodEquiv x.1).symm x.2 + (g.toAdd : RealPlane₄)) :=
  by
  let := P.coveringAction
  change (x.1, (P.periodEquiv x.1).symm (x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄))) = _
  simp only [map_add, LinearEquiv.symm_apply_apply]

theorem HolomorphicPeriodMap.coveringAction_continuous {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    ContinuousConstSMul (Multiplicative standardLattice) (B × ComplexPlane₂) := by
  let := P.coveringAction
  constructor
  intro g
  change
    Continuous
      (fun x : B × ComplexPlane₂ => (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))
  exact
    continuous_fst.prodMk
      (continuous_snd.add
        ((P.holomorphic_periodEquiv_const (g.toAdd : RealPlane₄)).continuous.comp continuous_fst))

theorem HolomorphicPeriodMap.coveringAction_free {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    IsCancelSMul (Multiplicative standardLattice) (B × ComplexPlane₂) := by
  let := P.coveringAction
  constructor
  intro g h x he
  have he' := congrArg (fun y => (P.realTrivialization y).2) he
  rw [P.realTrivialization_smul, P.realTrivialization_smul] at he'
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact add_left_cancel he'

theorem HolomorphicPeriodMap.quotientMap_smul {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    P.quotientMap (g • x) = P.quotientMap x := by
  let := P.coveringAction
  have hg : standardLattice.mkQ (g.toAdd : RealPlane₄) = 0 :=
    (Submodule.Quotient.mk_eq_zero standardLattice).mpr g.toAdd.property
  change
    (x.1,
        standardLattice.mkQ
          ((P.periodEquiv x.1).symm (x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))) =
      _
  simp only [map_add, LinearEquiv.symm_apply_apply, hg, add_zero]
  rfl

theorem HolomorphicPeriodMap.quotientMap_orbit {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    ∀ x y : B × ComplexPlane₂,
      P.quotientMap x = P.quotientMap y ↔
        x ∈ MulAction.orbit (Multiplicative standardLattice) y := by
  let := P.coveringAction
  rintro ⟨b, z⟩ ⟨b', w⟩
  constructor
  · intro h
    have hb : b = b' := congrArg Prod.fst h
    subst b'
    have hv : (P.periodEquiv b).symm z - (P.periodEquiv b).symm w ∈ standardLattice :=
      (Submodule.Quotient.eq standardLattice).mp (congrArg Prod.snd h)
    refine ⟨Multiplicative.ofAdd ⟨_, hv⟩, ?_⟩
    change (b, w + P.periodEquiv b ((P.periodEquiv b).symm z - (P.periodEquiv b).symm w)) = (b, z)
    simp only [map_sub, LinearEquiv.apply_symm_apply]
    congr 1
    abel
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact P.quotientMap_smul g (b', w)

theorem HolomorphicPeriodMap.quotientCoveringMap {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    letI := P.coveringAction
    IsQuotientCoveringMap P.quotientMap (Multiplicative standardLattice) := by
  let := P.coveringAction
  have := P.coveringAction_continuous
  have := P.coveringAction_free
  exact
    quotientCoveringMap_of_localHomeomorph P.quotientMap_localHomeomorph P.quotientMap_surjective
      P.quotientMap_orbit

@[instance_reducible]
def HolomorphicPeriodMap.coveringChartedSpace {V B : Type*} [NormedAddCommGroup V]
    [TopologicalSpace B] [ChartedSpace V B] :
    ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace in
theorem HolomorphicPeriodMap.coveringManifold {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := modelWithCornersSelf ℂ V) (I' := modelWithCornersSelf ℂ ComplexPlane₂) B
      ComplexPlane₂

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.coveringAction_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (g : Multiplicative standardLattice) :
    letI := P.coveringAction
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (fun x : B × ComplexPlane₂ => g • x) := by
  let := P.coveringAction
  rw [modelWithCornersSelf_prod]
  change
    ContMDiff _ _ ω
      (fun x : B × ComplexPlane₂ => (x.1, x.2 + P.periodEquiv x.1 (g.toAdd : RealPlane₄)))
  exact
    contMDiff_fst.prodMk
      (contMDiff_snd.add
        ((P.holomorphic_periodEquiv_const (g.toAdd : RealPlane₄)).comp contMDiff_fst))

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
@[instance_reducible]
def HolomorphicPeriodMap.totalChartedSpace {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    ChartedSpace (V × ComplexPlane₂) P.TotalSpace := by
  let := P.coveringAction
  exact CoveringQuotient.chartedSpace (E := V × ComplexPlane₂) P.quotientCoveringMap

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.totalSpace_isManifold {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.TotalSpace := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  exact
    CoveringQuotient.isManifold (E := V × ComplexPlane₂) P.quotientCoveringMap ω
      P.coveringAction_holomorphic

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.quotientMap_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω P.quotientMap := by
  let := P.coveringAction
  have : IsManifold (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (B × ComplexPlane₂) := by
    infer_instance
  exact
    CoveringQuotient.contMDiff_project (E := V × ComplexPlane₂) P.quotientCoveringMap ω
      P.coveringAction_holomorphic

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
def HolomorphicPeriodMap.projection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) : P.TotalSpace → B :=
  Prod.fst

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.projection_surjective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    Function.Surjective P.projection := fun b => ⟨(b, 0), rfl⟩

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.projection_proper {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) :
    IsProperMap P.projection :=
  isProperMap_fst_of_compactSpace

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
def HolomorphicPeriodMap.torusHomeomorph {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    RealTorus₄ ≃ₜ (P.point b).Torus
    where
  toEquiv :=
    (Submodule.Quotient.equiv standardLattice (P.point b).lattice
        ((P.periodEquiv b).restrictScalars ℤ) (P.periodEquiv_map_lattice b)).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      (P.point b).lattice.continuous_mkQ.comp (P.periodEquiv b).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply (P.point b).lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp
        (P.periodEquiv b).symm.toContinuousLinearEquiv.continuous

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
def HolomorphicPeriodMap.fibreInclusion {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) (b : B) :
    (P.point b).Torus → P.TotalSpace := fun z => (b, (P.torusHomeomorph b).symm z)

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.fibreInclusion_injective {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) : Function.Injective (P.fibreInclusion b) := by
  intro x y h
  exact (P.torusHomeomorph b).symm.injective (congrArg Prod.snd h)

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
@[simp]
theorem HolomorphicPeriodMap.fibreInclusion_mkQ {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (z : ComplexPlane₂) :
    P.fibreInclusion b ((P.point b).lattice.mkQ z) = P.quotientMap (b, z) :=
  rfl

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.range_fibreInclusion {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) : Set.range (P.fibreInclusion b) = P.projection ⁻¹' { b } := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hz
    have hb : z.1 = b := hz
    refine ⟨P.torusHomeomorph b z.2, ?_⟩
    simp only [fibreInclusion, Homeomorph.symm_apply_apply, ← hb, Prod.mk.eta]

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
theorem HolomorphicPeriodMap.fibreInclusion_holomorphic {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    [IsManifold (modelWithCornersSelf ℂ V) ω B] (b : B) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      ω (P.fibreInclusion b) := by
  let := P.totalChartedSpace
  apply DiscreteQuotient.contMDiff_of_comp_mkQ (P.point b).lattice
  have h :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      ω (fun z : ComplexPlane₂ => (b, z)) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_const.prodMk contMDiff_id
  exact P.quotientMap_holomorphic.comp h

attribute [local instance] HolomorphicPeriodMap.coveringChartedSpace
    HolomorphicPeriodMap.coveringManifold in
def HolomorphicPeriodMap.zeroSection {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B) : B → P.TotalSpace :=
  fun b => (b, 0)

structure SpecialPeriods.CuspFamily.Data where
  μ : ℂ → ℂ
  b : ℂ → ℂ
  h : ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  holomorphic :
    ∀ i j,
      ContDiffOn ℂ ω (fun t => SpecialPeriods.cuspCorrection μ b h t i j) (Metric.ball 0 radius)
  smallDrift : ToricSpace.SmallDrift (SpecialPeriods.cuspCorrection μ b h) radius

abbrev SpecialPeriods.CuspFamily.Data.correction (D : SpecialPeriods.CuspFamily.Data) :
    ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
  SpecialPeriods.cuspCorrection D.μ D.b D.h

theorem SpecialPeriods.CuspFamily.Data.logarithmic_height (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    Real.log ‖CuspUniformization.exponential (s : ℂ)‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))
    (((SpecialPeriods.CuspFamily.mem_logBase _ _).mp s.2).trans D.radius_lt_one)

theorem SpecialPeriods.CuspFamily.Data.logarithmic_drift (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    ToricSpace.entryNorm
        (ToricSpace.driftMatrix D.correction (CuspUniformization.exponential (s : ℂ))) ≤
      -Real.log ‖CuspUniformization.exponential (s : ℂ)‖ / 4 :=
  D.smallDrift _ (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))
    ((SpecialPeriods.CuspFamily.mem_logBase _ _).mp s.2)

def SpecialPeriods.CuspFamily.Data.point (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) : PeriodDomain :=
  SpecialPeriods.cuspPeriodDomain D.μ D.b D.h s (D.logarithmic_height s) (D.logarithmic_drift s)

theorem SpecialPeriods.CuspFamily.Data.correction_entry_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) (i j : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun s : SpecialPeriods.CuspFamily.LogBase D.radius =>
        D.correction (CuspUniformization.exponential (s : ℂ)) i j) := by
  intro s
  have hC :
    ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun t => D.correction t i j) (CuspUniformization.exponential (s : ℂ)) :=
    ((D.holomorphic i j).contDiffAt (Metric.isOpen_ball.mem_nhds s.2)).contMDiffAt
  exact
    hC.comp s
      ((CuspUniformization.exponential_holomorphic.contMDiff.comp
          contMDiff_subtype_val).contMDiffAt)

def SpecialPeriods.CuspFamily.Data.periods (D : SpecialPeriods.CuspFamily.Data) :
    HolomorphicPeriodMap ℂ (SpecialPeriods.CuspFamily.LogBase D.radius)
    where
  point := D.point
  holomorphic_tau := contMDiff_subtype_val.add (D.correction_entry_holomorphic 0 1)
  holomorphic_mu := D.correction_entry_holomorphic 1 1
  holomorphic_beta := by
    convert (D.correction_entry_holomorphic 1 0).sub contMDiff_subtype_val using 1
    funext s
    change
      D.b (CuspUniformization.exponential (s : ℂ)) - (s : ℂ) -
          D.h (CuspUniformization.exponential (s : ℂ)) =
        (D.b (CuspUniformization.exponential (s : ℂ)) -
            D.h (CuspUniformization.exponential (s : ℂ))) -
          (s : ℂ)
    ring

@[simp]
theorem SpecialPeriods.CuspFamily.Data.periods_point (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) : D.periods.point s = D.point s :=
  rfl

theorem SpecialPeriods.CuspFamily.Data.point_leftBlock (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    (D.point s).val.leftBlock = CuspUniformization.logarithmicPeriod D.correction (s : ℂ) :=
  SpecialPeriods.cuspPeriodPoint_leftBlock D.μ D.b D.h s

abbrev SpecialPeriods.CuspFamily.Data.TotalSpace (D : SpecialPeriods.CuspFamily.Data) :=
  D.periods.TotalSpace

def SpecialPeriods.CuspFamily.Data.familyCover (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.LogCover D.radius → D.TotalSpace :=
  D.periods.quotientMap ∘ SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius

@[simp]
theorem SpecialPeriods.CuspFamily.Data.familyCover_apply (D : SpecialPeriods.CuspFamily.Data)
    (x : CuspUniformization.LogCover D.radius) :
    D.familyCover x = D.periods.quotientMap (⟨x.1.1, x.2⟩, x.1.2) :=
  rfl

theorem SpecialPeriods.CuspFamily.Data.familyCover_surjective
    (D : SpecialPeriods.CuspFamily.Data) : Function.Surjective D.familyCover :=
  D.periods.quotientMap_surjective.comp
    (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius).surjective

theorem SpecialPeriods.CuspFamily.Data.familyCover_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.familyCover := by
  let := D.periods.totalChartedSpace
  exact
    D.periods.quotientMap_holomorphic.comp
      (SpecialPeriods.CuspFamily.logCoverProductBiholomorph D.radius).contMDiff

theorem SpecialPeriods.CuspFamily.Data.familyCover_isLocalDiffeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.familyCover := by
  let := D.periods.totalChartedSpace
  let := D.periods.coveringAction
  have hq :=
    CoveringQuotient.project_isLocalDiffeomorph D.periods.quotientCoveringMap
      D.periods.coveringAction_holomorphic
  intro x
  exact
    ((SpecialPeriods.CuspFamily.logCoverProductBiholomorph D.radius).isLocalDiffeomorph x).comp
      (K := modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (P := D.TotalSpace)
      (hq (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius x))

theorem SpecialPeriods.CuspFamily.Data.quotientMap_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂) :
    D.periods.quotientMap x = D.periods.quotientMap y ↔
      x.1 = y.1 ∧ x.2 - y.2 ∈ (D.periods.point y.1).lattice := by
  rcases x with ⟨s, z⟩
  rcases y with ⟨t, w⟩
  constructor
  · intro he
    have hs : s = t := congrArg Prod.fst he
    subst t
    refine ⟨rfl, ?_⟩
    apply (Submodule.Quotient.eq _).mp
    exact (D.periods.fibreInclusion_injective s) he
  · rintro ⟨hs, he⟩
    dsimp only at hs he
    subst t
    exact congrArg (D.periods.fibreInclusion s) ((Submodule.Quotient.eq _).mpr he)

theorem SpecialPeriods.CuspFamily.Data.familyCover_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : CuspUniformization.LogCover D.radius) :
    D.familyCover x = D.familyCover y ↔
      x.1.1 = y.1.1 ∧
        ∃ m n : Fin 2 → ℤ,
          x.1.2 =
            y.1.2 + (fun i => (m i : ℂ)) +
              CuspUniformization.logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ)) := by
  let s : SpecialPeriods.CuspFamily.LogBase D.radius := ⟨y.1.1, y.2⟩
  have hlat :
    (D.periods.point s).lattice =
      (CuspUniformization.periodData D.correction y.1.1 (D.logarithmic_height s)
          (D.logarithmic_drift s)).lattice := by
    exact
      (SpecialPeriods.cusp_period_lattice_eq D.μ D.b D.h (D.point s) y.1.1 rfl rfl rfl
          (D.logarithmic_height s) (D.logarithmic_drift s)).symm
  rw [familyCover_apply, familyCover_apply, D.quotientMap_eq_iff]
  change
    (⟨x.1.1, x.2⟩ : SpecialPeriods.CuspFamily.LogBase D.radius) = s ∧
        x.1.2 - y.1.2 ∈ (D.periods.point s).lattice ↔
      _
  rw [hlat, FullPeriodMatrix.mem_lattice_iff]
  constructor
  · rintro ⟨hs, m, n, hmn⟩
    refine ⟨congrArg Subtype.val hs, m, n, ?_⟩
    change
      x.1.2 - y.1.2 =
        (fun i => (m i : ℂ)) +
          CuspUniformization.logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ)) at hmn
    rw [sub_eq_iff_eq_add] at hmn
    rw [hmn]
    abel
  · rintro ⟨hs, m, n, hmn⟩
    refine ⟨Subtype.ext hs, m, n, ?_⟩
    change
      x.1.2 - y.1.2 =
        (fun i => (m i : ℂ)) +
          CuspUniformization.logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ))
    rw [hmn]
    abel

inductive Elliptic.Kind where
  | three
  | four
  deriving DecidableEq

instance Elliptic.instLocal1 : Fintype Kind :=
  ⟨{.three, .four}, by intro j; cases j <;> simp⟩

def Elliptic.Kind.order : Elliptic.Kind → ℕ
  | .three => 3
  | .four => 4

def Elliptic.Kind.matrix : Elliptic.Kind → LatticeMatrix
  | .three => A₁
  | .four => A₂

def Elliptic.Kind.twist : Elliptic.Kind → PeriodLattice
  | .three => ε
  | .four => -ε'

theorem Elliptic.Kind.order_pos (j : Elliptic.Kind) : 0 < j.order := by cases j <;> decide

theorem Elliptic.Kind.matrix_pow_order (j : Elliptic.Kind) : j.matrix ^ j.order = 1 := by
  cases j <;> decide

theorem Elliptic.Kind.matrix_fixes_twist (j : Elliptic.Kind) : j.matrix *ᵥ j.twist = j.twist := by
  cases j <;> decide

abbrev Elliptic.RealCoordinates :=
  Fin 4 → ℝ

def Elliptic.realCast (v : PeriodLattice) : RealCoordinates := fun i => (v i : ℝ)

def Elliptic.flatLinear (j : Kind) : RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (j.matrix.map (Int.castRingHom ℝ)).mulVecLin

def Elliptic.flatAffine (j : Kind) (v : PeriodLattice) (x : RealCoordinates) : RealCoordinates :=
  flatLinear j x + (1 / (j.order : ℝ)) • realCast v

def Elliptic.FlatCongruent (x y : RealCoordinates) : Prop :=
  ∃ v : PeriodLattice, x - y = realCast v

def Elliptic.AdmissibleTwist (j : Kind) (v : PeriodLattice) : Prop :=
  j.matrix *ᵥ v = v ∧ if j = .three then ¬3 ∣ γ v else Odd (γ v)

theorem Elliptic.mainTwist_admissible (j : Kind) : AdmissibleTwist j j.twist := by
  refine ⟨j.matrix_fixes_twist, ?_⟩
  cases j <;> norm_num [Kind.twist, γ, ε, ε']

def Elliptic.periodEquiv (p : PeriodDomain) : RealCoordinates ≃L[ℝ] ComplexPlane₂ :=
  p.basis.equivFun.symm.toContinuousLinearEquiv

theorem Elliptic.periodEquiv_apply (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p x = ∑ i, x i • p.basis i :=
  p.basis.equivFun_symm_apply x

theorem Elliptic.periodEquiv_matrix (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p x = p.val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [periodEquiv_apply]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, PeriodDomain.basis_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  change (x k : ℂ) * p.val.matrix i k = p.val.matrix i k * (x k : ℂ)
  exact mul_comm _ _

theorem Elliptic.periodEquiv_realCast (p : PeriodDomain) (v : PeriodLattice) :
    periodEquiv p (realCast v) = ∑ i, v i • p.basis i := by
  rw [periodEquiv_apply]
  simp only [realCast, Int.cast_smul_eq_zsmul]

theorem Elliptic.periodEquiv_mem_lattice_iff (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p x ∈ p.lattice ↔ ∃ v : PeriodLattice, x = realCast v := by
  rw [p.lattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, (periodEquiv p).injective ?_⟩
    rw [periodEquiv_realCast]
    exact hv.symm
  · rintro ⟨v, rfl⟩
    exact ⟨v, (periodEquiv_realCast p v).symm⟩

def Elliptic.flatProjection (p : PeriodDomain) (x : RealCoordinates) : p.Torus :=
  p.lattice.mkQ (periodEquiv p x)

theorem Elliptic.flatProjection_continuous (p : PeriodDomain) : Continuous (flatProjection p) :=
  p.lattice.continuous_mkQ.comp (periodEquiv p).continuous

theorem Elliptic.flatProjection_surjective (p : PeriodDomain) :
    Function.Surjective (flatProjection p) :=
  p.lattice.mkQ_surjective.comp (periodEquiv p).surjective

theorem Elliptic.flatProjection_eq_iff (p : PeriodDomain) (x y : RealCoordinates) :
    flatProjection p x = flatProjection p y ↔ FlatCongruent x y := by
  change
    (Submodule.Quotient.mk (periodEquiv p x) : p.Torus) =
        Submodule.Quotient.mk (periodEquiv p y) ↔
      _
  rw [Submodule.Quotient.eq, ← map_sub, periodEquiv_mem_lattice_iff]
  rfl

@[simp]
theorem Elliptic.flatProjection_add (p : PeriodDomain) (x y : RealCoordinates) :
    flatProjection p (x + y) = flatProjection p x + flatProjection p y := by
  simp only [flatProjection, map_add]

@[simp]
theorem Elliptic.flatProjection_realCast (p : PeriodDomain) (v : PeriodLattice) :
    flatProjection p (realCast v) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero p.lattice).mpr
  exact (periodEquiv_mem_lattice_iff p _).mpr ⟨v, rfl⟩

theorem Elliptic.flatLinear_realCast (j : Kind) (v : PeriodLattice) :
    flatLinear j (realCast v) = realCast (j.matrix *ᵥ v) := by
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) j.matrix v i).symm

theorem Elliptic.flatLinear_fixes_realCast (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    flatLinear j (realCast v) = realCast v := by rw [flatLinear_realCast, hv]

theorem Elliptic.flatAffine_iterate (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) (r : ℕ)
    (x : RealCoordinates) :
    (flatAffine j v)^[r] x =
      (j.matrix.map (Int.castRingHom ℝ)) ^ r *ᵥ x + ((r : ℝ) / (j.order : ℝ)) • realCast v := by
  induction r with
  | zero => simp
  | succ r
    ih =>
    rw [Function.iterate_succ_apply', ih, flatAffine, map_add, map_smul,
      flatLinear_fixes_realCast j v hv]
    have hlin :
      flatLinear j ((j.matrix.map (Int.castRingHom ℝ)) ^ r *ᵥ x) =
        (j.matrix.map (Int.castRingHom ℝ)) ^ (r + 1) *ᵥ x := by
      simp only [flatLinear, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, pow_succ']
    rw [hlin, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

theorem Elliptic.flatAffine_iterate_order (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (x : RealCoordinates) : (flatAffine j v)^[j.order] x = x + realCast v := by
  rw [flatAffine_iterate j v hv, ← Matrix.map_pow, j.matrix_pow_order]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  simp [hm]

theorem Elliptic.flatAffine_iterate_order_congruent (j : Kind) (v : PeriodLattice)
    (hv : j.matrix *ᵥ v = v) (x : RealCoordinates) :
    FlatCongruent ((flatAffine j v)^[j.order] x) x := by
  refine ⟨v, ?_⟩
  rw [flatAffine_iterate_order j v hv]
  abel

@[simp]
theorem Elliptic.flatLinear_gamma (j : Kind) (x : RealCoordinates) : flatLinear j x 0 = x 0 := by
  cases j <;> simp [flatLinear, Kind.matrix, A₁, A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem Elliptic.flatAffine_iterate_gamma (j : Kind) (v : PeriodLattice) (r : ℕ) (x : RealCoordinates) :
    (flatAffine j v)^[r] x 0 = x 0 + ((r : ℝ) / (j.order : ℝ)) * (γ v : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change flatLinear j ((flatAffine j v)^[r] x) 0 + (1 / (j.order : ℝ)) * (γ v : ℝ) = _
    rw [flatLinear_gamma, ih]
    push_cast
    ring

theorem Elliptic.flatAffine_iterate_not_congruent (j : Kind) (v : PeriodLattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (x : RealCoordinates) :
    ¬FlatCongruent ((flatAffine j v)^[r] x) x := by
  rintro ⟨w, hw⟩
  have hgamma := congrFun hw 0
  change (flatAffine j v)^[r] x 0 - x 0 = (w 0 : ℝ) at hgamma
  rw [flatAffine_iterate_gamma] at hgamma
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hreal : (r : ℝ) * (γ v : ℝ) = (j.order : ℝ) * (w 0 : ℝ) := by
    field_simp at hgamma
    nlinarith
  have hint : (r : ℤ) * γ v = (j.order : ℤ) * w 0 := by exact_mod_cast hreal
  cases j with
  | three =>
    have ha : ¬3 ∣ γ v := by simpa [AdmissibleTwist] using hv.2
    change r < 3 at hrm
    change (r : ℤ) * γ v = 3 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega
  | four =>
    have ha : Odd (γ v) := by simpa [AdmissibleTwist] using hv.2
    rcases ha with ⟨a, ha⟩
    change r < 4 at hrm
    change (r : ℤ) * γ v = 4 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega

theorem Elliptic.bad_three_twist_has_fixed_point (v : PeriodLattice) (hv : A₁ *ᵥ v = v)
    (ha : (3 : ℤ) ∣ γ v) : ∃ x : RealCoordinates, FlatCongruent (flatAffine .three v x) x := by
  obtain ⟨h₁, h₂⟩ := (A₁_fixed_iff v).mp hv
  obtain ⟨m, hm⟩ := ha
  have hm' : (v 0 : ℝ) = 3 * (m : ℝ) := by exact_mod_cast hm
  refine ⟨![0, -(v 3 : ℝ) / 3, -((v 3 : ℝ) + 2 * (v 0 : ℝ)) / 3, 0], ![m, 0, v 3, 0], ?_⟩
  ext i
  fin_cases i <;>
      simp [flatAffine, flatLinear, Kind.matrix, Kind.order, A₁, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, realCast, h₁, h₂, hm'] <;>
    ring

theorem Elliptic.bad_four_twist_has_square_fixed_point (v : PeriodLattice) (hv : A₂ *ᵥ v = v)
    (ha : Even (γ v)) : ∃ x : RealCoordinates, FlatCongruent ((flatAffine .four v)^[2] x) x := by
  obtain ⟨h₁, h₂⟩ := (A₂_fixed_iff v).mp hv
  obtain ⟨m, hm⟩ := ha
  have hm' : (v 0 : ℝ) = 2 * (m : ℝ) := by
    change v 0 = m + m at hm
    exact_mod_cast (show v 0 = 2 * m by omega)
  refine ⟨![0, 3 * (v 0 : ℝ) / 4, -3 * (v 0 : ℝ) / 4 - (v 3 : ℝ) / 2, 0], ![m, 0, v 3, 0], ?_⟩
  ext i
  fin_cases i <;>
      simp [Function.iterate_succ_apply, flatAffine, flatLinear, Kind.matrix, Kind.order, A₂,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, realCast, h₁, h₂, hm'] <;>
    ring

theorem Elliptic.flatAffine_free_iff (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ,
        0 < r → r < j.order → ∀ x : RealCoordinates, ¬FlatCongruent ((flatAffine j v)^[r] x) x) ↔
      AdmissibleTwist j v := by
  constructor
  · intro hfree
    refine ⟨hv, ?_⟩
    cases j with
    | three =>
      change ¬3 ∣ γ v
      intro ha
      obtain ⟨x, hx⟩ := bad_three_twist_has_fixed_point v hv ha
      exact hfree 1 (by decide) (by decide) x (by simpa using hx)
    | four =>
      change Odd (γ v)
      apply Int.not_even_iff_odd.mp
      intro ha
      obtain ⟨x, hx⟩ := bad_four_twist_has_square_fixed_point v hv ha
      exact hfree 2 (by decide) (by decide) x hx
  · intro ha r hr hrm x
    exact flatAffine_iterate_not_congruent j v ha r hr hrm x

def Elliptic.periodStep (j : Kind) (p : PeriodDomain) : PeriodDomain :=
  match j with
  | .three => p.step₁
  | .four => p.step₂

abbrev Elliptic.FixedPeriod (j : Kind) :=
  { p : PeriodDomain // periodStep j p = p }

def Elliptic.examplePeriodPoint : Kind → PeriodPoint
  | .three =>
    ⟨(1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2, (1 : ℂ) / 2 - Complex.I * (Real.sqrt 3 : ℂ) / 6,
      -Complex.I⟩
  | .four => ⟨Complex.I, (1 - Complex.I) / 2, -Complex.I⟩

theorem Elliptic.examplePeriodPoint_tau_im_pos (j : Kind) : 0 < (examplePeriodPoint j).τ.im := by
  cases j
  · simp only [examplePeriodPoint, Complex.div_ofNat_im, Complex.add_im, Complex.one_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      MulZeroClass.zero_mul, one_mul, zero_add]
    positivity
  · norm_num [examplePeriodPoint]

@[simp]
theorem Elliptic.examplePeriodPoint_beta_im (j : Kind) : (examplePeriodPoint j).β.im = -1 := by
  cases j <;> norm_num [examplePeriodPoint]

theorem Elliptic.examplePeriodPoint_admissible (j : Kind) : (examplePeriodPoint j).Admissible := by
  refine ⟨examplePeriodPoint_tau_im_pos j, ?_⟩
  have hn : 0 ≤ 6 * (examplePeriodPoint j).μ.im ^ 2 / (examplePeriodPoint j).τ.im :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (examplePeriodPoint_tau_im_pos j).le
  rw [PeriodPoint.discriminant, examplePeriodPoint_beta_im]
  linarith

def Elliptic.examplePeriod (j : Kind) : PeriodDomain :=
  ⟨examplePeriodPoint j, examplePeriodPoint_admissible j⟩

theorem Elliptic.examplePeriodPoint_three_fixed :
    (examplePeriodPoint .three).step₁ = examplePeriodPoint .three := by
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have ht : 1 + Complex.I * (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  apply PeriodPoint.ext <;> dsimp [examplePeriodPoint, PeriodPoint.step₁] <;> field_simp [ht] <;>
        ring_nf <;>
      simp [Complex.I_sq, hs] <;>
    ring

theorem Elliptic.examplePeriodPoint_four_fixed :
    (examplePeriodPoint .four).step₂ = examplePeriodPoint .four := by
  apply PeriodPoint.ext <;> apply Complex.ext <;>
    norm_num [examplePeriodPoint, PeriodPoint.step₂, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]

theorem Elliptic.examplePeriod_fixed (j : Kind) :
    periodStep j (examplePeriod j) = examplePeriod j := by
  cases j
  · exact Subtype.ext examplePeriodPoint_three_fixed
  · exact Subtype.ext examplePeriodPoint_four_fixed

def Elliptic.exampleFixedPeriod (j : Kind) : FixedPeriod j :=
  ⟨examplePeriod j, examplePeriod_fixed j⟩

def Elliptic.linearMatrix (j : Kind) (p : PeriodDomain) : Matrix (Fin 2) (Fin 2) ℂ :=
  match j with
  | .three => p.val.R₁
  | .four => p.val.R₂

def Elliptic.linearEquiv (j : Kind) (p : FixedPeriod j) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  match j with
  | .three => p.val.R₁Equiv
  | .four => p.val.R₂Equiv

theorem Elliptic.linearEquiv_apply (j : Kind) (p : FixedPeriod j) (z : ComplexPlane₂) :
    linearEquiv j p z = linearMatrix j p.val *ᵥ z := by
  cases j
  · exact p.val.R₁Equiv_apply z
  · exact p.val.R₂Equiv_apply z

theorem Elliptic.linearEquiv_map_lattice (j : Kind) (p : FixedPeriod j) :
    p.val.lattice.map ((linearEquiv j p).toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.lattice := by
  cases j
  · exact p.val.R₁Equiv_map_lattice.trans (congrArg PeriodDomain.lattice p.property)
  · exact p.val.R₂Equiv_map_lattice.trans (congrArg PeriodDomain.lattice p.property)

theorem Elliptic.linearMatrix_period_matrix (j : Kind) (p : FixedPeriod j) :
    linearMatrix j p.val * p.val.val.matrix =
      p.val.val.matrix * j.matrix.map (Int.castRingHom ℂ) := by
  cases j
  · have hp : p.val.val.step₁ = p.val.val := congrArg Subtype.val p.property
    have hm := p.val.val.step₁_matrix (p.val.val.τ_ne_zero p.val.property.1)
    rw [hp] at hm
    have hTA : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
      have h : T₁.transpose * A₁ = 1 := by decide
      simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
        congrArg (fun A : LatticeMatrix => A.map (Int.castRingHom ℂ)) h
    simpa only [linearMatrix, Kind.matrix, Matrix.mul_assoc, hTA, Matrix.mul_one] using
      (congrArg (fun A => A * A₁.map (Int.castRingHom ℂ)) hm).symm
  · have hp : p.val.val.step₂ = p.val.val := congrArg Subtype.val p.property
    have hm := p.val.val.step₂_matrix (p.val.val.τ_ne_zero p.val.property.1)
    rw [hp] at hm
    have hTA : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
      have h : T₂.transpose * A₂ = 1 := by decide
      simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
        congrArg (fun A : LatticeMatrix => A.map (Int.castRingHom ℂ)) h
    simpa only [linearMatrix, Kind.matrix, Matrix.mul_assoc, hTA, Matrix.mul_one] using
      (congrArg (fun A => A * A₂.map (Int.castRingHom ℂ)) hm).symm

theorem Elliptic.flatLinear_complexCast (j : Kind) (x : RealCoordinates) :
    (fun i => ((flatLinear j x) i : ℂ)) =
      (j.matrix.map (Int.castRingHom ℂ)) *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [flatLinear, Matrix.mulVec, dotProduct]

theorem Elliptic.linearEquiv_periodEquiv (j : Kind) (p : FixedPeriod j) (x : RealCoordinates) :
    linearEquiv j p (periodEquiv p.val x) = periodEquiv p.val (flatLinear j x) := by
  rw [linearEquiv_apply, periodEquiv_matrix, periodEquiv_matrix, flatLinear_complexCast,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, linearMatrix_period_matrix]

def Elliptic.linearBiholomorph (j : Kind) (p : FixedPeriod j) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.val.Torus p.val.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.val.lattice p.val.lattice (linearEquiv j p)
    (linearEquiv_map_lattice j p)

@[simp]
theorem Elliptic.linearBiholomorph_mkQ (j : Kind) (p : FixedPeriod j) (z : ComplexPlane₂) :
    linearBiholomorph j p (p.val.lattice.mkQ z) = p.val.lattice.mkQ (linearEquiv j p z) :=
  rfl

theorem Elliptic.linearBiholomorph_flatProjection (j : Kind) (p : FixedPeriod j)
    (x : RealCoordinates) :
    linearBiholomorph j p (flatProjection p.val x) = flatProjection p.val (flatLinear j x) := by
  change linearBiholomorph j p (p.val.lattice.mkQ (periodEquiv p.val x)) = _
  rw [linearBiholomorph_mkQ, linearEquiv_periodEquiv]
  rfl

def Elliptic.torusTranslation (p : PeriodDomain) (a : p.Torus) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.Torus p.Torus ω
    where
  toFun x := x + a
  invFun x := x - a
  left_inv x := add_sub_cancel_right x a
  right_inv x := sub_add_cancel x a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

def Elliptic.affineBiholomorph (j : Kind) (p : FixedPeriod j) (v : PeriodLattice) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.val.Torus p.val.Torus ω :=
  (linearBiholomorph j p).trans
    (torusTranslation p.val (flatProjection p.val ((1 / (j.order : ℝ)) • realCast v)))

theorem Elliptic.affineBiholomorph_apply (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (x : p.val.Torus) :
    affineBiholomorph j p v x =
      linearBiholomorph j p x + flatProjection p.val ((1 / (j.order : ℝ)) • realCast v) :=
  rfl

theorem Elliptic.affineBiholomorph_flatProjection (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (x : RealCoordinates) :
    affineBiholomorph j p v (flatProjection p.val x) = flatProjection p.val (flatAffine j v x) := by
  rw [affineBiholomorph_apply, linearBiholomorph_flatProjection, flatAffine, flatProjection_add]

theorem Elliptic.affineBiholomorph_iterate_flatProjection (j : Kind) (p : FixedPeriod j)
    (v : PeriodLattice) (r : ℕ) (x : RealCoordinates) :
    (affineBiholomorph j p v)^[r] (flatProjection p.val x) =
      flatProjection p.val ((flatAffine j v)^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      affineBiholomorph_flatProjection]

def Elliptic.affinePermutation (j : Kind) (p : FixedPeriod j) (v : PeriodLattice) :
    Equiv.Perm p.val.Torus :=
  (affineBiholomorph j p v).toEquiv

theorem Elliptic.affinePermutation_pow_flatProjection (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (r : ℕ) (x : RealCoordinates) :
    (affinePermutation j p v ^ r) (flatProjection p.val x) =
      flatProjection p.val ((flatAffine j v)^[r] x) := by
  rw [Equiv.Perm.coe_pow]
  exact affineBiholomorph_iterate_flatProjection j p v r x

theorem Elliptic.affinePermutation_pow_order (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (hv : j.matrix *ᵥ v = v) : affinePermutation j p v ^ j.order = 1 := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := flatProjection_surjective p.val y
  change (affinePermutation j p v ^ j.order) (flatProjection p.val x) = flatProjection p.val x
  rw [affinePermutation_pow_flatProjection]
  exact (flatProjection_eq_iff p.val _ _).mpr (flatAffine_iterate_order_congruent j v hv x)

theorem Elliptic.affinePermutation_pow_ne (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (y : p.val.Torus) :
    (affinePermutation j p v ^ r) y ≠ y := by
  obtain ⟨x, rfl⟩ := flatProjection_surjective p.val y
  rw [affinePermutation_pow_flatProjection]
  exact fun h =>
    flatAffine_iterate_not_congruent j v hv r hr hrm x ((flatProjection_eq_iff p.val _ _).mp h)

theorem Elliptic.affinePermutation_free_iff (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (hv : j.matrix *ᵥ v = v) :
    (∀ r, 0 < r → r < j.order → ∀ y : p.val.Torus, (affinePermutation j p v ^ r) y ≠ y) ↔
      AdmissibleTwist j v := by
  constructor
  · intro h
    apply (flatAffine_free_iff j v hv).mp
    intro r hr hrm x hx
    apply h r hr hrm (flatProjection p.val x)
    rw [affinePermutation_pow_flatProjection]
    exact (flatProjection_eq_iff p.val _ _).mpr hx
  · intro ha
    exact affinePermutation_pow_ne j p v ha

private theorem Elliptic.sum_zsmul_basisFun_mo1973_9836 (v : PeriodLattice) :
    (∑ i, v i • Pi.basisFun ℝ (Fin 4) i) = realCast v := by
  ext k
  simp [Pi.basisFun_apply, realCast, Pi.single_apply]

theorem Elliptic.standardLattice_mem_iff (x : RealCoordinates) :
    x ∈ standardLattice ↔ ∃ v : PeriodLattice, x = realCast v := by
  rw [standardLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hv.symm.trans (sum_zsmul_basisFun_mo1973_9836 v)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, sum_zsmul_basisFun_mo1973_9836 v⟩

theorem Elliptic.flatTorus_mkQ_eq_iff (x y : RealCoordinates) :
    standardLattice.mkQ x = standardLattice.mkQ y ↔ FlatCongruent x y := by
  change (Submodule.Quotient.mk x : RealTorus₄) = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq, standardLattice_mem_iff]
  rfl

theorem Elliptic.periodEquiv_map_standardLattice (p : PeriodDomain) :
    standardLattice.map ((periodEquiv p).toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.lattice := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (periodEquiv_mem_lattice_iff p x).mpr ((standardLattice_mem_iff x).mp hx)
  · intro hz
    refine ⟨(periodEquiv p).symm z, ?_, (periodEquiv p).apply_symm_apply z⟩
    apply (standardLattice_mem_iff _).mpr
    apply (periodEquiv_mem_lattice_iff p _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz

def Elliptic.flatTorusPeriodHomeomorph (p : PeriodDomain) : RealTorus₄ ≃ₜ p.Torus
    where
  toEquiv :=
    (Submodule.Quotient.equiv standardLattice p.lattice
        ((periodEquiv p).toLinearEquiv.restrictScalars ℤ)
        (periodEquiv_map_standardLattice p)).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact p.lattice.continuous_mkQ.comp (periodEquiv p).continuous
  continuous_invFun := by
    apply p.lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp (periodEquiv p).symm.continuous

@[simp]
theorem Elliptic.flatTorusPeriodHomeomorph_mkQ (p : PeriodDomain) (x : RealCoordinates) :
    flatTorusPeriodHomeomorph p (standardLattice.mkQ x) = flatProjection p x :=
  rfl

@[simp]
theorem Elliptic.flatTorusPeriodHomeomorph_symm_flatProjection (p : PeriodDomain)
    (x : RealCoordinates) :
    (flatTorusPeriodHomeomorph p).symm (flatProjection p x) = standardLattice.mkQ x := by
  rw [← flatTorusPeriodHomeomorph_mkQ, Homeomorph.symm_apply_apply]

def Elliptic.flatTorusAffine (j : Kind) (v : PeriodLattice) : RealTorus₄ ≃ₜ RealTorus₄ :=
  ((flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).trans
        (affineBiholomorph j (exampleFixedPeriod j) v).toHomeomorph).trans
    (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).symm

@[simp]
theorem Elliptic.flatTorusAffine_mkQ (j : Kind) (v : PeriodLattice) (x : RealCoordinates) :
    flatTorusAffine j v (standardLattice.mkQ x) = standardLattice.mkQ (flatAffine j v x) := by
  change
    (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).symm
        (affineBiholomorph j (exampleFixedPeriod j) v
          (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val (standardLattice.mkQ x))) =
      _
  rw [flatTorusPeriodHomeomorph_mkQ, affineBiholomorph_flatProjection,
    flatTorusPeriodHomeomorph_symm_flatProjection]

theorem Elliptic.flatTorusAffine_periodHomeomorph (j : Kind) (p : FixedPeriod j) (v : PeriodLattice)
    (y : RealTorus₄) :
    flatTorusPeriodHomeomorph p.val (flatTorusAffine j v y) =
      affineBiholomorph j p v (flatTorusPeriodHomeomorph p.val y) := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_mkQ, flatTorusPeriodHomeomorph_mkQ, flatTorusPeriodHomeomorph_mkQ,
    affineBiholomorph_flatProjection]

theorem Elliptic.flatTorusAffine_iterate_mkQ (j : Kind) (v : PeriodLattice) (r : ℕ)
    (x : RealCoordinates) :
    (flatTorusAffine j v)^[r] (standardLattice.mkQ x) =
      standardLattice.mkQ ((flatAffine j v)^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, flatTorusAffine_mkQ]

theorem Elliptic.flatTorusAffine_iterate_order (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v)
    (y : RealTorus₄) : (flatTorusAffine j v)^[j.order] y = y := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_iterate_mkQ]
  exact (flatTorus_mkQ_eq_iff _ _).mpr (flatAffine_iterate_order_congruent j v hv x)

theorem Elliptic.flatTorusAffine_iterate_ne (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (y : RealTorus₄) : (flatTorusAffine j v)^[r] y ≠ y :=
  by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_iterate_mkQ]
  exact fun h =>
    flatAffine_iterate_not_congruent j v hv r hr hrm x ((flatTorus_mkQ_eq_iff _ _).mp h)

def Elliptic.flatTorusPermutation (j : Kind) (v : PeriodLattice) : Equiv.Perm RealTorus₄ :=
  (flatTorusAffine j v).toEquiv

theorem Elliptic.flatTorusPermutation_pow_mkQ (j : Kind) (v : PeriodLattice) (r : ℕ)
    (x : RealCoordinates) :
    (flatTorusPermutation j v ^ r) (standardLattice.mkQ x) =
      standardLattice.mkQ ((flatAffine j v)^[r] x) := by
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_mkQ j v r x

theorem Elliptic.flatTorusPermutation_pow_order (j : Kind) (v : PeriodLattice)
    (hv : j.matrix *ᵥ v = v) : flatTorusPermutation j v ^ j.order = 1 := by
  apply Equiv.ext
  intro y
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_order j v hv y

theorem Elliptic.flatTorusPermutation_pow_ne (j : Kind) (v : PeriodLattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (y : RealTorus₄) :
    (flatTorusPermutation j v ^ r) y ≠ y := by
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_ne j v hv r hr hrm y

theorem Elliptic.flatTorusPermutation_free_iff (j : Kind) (v : PeriodLattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ y : RealTorus₄, (flatTorusPermutation j v ^ r) y ≠ y) ↔
      AdmissibleTwist j v := by
  constructor
  · intro h
    apply (flatAffine_free_iff j v hv).mp
    intro r hr hrm x hx
    apply h r hr hrm (standardLattice.mkQ x)
    rw [flatTorusPermutation_pow_mkQ]
    exact (flatTorus_mkQ_eq_iff _ _).mpr hx
  · intro ha
    exact flatTorusPermutation_pow_ne j v ha

def SpecialPeriods.CuspFamily.cuspIntegralMatrix (k : ℤ) : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, k, 1, 0; -k, 0, 0, 1]

@[simp]
theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_zero : cuspIntegralMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspIntegralMatrix]

@[simp]
theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_one : cuspIntegralMatrix 1 = M₀ :=
  rfl

/-- The integral cusp family is the exchange generated by the dual-cusp nilpotent. -/
theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_toLin_eq_exchange (k : ℤ) :
    Matrix.toLin' (cuspIntegralMatrix k) =
      Module.End.oneAddSMul dualCuspN k := by
  ext x i
  fin_cases x <;> fin_cases i <;>
    norm_num [cuspIntegralMatrix, Module.End.oneAddSMul, dualCuspN, M₀,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Module.End.one_eq_id,
      Pi.single_apply]

theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_add (k l : ℤ) :
    cuspIntegralMatrix (k + l) = cuspIntegralMatrix k * cuspIntegralMatrix l := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, cuspIntegralMatrix_toLin_eq_exchange,
    cuspIntegralMatrix_toLin_eq_exchange, cuspIntegralMatrix_toLin_eq_exchange]
  exact (Module.End.oneAddSMul_mul_oneAddSMul
    dualCuspN_square_zero k l).symm

/-- The real base change of the cusp matrix is the exchange generated by the
scalar-extended dual-cusp nilpotent. -/
theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_real_toLin_eq_exchange (k : ℤ) :
    Matrix.toLin' ((cuspIntegralMatrix k).map (Int.castRingHom ℝ)) =
      Module.End.oneAddSMul dualCuspNReal (k : ℝ) := by
  apply LinearMap.ext
  intro x
  rw [Module.End.oneAddSMul_apply, dualCuspNReal_apply]
  ext i
  fin_cases i <;>
    simp [cuspIntegralMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

def SpecialPeriods.CuspFamily.cuspRealEquiv (k : ℤ) : RealPlane₄ ≃ₗ[ℝ] RealPlane₄ :=
  Module.End.oneAddSMulEquiv
    dualCuspNReal dualCuspNReal_square_zero (k : ℝ)

theorem SpecialPeriods.CuspFamily.cuspRealEquiv_apply (k : ℤ) (x : RealPlane₄) :
    cuspRealEquiv k x = (cuspIntegralMatrix k).map (Int.castRingHom ℝ) *ᵥ x := by
  simpa [cuspRealEquiv] using
    DFunLike.congr_fun (cuspIntegralMatrix_real_toLin_eq_exchange k).symm x

@[simp]
theorem SpecialPeriods.CuspFamily.cuspRealEquiv_zero :
    cuspRealEquiv 0 = LinearEquiv.refl ℝ RealPlane₄ := by
  apply LinearEquiv.ext
  intro x
  simp [cuspRealEquiv]

theorem SpecialPeriods.CuspFamily.cuspRealEquiv_add_apply (k l : ℤ) (x : RealPlane₄) :
    cuspRealEquiv (k + l) x = cuspRealEquiv k (cuspRealEquiv l x) := by
  simpa [cuspRealEquiv, Module.End.mul_apply] using
    DFunLike.congr_fun
      (Module.End.oneAddSMul_mul_oneAddSMul dualCuspNReal_square_zero
        (k : ℝ) (l : ℝ)).symm x

@[simp]
theorem SpecialPeriods.CuspFamily.cuspRealEquiv_neg (k : ℤ) :
    cuspRealEquiv (-k) = (cuspRealEquiv k).symm := by
  apply LinearEquiv.ext
  intro x
  change Module.End.oneAddSMul dualCuspNReal ((-k : ℤ) : ℝ) x =
    Module.End.oneAddSMul dualCuspNReal (-(k : ℝ)) x
  rw [Int.cast_neg]

theorem SpecialPeriods.CuspFamily.cuspRealEquiv_realCast (k : ℤ) (v : PeriodLattice) :
    cuspRealEquiv k (Elliptic.realCast v) = Elliptic.realCast (cuspIntegralMatrix k *ᵥ v) := by
  rw [cuspRealEquiv_apply]
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) (cuspIntegralMatrix k) v i).symm

theorem SpecialPeriods.CuspFamily.cuspRealEquiv_complexCast (k : ℤ) (x : RealPlane₄) :
    (fun i => ((cuspRealEquiv k x) i : ℂ)) =
      (cuspIntegralMatrix k).map (Int.castRingHom ℂ) *ᵥ (fun i => (x i : ℂ)) := by
  rw [cuspRealEquiv_apply]
  ext i
  fin_cases i <;>
    simp [cuspIntegralMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem SpecialPeriods.CuspFamily.cuspRealEquiv_mem_standardLattice (k : ℤ) {x : RealPlane₄}
    (hx : x ∈ standardLattice) : cuspRealEquiv k x ∈ standardLattice := by
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact
    (Elliptic.standardLattice_mem_iff _).mpr
      ⟨cuspIntegralMatrix k *ᵥ v, cuspRealEquiv_realCast k v⟩

theorem SpecialPeriods.CuspFamily.cuspRealEquiv_map_standardLattice (k : ℤ) :
    standardLattice.map ((cuspRealEquiv k).restrictScalars ℤ).toLinearMap = standardLattice := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact cuspRealEquiv_mem_standardLattice k hy
  · intro hx
    refine ⟨cuspRealEquiv (-k) x, cuspRealEquiv_mem_standardLattice (-k) hx, ?_⟩
    change cuspRealEquiv k (cuspRealEquiv (-k) x) = x
    rw [cuspRealEquiv_neg, LinearEquiv.apply_symm_apply]

def SpecialPeriods.CuspFamily.cuspTorusLinearEquiv (k : ℤ) : RealTorus₄ ≃ₗ[ℤ] RealTorus₄ :=
  Submodule.Quotient.equiv standardLattice standardLattice ((cuspRealEquiv k).restrictScalars ℤ)
    (cuspRealEquiv_map_standardLattice k)

def SpecialPeriods.CuspFamily.cuspTorusHomeomorph (k : ℤ) : RealTorus₄ ≃ₜ RealTorus₄
    where
  toEquiv := (cuspTorusLinearEquiv k).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp (cuspRealEquiv k).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp
        (cuspRealEquiv k).symm.toContinuousLinearEquiv.continuous

@[simp]
theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ (k : ℤ) (x : RealPlane₄) :
    cuspTorusHomeomorph k (standardLattice.mkQ x) = standardLattice.mkQ (cuspRealEquiv k x) :=
  rfl

@[simp]
theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_apply (x : RealTorus₄) :
    cuspTorusHomeomorph 0 x = x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_zero]
  rfl

@[simp]
theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_eq :
    cuspTorusHomeomorph 0 = Homeomorph.refl RealTorus₄ := by
  apply Homeomorph.ext
  exact cuspTorusHomeomorph_zero_apply

theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_add_apply (k l : ℤ) (x : RealTorus₄) :
    cuspTorusHomeomorph (k + l) x = cuspTorusHomeomorph k (cuspTorusHomeomorph l x) := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, cuspTorusHomeomorph_mkQ, cuspTorusHomeomorph_mkQ,
    cuspRealEquiv_add_apply]

@[instance_reducible]
def SpecialPeriods.CuspFamily.cuspTorusAction : MulAction (Multiplicative ℤ) RealTorus₄
    where
  smul k x := cuspTorusHomeomorph k.toAdd x
  one_smul := cuspTorusHomeomorph_zero_apply
  mul_smul k l := cuspTorusHomeomorph_add_apply k.toAdd l.toAdd

@[simp]
theorem SpecialPeriods.CuspFamily.cusp_exponential_sub_int (s : ℂ) (k : ℤ) :
    CuspUniformization.exponential (s - (k : ℂ)) = CuspUniformization.exponential s := by
  rw [sub_eq_add_neg, ← Int.cast_neg, CuspUniformization.exponential_add,
    CuspUniformization.exponential_int, mul_one]

theorem SpecialPeriods.CuspFamily.cuspPeriodPoint_matrix_covariance (μ b h : ℂ → ℂ) (s : ℂ)
    (k : ℤ) :
    (SpecialPeriods.cuspPeriodPoint μ b h (s - (k : ℂ))).matrix *
        (cuspIntegralMatrix k).map (Int.castRingHom ℂ) =
      (SpecialPeriods.cuspPeriodPoint μ b h s).matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
      simp [PeriodPoint.matrix, SpecialPeriods.cuspPeriodPoint, cuspIntegralMatrix,
        Matrix.mul_apply, Fin.sum_univ_four, cusp_exponential_sub_int] <;>
    ring

@[simp]
theorem CuspUniformization.exponential_add_int (s : ℂ) (k : ℤ) :
    exponential (s + k) = exponential s := by rw [exponential_add, exponential_int, mul_one]

theorem CuspUniformization.logarithmicPeriod_mulVec_add_int (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (k : ℤ) (n : Fin 2 → ℤ) :
    logarithmicPeriod C (s + k) *ᵥ (fun i => (n i : ℂ)) =
      logarithmicPeriod C s *ᵥ (fun i => (n i : ℂ)) + fun i =>
        (k : ℂ) * (ToricSpace.cuspVector n i : ℂ) := by
  ext i
  simp only [Pi.add_apply, logarithmicPeriod_apply, exponential_add_int]
  ring

@[ext]
structure CuspUniformization.LogDeck where
  k : ℤ
  m : Fin 2 → ℤ
  n : Fin 2 → ℤ
  deriving DecidableEq

instance CuspUniformization.LogDeck.instLocal1 : One CuspUniformization.LogDeck :=
  ⟨⟨0, 0, 0⟩⟩

instance CuspUniformization.LogDeck.instLocal2 : Mul CuspUniformization.LogDeck :=
  ⟨fun g h => ⟨g.k + h.k, g.m + h.m + h.k • ToricSpace.cuspVector g.n, g.n + h.n⟩⟩

instance CuspUniformization.LogDeck.instLocal3 : Inv CuspUniformization.LogDeck :=
  ⟨fun g => ⟨-g.k, -g.m + g.k • ToricSpace.cuspVector g.n, -g.n⟩⟩

@[simp]
theorem CuspUniformization.LogDeck.mul_k (g h : CuspUniformization.LogDeck) :
    (g * h).k = g.k + h.k :=
  rfl

@[simp]
theorem CuspUniformization.LogDeck.mul_m (g h : CuspUniformization.LogDeck) :
    (g * h).m = g.m + h.m + h.k • ToricSpace.cuspVector g.n :=
  rfl

@[simp]
theorem CuspUniformization.LogDeck.mul_n (g h : CuspUniformization.LogDeck) :
    (g * h).n = g.n + h.n :=
  rfl

instance CuspUniformization.LogDeck.instLocal4 : Group CuspUniformization.LogDeck
    where
  mul_assoc g h
    l := by
    apply CuspUniformization.LogDeck.ext
    · simp only [mul_k, add_assoc]
    · simp only [mul_m, mul_k, mul_n, ToricSpace.cuspVector_add, smul_add, add_smul]
      abel
    · simp only [mul_n, add_assoc]
  one_mul
    g := by
    have hone : (1 : CuspUniformization.LogDeck) = ⟨0, 0, 0⟩ := rfl
    apply CuspUniformization.LogDeck.ext <;> simp [hone]
  mul_one
    g := by
    have hone : (1 : CuspUniformization.LogDeck) = ⟨0, 0, 0⟩ := rfl
    apply CuspUniformization.LogDeck.ext <;> simp [hone]
  inv_mul_cancel
    g := by
    have hone : (1 : CuspUniformization.LogDeck) = ⟨0, 0, 0⟩ := rfl
    have hinv : g⁻¹ = ⟨-g.k, -g.m + g.k • ToricSpace.cuspVector g.n, -g.n⟩ := rfl
    apply CuspUniformization.LogDeck.ext
    · simp [hone, hinv]
    · ext i
      fin_cases i <;> simp [hone, hinv, ToricSpace.cuspVector]
    · simp [hone, hinv]

def CuspUniformization.logDeckTransform (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck)
    (x : ℂ × ComplexPlane₂) : ℂ × ComplexPlane₂ :=
  (x.1 + g.k, x.2 + (fun i => (g.m i : ℂ)) + logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)))

@[simp]
theorem CuspUniformization.logDeckTransform_fst (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck)
    (x : ℂ × ComplexPlane₂) : (logDeckTransform C g x).1 = x.1 + g.k :=
  rfl

@[simp]
theorem CuspUniformization.logDeckTransform_snd (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g : LogDeck)
    (x : ℂ × ComplexPlane₂) :
    (logDeckTransform C g x).2 =
      x.2 + (fun i => (g.m i : ℂ)) + logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)) :=
  rfl

@[simp]
theorem CuspUniformization.logDeckTransform_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ℂ × ComplexPlane₂) : logDeckTransform C 1 x = x := by
  have hone : (1 : LogDeck) = ⟨0, 0, 0⟩ := rfl
  apply Prod.ext
  · simp [hone, logDeckTransform]
  · ext i
    fin_cases i <;> simp [hone, logDeckTransform, Matrix.vecHead, Matrix.vecTail]

theorem CuspUniformization.logDeckTransform_mul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (g h : LogDeck)
    (x : ℂ × ComplexPlane₂) :
    logDeckTransform C (g * h) x = logDeckTransform C g (logDeckTransform C h x) := by
  apply Prod.ext
  · simp only [logDeckTransform_fst, LogDeck.mul_k, Int.cast_add]
    ring
  · ext i
    simp only [logDeckTransform_snd, logDeckTransform_fst, LogDeck.mul_m, LogDeck.mul_n,
      logarithmicPeriod_mulVec_add_int, Pi.add_apply, Pi.smul_apply]
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_id]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem CuspUniformization.logDeckTransform_eq_self_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (g : LogDeck) (x : ℂ × ComplexPlane₂)
    (hP : Function.Bijective ((logarithmicPeriod C x.1).map Complex.im).mulVecLin) :
    logDeckTransform C g x = x ↔ g = 1 := by
  constructor
  · intro hx
    have hk : g.k = 0 := by
      have he := congrArg Prod.fst hx
      have he' : (g.k : ℂ) = 0 := by simpa only [logDeckTransform_fst, add_eq_left] using he
      exact_mod_cast he'
    let p : FullPeriodMatrix := ⟨logarithmicPeriod C x.1, hP⟩
    have he : p.periodLinear ((fun i => (g.m i : ℝ)), fun i => (g.n i : ℝ)) = p.periodLinear 0 := by
      have hs : (fun i => (g.m i : ℂ)) + logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)) = 0 := by
        have hs := congrArg Prod.snd hx
        simpa only [logDeckTransform_snd, add_assoc, add_eq_left] using hs
      rw [map_zero]
      ext i
      simpa [FullPeriodMatrix.periodLinear, p] using congrFun hs i
    have he' := p.periodLinear_bijective.injective he
    apply LogDeck.ext hk
    · ext i
      have hm := congrFun (congrArg Prod.fst he') i
      change (g.m i : ℝ) = 0 at hm
      change g.m i = 0
      exact_mod_cast hm
    · ext i
      have hn := congrFun (congrArg Prod.snd he') i
      change (g.n i : ℝ) = 0 at hn
      change g.n i = 0
      exact_mod_cast hn
  · rintro rfl
    exact logDeckTransform_one C x

theorem CuspUniformization.logDeckTransform_mem_logDomain (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (g : LogDeck) (x : ℂ × ComplexPlane₂) :
    logDeckTransform C g x ∈ logDomain ε ↔ x ∈ logDomain ε := by simp

def CuspUniformization.logCoverTransform (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (g : LogDeck)
    (x : LogCover ε) : LogCover ε :=
  ⟨logDeckTransform C g x, (logDeckTransform_mem_logDomain C ε g x).mpr x.2⟩

@[simp]
theorem CuspUniformization.logCoverTransform_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (g : LogDeck) (x : LogCover ε) :
    (logCoverTransform C ε g x : ℂ × ComplexPlane₂) = logDeckTransform C g x :=
  rfl

@[instance_reducible]
def CuspUniformization.logCoverAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    MulAction LogDeck (LogCover ε)
    where
  smul := logCoverTransform C ε
  one_smul x := Subtype.ext (logDeckTransform_one C x)
  mul_smul g h x := Subtype.ext (logDeckTransform_mul C g h x)

theorem CuspUniformization.logarithmicPeriod_logDomain_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (i j : Fin 2) :
    ContDiffOn ℂ ω (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 i j) (logDomain ε) := by
  have he : ContDiff ℂ ω (fun x : ℂ × ComplexPlane₂ => exponential x.1) :=
    exponential_holomorphic.comp contDiff_fst
  change
    ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ =>
        x.1 * (B₀.map (Int.castRingHom ℂ)) i j + C (exponential x.1) i j)
      _
  exact
    (contDiff_fst.mul contDiff_const).contDiffOn.add
      ((hC i j).comp he.contDiffOn (fun x hx => hx))

theorem CuspUniformization.logarithmicPeriod_logDomain_mulVec_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (n : Fin 2 → ℤ) :
    ContDiffOn ℂ ω (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 *ᵥ (fun i => (n i : ℂ)))
      (logDomain ε) := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact
    ((logarithmicPeriod_logDomain_holomorphic C ε hC i 0).mul contDiffOn_const).add
      ((logarithmicPeriod_logDomain_holomorphic C ε hC i 1).mul contDiffOn_const)

theorem CuspUniformization.logDeckTransform_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (g : LogDeck) :
    ContDiffOn ℂ ω (logDeckTransform C g) (logDomain ε) := by
  have hv :
    ContDiffOn ℂ ω
      (fun x : ℂ × ComplexPlane₂ => logarithmicPeriod C x.1 *ᵥ (fun i => (g.n i : ℂ)))
      (logDomain ε) :=
    logarithmicPeriod_logDomain_mulVec_holomorphic C ε hC g.n
  exact
    (contDiff_fst.add contDiff_const).contDiffOn.prodMk
      ((contDiff_snd.add contDiff_const).contDiffOn.add hv)

theorem CuspUniformization.logCover_action_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) (g : LogDeck) :
    letI := logCoverAction C ε
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun x : LogCover ε => g • x) := by
  let := logCoverAction C ε
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
        (fun y : LogCover ε => ((g • y : LogCover ε) : ℂ × ComplexPlane₂)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun y : LogCover ε => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  have h := (logDeckTransform_holomorphic C ε hC g).contMDiffOn
  exact
    (h.contMDiffAt ((logDomain ε).isOpen.mem_nhds x.2)).comp x contMDiff_subtype_val.contMDiffAt

theorem CuspUniformization.logCover_continuousConstSMul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    letI := logCoverAction C ε
    ContinuousConstSMul LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  exact ⟨fun g => (logCover_action_holomorphic C ε hC g).continuous⟩

theorem CuspUniformization.logCover_free_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift C ε) :
    letI := logCoverAction C ε
    IsCancelSMul LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  have hs : ‖exponential x.1.1‖ < ε := (mem_logDomain ε x).mp x.2
  have hp : 0 < ‖exponential x.1.1‖ := norm_pos_iff.mpr (exponential_ne_zero _)
  apply
    (logDeckTransform_eq_self_iff C g x
        (logarithmicPeriod_nondegenerate C x.1.1 (Real.log_neg hp (hs.trans hε1))
          (hR _ hp hs))).mp
  exact congrArg Subtype.val hx

theorem CuspUniformization.totalPeriodRelated_iff_exists_logDeck
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (p q : ℂ × ComplexPlane₂) :
    TotalPeriodRelated C p q ↔ ∃ g : LogDeck, logDeckTransform C g q = p := by
  constructor
  · rintro ⟨k, m, n, hs, hz⟩
    exact ⟨⟨k, m, n⟩, Prod.ext hs.symm hz.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.k, g.m, g.n, (congrArg Prod.fst hg).symm, (congrArg Prod.snd hg).symm⟩

theorem CuspUniformization.puncturedCuspCover_eq_iff_orbit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p q : LogCover ε) :
    letI := logCoverAction C ε
    puncturedCuspCover C ε p = puncturedCuspCover C ε q ↔ p ∈ MulAction.orbit LogDeck q := by
  let := logCoverAction C ε
  rw [puncturedCuspCover_eq_iff, totalPeriodRelated_iff_exists_logDeck]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

@[instance_reducible]
def SpecialPeriods.CuspFamily.Data.totalAction (D : SpecialPeriods.CuspFamily.Data) :
    MulAction (Multiplicative ℤ) D.TotalSpace := by
  let := SpecialPeriods.CuspFamily.logBaseAction D.radius
  let := SpecialPeriods.CuspFamily.cuspTorusAction
  exact
    inferInstanceAs
      (MulAction (Multiplicative ℤ) (SpecialPeriods.CuspFamily.LogBase D.radius × RealTorus₄))

theorem SpecialPeriods.CuspFamily.Data.totalAction_continuous
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.totalAction
    ContinuousConstSMul (Multiplicative ℤ) D.TotalSpace := by
  let := D.totalAction
  constructor
  intro k
  exact
    ((SpecialPeriods.CuspFamily.logBaseTranslate_holomorphic D.radius k.toAdd).continuous.comp
          continuous_fst).prodMk
      ((SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd).continuous.comp continuous_snd)

theorem SpecialPeriods.CuspFamily.Data.periodEquiv_matrix (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv s x = (D.periods.point s).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem SpecialPeriods.CuspFamily.Data.periodEquiv_monodromy (D : SpecialPeriods.CuspFamily.Data)
    (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k s)
        (SpecialPeriods.CuspFamily.cuspRealEquiv k x) =
      D.periods.periodEquiv s x := by
  rw [D.periodEquiv_matrix, SpecialPeriods.CuspFamily.cuspRealEquiv_complexCast,
    Matrix.mulVec_mulVec, D.periodEquiv_matrix]
  change
    ((SpecialPeriods.cuspPeriodPoint D.μ D.b D.h ((s : ℂ) - (k : ℂ))).matrix *
          (SpecialPeriods.CuspFamily.cuspIntegralMatrix k).map (Int.castRingHom ℂ)) *ᵥ
        (fun i => (x i : ℂ)) =
      _
  rw [SpecialPeriods.CuspFamily.cuspPeriodPoint_matrix_covariance]
  rfl

theorem SpecialPeriods.CuspFamily.Data.periodEquiv_symm_monodromy
    (D : SpecialPeriods.CuspFamily.Data) (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (z : ComplexPlane₂) :
    (D.periods.periodEquiv (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k s)).symm z =
      SpecialPeriods.CuspFamily.cuspRealEquiv k ((D.periods.periodEquiv s).symm z) := by
  apply
    (D.periods.periodEquiv (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k s)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_monodromy, LinearEquiv.apply_symm_apply]

def SpecialPeriods.CuspFamily.Data.complexLift (D : SpecialPeriods.CuspFamily.Data)
    (k : Multiplicative ℤ) (x : SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂) :
    SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂ :=
  (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1, x.2)

theorem SpecialPeriods.CuspFamily.Data.complexLift_quotientMap
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ)
    (x : SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂) :
    letI := D.totalAction
    D.periods.quotientMap (D.complexLift k x) = k • D.periods.quotientMap x := by
  let := D.totalAction
  change
    (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1,
        standardLattice.mkQ
          ((D.periods.periodEquiv
                (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1)).symm
            x.2)) =
      (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1,
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd
          (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [D.periodEquiv_symm_monodromy, SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ]

theorem SpecialPeriods.CuspFamily.Data.complexLift_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (D.complexLift k) := by
  rw [modelWithCornersSelf_prod]
  exact
    ((SpecialPeriods.CuspFamily.logBaseTranslate_holomorphic D.radius k.toAdd).comp
          contMDiff_fst).prodMk
      contMDiff_snd

theorem SpecialPeriods.CuspFamily.Data.totalAction_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) :
    letI := D.periods.totalChartedSpace
    letI := D.totalAction
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun x : D.TotalSpace => k • x) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  let := D.periods.coveringAction
  apply
    CoveringQuotient.contMDiff_of_comp D.periods.quotientCoveringMap
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
  have hf := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic k)
  exact hf.congr (fun x => (D.complexLift_quotientMap k x).symm)

theorem SpecialPeriods.CuspFamily.Data.familyCover_logarithmicShift
    (D : SpecialPeriods.CuspFamily.Data) (k : ℤ) (x : CuspUniformization.LogCover D.radius) :
    letI := D.totalAction
    D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius ⟨k, 0, 0⟩ x) =
      Multiplicative.ofAdd (-k) • D.familyCover x := by
  let := D.totalAction
  have he :
    SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius
        (CuspUniformization.logCoverTransform D.correction D.radius ⟨k, 0, 0⟩ x) =
      D.complexLift (Multiplicative.ofAdd (-k))
        (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius x) := by
    apply Prod.ext
    · apply Subtype.ext
      change x.1.1 + (k : ℂ) = x.1.1 - ((-k : ℤ) : ℂ)
      simp only [Int.cast_neg, sub_neg_eq_add]
    · simp only [SpecialPeriods.CuspFamily.logCoverProductEquiv_snd,
        CuspUniformization.logCoverTransform_coe, CuspUniformization.logDeckTransform_snd,
        Pi.zero_apply, Int.cast_zero, ofAdd_neg]
      change
        x.1.2 + (0 : ComplexPlane₂) +
            CuspUniformization.logarithmicPeriod D.correction x.1.1 *ᵥ 0 =
          x.1.2
      rw [add_zero, Matrix.mulVec_zero, add_zero]
  change D.periods.quotientMap (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius _) = _
  rw [he, D.complexLift_quotientMap]
  rfl

theorem SpecialPeriods.CuspFamily.Data.familyCover_period (D : SpecialPeriods.CuspFamily.Data)
    (m n : Fin 2 → ℤ) (x : CuspUniformization.LogCover D.radius) :
    D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius ⟨0, m, n⟩ x) =
      D.familyCover x := by
  apply (D.familyCover_eq_iff _ x).mpr
  refine ⟨?_, m, n, rfl⟩
  change x.1.1 + ((0 : ℤ) : ℂ) = x.1.1
  simp

theorem SpecialPeriods.CuspFamily.Data.familyCover_logDeck (D : SpecialPeriods.CuspFamily.Data)
    (g : CuspUniformization.LogDeck) (x : CuspUniformization.LogCover D.radius) :
    letI := D.totalAction
    D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius g x) =
      Multiplicative.ofAdd (-g.k) • D.familyCover x := by
  let := D.totalAction
  have hg : g = (⟨g.k, 0, 0⟩ : CuspUniformization.LogDeck) * ⟨0, g.m, g.n⟩ := by
    apply CuspUniformization.LogDeck.ext <;> simp
  have he :
    CuspUniformization.logCoverTransform D.correction D.radius g x =
      CuspUniformization.logCoverTransform D.correction D.radius ⟨g.k, 0, 0⟩
        (CuspUniformization.logCoverTransform D.correction D.radius ⟨0, g.m, g.n⟩ x) := by
    apply Subtype.ext
    exact
      (congrArg (fun u => CuspUniformization.logDeckTransform D.correction u x) hg).trans
        (CuspUniformization.logDeckTransform_mul D.correction _ _ x)
  rw [he, D.familyCover_logarithmicShift, D.familyCover_period]

def SpecialPeriods.CuspFamily.Data.Space (D : SpecialPeriods.CuspFamily.Data) : Type :=
  @MulAction.orbitRel.Quotient (Multiplicative ℤ) D.TotalSpace _ D.totalAction

instance SpecialPeriods.CuspFamily.Data.spaceTopology (D : SpecialPeriods.CuspFamily.Data) :
    TopologicalSpace D.Space :=
  inferInstanceAs
    (TopologicalSpace
      (@MulAction.orbitRel.Quotient (Multiplicative ℤ) D.TotalSpace _ D.totalAction))

def SpecialPeriods.CuspFamily.Data.quotient (D : SpecialPeriods.CuspFamily.Data) :
    D.TotalSpace → D.Space := by
  let := D.totalAction
  exact Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) D.TotalSpace)

theorem SpecialPeriods.CuspFamily.Data.quotient_surjective (D : SpecialPeriods.CuspFamily.Data) :
    Function.Surjective D.quotient :=
  Quotient.mk_surjective

theorem SpecialPeriods.CuspFamily.Data.quotient_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : D.TotalSpace) :
    letI := D.totalAction
    D.quotient x = D.quotient y ↔ ∃ k : Multiplicative ℤ, k • y = x :=
  Quotient.eq''

@[simp]
theorem SpecialPeriods.CuspFamily.Data.quotient_smul (D : SpecialPeriods.CuspFamily.Data)
    (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    D.quotient (k • x) = D.quotient x := by
  let := D.totalAction
  exact (D.quotient_eq_iff _ _).mpr ⟨k, rfl⟩

def SpecialPeriods.CuspFamily.Data.projection (D : SpecialPeriods.CuspFamily.Data) :
    D.Space → SpecialPeriods.CuspFamily.puncturedDisc D.radius := by
  let := SpecialPeriods.CuspFamily.logBaseAction D.radius
  let := D.totalAction
  exact
    Quotient.lift (fun x : D.TotalSpace => SpecialPeriods.CuspFamily.baseExponential D.radius x.1)
      (by
        rintro x y ⟨k, hk⟩
        rw [← hk]
        exact SpecialPeriods.CuspFamily.baseExponential_smul D.radius k y.1)

@[simp]
theorem SpecialPeriods.CuspFamily.Data.projection_quotient (D : SpecialPeriods.CuspFamily.Data)
    (x : D.TotalSpace) :
    D.projection (D.quotient x) = SpecialPeriods.CuspFamily.baseExponential D.radius x.1 :=
  rfl

theorem SpecialPeriods.CuspFamily.Data.quotientCoveringMap (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.totalAction
    IsQuotientCoveringMap D.quotient (Multiplicative ℤ) := by
  let := SpecialPeriods.CuspFamily.logBaseAction D.radius
  let := D.totalAction
  let := D.totalAction_continuous
  refine
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_smul := ContinuousConstSMul.continuous_const_smul
      apply_eq_iff_mem_orbit := Quotient.eq''
      disjoint := ?_ }
  intro x
  obtain ⟨U, hU, hd⟩ := (SpecialPeriods.CuspFamily.baseExponential_covering D.radius).disjoint x.1
  refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
  rintro k ⟨z, ⟨w, hw, rfl⟩, hz⟩
  exact hd k ⟨k • w.1, ⟨w.1, hw, rfl⟩, hz⟩

@[instance_reducible]
def SpecialPeriods.CuspFamily.Data.chartedSpace (D : SpecialPeriods.CuspFamily.Data) :
    ChartedSpace (ℂ × ComplexPlane₂) D.Space := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact CoveringQuotient.chartedSpace (E := ℂ × ComplexPlane₂) D.quotientCoveringMap

theorem SpecialPeriods.CuspFamily.Data.quotient_holomorphic (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.contMDiff_project D.quotientCoveringMap ω D.totalAction_holomorphic

theorem SpecialPeriods.CuspFamily.Data.quotient_isLocalDiffeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact
    CoveringQuotient.project_isLocalDiffeomorph D.quotientCoveringMap D.totalAction_holomorphic

def SpecialPeriods.CuspFamily.Data.iteratedCover (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.LogCover D.radius → D.Space :=
  D.quotient ∘ D.familyCover

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_surjective
    (D : SpecialPeriods.CuspFamily.Data) : Function.Surjective D.iteratedCover :=
  D.quotient_surjective.comp D.familyCover_surjective

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.iteratedCover := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  exact D.quotient_holomorphic.comp D.familyCover_holomorphic

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_isLocalDiffeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.iteratedCover := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  intro x
  exact
    (D.familyCover_isLocalDiffeomorph x).comp (K := modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (P := D.Space) (D.quotient_isLocalDiffeomorph (D.familyCover x))

@[simp]
theorem SpecialPeriods.CuspFamily.Data.projection_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (x : CuspUniformization.LogCover D.radius) :
    (D.projection (D.iteratedCover x) : ℂ) = CuspUniformization.exponential x.1.1 :=
  rfl

theorem CuspUniformization.mem_logDomain_iff_im (ε : ℝ) (hε : 0 < ε) (p : ℂ × ComplexPlane₂) :
    p ∈ logDomain ε ↔ -Real.log ε / (2 * Real.pi) < p.1.im := by
  rw [mem_logDomain, ← Real.log_lt_log_iff (norm_pos_iff.mpr (exponential_ne_zero p.1)) hε,
    log_norm_exponential, div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  constructor <;> intro h <;> nlinarith

theorem CuspUniformization.logDomain_nonempty (ε : ℝ) (hε : 0 < ε) :
    (logDomain ε : Set (ℂ × ComplexPlane₂)).Nonempty := by
  refine ⟨(((↑(-Real.log ε / (2 * Real.pi) + 1) : ℂ) * Complex.I), 0), ?_⟩
  apply (mem_logDomain_iff_im ε hε _).mpr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, MulZeroClass.mul_zero, add_zero]
  linarith

abbrev ThreefoldOverlapMappingTorus.Cusp.monodromy : RealTorus₄ ≃ₜ RealTorus₄ :=
  SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1

abbrev ThreefoldOverlapMappingTorus.Cusp.Boundary :=
  MappingTorus.Torus monodromy

private def ThreefoldOverlapMappingTorus.Cusp.monodromyHom_mo1973_10002 :
    Multiplicative ℤ →* (RealTorus₄ ≃ₜ RealTorus₄)
    where
  toFun k := SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd
  map_one' := SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_eq
  map_mul' k
    l := by
    apply Homeomorph.ext
    exact SpecialPeriods.CuspFamily.cuspTorusHomeomorph_add_apply k.toAdd l.toAdd

theorem ThreefoldOverlapMappingTorus.Cusp.monodromy_zpow (k : ℤ) :
    monodromy ^ k = SpecialPeriods.CuspFamily.cuspTorusHomeomorph k := by
  have h := map_zpow monodromyHom_mo1973_10002 (Multiplicative.ofAdd (1 : ℤ)) k
  change
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph (((Multiplicative.ofAdd (1 : ℤ)) ^ k).toAdd) =
      monodromy ^ k at h
  simpa using h.symm

def ThreefoldOverlapMappingTorus.Cusp.heightThreshold (r : ℝ) : ℝ :=
  -Real.log r / (2 * Real.pi)

abbrev ThreefoldOverlapMappingTorus.Cusp.Height (r : ℝ) :=
  Set.Ioi (heightThreshold r)

theorem ThreefoldOverlapMappingTorus.Cusp.mem_logBase_iff_height (r : ℝ) (hr : 0 < r) (s : ℂ) :
    s ∈ SpecialPeriods.CuspFamily.logBase r ↔ heightThreshold r < s.im := by
  simpa only [SpecialPeriods.CuspFamily.mem_logBase, CuspUniformization.mem_logDomain,
    heightThreshold] using (CuspUniformization.mem_logDomain_iff_im r hr (s, (0 : ComplexPlane₂)))

def ThreefoldOverlapMappingTorus.Cusp.logPoint (r : ℝ) (hr : 0 < r) (t : ℝ) (h : Height r) :
    SpecialPeriods.CuspFamily.LogBase r :=
  ⟨(t : ℂ) + (h : ℝ) * Complex.I,
    (mem_logBase_iff_height r hr _).mpr
      (by
        simpa only [Height, Set.mem_Ioi, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, MulZeroClass.mul_zero, zero_add,
          add_zero] using h.property)⟩

@[simp]
theorem ThreefoldOverlapMappingTorus.Cusp.logPoint_re (r : ℝ) (hr : 0 < r) (t : ℝ)
    (h : Height r) : (logPoint r hr t h : ℂ).re = t := by simp [logPoint]

@[simp]
theorem ThreefoldOverlapMappingTorus.Cusp.logPoint_im (r : ℝ) (hr : 0 < r) (t : ℝ)
    (h : Height r) : (logPoint r hr t h : ℂ).im = (h : ℝ) := by simp [logPoint]

def ThreefoldOverlapMappingTorus.Cusp.logBaseHeightHomeomorph (r : ℝ) (hr : 0 < r) :
    SpecialPeriods.CuspFamily.LogBase r ≃ₜ Height r × ℝ
    where
  toFun s := (⟨(s : ℂ).im, (mem_logBase_iff_height r hr s).mp s.property⟩, (s : ℂ).re)
  invFun p := logPoint r hr p.2 p.1
  left_inv
    s := by
    apply Subtype.ext
    apply Complex.ext <;> simp [logPoint]
  right_inv
    p := by
    apply Prod.ext
    · apply Subtype.ext
      exact logPoint_im r hr p.2 p.1
    · exact logPoint_re r hr p.2 p.1
  continuous_toFun :=
    ((Complex.continuous_im.comp continuous_subtype_val).subtype_mk _).prodMk
      (Complex.continuous_re.comp continuous_subtype_val)
  continuous_invFun :=
    ((Complex.continuous_ofReal.comp continuous_snd).add
          ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
            continuous_const)).subtype_mk
      _

theorem ThreefoldOverlapMappingTorus.Cusp.logPoint_translate (r : ℝ) (hr : 0 < r) (k : ℤ) (t : ℝ)
    (h : Height r) :
    SpecialPeriods.CuspFamily.logBaseTranslate r k (logPoint r hr t h) =
      logPoint r hr (t - (k : ℝ)) h := by
  apply Subtype.ext
  change (t : ℂ) + (h : ℝ) * Complex.I - (k : ℂ) = ((t - (k : ℝ) : ℝ) : ℂ) + (h : ℝ) * Complex.I
  push_cast
  ring

def ThreefoldOverlapMappingTorus.Cusp.familyCylinderHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) : D.TotalSpace ≃ₜ Height D.radius × (ℝ × RealTorus₄) :=
  ((logBaseHeightHomeomorph D.radius D.radius_pos).prodCongr (Homeomorph.refl RealTorus₄)).trans
    (Homeomorph.prodAssoc (Height D.radius) ℝ RealTorus₄)

theorem ThreefoldOverlapMappingTorus.Cusp.familyCylinderHomeomorph_smul
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    familyCylinderHomeomorph D (k • x) =
      ((familyCylinderHomeomorph D x).1,
        MappingTorus.deck monodromy (-k.toAdd) (familyCylinderHomeomorph D x).2) := by
  let := D.totalAction
  apply Prod.ext
  · apply Subtype.ext
    change ((x.1 : ℂ) - (k.toAdd : ℂ)).im = (x.1 : ℂ).im
    simp
  · apply Prod.ext
    · change ((x.1 : ℂ) - (k.toAdd : ℂ)).re = (x.1 : ℂ).re + ((-k.toAdd : ℤ) : ℝ)
      simp [sub_eq_add_neg]
    · change
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd x.2 =
          (monodromy ^ (-(-k.toAdd))) x.2
      rw [neg_neg, monodromy_zpow]

def CuspHoneycombHexagon.CommonFibres.descend {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (x : X) : Y :=
  g (hf x).choose

theorem CuspHoneycombHexagon.CommonFibres.descend_apply {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (hfg : ∀ a b, f a = f b → g a = g b) (a : A) :
    descend f g hf (f a) = g a :=
  hfg _ a (hf (f a)).choose_spec

theorem CuspHoneycombHexagon.CommonFibres.descend_surjective {A X Y : Type*} (f : A → X)
    (g : A → Y) (hf : Function.Surjective f) (hfg : ∀ a b, f a = f b → g a = g b)
    (hg : Function.Surjective g) : Function.Surjective (descend f g hf) := by
  intro y
  obtain ⟨a, rfl⟩ := hg y
  exact ⟨f a, descend_apply f g hf hfg a⟩

theorem CuspHoneycombHexagon.CommonFibres.descend_injective {A X Y : Type*} (f : A → X)
    (g : A → Y) (hf : Function.Surjective f) (hgf : ∀ a b, g a = g b → f a = f b) :
    Function.Injective (descend f g hf) := by
  intro x y h
  have he := hgf (hf x).choose (hf y).choose h
  exact (hf x).choose_spec.symm.trans (he.trans (hf y).choose_spec)

theorem CuspHoneycombHexagon.CommonFibres.descend_continuous {A X Y : Type*} (f : A → X)
    (g : A → Y) (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] (hq : Topology.IsQuotientMap f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b → g a = g b) : Continuous (descend f g hf) := by
  apply hq.continuous_iff.mpr
  have he : descend f g hf ∘ f = g := funext (descend_apply f g hf hfg)
  rwa [he]

def CuspHoneycombHexagon.CommonFibres.homeomorph {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace A] [T2Space X] [T2Space Y] (hfc : Continuous f) (hgc : Continuous g)
    (hg : Function.Surjective g) (hfg : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  have hX : IsCompact (Set.univ : Set X) := by
    rw [← Set.range_eq_univ.mpr hf]
    exact isCompact_range hfc
  letI : CompactSpace X := ⟨hX⟩
  have hd : Continuous (descend f g hf) :=
    descend_continuous f g hf (hfc.isClosedMap.isQuotientMap hfc hf) hgc (fun a b => (hfg a b).mp)
  let e : X ≃ Y :=
    Equiv.ofBijective (descend f g hf)
      ⟨descend_injective f g hf (fun a b => (hfg a b).mpr),
        descend_surjective f g hf (fun a b => (hfg a b).mp) hg⟩
  exact Equiv.toHomeomorphOfContinuousClosed e hd hd.isClosedMap

@[simp]
theorem CuspHoneycombHexagon.CommonFibres.homeomorph_apply {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace A] [T2Space X] [T2Space Y] (hfc : Continuous f) (hgc : Continuous g)
    (hg : Function.Surjective g) (hfg : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    homeomorph f g hf hfc hgc hg hfg (f a) = g a :=
  descend_apply f g hf (fun a b => (hfg a b).mp) a

private def ThreefoldOverlapMappingTorus.Cusp.commonQuotientHomeomorph_mo1973_10028
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y] (f : A → X)
    (g : A → Y) (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (he : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  let e : X ≃ Y :=
    Equiv.ofBijective (CuspHoneycombHexagon.CommonFibres.descend f g hf.surjective)
      ⟨CuspHoneycombHexagon.CommonFibres.descend_injective f g hf.surjective
          (fun a b => (he a b).mpr),
        CuspHoneycombHexagon.CommonFibres.descend_surjective f g hf.surjective
          (fun a b => (he a b).mp) hg.surjective⟩
  refine
    { toEquiv := e
      continuous_toFun :=
        CuspHoneycombHexagon.CommonFibres.descend_continuous f g hf.surjective hf hg.continuous
          (fun a b => (he a b).mp)
      continuous_invFun := ?_ }
  apply hg.continuous_iff.mpr
  change Continuous (e.symm ∘ g)
  have hcomp : e.symm ∘ g = f := by
    funext a
    apply e.injective
    change e (e.symm (g a)) = e (f a)
    rw [e.apply_symm_apply]
    exact
      (CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (he a b).mp)
          a).symm
  rw [hcomp]
  exact hf.continuous

private theorem ThreefoldOverlapMappingTorus.Cusp.commonQuotientHomeomorph_apply_mo1973_10029
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y] (f : A → X)
    (g : A → Y) (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (he : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    commonQuotientHomeomorph_mo1973_10028 f g hf hg he (f a) = g a :=
  CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (he a b).mp) a

def ThreefoldOverlapMappingTorus.Cusp.cylinderProjection (r : ℝ) :
    C(Height r × (ℝ × RealTorus₄), Height r × Boundary) :=
  ⟨Prod.map id (MappingTorus.mk monodromy),
    continuous_id.prodMap (MappingTorus.mk_continuous monodromy)⟩

theorem ThreefoldOverlapMappingTorus.Cusp.cylinderProjection_isOpenQuotientMap (r : ℝ) :
    IsOpenQuotientMap (cylinderProjection r) :=
  IsOpenQuotientMap.id.prodMap
    ⟨MappingTorus.mk_surjective monodromy, MappingTorus.mk_continuous monodromy,
      MappingTorus.mk_open monodromy⟩

def ThreefoldOverlapMappingTorus.Cusp.familyProductMap (D : SpecialPeriods.CuspFamily.Data) :
    C(D.TotalSpace, Height D.radius × Boundary) :=
  (cylinderProjection D.radius).comp
    ⟨familyCylinderHomeomorph D, (familyCylinderHomeomorph D).continuous⟩

theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_isOpenQuotientMap
    (D : SpecialPeriods.CuspFamily.Data) : IsOpenQuotientMap (familyProductMap D) :=
  (cylinderProjection_isOpenQuotientMap D.radius).comp
    (familyCylinderHomeomorph D).isOpenQuotientMap

theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_smul
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    familyProductMap D (k • x) = familyProductMap D x := by
  let := D.totalAction
  change Prod.map id (MappingTorus.mk monodromy) (familyCylinderHomeomorph D (k • x)) = _
  rw [familyCylinderHomeomorph_smul]
  exact Prod.ext rfl (MappingTorus.mk_deck monodromy (-k.toAdd) _)

theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_eq_iff
    (D : SpecialPeriods.CuspFamily.Data) (x y : D.TotalSpace) :
    familyProductMap D x = familyProductMap D y ↔ D.quotient x = D.quotient y := by
  let := D.totalAction
  constructor
  · intro h
    have hheight : (x.1 : ℂ).im = (y.1 : ℂ).im :=
      congrArg (fun p : Height D.radius × Boundary => (p.1 : ℝ)) h
    have htime := congrArg Prod.snd h
    change
      MappingTorus.mk monodromy ((x.1 : ℂ).re, x.2) =
        MappingTorus.mk monodromy ((y.1 : ℂ).re, y.2) at htime
    obtain ⟨n, ht, hx⟩ := (MappingTorus.mk_eq_mk_iff monodromy _ _).mp htime
    apply (D.quotient_eq_iff x y).mpr
    refine ⟨Multiplicative.ofAdd n, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      apply Complex.ext
      · change ((y.1 : ℂ) - (n : ℂ)).re = (x.1 : ℂ).re
        change (y.1 : ℂ).re = (x.1 : ℂ).re + (n : ℝ) at ht
        simp only [Complex.sub_re, Complex.intCast_re]
        linarith
      · change ((y.1 : ℂ) - (n : ℂ)).im = (x.1 : ℂ).im
        simpa only [Complex.sub_im, Complex.intCast_im, sub_zero] using hheight.symm
    · change SpecialPeriods.CuspFamily.cuspTorusHomeomorph n y.2 = x.2
      change y.2 = (monodromy ^ (-n)) x.2 at hx
      rw [monodromy_zpow] at hx
      rw [hx, ← SpecialPeriods.CuspFamily.cuspTorusHomeomorph_add_apply, add_neg_cancel,
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_apply]
  · intro h
    obtain ⟨k, hk⟩ := (D.quotient_eq_iff x y).mp h
    rw [← hk, familyProductMap_smul]

theorem ThreefoldOverlapMappingTorus.Cusp.familyQuotient_isQuotientMap
    (D : SpecialPeriods.CuspFamily.Data) : Topology.IsQuotientMap D.quotient := by
  let := D.totalAction
  exact D.quotientCoveringMap.toIsQuotientMap

def ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) : D.Space ≃ₜ Height D.radius × Boundary :=
  commonQuotientHomeomorph_mo1973_10028 D.quotient (familyProductMap D)
    (familyQuotient_isQuotientMap D) (familyProductMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (familyProductMap_eq_iff D x y).symm)

@[simp]
theorem ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph_quotient
    (D : SpecialPeriods.CuspFamily.Data) (x : D.TotalSpace) :
    familyProductHomeomorph D (D.quotient x) = familyProductMap D x :=
  commonQuotientHomeomorph_apply_mo1973_10029 D.quotient (familyProductMap D)
    (familyQuotient_isQuotientMap D) (familyProductMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (familyProductMap_eq_iff D x y).symm) x

theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_logPoint
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    familyProductMap D (logPoint D.radius D.radius_pos t h, x) =
      (h, MappingTorus.mk monodromy (t, x)) := by
  apply Prod.ext
  · apply Subtype.ext
    exact logPoint_im D.radius D.radius_pos t h
  · change MappingTorus.mk monodromy ((logPoint D.radius D.radius_pos t h : ℂ).re, x) = _
    rw [logPoint_re]

theorem ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph_symm_mk
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    (familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x)) =
      D.quotient (logPoint D.radius D.radius_pos t h, x) := by
  simpa only [familyProductHomeomorph_quotient, familyProductMap_logPoint] using
    (familyProductHomeomorph D).symm_apply_apply
      (D.quotient (logPoint D.radius D.radius_pos t h, x))

abbrev CuspUniformization.LogModel :=
  ℂ × ComplexPlane₂

def CuspUniformization.logCoordinateLinear : LogModel ≃ₗ[ℂ] ToricCharts.CoordinateSpace 3
    where
  toFun p := ![p.2 0, p.2 1, p.1]
  invFun w := (w 2, ![w 0, w 1])
  left_inv
    p := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  right_inv
    w := by
    ext i
    fin_cases i <;> rfl
  map_add' p
    q := by
    ext i
    fin_cases i <;> rfl
  map_smul' c
    p := by
    ext i
    fin_cases i <;> rfl

def CuspUniformization.logCoordinateEquiv : LogModel ≃L[ℂ] ToricCharts.CoordinateSpace 3 :=
  logCoordinateLinear.toContinuousLinearEquiv

def CuspUniformization.totalExponentialCoordinates (p : LogModel) :
    ToricCharts.CoordinateSpace 3 :=
  ![exponential (p.2 0), exponential (p.2 1), exponential p.1]

theorem CuspUniformization.totalExponentialCoordinates_mem_torus (p : LogModel) :
    totalExponentialCoordinates p ∈ ToricCharts.torus := by
  intro i
  fin_cases i <;> exact exponential_ne_zero _

theorem CuspUniformization.totalExponentialCoordinates_holomorphic :
    ContDiff ℂ ω totalExponentialCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 0).comp contDiff_snd)
  · exact exponential_holomorphic.comp ((contDiff_apply ℂ ℂ 1).comp contDiff_snd)
  · exact exponential_holomorphic.comp contDiff_fst

def CuspUniformization.totalExponentialDerivative (p : LogModel) :
    LogModel ≃L[ℂ] ToricCharts.CoordinateSpace 3 :=
  ((ContinuousLinearEquiv.unitsEquivAut ℂ
            (Units.mk0 (exponential p.1 * (2 * Real.pi * Complex.I))
              (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero))).prodCongr
        (exponentialPairDerivative p.2)).trans
    logCoordinateEquiv

theorem CuspUniformization.totalExponentialCoordinates_hasFDerivAt (p : LogModel) :
    HasFDerivAt totalExponentialCoordinates
      (totalExponentialDerivative p : LogModel →L[ℂ] ToricCharts.CoordinateSpace 3) p := by
  convert!
    logCoordinateEquiv.hasFDerivAt.comp p
      (((exponential_hasDerivAt p.1).hasFDerivAt_equiv
            (mul_ne_zero (exponential_ne_zero _) exponential_factor_ne_zero)).prodMap
        p (exponentialPair_hasFDerivAt p.2)) using
    1

def CuspUniformization.totalExponentialChart (p : LogModel) :
    OpenPartialHomeomorph LogModel (ToricCharts.CoordinateSpace 3) :=
  totalExponentialCoordinates_holomorphic.contDiffAt.toOpenPartialHomeomorph
    totalExponentialCoordinates (totalExponentialCoordinates_hasFDerivAt p) (by simp)

theorem CuspUniformization.totalExponentialChart_mem_source (p : LogModel) :
    p ∈ (totalExponentialChart p).source :=
  totalExponentialCoordinates_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    (totalExponentialCoordinates_hasFDerivAt p) (by simp)

theorem CuspUniformization.totalExponentialChart_holomorphic (p : LogModel) :
    ContDiffOn ℂ ω (totalExponentialChart p) (totalExponentialChart p).source :=
  totalExponentialCoordinates_holomorphic.contDiffOn

theorem CuspUniformization.totalExponentialChart_symm_holomorphic (p : LogModel) :
    ContDiffOn ℂ ω (totalExponentialChart p).symm (totalExponentialChart p).target := by
  intro w hw
  exact
    ((totalExponentialChart p).contDiffAt_symm hw
        (totalExponentialCoordinates_hasFDerivAt ((totalExponentialChart p).symm w))
        totalExponentialCoordinates_holomorphic.contDiffAt).contDiffWithinAt

theorem CuspUniformization.totalExponentialCoordinates_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω totalExponentialCoordinates := by
  intro p
  refine
    ⟨{  toPartialEquiv := (totalExponentialChart p).toPartialEquiv
        open_source := (totalExponentialChart p).open_source
        open_target := (totalExponentialChart p).open_target
        contMDiffOn_toFun := (totalExponentialChart_holomorphic p).contMDiffOn
        contMDiffOn_invFun := (totalExponentialChart_symm_holomorphic p).contMDiffOn },
      totalExponentialChart_mem_source p, ?_⟩
  intro q _
  rfl

theorem CuspUniformization.torusPoint_isLocalDiffeomorphAt {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω torusPoint z := by
  refine
    ⟨{  toPartialEquiv := torusChart.symm.toPartialEquiv
        open_source := torusChart.open_target
        open_target := torusChart.open_source
        contMDiffOn_toFun := torusPoint_holomorphic
        contMDiffOn_invFun := ToricSpace.torusCoordinates_holomorphic }, hz, ?_⟩
  intro w _
  rfl

theorem CuspUniformization.totalExponentialPoint_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω totalExponentialPoint := by
  intro p
  change
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (torusPoint ∘ totalExponentialCoordinates) p
  exact
    (totalExponentialCoordinates_isLocalDiffeomorph p).comp (K :=
      modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) (P := ToricSpace.Space)
      (torusPoint_isLocalDiffeomorphAt (totalExponentialCoordinates_mem_torus p))

theorem CuspUniformization.totalExponentialLift_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalExponentialLift ε) := by
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      totalExponentialPoint_isLocalDiffeomorph (logDomain ε)
      (ToricSpace.tubeOpen (CuspQuotient.disc ε))
      (fun p hp => (totalExponentialLift ε ⟨p, hp⟩).prop)

theorem CuspUniformization.puncturedExponential_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedExponential ε) := by
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (totalExponentialLift_isLocalDiffeomorph ε) (puncturedTubeOpen ε)
      (fun p => (puncturedExponential ε p).prop)

theorem contMDiff_of_comp_localDiffeomorph {E F F' H K K' M N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F']
    [NormedSpace ℂ F'] [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace K']
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
    [TopologicalSpace P] [ChartedSpace K' P] (I : ModelWithCorners ℂ E H)
    (J : ModelWithCorners ℂ F K) (L : ModelWithCorners ℂ F' K') {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) (hsurj : Function.Surjective f) {g : N → P}
    (hgf : ContMDiff I L ω (g ∘ f)) : ContMDiff J L ω g := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have h := hgf.contMDiffAt.comp (f x) (hf x).localInverse_contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(hf x).localInverse_eventuallyEq_right] with z hz
  change g z = g (f ((hf x).localInverse z))
  rw [show f ((hf x).localInverse z) = z from hz]

theorem CuspUniformization.quotientMap_isLocalDiffeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (CuspQuotient.quotientMap C ε) :=
  by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    CoveringQuotient.project_isLocalDiffeomorph
      (CuspQuotient.quotientMap_covering C ε hε hε1 hC hR)
      (fun g => ToricSpace.tubeTranslate_holomorphic C (CuspQuotient.disc ε) g.toAdd hC)

theorem CuspUniformization.puncturedQuotientMap_isLocalDiffeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedQuotientMap C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (quotientMap_isLocalDiffeomorph C ε hε hε1 hC hR) (puncturedTubeOpen ε)
      (puncturedQuotientOpen C ε) (fun _ hx => hx)

theorem CuspUniformization.puncturedCuspCover_isLocalDiffeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro p
  change
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (puncturedQuotientMap C ε ∘ puncturedExponential ε) p
  exact
    (puncturedExponential_isLocalDiffeomorph ε p).comp (K :=
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))) (P := PuncturedQuotient C ε)
      (puncturedQuotientMap_isLocalDiffeomorph C ε hε hε1 hC hR (puncturedExponential ε p))

theorem CuspUniformization.puncturedCuspCover_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR).contMDiff

theorem CuspUniformization.puncturedCuspCover_isLocalHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsLocalHomeomorph (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR).isLocalHomeomorph

theorem CuspUniformization.puncturedCuspCover_isOpenMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsOpenMap (puncturedCuspCover C ε) :=
  (puncturedCuspCover_isLocalHomeomorph C ε hε hε1 hC hR).isOpenMap

def CuspUniformization.totalPeriodRelation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Setoid (LogCover ε) where
  r p q := TotalPeriodRelated C p q
  iseqv :=
    { refl p := (puncturedCuspCover_eq_iff C ε p p).mp rfl
      symm
        h :=
        (puncturedCuspCover_eq_iff C ε _ _).mp ((puncturedCuspCover_eq_iff C ε _ _).mpr h).symm
      trans h
        h' :=
        (puncturedCuspCover_eq_iff C ε _ _).mp
          (((puncturedCuspCover_eq_iff C ε _ _).mpr h).trans
            ((puncturedCuspCover_eq_iff C ε _ _).mpr h')) }

abbrev CuspUniformization.TotalPeriodQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  Quotient (totalPeriodRelation C ε)

def CuspUniformization.totalPeriodQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    LogCover ε → TotalPeriodQuotient C ε :=
  Quotient.mk (totalPeriodRelation C ε)

theorem CuspUniformization.totalPeriodQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Surjective (totalPeriodQuotientMap C ε) :=
  Quotient.mk_surjective

theorem CuspUniformization.totalPeriodQuotientMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Continuous (totalPeriodQuotientMap C ε) :=
  continuous_quotient_mk'

@[simp]
theorem CuspUniformization.totalPeriodQuotientMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p q : LogCover ε) :
    totalPeriodQuotientMap C ε p = totalPeriodQuotientMap C ε q ↔ TotalPeriodRelated C p q :=
  Quotient.eq''

def CuspUniformization.totalUniformizationMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    TotalPeriodQuotient C ε → PuncturedQuotient C ε :=
  Quotient.lift (puncturedCuspCover C ε) fun p q h => (puncturedCuspCover_eq_iff C ε p q).mpr h

theorem CuspUniformization.totalUniformizationMap_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Bijective (totalUniformizationMap C ε) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro h
        exact Quotient.sound ((puncturedCuspCover_eq_iff C ε p q).mp h)
  · intro q
    obtain ⟨p, hp⟩ := puncturedCuspCover_surjective C ε q
    exact ⟨totalPeriodQuotientMap C ε p, hp⟩

def CuspUniformization.totalUniformizationEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    TotalPeriodQuotient C ε ≃ PuncturedQuotient C ε :=
  Equiv.ofBijective (totalUniformizationMap C ε) (totalUniformizationMap_bijective C ε)

@[simp]
theorem CuspUniformization.totalUniformizationEquiv_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : LogCover ε) :
    totalUniformizationEquiv C ε (totalPeriodQuotientMap C ε p) = puncturedCuspCover C ε p :=
  rfl

@[simp]
theorem CuspUniformization.totalUniformizationEquiv_symm_cover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : LogCover ε) :
    (totalUniformizationEquiv C ε).symm (puncturedCuspCover C ε p) =
      totalPeriodQuotientMap C ε p := by
  simpa only [totalUniformizationEquiv_quotientMap] using
    (totalUniformizationEquiv C ε).symm_apply_apply (totalPeriodQuotientMap C ε p)

theorem CuspUniformization.totalUniformizationMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Continuous (totalUniformizationMap C ε) := by
  apply Continuous.quotient_lift
  exact
    ((CuspQuotient.quotientMap_continuous C ε).comp
          (totalExponentialLift_holomorphic ε).continuous).subtype_mk
      _

theorem CuspUniformization.totalUniformizationMap_isOpenMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsOpenMap (totalUniformizationMap C ε) := by
  apply
    IsOpenMap.of_comp (totalPeriodQuotientMap_continuous C ε)
      (totalPeriodQuotientMap_surjective C ε)
  exact puncturedCuspCover_isOpenMap C ε hε hε1 hC hR

def CuspUniformization.totalUniformizationHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : TotalPeriodQuotient C ε ≃ₜ PuncturedQuotient C ε :=
  (totalUniformizationEquiv C ε).toHomeomorphOfContinuousOpen
    (totalUniformizationMap_continuous C ε) (totalUniformizationMap_isOpenMap C ε hε hε1 hC hR)

@[simp]
theorem CuspUniformization.totalUniformizationHomeomorph_symm_cover
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : LogCover ε) :
    (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm (puncturedCuspCover C ε p) =
      totalPeriodQuotientMap C ε p :=
  totalUniformizationEquiv_symm_cover C ε p

theorem CuspUniformization.puncturedCuspCover_covering (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := logCoverAction C ε
    IsQuotientCoveringMap (puncturedCuspCover C ε) LogDeck := by
  let := logCoverAction C ε
  let := logCover_continuousConstSMul C ε hC
  let := logCover_free_action C ε hε1 hR
  exact
    quotientCoveringMap_of_localHomeomorph (puncturedCuspCover_isLocalHomeomorph C ε hε hε1 hC hR)
      (puncturedCuspCover_surjective C ε) (puncturedCuspCover_eq_iff_orbit C ε)

theorem CuspUniformization.totalPeriodQuotientMap_covering (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := logCoverAction C ε
    IsQuotientCoveringMap (totalPeriodQuotientMap C ε) LogDeck := by
  let := logCoverAction C ε
  have h :=
    (puncturedCuspCover_covering C ε hε hε1 hC hR).homeomorph_comp
      (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm
  have he :
    (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm ∘ puncturedCuspCover C ε =
      totalPeriodQuotientMap C ε := by
    funext p
    exact totalUniformizationHomeomorph_symm_cover C ε hε hε1 hC hR p
  rwa [he] at h

@[instance_reducible]
def CuspUniformization.totalPeriodQuotientChartedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    ChartedSpace (ℂ × ComplexPlane₂) (TotalPeriodQuotient C ε) :=
  letI := logCoverAction C ε
  CoveringQuotient.chartedSpace (E := ℂ × ComplexPlane₂)
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR)

theorem CuspUniformization.totalPeriodQuotientMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (totalPeriodQuotientMap C ε) := by
  let := logCoverAction C ε
  exact
    CoveringQuotient.contMDiff_project (totalPeriodQuotientMap_covering C ε hε hε1 hC hR) ω
      (logCover_action_holomorphic C ε hC)

theorem CuspUniformization.totalUniformizationMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalUniformizationMap C ε) := by
  let := logCoverAction C ε
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply
    CoveringQuotient.contMDiff_of_comp (totalPeriodQuotientMap_covering C ε hε hε1 hC hR)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
  exact puncturedCuspCover_holomorphic C ε hε hε1 hC hR

theorem CuspUniformization.totalUniformizationEquiv_symm_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (totalUniformizationEquiv C ε).symm := by
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply
    contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR) (puncturedCuspCover_surjective C ε)
  have he :
    (totalUniformizationEquiv C ε).symm ∘ puncturedCuspCover C ε = totalPeriodQuotientMap C ε := by
    funext p
    exact totalUniformizationEquiv_symm_cover C ε p
  rw [he]
  exact totalPeriodQuotientMap_holomorphic C ε hε hε1 hC hR

def CuspUniformization.totalUniformizationBiholomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) (TotalPeriodQuotient C ε)
      (PuncturedQuotient C ε) ω := by
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    { toEquiv := totalUniformizationEquiv C ε
      contMDiff_toFun := totalUniformizationMap_holomorphic C ε hε hε1 hC hR
      contMDiff_invFun := totalUniformizationEquiv_symm_holomorphic C ε hε hε1 hC hR }

@[simp]
theorem CuspUniformization.totalUniformizationBiholomorph_quotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : LogCover ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    totalUniformizationBiholomorph C ε hε hε1 hC hR (totalPeriodQuotientMap C ε p) =
      puncturedCuspCover C ε p :=
  rfl

theorem SpecialPeriods.CuspFamily.Data.totalPeriodQuotientMap_eq_of_familyCover_eq
    (D : SpecialPeriods.CuspFamily.Data) {x y : CuspUniformization.LogCover D.radius}
    (h : D.familyCover x = D.familyCover y) :
    CuspUniformization.totalPeriodQuotientMap D.correction D.radius x =
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius y := by
  obtain ⟨hs, m, n, hmn⟩ := (D.familyCover_eq_iff x y).mp h
  apply (CuspUniformization.totalPeriodQuotientMap_eq_iff D.correction D.radius x y).mpr
  exact ⟨0, m, n, by simpa only [Int.cast_zero, add_zero] using hs, hmn⟩

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_logDeck (D : SpecialPeriods.CuspFamily.Data)
    (g : CuspUniformization.LogDeck) (x : CuspUniformization.LogCover D.radius) :
    D.iteratedCover (CuspUniformization.logCoverTransform D.correction D.radius g x) =
      D.iteratedCover x := by
  let := D.totalAction
  change
    D.quotient (D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius g x)) =
      D.quotient (D.familyCover x)
  rw [D.familyCover_logDeck, D.quotient_smul]

theorem SpecialPeriods.CuspFamily.Data.iteratedCover_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : CuspUniformization.LogCover D.radius) :
    D.iteratedCover x = D.iteratedCover y ↔
      CuspUniformization.TotalPeriodRelated D.correction x y := by
  let := D.totalAction
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (D.quotient_eq_iff (D.familyCover x) (D.familyCover y)).mp h
    let z := CuspUniformization.logCoverTransform D.correction D.radius ⟨-k.toAdd, 0, 0⟩ y
    have hz : D.familyCover z = k • D.familyCover y := by
      simpa only [neg_neg, ofAdd_toAdd] using D.familyCover_logarithmicShift (-k.toAdd) y
    have hxy := D.totalPeriodQuotientMap_eq_of_familyCover_eq (hk.symm.trans hz.symm)
    have hzy :
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius z =
        CuspUniformization.totalPeriodQuotientMap D.correction D.radius y := by
      apply (CuspUniformization.totalPeriodQuotientMap_eq_iff D.correction D.radius z y).mpr
      exact ⟨-k.toAdd, 0, 0, rfl, rfl⟩
    exact
      (CuspUniformization.totalPeriodQuotientMap_eq_iff D.correction D.radius x y).mp
        (hxy.trans hzy)
  · intro h
    obtain ⟨g, hg⟩ :=
      (CuspUniformization.totalPeriodRelated_iff_exists_logDeck D.correction x y).mp h
    have he : CuspUniformization.logCoverTransform D.correction D.radius g y = x := Subtype.ext hg
    rw [← he, D.iteratedCover_logDeck]

def SpecialPeriods.CuspFamily.Data.directToIterated (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.TotalPeriodQuotient D.correction D.radius → D.Space :=
  Quotient.lift D.iteratedCover (fun x y h => (D.iteratedCover_eq_iff x y).mpr h)

theorem SpecialPeriods.CuspFamily.Data.directToIterated_bijective
    (D : SpecialPeriods.CuspFamily.Data) : Function.Bijective D.directToIterated := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro he
        exact Quotient.sound ((D.iteratedCover_eq_iff x y).mp he)
  · intro y
    obtain ⟨x, rfl⟩ := D.iteratedCover_surjective y
    exact ⟨CuspUniformization.totalPeriodQuotientMap D.correction D.radius x, rfl⟩

def SpecialPeriods.CuspFamily.Data.directToIteratedEquiv (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.TotalPeriodQuotient D.correction D.radius ≃ D.Space :=
  Equiv.ofBijective D.directToIterated D.directToIterated_bijective

@[simp]
theorem SpecialPeriods.CuspFamily.Data.directToIteratedEquiv_symm_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (x : CuspUniformization.LogCover D.radius) :
    D.directToIteratedEquiv.symm (D.iteratedCover x) =
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius x :=
  D.directToIteratedEquiv.symm_apply_apply
    (CuspUniformization.totalPeriodQuotientMap D.correction D.radius x)

theorem SpecialPeriods.CuspFamily.Data.directToIterated_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI :=
      CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.directToIterated := by
  let := CuspUniformization.logCoverAction D.correction D.radius
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  apply
    CoveringQuotient.contMDiff_of_comp
      (CuspUniformization.totalPeriodQuotientMap_covering D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift)
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
  exact D.iteratedCover_holomorphic

theorem SpecialPeriods.CuspFamily.Data.directToIteratedEquiv_symm_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI :=
      CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.directToIteratedEquiv.symm := by
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  apply
    contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      D.iteratedCover_isLocalDiffeomorph D.iteratedCover_surjective
  have he :
    D.directToIteratedEquiv.symm ∘ D.iteratedCover =
      CuspUniformization.totalPeriodQuotientMap D.correction D.radius :=
    funext D.directToIteratedEquiv_symm_iteratedCover
  rw [he]
  exact
    CuspUniformization.totalPeriodQuotientMap_holomorphic D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift

def SpecialPeriods.CuspFamily.Data.directQuotientBiholomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI :=
      CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (CuspUniformization.TotalPeriodQuotient D.correction D.radius) D.Space ω := by
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  exact
    { toEquiv := D.directToIteratedEquiv
      contMDiff_toFun := D.directToIterated_holomorphic
      contMDiff_invFun := D.directToIteratedEquiv_symm_holomorphic }

def SpecialPeriods.CuspFamily.Data.puncturedFamilyBiholomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.chartedSpace
    letI :=
      CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
        D.smallDrift
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) D.Space
      (CuspUniformization.PuncturedQuotient D.correction D.radius) ω := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  exact
    D.directQuotientBiholomorph.symm.trans
      (CuspUniformization.totalUniformizationBiholomorph D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift)

@[simp]
theorem SpecialPeriods.CuspFamily.Data.puncturedFamilyBiholomorph_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (x : CuspUniformization.LogCover D.radius) :
    letI := D.chartedSpace
    letI :=
      CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
        D.smallDrift
    D.puncturedFamilyBiholomorph (D.iteratedCover x) =
      CuspUniformization.puncturedCuspCover D.correction D.radius x := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  let :=
    CuspUniformization.totalPeriodQuotientChartedSpace D.correction D.radius D.radius_pos
      D.radius_lt_one D.holomorphic D.smallDrift
  change
    CuspUniformization.totalUniformizationBiholomorph D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
        (D.directToIteratedEquiv.symm (D.iteratedCover x)) =
      _
  rw [D.directToIteratedEquiv_symm_iteratedCover,
    CuspUniformization.totalUniformizationBiholomorph_quotientMap]

theorem SpecialPeriods.CuspFamily.Data.puncturedFamilyBiholomorph_preserves_base
    (D : SpecialPeriods.CuspFamily.Data) (x : D.Space) :
    letI := D.chartedSpace
    letI :=
      CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
        D.smallDrift
    CuspQuotient.projection D.correction D.radius (D.puncturedFamilyBiholomorph x) =
      (D.projection x : ℂ) := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  obtain ⟨y, rfl⟩ := D.iteratedCover_surjective x
  rw [D.puncturedFamilyBiholomorph_iteratedCover, D.projection_iteratedCover]
  exact CuspUniformization.projection_totalCuspCover D.correction D.radius y

def ThreefoldOverlapMappingTorus.Cusp.heightContraction (r : ℝ) (h : Height r) :
    (ContinuousMap.const (Height r) h).Homotopy (ContinuousMap.id (Height r))
    where
  toFun
    p :=
    ⟨(1 - (p.1 : ℝ)) * (h : ℝ) + (p.1 : ℝ) * (p.2 : ℝ),
      (convex_Ioi (heightThreshold r)) h.property p.2.property (sub_nonneg.mpr p.1.property.2)
        p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩
  continuous_toFun :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change (1 - (0 : ℝ)) * (h : ℝ) + 0 * (x : ℝ) = (h : ℝ)
    simp only [sub_zero, one_mul, MulZeroClass.zero_mul, add_zero]
  map_one_left
    x := by
    apply Subtype.ext
    change (1 - (1 : ℝ)) * (h : ℝ) + 1 * (x : ℝ) = (x : ℝ)
    simp only [sub_self, MulZeroClass.zero_mul, one_mul, zero_add]

def ThreefoldOverlapMappingTorus.Cusp.heightProductHomotopyEquiv (r : ℝ) (h : Height r) :
    (Height r × Boundary) ≃ₕ Boundary
    where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const Boundary h).prodMk (ContinuousMap.id Boundary)
  left_inv :=
    (show (ContinuousMap.const (Height r) h).Homotopic (ContinuousMap.id (Height r)) from
          ⟨heightContraction r h⟩).prodMap
      (.refl (ContinuousMap.id Boundary))
  right_inv := .refl (ContinuousMap.id Boundary)

def ThreefoldOverlapMappingTorus.Cusp.familyMappingTorusHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) : D.Space ≃ₕ Boundary :=
  (familyProductHomeomorph D).toHomotopyEquiv.trans (heightProductHomotopyEquiv D.radius h)

def ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    D.Space ≃ₜ CuspUniformization.PuncturedQuotient D.correction D.radius := by
  letI := D.chartedSpace
  letI :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact D.puncturedFamilyBiholomorph.toHomeomorph

@[simp]
theorem ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (p : CuspUniformization.LogCover D.radius) :
    puncturedFamilyHomeomorph D (D.iteratedCover p) =
      CuspUniformization.puncturedCuspCover D.correction D.radius p := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact D.puncturedFamilyBiholomorph_iteratedCover p

theorem ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_base
    (D : SpecialPeriods.CuspFamily.Data) (q : D.Space) :
    CuspQuotient.projection D.correction D.radius (puncturedFamilyHomeomorph D q) =
      (D.projection q : ℂ) := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact D.puncturedFamilyBiholomorph_preserves_base q

theorem ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (x : RealPlane₄) :
    puncturedFamilyHomeomorph D (D.quotient (s, standardLattice.mkQ x)) =
      CuspUniformization.puncturedCuspCover D.correction D.radius
        ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩ := by
  have he :
    D.iteratedCover ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩ =
      D.quotient (s, standardLattice.mkQ x) := by
    change
      D.quotient
          (s, standardLattice.mkQ ((D.periods.periodEquiv s).symm (D.periods.periodEquiv s x))) =
        _
    rw [LinearEquiv.symm_apply_apply]
  rw [← he, puncturedFamilyHomeomorph_iteratedCover]

def ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.PuncturedQuotient D.correction D.radius ≃ₜ Height D.radius × Boundary :=
  (puncturedFamilyHomeomorph D).symm.trans (familyProductHomeomorph D)

def ThreefoldOverlapMappingTorus.Cusp.puncturedMappingTorusHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) :
    CuspUniformization.PuncturedQuotient D.correction D.radius ≃ₕ Boundary :=
  (puncturedFamilyHomeomorph D).symm.toHomotopyEquiv.trans (familyMappingTorusHomotopyEquiv D h)

def ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion (D : SpecialPeriods.CuspFamily.Data)
    (h : Height D.radius) :
    C(Boundary, CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (puncturedMappingTorusHomotopyEquiv D h).invFun

def ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder (D : SpecialPeriods.CuspFamily.Data)
    (h : Height D.radius) :
    C(ℝ × RealTorus₄, CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp ⟨MappingTorus.mk monodromy, MappingTorus.mk_continuous monodromy⟩

theorem ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_apply
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    boundaryCylinder D h (t, x) =
      puncturedFamilyHomeomorph D (D.quotient (logPoint D.radius D.radius_pos t h, x)) := by
  change
    puncturedFamilyHomeomorph D
        ((familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x))) =
      _
  rw [familyProductHomeomorph_symm_mk]

theorem ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealPlane₄) :
    boundaryCylinder D h (t, standardLattice.mkQ x) =
      CuspUniformization.puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos t h : ℂ),
            D.periods.periodEquiv (logPoint D.radius D.radius_pos t h) x),
          (logPoint D.radius D.radius_pos t h).property⟩ := by
  rw [boundaryCylinder_apply, puncturedFamilyHomeomorph_realCoordinates]

theorem ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_base
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius (boundaryCylinder D h (t, x)) =
      CuspUniformization.exponential ((t : ℂ) + (h : ℝ) * Complex.I) := by
  rw [boundaryCylinder_apply, puncturedFamilyHomeomorph_base, D.projection_quotient]
  rfl

def ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured (D : SpecialPeriods.CuspFamily.Data)
    (h : Height D.radius) :
    C(RealTorus₄, CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp (MappingTorus.HomologyCover.fibreInclusion monodromy)

theorem ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (x : RealPlane₄) :
    fibreToPunctured D h (standardLattice.mkQ x) =
      CuspUniformization.puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos 0 h : ℂ),
            D.periods.periodEquiv (logPoint D.radius D.radius_pos 0 h) x),
          (logPoint D.radius D.radius_pos 0 h).property⟩ :=
  boundaryCylinder_realCoordinates D h 0 x

abbrev ThreefoldHomologyFinitenessCusp.FullSpace (D : SpecialPeriods.CuspFamily.Data) :=
  CuspQuotient.QuotientSpace D.correction D.radius

def ThreefoldHomologyFinitenessCusp.parameterNorm (D : SpecialPeriods.CuspFamily.Data) :
    C(FullSpace D, ℝ) :=
  ⟨fun x => ‖CuspQuotient.projection D.correction D.radius x‖,
    (CuspQuotient.projection_continuous D.correction D.radius).norm⟩

private theorem ThreefoldHomologyFinitenessCusp.exponential_norm_mo1973_10230 (s : ℂ) :
    ‖CuspUniformization.exponential s‖ = Real.exp (-2 * Real.pi * s.im) :=
  (Real.exp_log (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero s))).symm.trans
    (congrArg Real.exp (CuspUniformization.log_norm_exponential s))

theorem ThreefoldHomologyFinitenessCusp.parameterNorm_product_symm
    (D : SpecialPeriods.CuspFamily.Data)
    (p :
      ThreefoldOverlapMappingTorus.Cusp.Height D.radius ×
        ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    parameterNorm D ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm p) =
      Real.exp (-2 * Real.pi * (p.1 : ℝ)) := by
  rcases p with ⟨h, y⟩
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective ThreefoldOverlapMappingTorus.Cusp.monodromy y
  change
    ‖CuspQuotient.projection D.correction D.radius
          (ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph D
            ((ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph D).symm
              (h, MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, x))))‖ =
      _
  rw [ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph_symm_mk,
    ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_base, D.projection_quotient]
  change
    ‖CuspUniformization.exponential
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h)‖ =
      _
  rw [exponential_norm_mo1973_10230, ThreefoldOverlapMappingTorus.Cusp.logPoint_im]

theorem ThreefoldHomologyFinitenessCusp.parameterNorm_punctured
    (D : SpecialPeriods.CuspFamily.Data)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D x =
      Real.exp
        (-2 * Real.pi *
          ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1 : ℝ)) := by
  have h :=
    parameterNorm_product_symm D
      (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x)
  rwa [Homeomorph.symm_apply_apply] at h

def ThreefoldHomologyFinitenessCusp.heightCutoff (r H : ℝ) :
    C(unitInterval × ThreefoldOverlapMappingTorus.Cusp.Height r,
      ThreefoldOverlapMappingTorus.Cusp.Height r)
    where
  toFun
    p :=
    ⟨(p.2 : ℝ) + (p.1 : ℝ) * (Max.max (p.2 : ℝ) H - (p.2 : ℝ)),
      lt_of_lt_of_le p.2.property
        (le_add_of_nonneg_right (mul_nonneg p.1.property.1 (sub_nonneg.mpr (le_max_left _ _))))⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (((continuous_subtype_val.comp continuous_snd).max continuous_const).sub
              (continuous_subtype_val.comp continuous_snd)))).subtype_mk
      _

@[simp]
theorem ThreefoldHomologyFinitenessCusp.heightCutoff_zero (r H : ℝ)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) : heightCutoff r H (0, h) = h := by
  apply Subtype.ext
  change (h : ℝ) + 0 * (Max.max (h : ℝ) H - (h : ℝ)) = (h : ℝ)
  simp

theorem ThreefoldHomologyFinitenessCusp.heightCutoff_one (r H : ℝ)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) :
    (heightCutoff r H (1, h) : ℝ) = Max.max (h : ℝ) H := by
  change (h : ℝ) + 1 * (Max.max (h : ℝ) H - (h : ℝ)) = _
  ring

theorem ThreefoldHomologyFinitenessCusp.heightCutoff_ge (r H : ℝ) (t : unitInterval)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) : (h : ℝ) ≤ (heightCutoff r H (t, h) : ℝ) :=
  le_add_of_nonneg_right (mul_nonneg t.property.1 (sub_nonneg.mpr (le_max_left _ _)))

theorem ThreefoldHomologyFinitenessCusp.heightCutoff_fixed (r H : ℝ) (t : unitInterval)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height r) (hh : H ≤ (h : ℝ)) :
    heightCutoff r H (t, h) = h := by
  apply Subtype.ext
  change (h : ℝ) + (t : ℝ) * (Max.max (h : ℝ) H - (h : ℝ)) = (h : ℝ)
  rw [max_eq_left hh, sub_self, MulZeroClass.mul_zero, add_zero]

def ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff (D : SpecialPeriods.CuspFamily.Data)
    (H : ℝ) :
    C(unitInterval × CuspUniformization.PuncturedQuotient D.correction D.radius,
      CuspUniformization.PuncturedQuotient D.correction D.radius)
    where
  toFun
    p :=
    (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
      (heightCutoff D.radius H
          (p.1, (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D p.2).1),
        (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D p.2).2)
  continuous_toFun :=
    (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm.continuous.comp
      (((heightCutoff D.radius H).continuous.comp
            (continuous_fst.prodMk
              (continuous_fst.comp
                ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).continuous.comp
                  continuous_snd)))).prodMk
        (continuous_snd.comp
          ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).continuous.comp
            continuous_snd)))

theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_product
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D
        (puncturedHeightCutoff D H (t, x)) =
      (heightCutoff D.radius H
          (t, (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1),
        (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).2) :=
  (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).apply_symm_apply _

@[simp]
theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_zero
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    puncturedHeightCutoff D H (0, x) = x := by
  apply (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).injective
  rw [puncturedHeightCutoff_product, heightCutoff_zero]

theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_parameterNorm
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (t, x)) =
      Real.exp
        (-2 * Real.pi *
          (heightCutoff D.radius H
              (t, (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1) :
            ℝ)) := by exact parameterNorm_product_symm D _

theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_norm_nonincrease
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (t, x)) ≤ parameterNorm D x := by
  rw [puncturedHeightCutoff_parameterNorm, parameterNorm_punctured]
  apply Real.exp_le_exp.mpr
  have hh :=
    heightCutoff_ge D.radius H t
      (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1
  nlinarith [Real.pi_pos]

def ThreefoldHomologyFinitenessCusp.cutoffRadius (H : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * H)

theorem ThreefoldHomologyFinitenessCusp.cutoffRadius_pos (H : ℝ) : 0 < cutoffRadius H :=
  Real.exp_pos _

theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_one_norm_le
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius) :
    parameterNorm D (puncturedHeightCutoff D H (1, x)) ≤ cutoffRadius H := by
  rw [puncturedHeightCutoff_parameterNorm, heightCutoff_one]
  apply Real.exp_le_exp.mpr
  have hh :=
    le_max_right ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1 : ℝ) H
  nlinarith [Real.pi_pos]

theorem ThreefoldHomologyFinitenessCusp.puncturedHeightCutoff_fixed
    (D : SpecialPeriods.CuspFamily.Data) (H : ℝ) (t : unitInterval)
    (x : CuspUniformization.PuncturedQuotient D.correction D.radius)
    (hx : parameterNorm D x < cutoffRadius H) : puncturedHeightCutoff D H (t, x) = x := by
  have hh : H ≤ ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D x).1 : ℝ) := by
    rw [parameterNorm_punctured] at hx
    have he := Real.exp_lt_exp.mp hx
    nlinarith [Real.pi_pos]
  apply (ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).injective
  rw [puncturedHeightCutoff_product, heightCutoff_fixed D.radius H t _ hh]

theorem ThreefoldHomologyFinitenessCusp.cutoffRadius_threshold_lt {δ : ℝ} (hδ : 0 < δ) :
    cutoffRadius (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1) < δ := by
  apply (Real.log_lt_log_iff (cutoffRadius_pos _) hδ).mp
  change
    Real.log
        (Real.exp (-2 * Real.pi * (ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ + 1))) <
      Real.log δ
  rw [Real.log_exp]
  have ht : 2 * Real.pi * ThreefoldOverlapMappingTorus.Cusp.heightThreshold δ = -Real.log δ := by
    unfold ThreefoldOverlapMappingTorus.Cusp.heightThreshold
    exact mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) Real.pi_pos))
  nlinarith [Real.pi_pos]

theorem ToricSpace.factors_continuous (s : ToricFan.Triangle) : Continuous (factors s) := by
  apply continuous_pi
  intro i
  change Continuous (fun u : ActingTorus => ∏ j, (u j : ℂ) ^ s.dual i j)
  exact
    continuous_finsetProd _
      (fun j _ =>
        (Units.continuous_val.comp (continuous_apply j)).zpow₀ _ (fun u => Or.inl (u j).ne_zero))

theorem ToricSpace.torusAction_joint_continuous :
    Continuous (fun p : ActingTorus × Space => torusAction p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨u, x⟩
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hlocal :
    Continuous
      (fun p : ActingTorus × ToricCharts.CoordinateSpace 3 =>
        ToricSpace.inclusion s (scale s p.1 p.2)) :=
    (inclusion_openEmbedding s).continuous.comp
      (((factors_continuous s).comp continuous_fst).mul continuous_snd)
  apply
    (((Topology.IsOpenEmbedding.id (X := ActingTorus)).prodMap
            (inclusion_openEmbedding s)).continuousAt_iff
        (g := fun p : ActingTorus × Space => torusAction p.1 p.2) (x := (u, z))).mp
  change
    ContinuousAt
      (fun p : ActingTorus × ToricCharts.CoordinateSpace 3 =>
        torusAction p.1 (ToricSpace.inclusion s p.2))
      (u, z)
  simpa only [torusAction_inclusion] using hlocal.continuousAt (x := (u, z))

theorem ToricSpace.fibreMultiplier_continuous : Continuous fibreMultiplier := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

def CuspRetraction.realToComplex : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ)
    where
  toFun v i := (v i : ℂ)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp [Complex.real_smul]

@[simp]
theorem CuspRetraction.realToComplex_apply (v : Fin 2 → ℝ) (i : Fin 2) :
    realToComplex v i = (v i : ℂ) :=
  rfl

theorem CuspRetraction.realToComplex_continuous : Continuous realToComplex := by
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_apply i)

@[simp]
theorem CuspRetraction.norm_realToComplex (v : Fin 2 → ℝ) : ‖realToComplex v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realToComplex_apply, Complex.norm_real] using norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [realToComplex_apply, Complex.norm_real] using norm_le_pi_norm (realToComplex v) i

def CuspRetraction.expFibreUnits (a : Fin 2 → ℂ) : Fin 2 → ℂˣ := fun i =>
  Units.mk0 (CuspUniformization.exponential (a i)) (CuspUniformization.exponential_ne_zero _)

@[simp]
theorem CuspRetraction.expFibreUnits_coe (a : Fin 2 → ℂ) (i : Fin 2) :
    (expFibreUnits a i : ℂ) = CuspUniformization.exponential (a i) :=
  rfl

@[simp]
theorem CuspRetraction.expFibreUnits_zero : expFibreUnits 0 = 1 := by
  ext i
  simp [expFibreUnits]

theorem CuspRetraction.expFibreUnits_add (a b : Fin 2 → ℂ) :
    expFibreUnits (a + b) = expFibreUnits a * expFibreUnits b := by
  ext i
  simp [expFibreUnits, CuspUniformization.exponential_add]

theorem CuspRetraction.expFibreUnits_continuous : Continuous expFibreUnits := by
  apply continuous_pi
  intro i
  apply Units.continuous_iff.mpr
  have h : Continuous (fun a : Fin 2 → ℂ => CuspUniformization.exponential (a i)) :=
    CuspUniformization.exponential_holomorphic.continuous.comp (continuous_apply i)
  exact ⟨h, h.inv₀ (fun a => CuspUniformization.exponential_ne_zero (a i))⟩

def CuspRetraction.expFibreAction (a : Fin 2 → ℂ) (x : ToricSpace.Space) : ToricSpace.Space :=
  ToricSpace.torusAction (ToricSpace.fibreMultiplier (expFibreUnits a)) x

@[simp]
theorem CuspRetraction.expFibreAction_zero (x : ToricSpace.Space) : expFibreAction 0 x = x := by
  simp [expFibreAction]

theorem CuspRetraction.expFibreAction_add (a b : Fin 2 → ℂ) (x : ToricSpace.Space) :
    expFibreAction a (expFibreAction b x) = expFibreAction (a + b) x := by
  simp only [expFibreAction, ToricSpace.torusAction_mul, expFibreUnits_add,
    ToricSpace.fibreMultiplier_mul]

@[simp]
theorem CuspRetraction.time_expFibreAction (a : Fin 2 → ℂ) (x : ToricSpace.Space) :
    ToricSpace.time (expFibreAction a x) = ToricSpace.time x :=
  ToricSpace.time_fibreMultiplier _ _

theorem CuspRetraction.expFibreAction_continuous :
    Continuous (fun p : (Fin 2 → ℂ) × ToricSpace.Space => expFibreAction p.1 p.2) := by
  have h :
    Continuous
      (fun p : (Fin 2 → ℂ) × ToricSpace.Space =>
        (ToricSpace.fibreMultiplier (expFibreUnits p.1), p.2)) :=
    ((ToricSpace.fibreMultiplier_continuous.comp expFibreUnits_continuous).comp
          continuous_fst).prodMk
      continuous_snd
  change
    Continuous
      ((fun p : ToricSpace.ActingTorus × ToricSpace.Space => ToricSpace.torusAction p.1 p.2) ∘
        (fun p : (Fin 2 → ℂ) × ToricSpace.Space =>
          (ToricSpace.fibreMultiplier (expFibreUnits p.1), p.2)))
  exact Continuous.comp ToricSpace.torusAction_joint_continuous h

theorem CuspRetraction.expFibreAction_translate (a : Fin 2 → ℂ) (v : Fin 2 → ℤ)
    (x : ToricSpace.Space) :
    expFibreAction a (ToricSpace.translate v x) = ToricSpace.translate v (expFibreAction a x) :=
  ToricSpace.fibreMultiplier_translate _ _ _

theorem CuspRetraction.torusCoordinates_expFibreAction (a : Fin 2 → ℂ) {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) (i : Fin 2) :
    ToricSpace.torusCoordinates (expFibreAction a x) i.castSucc =
      CuspUniformization.exponential (a i) * ToricSpace.torusCoordinates x i.castSucc := by
  rw [expFibreAction, ToricSpace.torusCoordinates_action _ hx]
  fin_cases i <;> rfl

theorem CuspRetraction.position_expFibreAction (a : Fin 2 → ℂ) {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) :
    ToricSpace.position (expFibreAction a x) =
      ToricSpace.position x +
        (Real.log ‖ToricSpace.time x‖)⁻¹ • (fun i => -2 * Real.pi * (a i).im) := by
  ext i
  simp only [ToricSpace.position, time_expFibreAction, ToricSpace.logCoordinates,
    ToricSpace.logNorm, torusCoordinates_expFibreAction a hx, norm_mul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr (CuspUniformization.exponential_ne_zero _))
      (norm_ne_zero_iff.mpr (ToricSpace.torusCoordinates_nonzero hx _)),
    CuspUniformization.log_norm_exponential]
  ring

theorem CuspRetraction.twistedTranslate_eq_expFibreAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    ToricSpace.twistedTranslate C v x =
      expFibreAction (C (ToricSpace.time x) *ᵥ (fun i => (v i : ℂ)))
        (ToricSpace.translate (ToricSpace.cuspVector v) x) := by
  unfold ToricSpace.twistedTranslate ToricSpace.variableMultiplier
  rw [ToricSpace.time_translate]
  rfl

@[simp]
theorem CuspRetraction.position_of_time_zero {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) :
    ToricSpace.position x = 0 := by
  ext i
  simp [ToricSpace.position, hx]

def ToricSpace.displacementMatrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0] + (Real.log ‖t‖)⁻¹ • driftMatrix C t

theorem ToricSpace.displacementMatrix_mulVec (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (y : Fin 2 → ℝ) : displacementMatrix C t *ᵥ y = displacement C t y := by
  rw [displacementMatrix, Matrix.add_mulVec, Matrix.smul_mulVec]
  change
    !![(0 : ℝ), 1; -1, 0] *ᵥ y + (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ y) =
      realCuspVector y + (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ y)
  congr 1
  ext i
  fin_cases i <;> simp [realCuspVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def ToricSpace.inverseDisplacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (displacementMatrix C t)⁻¹.mulVecLin

@[simp]
theorem ToricSpace.inverseDisplacement_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (y z : Fin 2 → ℝ) :
    inverseDisplacement C t (y + z) = inverseDisplacement C t y + inverseDisplacement C t z :=
  map_add _ _ _

theorem ToricSpace.displacementMatrix_isUnit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    IsUnit (displacementMatrix C t) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro y
  obtain ⟨z, hz⟩ := (displacement_bijective C ht hR).surjective y
  exact ⟨z, (displacementMatrix_mulVec C t z).trans hz⟩

theorem ToricSpace.displacementMatrix_det_ne_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    (displacementMatrix C t).det ≠ 0 :=
  isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (displacementMatrix_isUnit C ht hR))

theorem ToricSpace.inverseDisplacement_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (y : Fin 2 → ℝ) : inverseDisplacement C t (displacement C t y) = y := by
  change (displacementMatrix C t)⁻¹ *ᵥ displacement C t y = y
  rw [← displacementMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (displacementMatrix_det_ne_zero C ht hR)),
    Matrix.one_mulVec]

theorem ToricSpace.displacement_inverseDisplacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (y : Fin 2 → ℝ) : displacement C t (inverseDisplacement C t y) = y := by
  rw [← displacementMatrix_mulVec]
  change displacementMatrix C t *ᵥ ((displacementMatrix C t)⁻¹ *ᵥ y) = y
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (displacementMatrix_det_ne_zero C ht hR)),
    Matrix.one_mulVec]

theorem ToricSpace.inverseDisplacement_norm_le (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (y : Fin 2 → ℝ) : ‖inverseDisplacement C t y‖ ≤ 2 * ‖y‖ := by
  have h := displacement_lower_bound C ht hR (inverseDisplacement C t y)
  rwa [displacement_inverseDisplacement C ht hR y] at h

theorem ToricSpace.displacementMatrix_continuousAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t) (ht0 : t ≠ 0) (htlog : Real.log ‖t‖ ≠ 0) :
    ContinuousAt (displacementMatrix C) t := by
  have hlog : ContinuousAt (fun s : ℂ => (Real.log ‖s‖)⁻¹) t :=
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr ht0)).comp continuous_norm.continuousAt).inv₀
      htlog
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change
    ContinuousAt
      (fun s : ℂ => !![(0 : ℝ), 1; -1, 0] i j + (Real.log ‖s‖)⁻¹ * (-2 * Real.pi * (C s i j).im))
      t
  exact
    continuousAt_const.add
      (hlog.mul (continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hC i j))))

theorem ToricSpace.inverseDisplacement_continuousAt_of_det_ne_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ} (hC : ∀ i j, ContinuousAt (fun s => C s i j) t)
    (ht0 : t ≠ 0) (htlog : Real.log ‖t‖ ≠ 0) (hdet : (displacementMatrix C t).det ≠ 0)
    (y : Fin 2 → ℝ) :
    ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2) (t, y) := by
  have hi : ContinuousAt (fun s : ℂ => (displacementMatrix C s)⁻¹) t :=
    (continuousAt_matrix_inv (displacementMatrix C t)
          (by simpa only [Ring.inverse_eq_inv'] using ContinuousInv₀.continuousAt_inv₀ hdet)).comp
      (displacementMatrix_continuousAt C hC ht0 htlog)
  have hm : Continuous (fun p : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hp : ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => (displacementMatrix C p.1)⁻¹) (t, y) :=
    ContinuousAt.comp (f := fun p : ℂ × (Fin 2 → ℝ) => p.1) (g := fun s : ℂ =>
      (displacementMatrix C s)⁻¹) hi continuous_fst.continuousAt
  exact hm.continuousAt.comp (hp.prodMk continuous_snd.continuousAt)

theorem ToricSpace.inverseDisplacement_continuousAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t) (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) (y : Fin 2 → ℝ) :
    ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2) (t, y) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  exact
    inverseDisplacement_continuousAt_of_det_ne_zero C hC ht0 ht.ne
      (displacementMatrix_det_ne_zero C ht hR) y

def CuspRetraction.frozen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (_t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  C 0

def CuspRetraction.correction (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : ToricSpace.Space) :
    Fin 2 → ℂ :=
  (D (ToricSpace.time x) - C (ToricSpace.time x)) *ᵥ
    realToComplex (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x))

def CuspRetraction.changeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : ToricSpace.Space) :
    ToricSpace.Space :=
  expFibreAction (correction C D x) x

@[simp]
theorem CuspRetraction.time_changeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ToricSpace.Space) : ToricSpace.time (changeTwist C D x) = ToricSpace.time x :=
  time_expFibreAction _ _

@[simp]
theorem CuspRetraction.correction_of_time_zero (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) : correction C D x = 0 := by
  rw [correction, position_of_time_zero hx, map_zero, map_zero, Matrix.mulVec_zero]

@[simp]
theorem CuspRetraction.changeTwist_of_time_zero (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) : changeTwist C D x = x := by
  rw [changeTwist, correction_of_time_zero C D hx, expFibreAction_zero]

def CuspRetraction.tubeChangeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : ToricSpace.Tube (CuspQuotient.disc ε)) : ToricSpace.Tube (CuspQuotient.disc ε) :=
  ⟨changeTwist C D x,
    by
    change ToricSpace.time (changeTwist C D x) ∈ CuspQuotient.disc ε
    rw [time_changeTwist]
    exact x.2⟩

abbrev CuspRetraction.ClosedTube (η : ℝ) :=
  { x : ToricSpace.Space // ‖ToricSpace.time x‖ ≤ η }

def CuspRetraction.closedTubeChangeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (x : ClosedTube η) : ClosedTube η :=
  ⟨changeTwist C D x, by
    rw [time_changeTwist]
    exact x.2⟩

theorem ToricSpace.position_continuousAt {x : Space} (hx : time x ≠ 0)
    (hlog : Real.log ‖time x‖ ≠ 0) : ContinuousAt position x := by
  have hxT : x ∈ openTorus := (mem_openTorus_iff x).mpr hx
  have hc : ContinuousAt torusCoordinates x :=
    torusCoordinates_holomorphic.continuousOn.continuousAt (openTorus_isOpen.mem_nhds hxT)
  have ht : ContinuousAt (fun y : Space => Real.log ‖time y‖) x :=
    ContinuousAt.comp (f := fun y : Space => ‖time y‖) (g := Real.log)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hx))
      time_holomorphic.continuous.continuousAt.norm
  apply continuousAt_pi.mpr
  intro i
  have hi : ContinuousAt (fun y : Space => torusCoordinates y i.castSucc) x :=
    (continuous_apply i.castSucc).continuousAt.comp hc
  have hli : ContinuousAt (fun y : Space => Real.log ‖torusCoordinates y i.castSucc‖) x :=
    ContinuousAt.comp (f := fun y : Space => ‖torusCoordinates y i.castSucc‖) (g := Real.log)
      (Real.continuousAt_log (norm_ne_zero_iff.mpr (torusCoordinates_nonzero hxT i.castSucc)))
      hi.norm
  exact hli.div ht hlog

theorem ToricSpace.position_norm_le_on_chartNeighbourhood {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {s : ToricFan.Triangle} {n : ℕ} {x : Space} (hx : x ∈ chartNeighbourhood s n ε) :
    ‖position x‖ ≤ Max.max 0 (positionBound s ((n : ℝ) + 2) ε) := by
  by_cases ht : time x = 0
  · have hp : position x = 0 := by
      ext i
      simp [position, ht]
    rw [hp, norm_zero]
    exact le_max_left _ _
  · obtain ⟨z, hz, rfl⟩ := hx
    have hzT : z ∈ ToricCharts.torus := by
      rw [← inclusion_preimage_openTorus s]
      exact (mem_openTorus_iff _).mpr ht
    have hS : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact
      (position_norm_bound s hzT hS hε hε1 hz.2 (fun j => (hz.1 j).le)).trans (le_max_right _ _)

theorem ToricSpace.position_locally_bounded {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {x : Space}
    (ht : ‖time x‖ < ε) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ y in 𝓝 x, ‖time y‖ < ε ∧ ‖position y‖ ≤ B := by
  obtain ⟨s, n, hx⟩ := chartNeighbourhood_cover ht
  refine ⟨Max.max 0 (positionBound s ((n : ℝ) + 2) ε), le_max_left _ _, ?_⟩
  filter_upwards [(chartNeighbourhood_open s n ε).mem_nhds hx] with y hy
  exact ⟨chartNeighbourhood_time hy, position_norm_le_on_chartNeighbourhood hε hε1 hy⟩

def CuspRetraction.complexEntryNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖fun i : Fin 2 => fun j : Fin 2 => A i j‖

theorem CuspRetraction.complexEntryNorm_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ complexEntryNorm A :=
  norm_nonneg _

theorem CuspRetraction.norm_complex_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    ‖A *ᵥ v‖ ≤ 2 * complexEntryNorm A * ‖v‖ := by
  apply
    (pi_norm_le_iff_of_nonneg
        (by
          have := complexEntryNorm_nonneg A
          positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, complexEntryNorm A * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact
        mul_le_mul
          ((norm_le_pi_norm (A i) j).trans
            (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 => A k l) i))
          (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * complexEntryNorm A * ‖v‖ := by simp; ring

theorem CuspRetraction.correction_norm_le (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    ‖correction C D x‖ ≤
      4 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
        ‖ToricSpace.position x‖ := by
  have hA := complexEntryNorm_nonneg (D (ToricSpace.time x) - C (ToricSpace.time x))
  calc
    ‖correction C D x‖ ≤
        2 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
          ‖ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)‖ := by
      simpa only [correction, norm_realToComplex] using
        norm_complex_mulVec_le (D (ToricSpace.time x) - C (ToricSpace.time x))
          (realToComplex
            (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)))
    _ ≤
        2 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
          (2 * ‖ToricSpace.position x‖) := by
      exact
        mul_le_mul_of_nonneg_left (ToricSpace.inverseDisplacement_norm_le C ht hR _)
          (by positivity)
    _ =
        4 * complexEntryNorm (D (ToricSpace.time x) - C (ToricSpace.time x)) *
          ‖ToricSpace.position x‖ := by ring

theorem CuspRetraction.correction_continuousAt_central (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousAt (fun t => C t i j) 0)
    (hD : ∀ i j, ContinuousAt (fun t => D t i j) 0) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hx : ToricSpace.time x = 0) :
    ContinuousAt (correction C D) x := by
  obtain ⟨B, hB, hbound⟩ :=
    ToricSpace.position_locally_bounded hε hε1 (x := x) (by simpa only [hx, norm_zero] using hε)
  have htime : Filter.Tendsto ToricSpace.time (𝓝 x) (𝓝 0) := by
    simpa only [hx] using (ToricSpace.time_holomorphic.continuous.continuousAt (x := x)).tendsto
  have hdelta :
    ContinuousAt (fun t : ℂ => fun i : Fin 2 => fun j : Fin 2 => D t i j - C t i j) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (hD i j).sub (hC i j)
  have hnorm :
    Filter.Tendsto
      (fun y : ToricSpace.Space =>
        complexEntryNorm (D (ToricSpace.time y) - C (ToricSpace.time y)))
      (𝓝 x) (𝓝 0) := by
    have hz : (fun i : Fin 2 => fun j : Fin 2 => D 0 i j - C 0 i j) = 0 := by
      ext i j
      simp only [hzero, sub_self, Pi.zero_apply]
    have h := hdelta.norm.tendsto.comp htime
    rw [hz, norm_zero] at h
    exact h
  have hlim :
    Filter.Tendsto
      (fun y : ToricSpace.Space =>
        4 * complexEntryNorm (D (ToricSpace.time y) - C (ToricSpace.time y)) * B)
      (𝓝 x) (𝓝 0) := by
    simpa only [MulZeroClass.mul_zero, MulZeroClass.zero_mul] using
      (tendsto_const_nhds.mul hnorm).mul (tendsto_const_nhds (x := B))
  have hb :
    ∀ᶠ y in 𝓝 x,
      ‖correction C D y‖ ≤
        4 * complexEntryNorm (D (ToricSpace.time y) - C (ToricSpace.time y)) * B := by
    filter_upwards [hbound] with y hy
    by_cases hy0 : ToricSpace.time y = 0
    · rw [correction_of_time_zero C D hy0, norm_zero]
      have := complexEntryNorm_nonneg (D (ToricSpace.time y) - C (ToricSpace.time y))
      positivity
    · have hn : 0 < ‖ToricSpace.time y‖ := norm_pos_iff.mpr hy0
      exact
        (correction_norm_le C D (Real.log_neg hn (hy.1.trans hε1)) (hR _ hn hy.1)).trans
          (mul_le_mul_of_nonneg_left hy.2
            (by
              have := complexEntryNorm_nonneg (D (ToricSpace.time y) - C (ToricSpace.time y))
              positivity))
  change Filter.Tendsto (correction C D) (𝓝 x) (𝓝 (correction C D x))
  rw [correction_of_time_zero C D hx]
  exact squeeze_zero_norm' hb hlim

theorem CuspRetraction.correction_continuousAt_of_time_ne_zero
    (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hx0 : ToricSpace.time x ≠ 0)
    (hxε : ‖ToricSpace.time x‖ < ε) : ContinuousAt (correction C D) x := by
  have hmem : ToricSpace.time x ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxε
  have hC' (i j) : ContinuousAt (fun t => C t i j) (ToricSpace.time x) :=
    (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hD' (i j) : ContinuousAt (fun t => D t i j) (ToricSpace.time x) :=
    (hD i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hn : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx0
  have ht : Real.log ‖ToricSpace.time x‖ < 0 := Real.log_neg hn (hxε.trans hε1)
  have htime : ContinuousAt ToricSpace.time x :=
    ToricSpace.time_holomorphic.continuous.continuousAt
  have hi :
    ContinuousAt
      (fun y : ToricSpace.Space =>
        ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y))
      x := by
    exact
      ContinuousAt.comp (f := fun y : ToricSpace.Space =>
        (ToricSpace.time y, ToricSpace.position y)) (g := fun p : ℂ × (Fin 2 → ℝ) =>
        ToricSpace.inverseDisplacement C p.1 p.2)
        (ToricSpace.inverseDisplacement_continuousAt C hC' ht (hR _ hn hxε)
          (ToricSpace.position x))
        (htime.prodMk (ToricSpace.position_continuousAt hx0 ht.ne))
  have hv :
    ContinuousAt
      (fun y : ToricSpace.Space =>
        realToComplex
          (ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y)))
      x := by
    exact
      ContinuousAt.comp (f := fun y : ToricSpace.Space =>
        ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y)) (g :=
        fun u : Fin 2 → ℝ => realToComplex u) realToComplex_continuous.continuousAt hi
  have hm :
    ContinuousAt (fun y : ToricSpace.Space => D (ToricSpace.time y) - C (ToricSpace.time y)) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact ((hD' i j).comp htime).sub ((hC' i j).comp htime)
  have hmul : Continuous (fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  change
    ContinuousAt
      ((fun p : Matrix (Fin 2) (Fin 2) ℂ × (Fin 2 → ℂ) => p.1 *ᵥ p.2) ∘
        (fun y : ToricSpace.Space =>
          (D (ToricSpace.time y) - C (ToricSpace.time y),
            realToComplex
              (ToricSpace.inverseDisplacement C (ToricSpace.time y) (ToricSpace.position y)))))
      x
  exact ContinuousAt.comp hmul.continuousAt (hm.prodMk hv)

theorem CuspRetraction.correction_continuousAt (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hxε : ‖ToricSpace.time x‖ < ε) :
    ContinuousAt (correction C D) x := by
  by_cases hx0 : ToricSpace.time x = 0
  · have hmem : (0 : ℂ) ∈ Metric.ball 0 ε := by simpa using hε
    exact
      correction_continuousAt_central C D hε hε1
        (fun i j => (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem))
        (fun i j => (hD i j).continuousAt (Metric.isOpen_ball.mem_nhds hmem)) hzero hR hx0
  · exact correction_continuousAt_of_time_ne_zero C D hε1 hC hD hR hx0 hxε

theorem CuspRetraction.changeTwist_continuousAt (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) {x : ToricSpace.Space} (hxε : ‖ToricSpace.time x‖ < ε) :
    ContinuousAt (changeTwist C D) x := by
  change
    ContinuousAt
      ((fun p : (Fin 2 → ℂ) × ToricSpace.Space => expFibreAction p.1 p.2) ∘
        (fun y : ToricSpace.Space => (correction C D y, y)))
      x
  exact
    ContinuousAt.comp expFibreAction_continuous.continuousAt
      ((correction_continuousAt C D hε hε1 hC hD hzero hR hxε).prodMk continuousAt_id)

theorem CuspRetraction.changeTwist_continuousOn (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) :
    ContinuousOn (changeTwist C D) (ToricSpace.time ⁻¹' Metric.ball 0 ε) := by
  intro x hx
  have hxε : ‖ToricSpace.time x‖ < ε := by
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx
  exact (changeTwist_continuousAt C D hε hε1 hC hD hzero hR hxε).continuousWithinAt

theorem CuspRetraction.tubeChangeTwist_continuous (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) : Continuous (tubeChangeTwist C D ε) :=
  (changeTwist_continuousOn C D hε hε1 hC hD hzero hR).domRestrict.subtype_mk _

theorem CuspRetraction.displacement_change_matrix (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ)
    (u : Fin 2 → ℝ) :
    ToricSpace.displacement C t u +
        (fun i => (-2 * Real.pi) * (((D t - C t) *ᵥ (fun j => (u j : ℂ))) i).im / Real.log ‖t‖) =
      ToricSpace.displacement D t u := by
  ext i
  simp only [ToricSpace.displacement, LinearMap.add_apply, LinearMap.smul_apply,
    Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.sub_apply, Complex.add_im, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.mul_zero,
    ToricSpace.driftMatrix, div_eq_mul_inv]
  ring

theorem CuspRetraction.position_changeTwist (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus) (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    ToricSpace.position (changeTwist C D x) =
      ToricSpace.displacement D (ToricSpace.time x)
        (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)) := by
  rw [changeTwist, position_expFibreAction _ hx]
  have h :=
    displacement_change_matrix C D (ToricSpace.time x)
      (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x))
  rw [ToricSpace.displacement_inverseDisplacement C ht hC] at h
  convert h using 1
  congr 1
  ext i
  have hu :
    realToComplex (ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)) =
      (fun j =>
        ((ToricSpace.inverseDisplacement C (ToricSpace.time x) (ToricSpace.position x)) j : ℂ)) :=
    by
    ext j
    rfl
  simp only [correction, hu, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem CuspRetraction.correction_reverse (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus) (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4)
    (hD :
      ToricSpace.entryNorm (ToricSpace.driftMatrix D (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    correction D C (changeTwist C D x) = -correction C D x := by
  unfold correction
  rw [time_changeTwist, position_changeTwist C D hx ht hC,
    ToricSpace.inverseDisplacement_displacement D ht hD]
  rw [show
      C (ToricSpace.time x) - D (ToricSpace.time x) =
        -(D (ToricSpace.time x) - C (ToricSpace.time x))
      by abel,
    Matrix.neg_mulVec]

theorem CuspRetraction.changeTwist_inverse_on_torus (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus) (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4)
    (hD :
      ToricSpace.entryNorm (ToricSpace.driftMatrix D (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    changeTwist D C (changeTwist C D x) = x := by
  change expFibreAction (correction D C (changeTwist C D x)) (changeTwist C D x) = x
  rw [correction_reverse C D hx ht hC hD]
  change expFibreAction (-correction C D x) (expFibreAction (correction C D x) x) = x
  rw [expFibreAction_add, neg_add_cancel, expFibreAction_zero]

theorem CuspRetraction.changeTwist_inverse_on_disc (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : ε < 1) (hC : ToricSpace.SmallDrift C ε) (hD : ToricSpace.SmallDrift D ε)
    {x : ToricSpace.Space} (hx : ‖ToricSpace.time x‖ < ε) :
    changeTwist D C (changeTwist C D x) = x := by
  by_cases hx0 : ToricSpace.time x = 0
  · rw [changeTwist_of_time_zero C D hx0, changeTwist_of_time_zero D C hx0]
  · have hp : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx0
    exact
      changeTwist_inverse_on_torus C D ((ToricSpace.mem_openTorus_iff x).mpr hx0)
        (Real.log_neg hp (hx.trans hε)) (hC _ hp hx) (hD _ hp hx)

theorem CuspRetraction.correction_twistedTranslate (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus)
    (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    correction C D (ToricSpace.twistedTranslate C v x) =
      correction C D x +
        (D (ToricSpace.time x) - C (ToricSpace.time x)) *ᵥ (fun i => (v i : ℂ)) := by
  unfold correction
  rw [ToricSpace.time_twistedTranslate,
    ToricSpace.position_twistedTranslate_displacement C v hx ht.ne,
    ToricSpace.inverseDisplacement_add, ToricSpace.inverseDisplacement_displacement C ht hC,
    map_add, Matrix.mulVec_add]
  congr 2

theorem CuspRetraction.changeTwist_equivariant_on_torus (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : ToricSpace.Space} (hx : x ∈ ToricSpace.openTorus)
    (ht : Real.log ‖ToricSpace.time x‖ < 0)
    (hC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (ToricSpace.time x)) ≤
        -Real.log ‖ToricSpace.time x‖ / 4) :
    changeTwist C D (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate D v (changeTwist C D x) := by
  change
    expFibreAction (correction C D (ToricSpace.twistedTranslate C v x))
        (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate D v (expFibreAction (correction C D x) x)
  rw [correction_twistedTranslate C D v hx ht hC, twistedTranslate_eq_expFibreAction C v x,
    twistedTranslate_eq_expFibreAction D v (expFibreAction (correction C D x) x),
    time_expFibreAction, ← expFibreAction_translate, expFibreAction_add, expFibreAction_add]
  congr 1
  rw [Matrix.sub_mulVec]
  abel

theorem CuspRetraction.changeTwist_equivariant_on_disc (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (h₀ : C 0 = D 0) {ε : ℝ} (hε : ε < 1) (hC : ToricSpace.SmallDrift C ε) (v : Fin 2 → ℤ)
    {x : ToricSpace.Space} (hx : ‖ToricSpace.time x‖ < ε) :
    changeTwist C D (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate D v (changeTwist C D x) := by
  by_cases hx0 : ToricSpace.time x = 0
  · rw [changeTwist_of_time_zero C D (by simpa only [ToricSpace.time_twistedTranslate] using hx0),
      changeTwist_of_time_zero C D hx0, twistedTranslate_eq_expFibreAction C v x,
      twistedTranslate_eq_expFibreAction D v x, hx0, h₀]
  · have hp : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx0
    exact
      changeTwist_equivariant_on_torus C D v ((ToricSpace.mem_openTorus_iff x).mpr hx0)
        (Real.log_neg hp (hx.trans hε)) (hC _ hp hx)

theorem CuspRetraction.changeTwist_frozen_equivariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : ε < 1) (hC : ToricSpace.SmallDrift C ε) (v : Fin 2 → ℤ) {x : ToricSpace.Space}
    (hx : ‖ToricSpace.time x‖ < ε) :
    changeTwist C (frozen C) (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate (frozen C) v (changeTwist C (frozen C) x) :=
  changeTwist_equivariant_on_disc C (frozen C) rfl hε hC v hx

theorem CuspRetraction.position_unit_fibreAction (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1)
    (x : ToricSpace.Space) :
    ToricSpace.position (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) =
      ToricSpace.position x := by
  by_cases hx0 : ToricSpace.time x = 0
  · rw [position_of_time_zero (by simpa only [ToricSpace.time_fibreMultiplier] using hx0),
      position_of_time_zero hx0]
  · have hx := (ToricSpace.mem_openTorus_iff x).mpr hx0
    ext i
    simp only [ToricSpace.position, ToricSpace.time_fibreMultiplier, ToricSpace.logCoordinates,
      ToricSpace.logNorm, ToricSpace.torusCoordinates_action _ hx, Pi.mul_apply]
    fin_cases i <;> simp [ToricSpace.fibreMultiplier, hu]

theorem CuspRetraction.changeTwist_unit_fibreAction (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ToricSpace.Space) :
    changeTwist C D (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) =
      ToricSpace.torusAction (ToricSpace.fibreMultiplier u) (changeTwist C D x) := by
  have hc :
    correction C D (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) = correction C D x :=
    by simp only [correction, ToricSpace.time_fibreMultiplier, position_unit_fibreAction u hu]
  simp only [changeTwist, hc, expFibreAction, ToricSpace.torusAction_mul]
  rw [mul_comm]

def CuspRetraction.tubeHomeomorph (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) :
    ToricSpace.Tube (CuspQuotient.disc ε) ≃ₜ ToricSpace.Tube (CuspQuotient.disc ε)
    where
  toFun := tubeChangeTwist C D ε
  invFun := tubeChangeTwist D C ε
  left_inv
    x := by
    apply Subtype.ext
    exact
      changeTwist_inverse_on_disc C D hε1 hRC hRD
        (by
          have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
          simpa only [Metric.mem_ball, dist_zero_right] using hx)
  right_inv
    x := by
    apply Subtype.ext
    exact
      changeTwist_inverse_on_disc D C hε1 hRD hRC
        (by
          have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
          simpa only [Metric.mem_ball, dist_zero_right] using hx)
  continuous_toFun := tubeChangeTwist_continuous C D hε hε1 hC hD hzero hRC
  continuous_invFun := tubeChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD

theorem CuspRetraction.closedTubeChangeTwist_continuous (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hR : ToricSpace.SmallDrift C ε) (hηε : η < ε) : Continuous (closedTubeChangeTwist C D η) := by
  have h : ContinuousOn (changeTwist C D) {x : ToricSpace.Space | ‖ToricSpace.time x‖ ≤ η} :=
    (changeTwist_continuousOn C D hε hε1 hC hD hzero hR).mono
      (fun x hx => by
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hx.trans_lt hηε)
  exact h.domRestrict.subtype_mk _

def CuspRetraction.closedTubeHomeomorph (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε) :
    ClosedTube η ≃ₜ ClosedTube η
    where
  toFun := closedTubeChangeTwist C D η
  invFun := closedTubeChangeTwist D C η
  left_inv x := Subtype.ext (changeTwist_inverse_on_disc C D hε1 hRC hRD (x.2.trans_lt hηε))
  right_inv x := Subtype.ext (changeTwist_inverse_on_disc D C hε1 hRD hRC (x.2.trans_lt hηε))
  continuous_toFun := closedTubeChangeTwist_continuous C D hε hε1 hC hD hzero hRC hηε
  continuous_invFun := closedTubeChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD hηε

def CuspRetraction.closedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) (v : Fin 2 → ℤ)
    (x : ClosedTube η) : ClosedTube η :=
  ⟨ToricSpace.twistedTranslate C v x, by simpa only [ToricSpace.time_twistedTranslate] using x.2⟩

def CuspRetraction.closedFibreAction (η : ℝ) (u : Fin 2 → ℂˣ) (x : ClosedTube η) : ClosedTube η :=
  ⟨ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x, by
    simpa only [ToricSpace.time_fibreMultiplier] using x.2⟩

theorem CuspRetraction.closedTubeHomeomorph_base (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (x : ClosedTube η) :
    ToricSpace.time
        (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x : ToricSpace.Space) =
      ToricSpace.time x :=
  time_changeTwist C D x

theorem CuspRetraction.closedTubeHomeomorph_fixes_central (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (x : ClosedTube η) (hx : ToricSpace.time (x : ToricSpace.Space) = 0) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x = x :=
  Subtype.ext (changeTwist_of_time_zero C D hx)

theorem CuspRetraction.closedTubeHomeomorph_equivariant (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (v : Fin 2 → ℤ) (x : ClosedTube η) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε (closedTranslate C η v x) =
      closedTranslate D η v (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x) :=
  Subtype.ext (changeTwist_equivariant_on_disc C D hzero hε1 hRC v (x.2.trans_lt hηε))

theorem CuspRetraction.closedTubeHomeomorph_fibre_torus (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε)) (hzero : C 0 = D 0)
    (hRC : ToricSpace.SmallDrift C ε) (hRD : ToricSpace.SmallDrift D ε) (hηε : η < ε)
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε (closedFibreAction η u x) =
      closedFibreAction η u (closedTubeHomeomorph C D hε hε1 hC hD hzero hRC hRD hηε x) :=
  Subtype.ext (changeTwist_unit_fibreAction C D u hu x)

theorem CuspRetraction.exists_common_frozen_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ}
    (hr : 0 < r) (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ ε : ℝ,
      0 < ε ∧ ε < r ∧ ε < 1 ∧ ToricSpace.SmallDrift C ε ∧ ToricSpace.SmallDrift (frozen C) ε := by
  have hC0 (i j) : ContinuousAt (fun t => C t i j) 0 :=
    (hC i j).continuousAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  obtain ⟨δ, hδ, hδ1, hRδ⟩ := ToricSpace.exists_smallDrift_radius C hC0
  obtain ⟨δ₀, hδ₀, _, hRδ₀⟩ :=
    ToricSpace.exists_smallDrift_radius (frozen C) (fun _ _ => continuousAt_const)
  refine
    ⟨Min.min (r / 2) (Min.min δ δ₀), lt_min (half_pos hr) (lt_min hδ hδ₀),
      (min_le_left _ _).trans_lt (half_lt_self hr),
      ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hδ1,
      hRδ.mono ((min_le_right _ _).trans (min_le_left _ _)),
      hRδ₀.mono ((min_le_right _ _).trans (min_le_right _ _))⟩

abbrev CuspRetraction.ClosedQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ) :=
  { x : CuspQuotient.QuotientSpace C ε // ‖CuspQuotient.projection C ε x‖ ≤ η }

def CuspRetraction.closedQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε)
    (x : ClosedTube η) : ClosedQuotient C ε η :=
  ⟨CuspQuotient.quotientMap C ε
      ⟨x, by
        change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
        simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩,
    x.2⟩

@[simp]
theorem CuspRetraction.closedQuotientMap_projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (x : ClosedTube η) :
    CuspQuotient.projection C ε (closedQuotientMap C hηε x) =
      ToricSpace.time (x : ToricSpace.Space) :=
  rfl

theorem CuspRetraction.closedQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) : Function.Surjective (closedQuotientMap C hηε) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨⟨x, hq⟩, rfl⟩

private def CuspRetraction.closedTubePreimageHomeomorph_mo1973_10381
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hηε : η < ε) :
    ClosedTube η ≃ₜ
      (CuspQuotient.quotientMap C ε ⁻¹'
        {q : CuspQuotient.QuotientSpace C ε | ‖CuspQuotient.projection C ε q‖ ≤ η})
    where
  toFun
    x :=
    ⟨⟨x, by
        change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε
        simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩,
      x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem CuspRetraction.closedQuotientMap_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {ε η : ℝ} (hηε : η < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (closedQuotientMap C hηε) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  let := CuspQuotient.continuous_action C ε hC
  have hq : IsOpenQuotientMap (CuspQuotient.quotientMap C ε) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact
    (hq.restrictPreimage
          {q : CuspQuotient.QuotientSpace C ε | ‖CuspQuotient.projection C ε q‖ ≤ η}).comp
      (closedTubePreimageHomeomorph_mo1973_10381 C hηε).isOpenQuotientMap

theorem CuspRetraction.closedQuotientMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hηε : η < ε) (x y : ClosedTube η) :
    closedQuotientMap C hηε x = closedQuotientMap C hηε y ↔
      ∃ v : Fin 2 → ℤ,
        ToricSpace.twistedTranslate C v (y : ToricSpace.Space) = (x : ToricSpace.Space) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  constructor
  · intro h
    have hrel := Quotient.exact (congrArg Subtype.val h)
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε)) at hrel
    obtain ⟨g, hg⟩ := hrel
    exact ⟨g.toAdd, congrArg Subtype.val hg⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    apply Quotient.sound
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc ε))
    exact ⟨Multiplicative.ofAdd v, Subtype.ext hv⟩

theorem CuspCentralHomology.cuspQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (δ : ℝ) : Function.Surjective (CuspQuotient.quotientMap C δ) :=
  Quotient.mk_surjective

abbrev CuspCentralHomology.OpenQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r δ : ℝ) :=
  { q : CuspQuotient.QuotientSpace C r // ‖CuspQuotient.projection C r q‖ < δ }

def CuspCentralHomology.openQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r)
    (x : ToricSpace.Tube (CuspQuotient.disc δ)) : OpenQuotient C r δ :=
  ⟨CuspQuotient.quotientMap C r
      ⟨x, by
        have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ := x.2
        exact Metric.ball_subset_ball hδr hx⟩,
    by
    change ‖ToricSpace.time (x : ToricSpace.Space)‖ < δ
    have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx⟩

theorem CuspCentralHomology.openQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r δ : ℝ} (hδr : δ ≤ r) : Function.Surjective (openQuotientMap C hδr) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  change ‖ToricSpace.time (x : ToricSpace.Space)‖ < δ at hq
  refine ⟨⟨x, ?_⟩, rfl⟩
  change ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ
  simpa only [Metric.mem_ball, dist_zero_right] using hq

private def CuspCentralHomology.openTubePreimageHomeomorph_mo1973_10400
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r) :
    ToricSpace.Tube (CuspQuotient.disc δ) ≃ₜ
      (CuspQuotient.quotientMap C r ⁻¹'
        {q : CuspQuotient.QuotientSpace C r | ‖CuspQuotient.projection C r q‖ < δ})
    where
  toFun
    x :=
    ⟨⟨x, Metric.ball_subset_ball hδr x.2⟩,
      by
      change ‖ToricSpace.time (x : ToricSpace.Space)‖ < δ
      have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 δ := x.2
      simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
  invFun
    x :=
    ⟨x.1.1, by
      change ToricSpace.time (x.1 : ToricSpace.Space) ∈ Metric.ball 0 δ
      have hx : ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ < δ := x.2
      simpa only [Metric.mem_ball, dist_zero_right] using hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem CuspCentralHomology.openQuotientMap_isOpenQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r δ : ℝ} (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsOpenQuotientMap (openQuotientMap C hδr) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc r)
  let := CuspQuotient.continuous_action C r hC
  have hq : IsOpenQuotientMap (CuspQuotient.quotientMap C r) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact
    (hq.restrictPreimage
          {q : CuspQuotient.QuotientSpace C r | ‖CuspQuotient.projection C r q‖ < δ}).comp
      (openTubePreimageHomeomorph_mo1973_10400 C hδr).isOpenQuotientMap

theorem CuspCentralHomology.openQuotientMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ}
    (hδr : δ ≤ r) (x y : ToricSpace.Tube (CuspQuotient.disc δ)) :
    openQuotientMap C hδr x = openQuotientMap C hδr y ↔
      CuspQuotient.quotientMap C δ x = CuspQuotient.quotientMap C δ y := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc r)
  let := ToricSpace.tubeAction C (CuspQuotient.disc δ)
  constructor
  · intro h
    have hrel := Quotient.exact (congrArg Subtype.val h)
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r)) at hrel
    obtain ⟨g, hg⟩ := hrel
    have hg' :
      ToricSpace.twistedTranslate C g.toAdd (y : ToricSpace.Space) = (x : ToricSpace.Space) :=
      congrArg (fun z : ToricSpace.Tube (CuspQuotient.disc r) => (z : ToricSpace.Space)) hg
    apply Quotient.sound
    change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y
    exact ⟨g, Subtype.ext hg'⟩
  · intro h
    have hrel := Quotient.exact h
    change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y at hrel
    obtain ⟨g, hg⟩ := hrel
    have hg' :
      ToricSpace.twistedTranslate C g.toAdd (y : ToricSpace.Space) = (x : ToricSpace.Space) :=
      congrArg (fun z : ToricSpace.Tube (CuspQuotient.disc δ) => (z : ToricSpace.Space)) hg
    apply Subtype.ext
    apply Quotient.sound
    change
      (⟨(x : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r)) ∈
        MulAction.orbit CuspQuotient.LatticeGroup
          (⟨(y : ToricSpace.Space), _⟩ : ToricSpace.Tube (CuspQuotient.disc r))
    exact ⟨g, Subtype.ext hg'⟩

def CuspCentralHomology.openQuotientRadiusHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ}
    (hδr : δ ≤ r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    CuspQuotient.QuotientSpace C δ ≃ₜ OpenQuotient C r δ
    where
  toFun :=
    CuspHoneycombHexagon.CommonFibres.descend (CuspQuotient.quotientMap C δ)
      (openQuotientMap C hδr) (cuspQuotientMap_surjective C δ)
  invFun :=
    CuspHoneycombHexagon.CommonFibres.descend (openQuotientMap C hδr)
      (CuspQuotient.quotientMap C δ) (openQuotientMap_surjective C hδr)
  left_inv
    q := by
    obtain ⟨x, rfl⟩ := cuspQuotientMap_surjective C δ q
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr),
      CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mp)]
  right_inv
    q := by
    obtain ⟨x, rfl⟩ := openQuotientMap_surjective C hδr q
    rw [CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mp),
      CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
        (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr)]
  continuous_toFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous _ _ _ isQuotientMap_quotient_mk'
      (openQuotientMap_isOpenQuotientMap C hδr hC).continuous
      (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr)
  continuous_invFun :=
    CuspHoneycombHexagon.CommonFibres.descend_continuous _ _ _
      (openQuotientMap_isOpenQuotientMap C hδr hC).isQuotientMap
      (CuspQuotient.quotientMap_continuous C δ) (fun x y => (openQuotientMap_eq_iff C hδr x y).mp)

@[simp]
theorem CuspCentralHomology.openQuotientRadiusHomeomorph_quotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (x : ToricSpace.Tube (CuspQuotient.disc δ)) :
    openQuotientRadiusHomeomorph C hδr hC (CuspQuotient.quotientMap C δ x) =
      openQuotientMap C hδr x :=
  CuspHoneycombHexagon.CommonFibres.descend_apply _ _ _
    (fun x y => (openQuotientMap_eq_iff C hδr x y).mpr) x

theorem CuspCentralHomology.openQuotientRadiusHomeomorph_projection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r δ : ℝ} (hδr : δ ≤ r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (q : CuspQuotient.QuotientSpace C δ) :
    CuspQuotient.projection C r (openQuotientRadiusHomeomorph C hδr hC q) =
      CuspQuotient.projection C δ q := by
  obtain ⟨x, rfl⟩ := cuspQuotientMap_surjective C δ q
  rw [openQuotientRadiusHomeomorph_quotientMap]
  rfl


end
