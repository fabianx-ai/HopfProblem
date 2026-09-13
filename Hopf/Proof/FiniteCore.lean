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
Original source lines 104760--105221; see PROVENANCE.md.
-/

import Hopf.LibShims
import Hopf.Proof.Hurewicz
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

def TrianglePeriodFamilyHomologyAlgebra.columnEquiv (H : Type*) [AddCommGroup H] :
    (H × (H × H)) ≃ₗ[ℤ] (H × (H × H)) :=
  ({    toFun := fun x => (x.1 + x.2.1 + x.2.2, x.2)
        invFun := fun x => (x.1 - x.2.1 - x.2.2, x.2)
        left_inv := by
          rintro ⟨a, b, c⟩
          apply Prod.ext
          · dsimp; abel
          · rfl
        right_inv := by
          rintro ⟨a, b, c⟩
          apply Prod.ext
          · dsimp; abel
          · rfl
        map_add' := by
          rintro ⟨a, b, c⟩ ⟨a', b', c'⟩
          apply Prod.ext
          · dsimp; abel
          · rfl } :
      (H × (H × H)) ≃+ (H × (H × H))).toIntLinearEquiv

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.columnEquiv_symm_apply (H : Type*) [AddCommGroup H]
    (x : H × (H × H)) : (columnEquiv H).symm x = (x.1 - x.2.1 - x.2.2, x.2) :=
  rfl

def TrianglePeriodFamilyHomologyAlgebra.rowEquiv (H : Type*) [AddCommGroup H] :
    (H × H) ≃ₗ[ℤ] (H × H) :=
  ({    toFun := fun x => (x.1, -x.1 - x.2)
        invFun := fun x => (x.1, -x.1 - x.2)
        left_inv := by
          rintro ⟨a, b⟩
          apply Prod.ext
          · rfl
          · dsimp; abel
        right_inv := by
          rintro ⟨a, b⟩
          apply Prod.ext
          · rfl
          · dsimp; abel
        map_add' := by
          rintro ⟨a, b⟩ ⟨a', b'⟩
          apply Prod.ext
          · rfl
          · dsimp; abel } :
      (H × H) ≃+ (H × H)).toIntLinearEquiv

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.rowEquiv_apply (H : Type*) [AddCommGroup H]
    (x : H × H) : rowEquiv H x = (x.1, -x.1 - x.2) :=
  rfl

def TrianglePeriodFamilyHomologyAlgebra.delta {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) : (H × H) →ₗ[ℤ] H :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun x := (P x.1 - x.1) + (Q x.2 - x.2)
      map_zero' := by simp
      map_add' x
        y := by
        dsimp
        rw [map_add, map_add]
        abel }

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.delta_apply {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) (x : H × H) : delta P Q x = (P x.1 - x.1) + (Q x.2 - x.2) :=
  rfl

def TrianglePeriodFamilyHomologyAlgebra.overlapMap {H : Type*} [AddCommGroup H] [Module ℤ H]
    (P Q : H →ₗ[ℤ] H) : (H × (H × H)) →ₗ[ℤ] (H × H) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun x := (x.1 + x.2.1 + x.2.2, -(x.1 + P x.2.1 + Q x.2.2))
      map_zero' := by simp
      map_add' x
        y := by
        apply Prod.ext
        · dsimp; abel
        · dsimp
          rw [map_add, map_add]
          abel }

@[simp]
theorem TrianglePeriodFamilyHomologyAlgebra.overlapMap_apply {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    overlapMap P Q x = (x.1 + x.2.1 + x.2.2, -(x.1 + P x.2.1 + Q x.2.2)) :=
  rfl

theorem TrianglePeriodFamilyHomologyAlgebra.row_overlapMap {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q x) = (x.1 + x.2.1 + x.2.2, delta P Q x.2) := by
  apply Prod.ext
  · rfl
  · change
      -(x.1 + x.2.1 + x.2.2) - -(x.1 + P x.2.1 + Q x.2.2) = (P x.2.1 - x.2.1) + (Q x.2.2 - x.2.2)
    abel

theorem TrianglePeriodFamilyHomologyAlgebra.row_overlapMap_column_symm {H : Type*}
    [AddCommGroup H] [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    rowEquiv H (overlapMap P Q ((columnEquiv H).symm x)) = (x.1, delta P Q x.2) := by
  rw [row_overlapMap, columnEquiv_symm_apply]
  apply Prod.ext
  · dsimp; abel
  · rfl

theorem TrianglePeriodFamilyHomologyAlgebra.overlapMap_eq_zero_iff {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (x : H × (H × H)) :
    overlapMap P Q x = 0 ↔ x.1 + x.2.1 + x.2.2 = 0 ∧ delta P Q x.2 = 0 := by
  constructor
  · intro h
    have hr := congrArg (rowEquiv H) h
    rw [row_overlapMap, map_zero] at hr
    exact ⟨congrArg Prod.fst hr, congrArg Prod.snd hr⟩
  · rintro ⟨hs, hd⟩
    apply (rowEquiv H).injective
    rw [row_overlapMap, map_zero]
    exact Prod.ext hs hd

theorem TrianglePeriodFamilyHomologyAlgebra.overlapMap_mem_range_iff {H : Type*} [AddCommGroup H]
    [Module ℤ H] (P Q : H →ₗ[ℤ] H) (y : H × H) :
    y ∈ LinearMap.range (overlapMap P Q) ↔ -y.1 - y.2 ∈ LinearMap.range (delta P Q) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.2, ?_⟩
    exact (congrArg Prod.snd (row_overlapMap P Q x)).symm
  · rintro ⟨bc, hbc⟩
    refine ⟨(columnEquiv H).symm (y.1, bc), ?_⟩
    apply (rowEquiv H).injective
    rw [row_overlapMap_column_symm, rowEquiv_apply, hbc]

abbrev PeriodLattice :=
  Fin 4 → ℤ

abbrev LatticeMatrix :=
  Matrix (Fin 4) (Fin 4) ℤ

def T₁ : LatticeMatrix :=
  !![1, 0, -6, 2; 0, -1, 1, 1; 0, -1, 0, 1; 0, 0, 0, 1]

def T₂ : LatticeMatrix :=
  !![1, 6, 0, -3; 0, 0, -1, 1; 0, 1, 0, 0; 0, 0, 0, 1]

def T₀ : LatticeMatrix :=
  !![1, 0, 0, 1; 0, 1, -1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def A₁ : LatticeMatrix :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]

def A₂ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]

def M₀ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1]

def ε : PeriodLattice :=
  ![1, 2, -4, 0]

def ε' : PeriodLattice :=
  ![1, 3, -3, 0]

def γ (v : PeriodLattice) : ℤ :=
  v 0

def B₀ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; -1, 0]

theorem det_T₁ : T₁.det = 1 := by decide

theorem det_T₂ : T₂.det = 1 := by decide

theorem T₁_cube : T₁ ^ 3 = 1 := by decide

theorem T₂_fourth : T₂ ^ 4 = 1 := by decide

theorem A₁_eq_transpose_sq : A₁ = (T₁ ^ 2).transpose := by decide

theorem A₂_eq_transpose_cube : A₂ = (T₂ ^ 3).transpose := by decide

theorem A₁_fixes_ε : A₁ *ᵥ ε = ε := by decide

theorem A₂_fixes_ε' : A₂ *ᵥ ε' = ε' := by decide

theorem γ_ε' : γ ε' = 1 :=
  rfl

theorem M₀_sub_one_mulVec (v : PeriodLattice) : (M₀ - 1) *ᵥ v = ![0, 0, v 1, -v 0] := by
  ext i
  fin_cases i <;> simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem M₀_sub_one_kernel (v : PeriodLattice) : (M₀ - 1) *ᵥ v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [M₀_sub_one_mulVec]
  constructor
  · intro h
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    change v 1 = 0 at h₂
    change -v 0 = 0 at h₃
    exact ⟨neg_eq_zero.mp h₃, h₂⟩
  · rintro ⟨h₀, h₁⟩
    simp [h₀, h₁]

theorem M₀_sub_one_range (v : PeriodLattice) : (∃ w : PeriodLattice, (M₀ - 1) *ᵥ w = v) ↔ v 0 = 0 ∧ v 1 = 0 :=
  by
  constructor
  · rintro ⟨w, rfl⟩
    simp [M₀_sub_one_mulVec]
  · rintro ⟨h₀, h₁⟩
    refine ⟨![-v 3, v 2, 0, 0], ?_⟩
    rw [M₀_sub_one_mulVec]
    ext i
    fin_cases i <;> simp [h₀, h₁]

theorem A₁_fixed_iff (v : PeriodLattice) : A₁ *ᵥ v = v ↔ v 1 = 2 * v 0 ∧ v 2 = -4 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂] <;> ring

theorem A₂_fixed_iff (v : PeriodLattice) : A₂ *ᵥ v = v ↔ v 1 = 3 * v 0 ∧ v 2 = -3 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂]
    ring

abbrev LocalSystemMatrices.Vec (n : ℕ) :=
  Fin n → ℤ

def LocalSystemMatrices.lastCoordinate : Vec 4 →ₗ[ℤ] ℤ :=
  LinearMap.proj 3

def LocalSystemMatrices.pairIndices : Fin 6 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3] ]

def LocalSystemMatrices.exteriorSquare (T : LatticeMatrix) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => (T.submatrix (pairIndices i) (pairIndices j)).det

def LocalSystemMatrices.tripleIndices : Fin 4 → Fin 3 → Fin 4 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3] ]

def LocalSystemMatrices.exteriorCube (T : LatticeMatrix) : LatticeMatrix := fun i j =>
  (T.submatrix (tripleIndices i) (tripleIndices j)).det

def PeriodTorusHigherHomologyExterior.squareA₁ : Matrix (Fin 6) (Fin 6) ℤ :=
  LocalSystemMatrices.exteriorSquare A₁

def PeriodTorusHigherHomologyExterior.squareA₂ : Matrix (Fin 6) (Fin 6) ℤ :=
  LocalSystemMatrices.exteriorSquare A₂

def PeriodTorusHigherHomologyExterior.squareM₀ : Matrix (Fin 6) (Fin 6) ℤ :=
  LocalSystemMatrices.exteriorSquare M₀

def PeriodTorusHigherHomologyExterior.cubeA₁ : LatticeMatrix :=
  LocalSystemMatrices.exteriorCube A₁

def PeriodTorusHigherHomologyExterior.cubeA₂ : LatticeMatrix :=
  LocalSystemMatrices.exteriorCube A₂

def PeriodTorusHigherHomologyExterior.cubeM₀ : LatticeMatrix :=
  LocalSystemMatrices.exteriorCube M₀

theorem PeriodTorusHigherHomologyExterior.squareA₁_eq :
    squareA₁ =
      !![0, 1, 0, 0, 0, 0;
        -1, -1, 0, 0, 0, 0;
        1, 0, 1, 0, 0, 0;
        -6, 0, 0, 1, 0, 0;
        6, 2, 6, -1, 0, 1;
        -8, -2, -6, 1, -1, -1] := by decide

theorem PeriodTorusHigherHomologyExterior.squareA₂_eq :
    squareA₂ =
      !![0, -1, 0, 0, 0, 0;
        1, 0, 0, 0, 0, 0;
        0, 1, 1, 0, 0, 0;
        0, -6, 0, 1, 0, 0;
        0, 3, 0, 0, 0, -1;
        -3, -6, -6, 1, 1, 0] := by decide

theorem PeriodTorusHigherHomologyExterior.squareM₀_eq :
    squareM₀ =
      !![1, 0, 0, 0, 0, 0;
        1, 1, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0;
        0, 0, 0, 1, 0, 0;
        1, 0, 0, 0, 1, 0;
        1, 1, 0, 0, 1, 1] := by decide

theorem PeriodTorusHigherHomologyExterior.cubeA₁_eq :
    cubeA₁ = !![1, 0, 0, 0; -1, 0, 1, 0; 1, -1, -1, 0; -2, -6, 0, 1] := by decide

theorem PeriodTorusHigherHomologyExterior.cubeA₂_eq :
    cubeA₂ = !![1, 0, 0, 0; 0, 0, -1, 0; 1, 1, 0, 0; 3, 0, -6, 1] := by decide

theorem PeriodTorusHigherHomologyExterior.cubeM₀_eq :
    cubeM₀ = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1] := by decide

def TrianglePeriodFamilyHomologyLattice.deltaOne : (PeriodLattice × PeriodLattice) →ₗ[ℤ] PeriodLattice :=
  TrianglePeriodFamilyHomologyAlgebra.delta A₁.mulVecLin A₂.mulVecLin

def TrianglePeriodFamilyHomologyLattice.deltaThree : (PeriodLattice × PeriodLattice) →ₗ[ℤ] PeriodLattice :=
  TrianglePeriodFamilyHomologyAlgebra.delta PeriodTorusHigherHomologyExterior.cubeA₁.mulVecLin
    PeriodTorusHigherHomologyExterior.cubeA₂.mulVecLin

def TrianglePeriodFamilyHomologyLattice.functionalOdd : PeriodLattice →ₗ[ℤ] ℤ :=
  LinearMap.proj 0

theorem TrianglePeriodFamilyHomologyLattice.functionalOdd_surjective :
    Function.Surjective functionalOdd := by
  intro a
  exact ⟨![a, 0, 0, 0], rfl⟩

theorem TrianglePeriodFamilyHomologyLattice.deltaOne_apply (b c : PeriodLattice) :
    deltaOne (b, c) =
      ![0, 6 * b 0 - b 1 + b 2 - c 1 - c 2, -6 * b 0 - b 1 - 2 * b 2 - 6 * c 0 + c 1 - c 2,
        -2 * b 0 + b 1 + 3 * c 0 + c 2] := by
  change (A₁ *ᵥ b - b) + (A₂ *ᵥ c - c) = _
  ext i
  fin_cases i <;> simp [A₁, A₂, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem TrianglePeriodFamilyHomologyLattice.deltaThree_apply (b c : PeriodLattice) :
    deltaThree (b, c) =
      ![0, -b 0 - b 1 + b 2 - c 1 - c 2, b 0 - b 1 - 2 * b 2 + c 0 + c 1 - c 2,
        -2 * b 0 - 6 * b 1 + 3 * c 0 - 6 * c 2] := by
  change
    (PeriodTorusHigherHomologyExterior.cubeA₁ *ᵥ b - b) +
        (PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ c - c) =
      _
  rw [PeriodTorusHigherHomologyExterior.cubeA₁_eq, PeriodTorusHigherHomologyExterior.cubeA₂_eq]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

def TrianglePeriodFamilyHomologyLattice.preimageOne (x : PeriodLattice) : PeriodLattice × PeriodLattice :=
  (![0, x 3, -x 1 - x 2 - 2 * x 3, 0], ![0, -2 * x 1 - x 2 - 3 * x 3, 0, 0])

def TrianglePeriodFamilyHomologyLattice.preimageThree (x : PeriodLattice) : PeriodLattice × PeriodLattice :=
  (![x 3, 0, x 3 - x 1 - x 2, 0], ![x 3, -2 * x 1 - x 2, 0, 0])

theorem TrianglePeriodFamilyHomologyLattice.deltaOne_preimage (x : PeriodLattice) :
    deltaOne (preimageOne x) = ![0, x 1, x 2, x 3] := by
  rw [preimageOne, deltaOne_apply]
  ext i
  fin_cases i <;> simp <;> ring

theorem TrianglePeriodFamilyHomologyLattice.deltaThree_preimage (x : PeriodLattice) :
    deltaThree (preimageThree x) = ![0, x 1, x 2, x 3] := by
  rw [preimageThree, deltaThree_apply]
  ext i
  fin_cases i <;> simp <;> ring

theorem TrianglePeriodFamilyHomologyLattice.deltaOne_range :
    LinearMap.range deltaOne = LinearMap.ker functionalOdd := by
  ext x
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    change functionalOdd (deltaOne (b, c)) = 0
    rw [deltaOne_apply]
    rfl
  · intro hx
    have hx0 : x 0 = 0 := hx
    refine ⟨preimageOne x, ?_⟩
    rw [deltaOne_preimage]
    ext i
    fin_cases i <;> simp [hx0]

theorem TrianglePeriodFamilyHomologyLattice.deltaThree_range :
    LinearMap.range deltaThree = LinearMap.ker functionalOdd := by
  ext x
  constructor
  · rintro ⟨⟨b, c⟩, rfl⟩
    change functionalOdd (deltaThree (b, c)) = 0
    rw [deltaThree_apply]
    rfl
  · intro hx
    have hx0 : x 0 = 0 := hx
    refine ⟨preimageThree x, ?_⟩
    rw [deltaThree_preimage]
    ext i
    fin_cases i <;> simp [hx0]

def TrianglePeriodFamilyHomologyLattice.cokernelOneEquiv :
    (PeriodLattice ⧸ LinearMap.range deltaOne) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ deltaOne_range).trans
    (functionalOdd.quotKerEquivOfSurjective functionalOdd_surjective)

def TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv :
    (PeriodLattice ⧸ LinearMap.range deltaThree) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ deltaThree_range).trans
    (functionalOdd.quotKerEquivOfSurjective functionalOdd_surjective)

@[simp]
theorem TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv_mk (x : PeriodLattice) :
    cokernelThreeEquiv (Submodule.Quotient.mk x) = x 0 := by
  simp [cokernelThreeEquiv]
  rfl

theorem ThreefoldHomology.SecondSource.kernel_coordinates (x y : PeriodLattice)
    (h : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    x 2 = -4 * x 0 ∧ y 1 = 3 * y 0 ∧ y 2 = 2 * x 0 - x 1 - 3 * y 0 := by
  rw [TrianglePeriodFamilyHomologyLattice.deltaOne_apply] at h
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  have h₃ := congrFun h 3
  change 6 * x 0 - x 1 + x 2 - y 1 - y 2 = 0 at h₁
  change -6 * x 0 - x 1 - 2 * x 2 - 6 * y 0 + y 1 - y 2 = 0 at h₂
  change -2 * x 0 + x 1 + 3 * y 0 + y 2 = 0 at h₃
  omega

def ThreefoldHomology.SecondSource.deltaVector : PeriodLattice :=
  ![0, 0, 0, 1]

def ThreefoldHomology.SecondSource.threeCoordinates (κ₃ κ₄ : ℤ) (x y : PeriodLattice) : Fin 2 → ℤ :=
  ![x 3 + (x 1 - 2 * x 0) + (κ₄ * y 0 - y 3) + κ₃ * x 0, x 0]

def ThreefoldHomology.SecondSource.fourCoordinates (_x y : PeriodLattice) : Fin 2 → ℤ :=
  ![0, -y 0]

def ThreefoldHomology.SecondSource.cuspCoordinates (κ₄ : ℤ) (x y : PeriodLattice) : PeriodLattice :=
  ![0, 0, x 1 - 2 * x 0, κ₄ * y 0 - y 3]

def ThreefoldHomology.SecondSource.threeWangVector (κ₃ : ℤ) (a : Fin 2 → ℤ) : PeriodLattice :=
  a 1 • ε + (a 0 - κ₃ * a 1) • deltaVector

def ThreefoldHomology.SecondSource.fourWangVector (κ₄ : ℤ) (a : Fin 2 → ℤ) : PeriodLattice :=
  a 1 • (-ε') + (2 * a 0 - κ₄ * a 1) • deltaVector

theorem ThreefoldHomology.SecondSource.threeCoordinates_reconstruct (κ₃ κ₄ : ℤ) (x y : PeriodLattice)
    (h : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    threeWangVector κ₃ (threeCoordinates κ₃ κ₄ x y) - A₂ *ᵥ cuspCoordinates κ₄ x y = x := by
  have hx₂ := (kernel_coordinates x y h).1
  ext i
  fin_cases i <;>
      simp [threeWangVector, threeCoordinates, cuspCoordinates, deltaVector, ε, A₂, hx₂] <;>
    ring

theorem ThreefoldHomology.SecondSource.fourCoordinates_reconstruct (κ₄ : ℤ) (x y : PeriodLattice)
    (h : TrianglePeriodFamilyHomologyLattice.deltaOne (x, y) = 0) :
    fourWangVector κ₄ (fourCoordinates x y) - cuspCoordinates κ₄ x y = y := by
  have hy₁ := (kernel_coordinates x y h).2.1
  have hy₂ := (kernel_coordinates x y h).2.2
  ext i
  fin_cases i <;>
      simp [fourWangVector, fourCoordinates, cuspCoordinates, deltaVector, ε', hy₁, hy₂] <;>
    ring

theorem ThreefoldHomology.SecondSource.cuspCoordinates_fixed (κ₄ : ℤ) (x y : PeriodLattice) :
    M₀ *ᵥ cuspCoordinates κ₄ x y = cuspCoordinates κ₄ x y := by
  ext i
  fin_cases i <;> simp [cuspCoordinates, M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]



end
