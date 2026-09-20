/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Hopf.LibShims
import Hopf.Proof.FiniteCore
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
import Hopf.Proof.Geometry.Manifold.Morse.MinimalSystem
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
import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Surjectivity
import Lib.Topology.Homeomorph.DiskCube

/-!
# Short-proof adapters for HopfProblem

This module owns finite, dependency-early bridges from the HopfProblem data to the reusable V10
algebraic interfaces.  It contains no analytic construction and makes no assertion that the
six-sphere carries a complex structure.
-/

open Matrix
open scoped Matrix

/-- The integral dual-cusp nilpotent as a lattice endomorphism. -/
abbrev dualCuspN : Module.End ℤ PeriodLattice :=
  Matrix.toLin' (M₀ - 1)

/-- The dual-cusp endomorphism is square-zero. -/
theorem dualCuspN_square_zero : dualCuspN * dualCuspN = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  change ((M₀ - 1) *ᵥ ((M₀ - 1) *ᵥ v)) i = 0
  rw [M₀_sub_one_mulVec, M₀_sub_one_mulVec]
  fin_cases i <;> rfl

/-- The real scalar extension of the dual-cusp nilpotent. -/
abbrev dualCuspNReal : Module.End ℝ (Fin 4 → ℝ) :=
  Matrix.toLin' ((M₀ - 1).map (Int.castRingHom ℝ))

/-- The scalar-extended dual-cusp operator has its integral coordinate formula. -/
@[simp]
theorem dualCuspNReal_apply (x : Fin 4 → ℝ) :
    dualCuspNReal x = ![0, 0, x 1, -x 0] := by
  ext i
  fin_cases i <;>
    simp [dualCuspNReal, M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

/-- The real scalar extension remains square-zero. -/
theorem dualCuspNReal_square_zero : dualCuspNReal * dualCuspNReal = 0 := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, dualCuspNReal_apply, dualCuspNReal_apply]
  ext i
  fin_cases i <;> simp

