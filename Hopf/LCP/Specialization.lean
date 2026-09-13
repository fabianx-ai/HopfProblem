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
import Lib.AlgebraicTopology.SingularHomology.CirclePaths
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
import Lib.Topology.MappingTorus.Wang
import Lib.Topology.Covering.Quotient
import Lib.Topology.Homotopy.SublevelRetraction
import Lib.AlgebraicTopology.SingularHomology.PathClass
import Lib.Topology.Homotopy.LocalCollapse
import Lib.Topology.Covering.InvariantSubset
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

theorem PeriodTorusHigherHomology.coordinatePeriodLoop_eq_projection (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinatePeriodLoop n v t = coordinateProjection n ((t : ℝ) • (fun i => (v i : ℝ))) := by
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem PeriodTorusHigherHomologyPontryagin.product11_skew (G : Type) [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G]
    (a b : SingularMayerVietoris.SingularHomology G 1) : product11 G a b = -product11 G b a :=
  PeriodTorusHigherHomology.crossProductHomology_pushforward_anticommute (additionMap G)
    (by ext p; exact add_comm p.2 p.1) a b

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

def PeriodTorusHigherHomology.omitHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin n) ℤ :=
  Fin.cons 0 A

def PeriodTorusHigherHomology.takeHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i))

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

theorem PeriodTorusHigherHomology.homeomorph_symm_add_of_add {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Add X] [Add Y] (e : X ≃ₜ Y) (he : ∀ x y, e (x + y) = e x + e y)
    (x y : Y) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

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

theorem PeriodTorusHigherHomology.positiveCircleCross_pointClass :
    positiveCircleCross Unit 0 (pointClass ()) =
      homeomorphHomologyEquiv
        (Homeomorph.prodUnique (PeriodTorusHigherHomology.CircleTopology.Circle) Unit).symm 1
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) :=
  crossProductHomology_pointClass_right (PeriodTorusHigherHomology.CircleTopology.Circle) Unit
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) ()
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


end
