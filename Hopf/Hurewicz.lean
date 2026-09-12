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
Original source lines 81183--104759; see PROVENANCE.md.
-/

import Hopf.LibShims
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
import Hopf.SphereTopology

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

def Degree.DiskCube.target {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Set V :=
  L ⁻¹' HigherHurewicz.realCubeSet n

theorem Degree.DiskCube.target_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : IsCompact (target L) :=
  L.toHomeomorph.isCompact_preimage.mpr (HigherHurewicz.isCompact_realCubeSet n)

theorem Degree.DiskCube.target_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Convex ℝ (target L) :=
  (HigherHurewicz.convex_realCubeSet n).linear_preimage L.toLinearMap

theorem Degree.DiskCube.target_interior_nonempty {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : (interior (target L)).Nonempty := by
  obtain ⟨v, hv⟩ := HigherHurewicz.interior_realCubeSet_nonempty n
  refine ⟨L.symm v, ?_⟩
  change L.symm v ∈ interior (L.toHomeomorph ⁻¹' HigherHurewicz.realCubeSet n)
  rw [← L.toHomeomorph.preimage_interior]
  change L (L.symm v) ∈ interior (HigherHurewicz.realCubeSet n)
  rwa [L.apply_symm_apply]

theorem Degree.DiskCube.exists_ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ∃ e : V ≃ₜ V,
      e '' Metric.closedBall (0 : V) 1 = target L ∧
        e '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L) := by
  obtain ⟨e, _, he, hb⟩ :=
    exists_homeomorph_image_eq (convex_closedBall (0 : V) 1)
      (show (interior (Metric.closedBall (0 : V) 1)).Nonempty from
        ⟨0, Metric.ball_subset_interior_closedBall (by simp)⟩)
      ((ProperSpace.isCompact_closedBall (0 : V) 1).isVonNBounded ℝ) (target_convex L)
      (target_interior_nonempty L) ((target_compact L).isVonNBounded ℝ)
  exact
    ⟨e, by
      simpa only [Metric.isClosed_closedBall.closure_eq,
        (target_compact L).isClosed.closure_eq] using he,
      hb⟩

def Degree.DiskCube.ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : V ≃ₜ V :=
  Classical.choose (exists_ambient L)

theorem Degree.DiskCube.ambient_image {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' Metric.closedBall (0 : V) 1 = target L :=
  (Classical.choose_spec (exists_ambient L)).1

theorem Degree.DiskCube.ambient_frontier {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L) :=
  (Classical.choose_spec (exists_ambient L)).2

theorem Degree.DiskCube.ambient_mem_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (v : V) :
    v ∈ Metric.closedBall (0 : V) 1 ↔ L (ambient L v) ∈ HigherHurewicz.realCubeSet n := by
  change v ∈ Metric.closedBall (0 : V) 1 ↔ ambient L v ∈ target L
  rw [← ambient_image]
  exact ((ambient L).injective.mem_set_image).symm

def Degree.DiskCube.homeomorph {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    Degree.DiskCylinder.Disk (E := V) ≃ₜ (Fin n → (unitInterval)) :=
  (((ambient L).trans L.toHomeomorph).subtype (ambient_mem_iff L)).trans
    (HigherHurewicz.realCubeHomeomorph n)

theorem Degree.DiskCube.boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ))
    (z : Degree.DiskCylinder.Disk (E := V)) :
    homeomorph L z ∈ Cube.boundary (Fin n) ↔ ‖(z : V)‖ = 1 := by
  change HigherHurewicz.realCubeHomeomorph n _ ∈ Cube.boundary (Fin n) ↔ _
  rw [HigherHurewicz.realCubeHomeomorph_mem_boundary_iff]
  change L (ambient L z.val) ∈ frontier (HigherHurewicz.realCubeSet n) ↔ _
  have hpre :
    L (ambient L z.val) ∈ frontier (HigherHurewicz.realCubeSet n) ↔
      ambient L z.val ∈ frontier (target L) := by
    change ambient L z.val ∈ L.toHomeomorph ⁻¹' frontier (HigherHurewicz.realCubeSet n) ↔ _
    rw [L.toHomeomorph.preimage_frontier]
    rfl
  rw [hpre, ← ambient_frontier]
  rw [(ambient L).injective.mem_set_image]
  rw [frontier_closedBall (0 : V) (one_ne_zero), mem_sphere_zero_iff_norm]

theorem Degree.DiskCube.symm_boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → (unitInterval)) :
    ‖((homeomorph L).symm z : V)‖ = 1 ↔ z ∈ Cube.boundary (Fin n) := by
  rw [← boundary_iff, Homeomorph.apply_symm_apply]

theorem simplyConnectedSpace_of_open_cover {X ι : Type*} [TopologicalSpace X] (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (hsimply : ∀ i, IsSimplyConnected (U i)) (o : X) (ho : ∀ i, o ∈ U i)
    (hinter : ∀ i j, IsPathConnected (U i ∩ U j)) : SimplyConnectedSpace X := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ U i := by
    intro x
    apply Set.mem_iUnion.mp
    rw [hcover]
    trivial
  let idx (x : X) : ι := (hcov x).choose
  have hidx (x : X) : x ∈ U (idx x) := (hcov x).choose_spec
  let c (x : X) : Path o x := SimplyConnectedCover.chartPath U hsimply o ho (idx x) x (hidx x)
  let F (x : X) : Path.Homotopic.Quotient o x := Path.Homotopic.Quotient.mk (c x)
  have hFi (i : ι) (x : X) (hx : x ∈ U i) :
    F x = Path.Homotopic.Quotient.mk (SimplyConnectedCover.chartPath U hsimply o ho i x hx) := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact SimplyConnectedCover.chartPath_homotopic U hsimply o ho hinter (idx x) i x (hidx x) hx
  have hF (i : ι) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
    (F x).trans (Path.Homotopic.Quotient.mk p) = F y := by
    have hx : x ∈ U i := by simpa using hp 0
    have hy : y ∈ U i := by simpa using hp 1
    rw [hFi i x hx, hFi i y hy, ← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
    exact
      SimplyConnectedCover.homotopic_of_mem (hsimply i) _ _
        (SimplyConnectedCover.trans_mem _ _
          (SimplyConnectedCover.chartPath_mem U hsimply o ho i x hx) hp)
        (SimplyConnectedCover.chartPath_mem U hsimply o ho i y hy)
  have hpc : PathConnectedSpace X :=
    { nonempty := ⟨o⟩
      joined := fun x y => ⟨(c x).symm.trans (c y)⟩ }
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpc, ?_⟩
  intro x y p q
  have hp := SimplyConnectedCover.section_trans_of_open_cover U hopen hcover o F hF p
  have hq := SimplyConnectedCover.section_trans_of_open_cover U hopen hcover o F hF q
  apply Path.Homotopic.Quotient.eq.mp
  have h :=
    congrArg (fun r : Path.Homotopic.Quotient o y => (F x).symm.trans r) (hp.trans hq.symm)
  simpa only [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] using h

theorem fundamentalGroup_eq_one_of_path {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (hx : ∀ g : FundamentalGroup X x, g = 1) (g : FundamentalGroup X y) : g = 1 := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  obtain ⟨h, rfl⟩ := e.surjective g
  rw [hx h, map_one]

theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) : SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 :=
  by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    exact fun _ => Subsingleton.elim _ _
  · intro hx
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, ?_⟩
    intro y γ
    exact
      Path.Homotopic.Quotient.eq.mp
        (fundamentalGroup_eq_one_of_path (PathConnectedSpace.somePath x y) hx
          (Path.Homotopic.Quotient.mk γ))

theorem simplyConnectedSpace_of_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hx : ∀ g : FundamentalGroup X x, g = 1) :
    SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_fundamentalGroup_eq_one x).mpr hx

theorem SphereHomology.twoOpenCover_pathConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩

theorem SphereHomology.twoOpenCover_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] (g : FundamentalGroup X D.base) : g = 1 := by
  have h :
    MonoidHom.id (FundamentalGroup X D.base) =
      (1 : FundamentalGroup X D.base →* FundamentalGroup X D.base) := by
    apply D.hom_ext
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomU a = 1
      rw [ha, map_one]
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomV a = 1
      rw [ha, map_one]
  exact DFunLike.congr_fun h g

theorem SphereHomology.twoOpenCover_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] : SimplyConnectedSpace X := by
  let := twoOpenCover_pathConnectedSpace D
  exact
    simplyConnectedSpace_of_fundamentalGroup_eq_one D.base
      (twoOpenCover_fundamentalGroup_eq_one D)

def SphereHomology.suspensionConeCover (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (x : X) : FundamentalGroupVanKampen.TwoOpenCover (CuspCentralHomology.Suspension X)
    where
  U := ⟨CuspCentralHomology.Suspension.northOpen, CuspCentralHomology.Suspension.northOpen_isOpen⟩
  V := ⟨CuspCentralHomology.Suspension.southOpen, CuspCentralHomology.Suspension.southOpen_isOpen⟩
  cover := CuspCentralHomology.Suspension.open_cover
  pathConnectedU := by
    change
      IsPathConnected
        (CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedV := by
    change
      IsPathConnected
        (CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X))
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  pathConnectedIntersection := by
    change IsPathConnected (CuspCentralHomology.Suspension.middleBand X)
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  base := CuspCentralHomology.Suspension.mk ⟨1 / 2, by norm_num⟩ x
  baseU := by
    change (1 / 2 : ℝ) < 3 / 4
    norm_num
  baseV := by
    change (1 / 4 : ℝ) < 1 / 2
    norm_num

instance SphereHomology.suspension_simplyConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : SimplyConnectedSpace (CuspCentralHomology.Suspension X) := by
  let D := suspensionConeCover X (Classical.choice (inferInstance : Nonempty X))
  let : SimplyConnectedSpace D.U := by
    change
      SimplyConnectedSpace
        (CuspCentralHomology.Suspension.northOpen : Set (CuspCentralHomology.Suspension X))
    infer_instance
  let : SimplyConnectedSpace D.V := by
    change
      SimplyConnectedSpace
        (CuspCentralHomology.Suspension.southOpen : Set (CuspCentralHomology.Suspension X))
    infer_instance
  exact twoOpenCover_simplyConnectedSpace D

instance SphereHomology.unitSphere_simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace (UnitSphere (n + 2)) :=
  (suspensionSphereHomeomorph (n + 1)).symm.toHomotopyEquiv.simplyConnectedSpace
theorem SphereHomology.unitSphere_piTwo_subsingleton (n : ℕ) (x : UnitSphere (n + 3)) :
    Subsingleton (π_ 2 (UnitSphere (n + 3)) x) := by
  let := unitSphere_homology_subsingleton (n + 2) 2 (by decide) (by omega)
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton


def ThirdHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    Additive (π_ 3 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3 :=
  HigherHurewicz.hurewiczLinearEquiv (m := 0) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def ThirdHurewicz.hurewiczPi3Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    π_ 3 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 3)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

def FourthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    Additive (π_ 4 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 4 :=
  HigherHurewicz.hurewiczLinearEquiv (m := 1) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def FourthHurewicz.hurewiczPi4Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    π_ 4 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 4)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

def FifthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    Additive (π_ 5 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 5 :=
  HigherHurewicz.hurewiczLinearEquiv (m := 2) x (by
    intro j hj hjn
    interval_cases j <;> infer_instance)

def FifthHurewicz.hurewiczPi5Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    π_ 5 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 5)
    where
  toFun a := Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a))
  invFun c := Additive.toMul ((hurewiczLinearEquiv x).symm (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul ((hurewiczLinearEquiv x).symm_apply_apply (Additive.ofMul a))
  right_inv c := congrArg Multiplicative.ofAdd ((hurewiczLinearEquiv x).apply_symm_apply (Multiplicative.toAdd c))
  map_mul' a b := by
    change Multiplicative.ofAdd (hurewiczLinearEquiv x (Additive.ofMul a + Additive.ofMul b)) = _
    exact congrArg Multiplicative.ofAdd (map_add (hurewiczLinearEquiv x) _ _)

abbrev SixSphereCube.StandardSphere :=
  SphereHomology.UnitSphere 6

def SixSphereCube.euclideanOnePointSphereHomeomorph :
    OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 6)) (ι := Fin 7) (by simp)

def SixSphereCube.sphereBasePoint : StandardSphere :=
  euclideanOnePointSphereHomeomorph (OnePoint.infty)

theorem Degree.Sphere.piTwo_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 2 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 2 (by decide) (by decide) x

theorem Degree.Sphere.piThree_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 3 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 3 (by decide) (by decide) x

theorem Degree.Sphere.piFour_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 4 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 4 (by decide) (by decide) x

theorem Degree.Sphere.piFive_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 5 SixSphereCube.StandardSphere x) :=
  HigherHurewicz.sphere_pi_subsingleton_of_lt 6 5 (by decide) (by decide) x

end Mathoverflow1973

end
