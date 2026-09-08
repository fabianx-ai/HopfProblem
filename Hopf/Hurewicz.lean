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

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.crossProductTriangle_zero_eq_zeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] :
    PeriodTorusHigherHomology.crossProductTriangle X Y 0 =
      PeriodTorusHigherHomology.crossProductZeroRight X Y 2 := by
  apply PeriodTorusHigherHomology.chainBilinearMap_ext X Y 2 0
  intro σ τ
  rw [PeriodTorusHigherHomology.crossProductTriangle_simplex,
    PeriodTorusHigherHomology.formalTriangleCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex,
    PeriodTorusHigherHomology.crossProductZeroRight_simplex]
  apply congrArg (FirstHurewicz.simplexChain (X × Y) 2)
  change
    (σ.prodMap τ).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 2 i, SingularMayerVietoris.stdVertices 0 0))) =
      (PeriodTorusHigherHomology.crossInsertRight
            (PeriodTorusHigherHomology.zeroSimplexValue τ)).comp
        σ
  rw [PeriodTorusHigherHomology.productAffineSimplex_point_right,
    SingularMayerVietoris.affineSimplex_stdVertices, ContinuousMap.comp_id]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.crossProductTriangle_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2) (y : Y) :
    PeriodTorusHigherHomology.crossProductTriangle X Y 0 a (FirstHurewicz.pointChain y) =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 2 a := by
  rw [crossProductTriangle_zero_eq_zeroRight, FirstHurewicz.pointChain,
    PeriodTorusHigherHomology.crossProductZeroRight_simplex_right]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.crossProductEdge_point_right (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1) (y : Y) :
    PeriodTorusHigherHomology.crossProductEdge X Y 0 a (FirstHurewicz.pointChain y) =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertRight y) 1 a := by
  rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductEdge_zero_simplex_right]
  rfl

abbrev SecondHurewicz.Remaining :=
  { j : Fin 2 // j ≠ 0 }

abbrev SecondHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

def SecondHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (unitInterval), X)
    where
  toFun z := z.1 (fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem SecondHurewicz.evaluation_zero {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 0) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inl rfl⟩

@[simp]
theorem SecondHurewicz.evaluation_one {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) : evaluation x (p, 1) = x :=
  GenLoop.boundary p _ ⟨⟨1, by decide⟩, Or.inr rfl⟩

@[simp]
theorem SecondHurewicz.evaluation_comp_right_zero {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_zero x p

@[simp]
theorem SecondHurewicz.evaluation_comp_right_one {X : Type} [TopologicalSpace X] (x : X) :
    (evaluation x).comp (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) =
      ContinuousMap.const (BasedLoopSpace x) x := by
  ext p
  exact evaluation_one x p

def SecondHurewicz.squareCoordinates : C((unitInterval) × (unitInterval), Fin 2 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 2) (z.1, fun _ => z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem SecondHurewicz.squareCoordinates_zero (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 0 = z.1 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem SecondHurewicz.squareCoordinates_one (z : (unitInterval) × (unitInterval)) :
    squareCoordinates z 1 = z.2 := by
  simp [squareCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

def SecondHurewicz.squareMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    C((unitInterval) × (unitInterval), X) :=
  p.val.comp squareCoordinates

theorem SecondHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
          (ContinuousMap.id (unitInterval))) =
      squareMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.intervalChain : FirstHurewicz.Chains (unitInterval) 1 :=
  FirstHurewicz.pathChain Path.id

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.intervalChain_boundary :
    FirstHurewicz.boundaryOne (unitInterval) intervalChain =
      FirstHurewicz.pointChain (1 : (unitInterval)) -
        FirstHurewicz.pointChain (0 : (unitInterval)) :=
  FirstHurewicz.boundaryOne_pathChain Path.id

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluation_right_zero_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) n) :
    FirstHurewicz.inducedChain (evaluation x) n
        (FirstHurewicz.inducedChain
          (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) n a) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((FirstHurewicz.inducedChain (evaluation x) n).comp
          (FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) n))
        a =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_right_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluation_right_one_chain {X : Type} [TopologicalSpace X] (x : X) (n : ℕ)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) n) :
    FirstHurewicz.inducedChain (evaluation x) n
        (FirstHurewicz.inducedChain
          (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) n a) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x) x) n a := by
  change
    ((FirstHurewicz.inducedChain (evaluation x) n).comp
          (FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) n))
        a =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_right_one]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluated_edge_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 1
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductEdge_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.evaluated_triangle_endpoint_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      0 := by
  simp only [intervalChain_boundary, map_sub, crossProductTriangle_point_right,
    evaluation_right_one_chain, evaluation_right_zero_chain, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 2 :=
  (FirstHurewicz.inducedChain (evaluation x) 2).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 3 :=
  (FirstHurewicz.inducedChain (evaluation x) 3).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1)
      intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1 a
          intervalChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.boundaryTwo_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    FirstHurewicz.boundaryTwo X (suspensionOne x a) = 0 := by
  change ((FirstHurewicz.singularComplex X).d 2 1).hom (suspensionOne x a) = 0
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 0]
  change
    FirstHurewicz.inducedChain (evaluation x) 1
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x) (unitInterval) 1
            (FirstHurewicz.boundaryOne (BasedLoopSpace x) a) intervalChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 0 a
            (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_endpoint_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.boundaryThree_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 0]
  change
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) intervalChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 0 a
            (FirstHurewicz.boundaryOne (unitInterval) intervalChain)) =
      _
  rw [map_add, evaluated_triangle_endpoint_cancel, add_zero]
  rfl

def SecondHurewicz.pathSquareCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 2
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryTwo_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
theorem SecondHurewicz.pathSquareCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathSquareCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

def SecondHurewicz.pathSquareClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
    (pathSquareCycle x p)

theorem SecondHurewicz.pathSquare_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathSquareCycle x p).1 - (pathSquareCycle x q).1 := by
  rw [boundaryThree_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem SecondHurewicz.pathSquareClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathSquareClass x p = pathSquareClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 2 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathSquare_homotopy_boundary x H⟩

theorem SecondHurewicz.pathSquareClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathSquareClass x p = pathSquareClass x q := by
  obtain ⟨H⟩ := h
  exact pathSquareClass_homotopy x H

@[simp]
theorem SecondHurewicz.pathSquareClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathSquareClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        2 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryThree_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

theorem SecondHurewicz.pathSquare_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathSquareCycle x (p.trans q)).1 - ((pathSquareCycle x p).1 + (pathSquareCycle x q).1) := by
  rw [map_neg, boundaryThree_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathSquareCycle_val]
  abel

theorem SecondHurewicz.pathSquareClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathSquareClass x (p.trans q) = pathSquareClass x p + pathSquareClass x q := by
  unfold pathSquareClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 2 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathSquare_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.productSquareChain :
    FirstHurewicz.Chains ((unitInterval) × (unitInterval)) 2 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
    intervalChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.productSquareChain_boundary :
    FirstHurewicz.boundaryTwo ((unitInterval) × (unitInterval)) productSquareChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft (1 : (unitInterval)))
            1 intervalChain -
          FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertLeft (0 : (unitInterval))) 1 intervalChain -
        (FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (1 : (unitInterval))) 1 intervalChain -
          FirstHurewicz.inducedChain
            (PeriodTorusHigherHomology.crossInsertRight (0 : (unitInterval))) 1 intervalChain) := by
  change
    ((FirstHurewicz.singularComplex ((unitInterval) × (unitInterval))).d 2 1).hom
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 1 intervalChain
          intervalChain) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 0]
  change
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (unitInterval) 1
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain) intervalChain -
        PeriodTorusHigherHomology.crossProductEdge (unitInterval) (unitInterval) 0 intervalChain
          (FirstHurewicz.boundaryOne (unitInterval) intervalChain) =
      _
  simp only [intervalChain_boundary, map_sub, LinearMap.sub_apply, crossProductEdge_point_right]
  simp only [FirstHurewicz.pointChain,
    PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.fundamentalSquareChain : FirstHurewicz.Chains (Fin 2 → (unitInterval)) 2 :=
  FirstHurewicz.inducedChain squareCoordinates 2 productSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.induced_intervalChain {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) :
    FirstHurewicz.inducedChain p.toContinuousMap 1 intervalChain = FirstHurewicz.pathChain p := by
  rw [intervalChain, FirstHurewicz.pathChain, FirstHurewicz.inducedChain_simplex]
  apply congrArg (FirstHurewicz.simplexChain X 1)
  ext s
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 2) p)) =
      FirstHurewicz.inducedChain (squareMap p) 2 productSquareChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 2) p).toContinuousMap (ContinuousMap.id (unitInterval)) 1
      intervalChain intervalChain
  rw [induced_intervalChain, FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 2).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 2) p).toContinuousMap.prodMap
              (ContinuousMap.id (unitInterval)))
            2))
        productSquareChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.squareChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    FirstHurewicz.Chains X 2 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 2) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareChain_boundary {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : FirstHurewicz.boundaryTwo X (squareChain p) = 0 :=
  boundaryTwo_suspensionOne_of_cycle x _ (FirstHurewicz.boundaryOne_loop (GenLoop.toLoop 0 p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.squareCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  pathSquareCycle x (GenLoop.toLoop (0 : Fin 2) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.squareHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : SingularMayerVietoris.SingularHomology X 2 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
    (squareCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareHomologyClass_eq_pathSquareClass {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    squareHomologyClass p = pathSquareClass x (GenLoop.toLoop (0 : Fin 2) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x} (h : GenLoop.Homotopic p q) :
    squareHomologyClass p = squareHomologyClass q :=
  pathSquareClass_homotopic x (GenLoop.homotopicTo (0 : Fin 2) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.const : GenLoop (Fin 2) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.squareHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    squareHomologyClass (GenLoop.const : GenLoop (Fin 2) X x) = 0 := by
  rw [squareHomologyClass_eq_pathSquareClass, toLoop_const, pathSquareClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    GenLoop.toLoop (0 : Fin 2) (GenLoop.transAt (0 : Fin 2) p q) =
      (GenLoop.toLoop (0 : Fin 2) p).trans (GenLoop.toLoop (0 : Fin 2) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 2))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 2)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.squareHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 2) X x) :
    squareHomologyClass (GenLoop.transAt (0 : Fin 2) p q) =
      squareHomologyClass p + squareHomologyClass q := by
  simp only [squareHomologyClass_eq_pathSquareClass, toLoop_transAt, pathSquareClass_trans]

def SecondHurewicz.mapGenLoop {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : C(GenLoop N X x, GenLoop N Y (f x))
    where
  toFun p := ⟨f.comp p.val, fun t ht => congrArg f (p.property t ht)⟩
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem SecondHurewicz.mapGenLoop_val {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : GenLoop N X x) : (mapGenLoop f x p).val = f.comp p.val :=
  rfl

@[simp]
theorem SecondHurewicz.mapGenLoop_const {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : mapGenLoop (N := N) f x GenLoop.const = GenLoop.const :=
  rfl

theorem SecondHurewicz.mapGenLoop_homotopic {N X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f x p) (mapGenLoop f x q) :=
  h.comp_continuousMap f

@[simp]
theorem SecondHurewicz.mapGenLoop_transAt {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] (f : C(X, Y)) (x : X) (i : N) (p q : GenLoop N X x) :
    mapGenLoop f x (GenLoop.transAt i p q) =
      GenLoop.transAt i (mapGenLoop f x p) (mapGenLoop f x q) := by
  apply GenLoop.ext
  intro t
  change f (if (t i : ℝ) ≤ 1 / 2 then _ else _) = if (t i : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> rfl

def SecondHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x → SingularMayerVietoris.SingularHomology X 2 :=
  Quotient.lift squareHomologyClass (fun _ _ h => squareHomologyClass_homotopic h)

def SecondHurewicz.hurewiczPi2 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 2 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (squareHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 2 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (squareHomologyClass (GenLoop.transAt (0 : Fin 2) q p)) =
        Multiplicative.ofAdd (squareHomologyClass p + squareHomologyClass q)
    rw [squareHomologyClass_transAt, add_comm]

def SecondHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 2 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2
    where
  toFun := (hurewiczPi2 x).toAdditiveLeft
  map_add' := (hurewiczPi2 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi2 x).toAdditiveLeft ℤ ℤ n a

theorem SecondHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 2) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (squareCycle p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  H.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.crossPoint_left {A : Type} [TopologicalSpace A] (n : ℕ)
    (t : (unitInterval)) (c : FirstHurewicz.Chains A n) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) A n (FirstHurewicz.pointChain t)
        c =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) n c := by
  rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.inducedChain_timeSlice {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (H : C((unitInterval) × A, X)) (t : (unitInterval)) (n : ℕ)
    (c : FirstHurewicz.Chains A n) :
    FirstHurewicz.inducedChain H n
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) n c) =
      FirstHurewicz.inducedChain (timeSlice H t) n c := by
  change
    ((FirstHurewicz.inducedChain H n).comp
          (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) n))
        c =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.prismOperator {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) :
    FirstHurewicz.Chains A n →ₗ[ℤ] FirstHurewicz.Chains X (n + 1) :=
  (FirstHurewicz.inducedChain H (n + 1)).comp
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n SecondHurewicz.intervalChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.prismOperator_apply {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X)) (c : FirstHurewicz.Chains A n) :
    prismOperator n H c =
      FirstHurewicz.inducedChain H (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n
          SecondHurewicz.intervalChain c) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.prismOperator_boundary {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (c : FirstHurewicz.Chains A (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom (prismOperator (n + 1) H c) =
      FirstHurewicz.inducedChain (timeSlice H 1) (n + 1) c -
          FirstHurewicz.inducedChain (timeSlice H 0) (n + 1) c -
        prismOperator n H (((FirstHurewicz.singularComplex A).d (n + 1) n).hom c) := by
  rw [prismOperator_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary n]
  change
    FirstHurewicz.inducedChain H (n + 1)
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) A (n + 1)
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain) c -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) A n
            SecondHurewicz.intervalChain
            (((FirstHurewicz.singularComplex A).d (n + 1) n).hom c)) =
      _
  simp only [SecondHurewicz.intervalChain_boundary, map_sub, LinearMap.sub_apply, crossPoint_left,
    inducedChain_timeSlice, prismOperator_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.prismOperator_domain {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] (n : ℕ) (f : C(A, B)) (H : C((unitInterval) × B, X))
    (c : FirstHurewicz.Chains A n) :
    prismOperator n (H.comp ((ContinuousMap.id (unitInterval)).prodMap f)) c =
      prismOperator n H (FirstHurewicz.inducedChain f n c) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f n
      SecondHurewicz.intervalChain c
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  simp only [prismOperator_apply, FirstHurewicz.inducedChain_comp, LinearMap.comp_apply]
  exact congrArg (FirstHurewicz.inducedChain H (n + 1)) h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.simplexPrism {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : C((unitInterval) × FirstHurewicz.Simplex n, X)) : FirstHurewicz.Chains X (n + 1) :=
  prismOperator n H
    (FirstHurewicz.simplexChain (FirstHurewicz.Simplex n) n
      (ContinuousMap.id (FirstHurewicz.Simplex n)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.prismOperator_simplex {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (n : ℕ) (H : C((unitInterval) × A, X))
    (smp : FirstHurewicz.SingularSimplex A n) :
    prismOperator n H (FirstHurewicz.simplexChain A n smp) =
      simplexPrism n (H.comp ((ContinuousMap.id (unitInterval)).prodMap smp)) := by
  have h :=
    prismOperator_domain n smp H
      (FirstHurewicz.simplexChain (FirstHurewicz.Simplex n) n
        (ContinuousMap.id (FirstHurewicz.Simplex n)))
  rw [FirstHurewicz.inducedChain_simplex, ContinuousMap.comp_id] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.simplexPrism_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (H : C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom (simplexPrism (n + 1) H) =
      FirstHurewicz.simplexChain X (n + 1) (timeSlice H 1) -
          FirstHurewicz.simplexChain X (n + 1) (timeSlice H 0) -
        ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ i.val •
            simplexPrism n
              (H.comp
                ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i))) := by
  rw [simplexPrism, prismOperator_boundary, FirstHurewicz.inducedChain_simplex,
    FirstHurewicz.inducedChain_simplex, ContinuousMap.comp_id, ContinuousMap.comp_id]
  rw [FirstHurewicz.boundary_simplex, map_sum]
  simp only [map_zsmul, ContinuousMap.id_comp, prismOperator_simplex]

def SecondHurewicz.SimplyConnected.simplexEndpointOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (t : (unitInterval)) : FirstHurewicz.Chains X n →ₗ[ℤ] FirstHurewicz.Chains X n :=
  FirstHurewicz.chainLift X n fun smp => FirstHurewicz.simplexChain X n (timeSlice (H smp) t)

@[simp]
theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (t : (unitInterval)) (smp : FirstHurewicz.SingularSimplex X n) :
    simplexEndpointOperator n H t (FirstHurewicz.simplexChain X n smp) =
      FirstHurewicz.simplexChain X n (timeSlice (H smp) t) :=
  FirstHurewicz.chainLift_simplex X n _ smp

def SecondHurewicz.SimplyConnected.simplexPrismOperator {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X)) :
    FirstHurewicz.Chains X n →ₗ[ℤ] FirstHurewicz.Chains X (n + 1) :=
  FirstHurewicz.chainLift X n fun smp => simplexPrism n (H smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.simplexPrismOperator_simplex {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (smp : FirstHurewicz.SingularSimplex X n) :
    simplexPrismOperator n H (FirstHurewicz.simplexChain X n smp) = simplexPrism n (H smp) :=
  FirstHurewicz.chainLift_simplex X n _ smp

def SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies {X : Type} [TopologicalSpace X]
    (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)) :
    Prop :=
  ∀ smp i,
    (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i)) =
      H (smp.comp (FirstHurewicz.simplexFace n i))

theorem SecondHurewicz.SimplyConnected.timeSlice_face {X : Type} [TopologicalSpace X] {n : ℕ}
    {H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X)}
    {H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X)}
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (i : Fin (n + 2)) (t : (unitInterval)) :
    (timeSlice (H' smp) t).comp (FirstHurewicz.simplexFace n i) =
      timeSlice (H (smp.comp (FirstHurewicz.simplexFace n i))) t :=
  congrArg (fun F => timeSlice F t) (h smp i)

theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (t : (unitInterval))
    (c : FirstHurewicz.Chains X (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (simplexEndpointOperator (n + 1) H' t c) =
      simplexEndpointOperator n H t (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((FirstHurewicz.singularComplex X).d (n + 1) n).hom).comp
        (simplexEndpointOperator (n + 1) H' t) =
      (simplexEndpointOperator n H t).comp ((FirstHurewicz.singularComplex X).d (n + 1) n).hom := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, simplexEndpointOperator_simplex,
      FirstHurewicz.boundary_simplex, map_sum, map_zsmul, timeSlice_face h]
  exact LinearMap.congr_fun hc c

theorem SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (c : FirstHurewicz.Chains X (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom
        (simplexPrismOperator (n + 1) H' c) =
      simplexEndpointOperator (n + 1) H' 1 c - simplexEndpointOperator (n + 1) H' 0 c -
        simplexPrismOperator n H (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) := by
  have hc :
    (((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom).comp
        (simplexPrismOperator (n + 1) H') =
      simplexEndpointOperator (n + 1) H' 1 - simplexEndpointOperator (n + 1) H' 0 -
        (simplexPrismOperator n H).comp ((FirstHurewicz.singularComplex X).d (n + 1) n).hom := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    have hface := h smp
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, simplexPrismOperator_simplex,
      simplexPrism_boundary, simplexEndpointOperator_simplex, FirstHurewicz.boundary_simplex,
      map_sum, map_zsmul, hface]
  exact LinearMap.congr_fun hc c

theorem SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero {X : Type}
    [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (h₀ : ∀ smp, timeSlice (H smp) 0 = smp) : simplexEndpointOperator n H 0 = LinearMap.id := by
  apply FirstHurewicz.chainMap_ext X n
  intro smp
  rw [simplexEndpointOperator_simplex, h₀]
  rfl

def SecondHurewicz.SimplyConnected.straightenedTwoCycle {X : Type} [TopologicalSpace X]
    (H₁ : FirstHurewicz.SingularSimplex X 1 → C((unitInterval) × FirstHurewicz.Simplex 1, X))
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 2
    (simplexEndpointOperator 2 H₂ 1 c.1)
    (by
      rw [simplexEndpointOperator_boundary 1 H₁ H₂ h,
        SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2
          c,
        map_zero])

theorem SecondHurewicz.SimplyConnected.straightenedTwoCycle_class {X : Type} [TopologicalSpace X]
    (H₁ : FirstHurewicz.SingularSimplex X 1 → C((unitInterval) × FirstHurewicz.Simplex 1, X))
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (h : FaceCompatibleHomotopies 1 H₁ H₂) (h₀ : ∀ smp, timeSlice (H₂ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (straightenedTwoCycle H₁ H₂ h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 2 _
        _).mpr
  refine ⟨simplexPrismOperator 2 H₂ c.1, ?_⟩
  rw [simplexPrismOperator_boundary 1 H₁ H₂ h, simplexEndpointOperator_zero 2 H₂ h₀,
    SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2 c,
    map_zero, sub_zero]
  rfl

structure SecondHurewicz.SimplyConnected.VertexHomotopyData {X : Type} [TopologicalSpace X]
    (x : X) (n : ℕ) where
  homotopy : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X)
  zero :
    ∀ (smp : C(FirstHurewicz.Simplex n, X)) (s : FirstHurewicz.Simplex n),
      homotopy smp (0, s) = smp s
  one_verticesBased : ∀ smp, VerticesBased x n (timeSlice (homotopy smp) 1)
  of_verticesBased :
    ∀ smp,
      VerticesBased x n smp →
        homotopy smp =
          smp.comp
            (ContinuousMap.snd :
              C((unitInterval) × FirstHurewicz.Simplex n, FirstHurewicz.Simplex n))
  face_compatible :
    ∀ smp : C(FirstHurewicz.Simplex (n + 1), X),
      FaceCompatible (fun i => homotopy (smp.comp (FirstHurewicz.simplexFace n i)))

def SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X)) :
    C((unitInterval) × SimplexBoundary (n + 1), X) :=
  glueFaceHomotopies (fun i => D.homotopy (smp.comp (FirstHurewicz.simplexFace n i)))
    (D.face_compatible smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X))
    (i : Fin (n + 2)) (r : (unitInterval)) (s : FirstHurewicz.Simplex n) :
    vertexBoundaryHomotopy D smp (r, simplexFaceBoundary n i s) =
      D.homotopy (smp.comp (FirstHurewicz.simplexFace n i)) (r, s) :=
  glueFaceHomotopies_face _ _ i r s

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexBoundaryHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X))
    (s : SimplexBoundary (n + 1)) : vertexBoundaryHomotopy D smp (0, s) = smp s.val :=
  glueFaceHomotopies_zero _ _ smp (fun i t => D.zero (smp.comp (FirstHurewicz.simplexFace n i)) t)
    s

def SecondHurewicz.SimplyConnected.vertexStepHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X)) :
    C((unitInterval) × FirstHurewicz.Simplex (n + 1), X) := by
  classical
    exact
    if VerticesBased x (n + 1) smp then
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × FirstHurewicz.Simplex (n + 1), FirstHurewicz.Simplex (n + 1)))
    else
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp)

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (h : VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × FirstHurewicz.Simplex (n + 1), FirstHurewicz.Simplex (n + 1))) := by
  classical simp only [vertexStepHomotopy, if_pos h]

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_not_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (h : ¬VerticesBased x (n + 1) smp) :
    vertexStepHomotopy D smp =
      extendBoundaryHomotopy smp (vertexBoundaryHomotopy D smp)
        (vertexBoundaryHomotopy_zero D smp) := by classical simp only [vertexStepHomotopy, if_neg h]

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_zero {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) (smp : C(FirstHurewicz.Simplex (n + 1), X))
    (s : FirstHurewicz.Simplex (n + 1)) : vertexStepHomotopy D smp (0, s) = smp s := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h]
    exact extendBoundaryHomotopy_bottom _ _ _ s

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_face_apply {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex n) :
    vertexStepHomotopy D smp (r, FirstHurewicz.simplexFace n i s) =
      D.homotopy (smp.comp (FirstHurewicz.simplexFace n i)) (r, s) := by
  classical
  by_cases h : VerticesBased x (n + 1) smp
  · rw [vertexStepHomotopy_of_verticesBased D smp h, D.of_verticesBased _ (h.face i)]
    rfl
  · rw [vertexStepHomotopy_of_not_verticesBased D smp h, extendBoundaryHomotopy_face]
    exact vertexBoundaryHomotopy_face D smp i r s

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_face {X : Type} [TopologicalSpace X]
    {x : X} {n : ℕ} (D : VertexHomotopyData x n) :
    FaceCompatibleHomotopies n D.homotopy (vertexStepHomotopy D) := by
  intro smp i
  ext u
  exact vertexStepHomotopy_face_apply D smp i u.1 u.2

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) :
    VerticesBased x (n + 1) (timeSlice (vertexStepHomotopy D smp) 1) := by
  intro k
  obtain ⟨i, j, hij⟩ := simplexVertex_exists_face n k
  change vertexStepHomotopy D smp (1, stdSimplex.vertex k) = x
  rw [← hij, vertexStepHomotopy_face_apply]
  exact D.one_verticesBased (smp.comp (FirstHurewicz.simplexFace n i)) j

theorem SecondHurewicz.SimplyConnected.vertexStepHomotopy_faceCompatible {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (D : VertexHomotopyData x n)
    (smp : C(FirstHurewicz.Simplex (n + 2), X)) :
    FaceCompatible
      (fun i => vertexStepHomotopy D (smp.comp (FirstHurewicz.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij r u
  rw [vertexStepHomotopy_face_apply, vertexStepHomotopy_face_apply,
    PeriodTorusLineBundle.ChernCocycle.singularSimplex_face_face smp hij]

def SecondHurewicz.SimplyConnected.VertexHomotopyData.next {X : Type} [TopologicalSpace X] {x : X}
    {n : ℕ} (D : SecondHurewicz.SimplyConnected.VertexHomotopyData x n) :
    SecondHurewicz.SimplyConnected.VertexHomotopyData x (n + 1)
    where
  homotopy := SecondHurewicz.SimplyConnected.vertexStepHomotopy D
  zero := SecondHurewicz.SimplyConnected.vertexStepHomotopy_zero D
  one_verticesBased := SecondHurewicz.SimplyConnected.vertexStepHomotopy_one_verticesBased D
  of_verticesBased := SecondHurewicz.SimplyConnected.vertexStepHomotopy_of_verticesBased D
  face_compatible := SecondHurewicz.SimplyConnected.vertexStepHomotopy_faceCompatible D

def SecondHurewicz.SimplyConnected.basedEdgePath {X : Type} [TopologicalSpace X] (x : X)
    (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) : Path x x :=
  (FirstHurewicz.simplexPath smp).cast h₀.symm h₁.symm

@[simp]
theorem SecondHurewicz.SimplyConnected.basedEdgePath_const {X : Type} [TopologicalSpace X]
    (x : X) :
    basedEdgePath x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) rfl rfl = Path.refl x := by
  apply Path.ext
  funext t
  rfl

def SecondHurewicz.SimplyConnected.chosenBasePath {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x y : X) : Path y x := by
  classical exact if h : y = x then (Path.refl x).cast h rfl else PathConnectedSpace.somePath y x

@[simp]
theorem SecondHurewicz.SimplyConnected.chosenBasePath_self {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : chosenBasePath x x = Path.refl x := by
  simp [chosenBasePath]

def SecondHurewicz.SimplyConnected.chosenNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (p : Path x x) : p.Homotopy (Path.refl x) := by
  classical
    exact
    if h : p = Path.refl x then (Path.Homotopy.refl (Path.refl x)).cast h.symm rfl
    else Classical.choice (SimplyConnectedSpace.paths_homotopic p (Path.refl x))

@[simp]
theorem SecondHurewicz.SimplyConnected.chosenNullHomotopy_refl {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    chosenNullHomotopy x (Path.refl x) = Path.Homotopy.refl (Path.refl x) := by
  simp [chosenNullHomotopy]
  rfl

def SecondHurewicz.SimplyConnected.vertexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 0, X)) :
    C((unitInterval) × FirstHurewicz.Simplex 0, X) :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).toContinuousMap.comp
    (ContinuousMap.fst : C((unitInterval) × FirstHurewicz.Simplex 0, (unitInterval)))

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 0, X))
    (s : FirstHurewicz.Simplex 0) : vertexHomotopy x smp (0, s) = smp s := by
  change chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) 0 = smp s
  rw [Path.source, FirstHurewicz.simplexZero_eq_vertex s]

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 0, X))
    (s : FirstHurewicz.Simplex 0) : vertexHomotopy x smp (1, s) = x :=
  (chosenBasePath x (smp (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))).target

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    vertexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 0) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 0) x := by
  ext t
  change chosenBasePath x x t.1 = x
  rw [chosenBasePath_self]
  rfl

def SecondHurewicz.SimplyConnected.edgeNullHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) :
    C((unitInterval) × FirstHurewicz.Simplex 1, X) :=
  (chosenNullHomotopy x (basedEdgePath x smp h₀ h₁)).toContinuousMap.comp
    ((ContinuousMap.id (unitInterval)).prodMap
      ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩)

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ h₁)
    (s : FirstHurewicz.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (0, s) = smp s := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (0, stdSimplexHomeomorphUnitInterval s) =
      smp s
  rw [ContinuousMap.HomotopyWith.apply_zero]
  change smp (stdSimplexHomeomorphUnitInterval.symm (stdSimplexHomeomorphUnitInterval s)) = smp s
  rw [stdSimplexHomeomorphUnitInterval.symm_apply_apply]

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ h₁)
    (s : FirstHurewicz.Simplex 1) : edgeNullHomotopy x smp h₀ h₁ (1, s) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (1, stdSimplexHomeomorphUnitInterval s) = x
  rw [ContinuousMap.HomotopyWith.apply_one]
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_vertex_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (h₀ h₁) (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero]
  exact Path.Homotopy.source _ t

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_vertex_one {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) (h₀ h₁)
    (t : (unitInterval)) :
    edgeNullHomotopy x smp h₀ h₁ (t, stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x := by
  change
    chosenNullHomotopy x (basedEdgePath x smp h₀ h₁) (t, stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_one]
  exact Path.Homotopy.target _ t

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeNullHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    edgeNullHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) rfl rfl =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 1) x := by
  ext t
  change
    chosenNullHomotopy x
        (basedEdgePath x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) rfl rfl)
        (t.1, stdSimplexHomeomorphUnitInterval t.2) =
      x
  rw [basedEdgePath_const, chosenNullHomotopy_refl]
  rfl

def SecondHurewicz.SimplyConnected.vertexInitialData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : VertexHomotopyData x 0
    where
  homotopy := vertexHomotopy x
  zero := vertexHomotopy_zero x
  one_verticesBased smp i := vertexHomotopy_one x smp (stdSimplex.vertex i)
  of_verticesBased smp
    h := by
    have hs : smp = ContinuousMap.const (FirstHurewicz.Simplex 0) x := verticesBased_zero_iff.mp h
    rw [hs, vertexHomotopy_const]
    rfl
  face_compatible
    smp :=
    faceCompatible_zero (fun i => vertexHomotopy x (smp.comp (FirstHurewicz.simplexFace 0 i)))

def SecondHurewicz.SimplyConnected.vertexStraighteningData {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : (n : ℕ) → VertexHomotopyData x n
  | 0 => vertexInitialData x
  | n + 1 => (vertexStraighteningData x n).next

def SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : C(FirstHurewicz.Simplex n, X)) :
    C((unitInterval) × FirstHurewicz.Simplex n, X) :=
  (vertexStraighteningData x n).homotopy smp

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) (s : FirstHurewicz.Simplex n) :
    vertexStraighteningHomotopy x n smp (0, s) = smp s :=
  (vertexStraighteningData x n).zero smp s

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) :
    timeSlice (vertexStraighteningHomotopy x n smp) 0 = smp := by
  ext s
  exact vertexStraighteningHomotopy_zero x n smp s

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    FaceCompatibleHomotopies n (vertexStraighteningHomotopy x n)
      (vertexStraighteningHomotopy x (n + 1)) :=
  vertexStepHomotopy_face (vertexStraighteningData x n)

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex (n + 1), X)) (i : Fin (n + 2)) (r : (unitInterval)) :
    (timeSlice (vertexStraighteningHomotopy x (n + 1) smp) r).comp
        (FirstHurewicz.simplexFace n i) =
      timeSlice (vertexStraighteningHomotopy x n (smp.comp (FirstHurewicz.simplexFace n i))) r :=
  timeSlice_face (vertexStraighteningHomotopy_face x n) smp i r

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_one_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) :
    VerticesBased x n (timeSlice (vertexStraighteningHomotopy x n smp) 1) :=
  (vertexStraighteningData x n).one_verticesBased smp

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) (h : VerticesBased x n smp) :
    vertexStraighteningHomotopy x n smp =
      smp.comp
        (ContinuousMap.snd :
          C((unitInterval) × FirstHurewicz.Simplex n, FirstHurewicz.Simplex n)) :=
  (vertexStraighteningData x n).of_verticesBased smp h

theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_of_verticesBased
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : C(FirstHurewicz.Simplex n, X)) (h : VerticesBased x n smp) (r : (unitInterval)) :
    timeSlice (vertexStraighteningHomotopy x n smp) r = smp := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n smp h]
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ) :
    vertexStraighteningHomotopy x n (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  rw [vertexStraighteningHomotopy_of_verticesBased x n _ (verticesBased_const x n)]
  rfl

def SecondHurewicz.SimplyConnected.stationarySimplexHomotopy {X : Type} [TopologicalSpace X]
    (n : ℕ) (smp : C(FirstHurewicz.Simplex n, X)) :
    C((unitInterval) × FirstHurewicz.Simplex n, X) :=
  smp.comp
    (ContinuousMap.snd : C((unitInterval) × FirstHurewicz.Simplex n, FirstHurewicz.Simplex n))

def SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X)) :
    C((unitInterval) × FirstHurewicz.Simplex 1, X) := by
  classical
    exact
    if h :
        smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
          smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x then
      edgeNullHomotopy x smp h.1 h.2
    else stationarySimplexHomotopy 1 smp

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (s : FirstHurewicz.Simplex 1) : edgeStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · exact edgeNullHomotopy_zero x smp _ _ s
  · rfl

theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_one {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (h₀ : smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x)
    (h₁ : smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x) (s : FirstHurewicz.Simplex 1) :
    edgeStraighteningHomotopy x smp (1, s) = x := by
  classical
  have h :
    smp (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x ∧
      smp (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = x :=
    ⟨h₀, h₁⟩
  rw [edgeStraighteningHomotopy, dif_pos h]
  exact edgeNullHomotopy_one x smp _ _ s

theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_vertex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (smp : C(FirstHurewicz.Simplex 1, X))
    (i : Fin 2) (t : (unitInterval)) :
    edgeStraighteningHomotopy x smp (t, stdSimplex.vertex (S := ℝ) i) =
      smp (stdSimplex.vertex (S := ℝ) i) := by
  classical
  unfold edgeStraighteningHomotopy
  split
  · rename_i h
    fin_cases i
    · exact (edgeNullHomotopy_vertex_zero x smp h.1 h.2 t).trans h.1.symm
    · exact (edgeNullHomotopy_vertex_one x smp h.1 h.2 t).trans h.2.symm
  · rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_const {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    edgeStraighteningHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 1) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 1) x := by
  classical
  simp only [edgeStraighteningHomotopy, ContinuousMap.const_apply]
  exact edgeNullHomotopy_const x

theorem SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 0 (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change
    edgeStraighteningHomotopy x smp (t, FirstHurewicz.simplexFace 0 i s) =
      smp (FirstHurewicz.simplexFace 0 i s)
  rw [FirstHurewicz.simplexZero_eq_vertex s, FirstHurewicz.simplexFace_vertex]
  exact edgeStraighteningHomotopy_vertex x smp _ t

theorem SecondHurewicz.SimplyConnected.nextFaceHomotopies_compatible {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 2)) :
    FaceCompatible (fun i => H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i))) := by
  apply faceCompatible_of_cofaceCompatible
  intro i j hij t s
  have hi :=
    congrArg (fun F : C((unitInterval) × FirstHurewicz.Simplex n, X) => F (t, s))
      (h (smp.comp (FirstHurewicz.simplexFace (n + 1) j.succ)) i)
  have hj :=
    congrArg (fun F : C((unitInterval) × FirstHurewicz.Simplex n, X) => F (t, s))
      (h (smp.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc)) j)
  change
    H' (smp.comp (FirstHurewicz.simplexFace (n + 1) j.succ))
        (t, FirstHurewicz.simplexFace n i s) =
      H
        ((smp.comp (FirstHurewicz.simplexFace (n + 1) j.succ)).comp
          (FirstHurewicz.simplexFace n i))
        (t, s) at hi
  change
    H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc))
        (t, FirstHurewicz.simplexFace n j s) =
      H
        ((smp.comp (FirstHurewicz.simplexFace (n + 1) i.castSucc)).comp
          (FirstHurewicz.simplexFace n j))
        (t, s) at hj
  rw [hi, hj]
  change
    H (smp.comp ((FirstHurewicz.simplexFace (n + 1) j.succ).comp (FirstHurewicz.simplexFace n i)))
        (t, s) =
      H
        (smp.comp
          ((FirstHurewicz.simplexFace (n + 1) i.castSucc).comp (FirstHurewicz.simplexFace n j)))
        (t, s)
  rw [PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij]

def SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 2)) :
    C((unitInterval) × SimplexBoundary (n + 2), X) :=
  glueFaceHomotopies (fun i => H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i)))
    (nextFaceHomotopies_compatible H H' h smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_face {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (smp : FirstHurewicz.SingularSimplex X (n + 2))
    (i : Fin (n + 3)) (t : (unitInterval)) (s : FirstHurewicz.Simplex (n + 1)) :
    coherentFaceBoundaryHomotopy H H' h smp (t, simplexFaceBoundary (n + 1) i s) =
      H' (smp.comp (FirstHurewicz.simplexFace (n + 1) i)) (t, s) :=
  glueFaceHomotopies_face _ _ i t s

theorem SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X (n + 2)) (b : SimplexBoundary (n + 2)) :
    coherentFaceBoundaryHomotopy H H' h smp (0, b) = smp b.val :=
  glueFaceHomotopies_zero _ _ smp
    (fun i s => h₀ (smp.comp (FirstHurewicz.simplexFace (n + 1) i)) s) b

def SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X (n + 2)) :
    C((unitInterval) × FirstHurewicz.Simplex (n + 2), X) :=
  extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
    (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X (n + 2)) (s : FirstHurewicz.Simplex (n + 2)) :
    extendCoherentSimplexHomotopy H H' h h₀ smp (0, s) = smp s :=
  extendBoundaryHomotopy_bottom _ _ _ s

theorem SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face {X : Type}
    [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : FaceCompatibleHomotopies n H H') (h₀ : ∀ smp s, H' smp (0, s) = smp s) :
    FaceCompatibleHomotopies (n + 1) H' (extendCoherentSimplexHomotopy H H' h h₀) := by
  intro smp i
  ext u
  rcases u with ⟨t, s⟩
  change
    extendBoundaryHomotopy smp (coherentFaceBoundaryHomotopy H H' h smp)
        (coherentFaceBoundaryHomotopy_zero H H' h h₀ smp)
        (t, FirstHurewicz.simplexFace (n + 1) i s) =
      _
  rw [extendBoundaryHomotopy_face]
  exact coherentFaceBoundaryHomotopy_face H H' h smp i t s

def SecondHurewicz.SimplyConnected.triangleBoundary : Set (FirstHurewicz.Simplex 2) :=
  {s | ∃ i, s i = 0}

def SecondHurewicz.SimplyConnected.BasedTriangle {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 2, X) // ∀ s ∈ triangleBoundary, τ s = x }

def SecondHurewicz.SimplyConnected.triangleQuotient :
    C((unitInterval) × (unitInterval), FirstHurewicz.Simplex 2)
    where
  toFun
    z :=
    ⟨![1 - (z.1 : ℝ), (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ), Min.min (z.1 : ℝ) (z.2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr z.1.property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min z.1.property.1 z.2.property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleQuotient_zero
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 0 = 1 - (z.1 : ℝ) :=
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleQuotient_one
    (z : (unitInterval) × (unitInterval)) :
    triangleQuotient z 1 = (z.1 : ℝ) - Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleQuotient_two
    (z : (unitInterval) × (unitInterval)) : triangleQuotient z 2 = Min.min (z.1 : ℝ) (z.2 : ℝ) :=
  rfl

def SecondHurewicz.SimplyConnected.triangleCubeQuotient :
    C(Fin 2 → (unitInterval), FirstHurewicz.Simplex 2) :=
  triangleQuotient.comp ⟨fun t => (t 0, t 1), by fun_prop⟩

theorem SecondHurewicz.SimplyConnected.triangleCubeQuotient_boundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : triangleCubeQuotient t ∈ triangleBoundary := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · refine ⟨2, ?_⟩
      change t 0 = 0 at hi
      change Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 1).property.1]
    · refine ⟨2, ?_⟩
      change t 1 = 0 at hi
      change Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_right (t 0).property.1]
  · fin_cases i
    · refine ⟨0, ?_⟩
      change t 0 = 1 at hi
      change 1 - (t 0 : ℝ) = 0
      simp [hi]
    · refine ⟨1, ?_⟩
      change t 1 = 1 at hi
      change (t 0 : ℝ) - Min.min (t 0 : ℝ) (t 1 : ℝ) = 0
      simp [hi, min_eq_left (t 0).property.2]

def SecondHurewicz.SimplyConnected.basedTriangleLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp triangleCubeQuotient, fun t ht => τ.property _ (triangleCubeQuotient_boundary t ht)⟩

theorem SecondHurewicz.SimplyConnected.squareMap_basedTriangleLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.squareMap (basedTriangleLoop τ) = τ.val.comp triangleQuotient := by
  ext z
  change
    τ.val
        (triangleQuotient
          (SecondHurewicz.squareCoordinates z 0, SecondHurewicz.squareCoordinates z 1)) =
      _
  rw [SecondHurewicz.squareCoordinates_zero, SecondHurewicz.squareCoordinates_one]
  rfl

def SecondHurewicz.SimplyConnected.basedTriangleClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : Additive (π_ 2 X x) :=
  Additive.ofMul (⟦basedTriangleLoop τ⟧ : π_ 2 X x)

def SecondHurewicz.SimplyConnected.constantBasedTriangle {X : Type} [TopologicalSpace X] (x : X) :
    BasedTriangle x :=
  ⟨ContinuousMap.const (FirstHurewicz.Simplex 2) x, fun _ _ => rfl⟩

def SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) : C((unitInterval) × FirstHurewicz.Simplex 2, X) :=
  extendCoherentSimplexHomotopy (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x) smp

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (s : FirstHurewicz.Simplex 2) :
    triangleEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 1 (edgeStraighteningHomotopy x)
      (triangleEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (stationarySimplexHomotopy 0) (edgeStraighteningHomotopy x)
    (edgeStraighteningHomotopy_face x) (edgeStraighteningHomotopy_zero x)

def SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) : C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  extendCoherentSimplexHomotopy (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x) smp

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) (s : FirstHurewicz.Simplex 3) :
    tetrahedronEdgeStraighteningHomotopy x smp (0, s) = smp s :=
  extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FaceCompatibleHomotopies 2 (triangleEdgeStraighteningHomotopy x)
      (tetrahedronEdgeStraighteningHomotopy x) :=
  extendCoherentSimplexHomotopy_face (edgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy_face x)
    (triangleEdgeStraighteningHomotopy_zero x)

theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_one_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (h : VerticesBased x 2 smp) (i : Fin 3) :
    (timeSlice (triangleEdgeStraighteningHomotopy x smp) 1).comp (FirstHurewicz.simplexFace 1 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 1) x := by
  rw [timeSlice_face (triangleEdgeStraighteningHomotopy_face x)]
  ext s
  exact
    edgeStraighteningHomotopy_one x (smp.comp (FirstHurewicz.simplexFace 1 i)) (h.face i 0)
      (h.face i 1) s

theorem SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_one_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (h : VerticesBased x 2 smp)
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ triangleBoundary) :
    timeSlice (triangleEdgeStraighteningHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face 1 (⟨s, hs⟩ : SimplexBoundary 2)
  have he : FirstHurewicz.simplexFace 1 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(FirstHurewicz.Simplex 1, X) => f t)
      (triangleEdgeStraighteningHomotopy_one_face x smp h i)

def SecondHurewicz.SimplyConnected.edgeStraightenedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2)
    (h : VerticesBased x 2 smp) : BasedTriangle x :=
  ⟨timeSlice (triangleEdgeStraighteningHomotopy x smp) 1,
    triangleEdgeStraighteningHomotopy_one_boundary x smp h⟩

def SecondHurewicz.SimplyConnected.vertexNormalizedSimplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (n : ℕ) (smp : FirstHurewicz.SingularSimplex X n) :
    FirstHurewicz.SingularSimplex X n :=
  timeSlice (vertexStraighteningHomotopy x n smp) 1

theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : FirstHurewicz.SingularSimplex X n) :
    VerticesBased x n (vertexNormalizedSimplex x n smp) :=
  vertexStraighteningHomotopy_one_verticesBased x n smp

theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (vertexNormalizedSimplex x (n + 1) smp).comp (FirstHurewicz.simplexFace n i) =
      vertexNormalizedSimplex x n (smp.comp (FirstHurewicz.simplexFace n i)) :=
  vertexStraighteningHomotopy_timeSlice_face x n smp i 1

theorem SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (n : ℕ)
    (smp : FirstHurewicz.SingularSimplex X n) (h : VerticesBased x n smp) :
    vertexNormalizedSimplex x n smp = smp :=
  vertexStraighteningHomotopy_timeSlice_of_verticesBased x n smp h 1

def SecondHurewicz.SimplyConnected.normalizedTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2) :
    BasedTriangle x :=
  edgeStraightenedTriangle x (vertexNormalizedSimplex x 2 smp)
    (vertexNormalizedSimplex_verticesBased x 2 smp)

theorem SecondHurewicz.SimplyConnected.normalizedTriangle_of_verticesBased {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) (h : VerticesBased x 2 smp) :
    normalizedTriangle x smp = edgeStraightenedTriangle x smp h := by
  apply Subtype.ext
  change
    timeSlice (triangleEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 2 smp)) 1 =
      timeSlice (triangleEdgeStraighteningHomotopy x smp) 1
  rw [vertexNormalizedSimplex_of_verticesBased x 2 smp h]

def SecondHurewicz.SimplyConnected.normalizedTetrahedronMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) :
    FirstHurewicz.SingularSimplex X 3 :=
  timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1

theorem SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) (i : Fin 4) :
    (normalizedTetrahedronMap x smp).comp (FirstHurewicz.simplexFace 2 i) =
      (normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i))).val := by
  change
    (timeSlice (tetrahedronEdgeStraighteningHomotopy x (vertexNormalizedSimplex x 3 smp)) 1).comp
        (FirstHurewicz.simplexFace 2 i) =
      _
  rw [timeSlice_face (tetrahedronEdgeStraighteningHomotopy_face x), vertexNormalizedSimplex_face]
  rfl

theorem SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) (i : Fin 4) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) :
    normalizedTetrahedronMap x smp (FirstHurewicz.simplexFace 2 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 2, X) => f s)
      (normalizedTetrahedronMap_face x smp i)
  exact hf.trans ((normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i))).property s hs)

def SecondHurewicz.SimplyConnected.normalizedTwoChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : FirstHurewicz.Chains X 2 →ₗ[ℤ] FirstHurewicz.Chains X 2 :=
  FirstHurewicz.chainLift X 2 fun smp =>
    FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTwoChain_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2) :
    normalizedTwoChain x (FirstHurewicz.simplexChain X 2 smp) =
      FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val :=
  FirstHurewicz.chainLift_simplex X 2 _ smp

theorem SecondHurewicz.SimplyConnected.normalizedTwoChain_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    normalizedTwoChain x =
      (simplexEndpointOperator 2 (triangleEdgeStraighteningHomotopy x) 1).comp
        (simplexEndpointOperator 2 (vertexStraighteningHomotopy x 2) 1) := by
  apply FirstHurewicz.chainMap_ext X 2
  intro smp
  simp only [normalizedTwoChain_simplex, LinearMap.comp_apply, simplexEndpointOperator_simplex]
  rfl

def SecondHurewicz.SimplyConnected.vertexNormalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  straightenedTwoCycle (vertexStraighteningHomotopy x 1) (vertexStraighteningHomotopy x 2)
    (vertexStraighteningHomotopy_face x 1) c

theorem SecondHurewicz.SimplyConnected.vertexNormalizedTwoCycle_class {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (vertexNormalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c :=
  straightenedTwoCycle_class _ _ (vertexStraighteningHomotopy_face x 1)
    (vertexStraighteningHomotopy_timeSlice_zero x 2) c

def SecondHurewicz.SimplyConnected.normalizedTwoCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  straightenedTwoCycle (edgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy_face x) (vertexNormalizedTwoCycle x c)

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTwoCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    (normalizedTwoCycle x c).val = normalizedTwoChain x c.val := by
  rw [normalizedTwoChain_eq]
  rfl

theorem SecondHurewicz.SimplyConnected.normalizedTwoCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (normalizedTwoCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c := by
  have h₀ : ∀ smp, timeSlice (triangleEdgeStraighteningHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleEdgeStraighteningHomotopy_zero x smp s
  exact
    (straightenedTwoCycle_class _ _ (triangleEdgeStraighteningHomotopy_face x) h₀
          (vertexNormalizedTwoCycle x c)).trans
      (vertexNormalizedTwoCycle_class x c)

def SecondHurewicz.SimplyConnected.tetrahedronOneSkeleton : Set (FirstHurewicz.Simplex 3) :=
  {s | ∃ i j : Fin 4, i ≠ j ∧ s i = 0 ∧ s j = 0}

def SecondHurewicz.SimplyConnected.BasedTetrahedron {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 3, X) // ∀ s ∈ tetrahedronOneSkeleton, τ s = x }

theorem SecondHurewicz.SimplyConnected.simplexFace_triangleBoundary (i : Fin 4)
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ triangleBoundary) :
    FirstHurewicz.simplexFace 2 i s ∈ tetrahedronOneSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, FirstHurewicz.simplexFace_apply_self 2 i s,
      (FirstHurewicz.simplexFace_apply_succAbove 2 i s j).trans hj⟩

def SecondHurewicz.SimplyConnected.basedTetrahedronFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTetrahedron x) (i : Fin 4) : BasedTriangle x :=
  ⟨τ.val.comp (FirstHurewicz.simplexFace 2 i), fun s hs =>
    τ.property _ (simplexFace_triangleBoundary i s hs)⟩

def SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend {n : ℕ} (t : (unitInterval))
    (a b : FirstHurewicz.Simplex n) : FirstHurewicz.Simplex n :=
  ⟨(1 - (t : ℝ)) • (a : Fin (n + 1) → ℝ) + (t : ℝ) • (b : Fin (n + 1) → ℝ),
    convex_stdSimplex ℝ _ a.property b.property (sub_nonneg.mpr t.property.2) t.property.1
      (by ring)⟩

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero {n : ℕ}
    (a b : FirstHurewicz.Simplex n) : tetrahedronSimplexBlend 0 a b = a := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) * a i + (0 : ℝ) * b i = a i
  simp

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one {n : ℕ}
    (a b : FirstHurewicz.Simplex n) : tetrahedronSimplexBlend 1 a b = b := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) * a i + (1 : ℝ) * b i = b i
  simp

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_self {n : ℕ} (t : (unitInterval))
    (a : FirstHurewicz.Simplex n) : tetrahedronSimplexBlend t a a = a := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * a i + (t : ℝ) * a i = a i
  ring

def SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap {n : ℕ} {Y : Type}
    [TopologicalSpace Y] (f g : C(Y, FirstHurewicz.Simplex n)) :
    C((unitInterval) × Y, FirstHurewicz.Simplex n)
    where
  toFun p := tetrahedronSimplexBlend p.1 (f p.2) (g p.2)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change
      Continuous fun p : (unitInterval) × Y => (1 - (p.1 : ℝ)) * f p.2 i + (p.1 : ℝ) * g p.2 i
    have hf : Continuous fun p : (unitInterval) × Y => f p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (f.continuous.comp continuous_snd))
    have hg : Continuous fun p : (unitInterval) × Y => g p.2 i :=
      (continuous_apply i).comp (continuous_subtype_val.comp (g.continuous.comp continuous_snd))
    exact
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul hf).add
        ((continuous_subtype_val.comp continuous_fst).mul hg)

theorem SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate {n : ℕ}
    (t : (unitInterval)) (a b : FirstHurewicz.Simplex n) (i : Fin (n + 1)) (ha : a i = 0)
    (hb : b i = 0) : tetrahedronSimplexBlend t a b i = 0 := by
  change (1 - (t : ℝ)) * a i + (t : ℝ) * b i = 0
  simp [ha, hb]

theorem SecondHurewicz.SimplyConnected.simplexFace_two_zero (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 0 s : Fin 4 → ℝ) = ![0, s 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_self 2 0 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 0 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 0 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 0 s 2

theorem SecondHurewicz.SimplyConnected.simplexFace_two_one (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 1 s : Fin 4 → ℝ) = ![s 0, 0, s 1, s 2] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 0
  · exact FirstHurewicz.simplexFace_apply_self 2 1 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 2

theorem SecondHurewicz.SimplyConnected.simplexFace_two_two (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 2 s : Fin 4 → ℝ) = ![s 0, s 1, 0, s 2] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 2 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 2 s 1
  · exact FirstHurewicz.simplexFace_apply_self 2 2 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 2 s 2

theorem SecondHurewicz.SimplyConnected.simplexFace_two_three (s : FirstHurewicz.Simplex 2) :
    (FirstHurewicz.simplexFace 2 3 s : Fin 4 → ℝ) = ![s 0, s 1, s 2, 0] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 2
  · exact FirstHurewicz.simplexFace_apply_self 2 3 s

def SecondHurewicz.SimplyConnected.BasedTetrahedron.ofFaces {X : Type} [TopologicalSpace X]
    {x : X} (τ : C(FirstHurewicz.Simplex 3, X))
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (τ.comp (FirstHurewicz.simplexFace 2 i)) s = x) :
    SecondHurewicz.SimplyConnected.BasedTetrahedron x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 i ⟨s, hi⟩
    have ht : t ∈ SecondHurewicz.SimplyConnected.triangleBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (FirstHurewicz.simplexFace 2 i t) = x at he
    rw [show FirstHurewicz.simplexFace 2 i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse 2 i ⟨s, hi⟩] at he
    exact he⟩

def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA :
    C(Fin 2 → (unitInterval), FirstHurewicz.Simplex 3)
    where
  toFun
    u :=
    ⟨![1 - Max.max (u 0 : ℝ) (u 1 : ℝ), (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        Min.min (u 0 : ℝ) (u 1 : ℝ), (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (u 1).property.1
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
        · rw [min_eq_left h, max_eq_right h]
          ring
        · rw [min_eq_right h, max_eq_left h]
          ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_boundary
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u ∈ tetrahedronOneSkeleton := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, 2, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hi
      refine ⟨2, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 0).property.1]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, 3, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_right (u 1).property.2,
          max_eq_left (u 1).property.2]
    · change u 1 = 1 at hi
      refine ⟨0, 1, by decide, ?_, ?_⟩ <;>
        simp [DFunLike.coe, tetrahedronQuadrilateralA, hi, min_eq_left (u 0).property.2,
          max_eq_right (u 0).property.2]

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_diagonal (t : (unitInterval)) :
    tetrahedronQuadrilateralA ![t, t] ∈ tetrahedronOneSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩ <;> simp [DFunLike.coe, tetrahedronQuadrilateralA]

def SecondHurewicz.SimplyConnected.tetrahedronQuarterShift :
    C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 3, s 0, s 1, s 2], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val

def SecondHurewicz.SimplyConnected.tetrahedronQuarterIndex : Fin 4 ≃ Fin 4
    where
  toFun i := ![1, 2, 3, 0] i
  invFun i := ![3, 0, 1, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_index (s : FirstHurewicz.Simplex 3)
    (i : Fin 4) : tetrahedronQuarterShift s (tetrahedronQuarterIndex i) = s i := by
  fin_cases i <;> rfl

theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_oneSkeleton
    (s : FirstHurewicz.Simplex 3) (hs : s ∈ tetrahedronOneSkeleton) :
    tetrahedronQuarterShift s ∈ tetrahedronOneSkeleton := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact
    ⟨tetrahedronQuarterIndex i, tetrahedronQuarterIndex j, fun h =>
      hij (tetrahedronQuarterIndex.injective h), by simpa, by simpa⟩

def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralLoop {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp tetrahedronQuadrilateralA, fun u hu =>
    τ.property _ (tetrahedronQuadrilateralA_boundary u hu)⟩

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuadrilateralA_diagonal t)

def SecondHurewicz.SimplyConnected.tetrahedronShiftedQuadrilateralLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) : GenLoop (Fin 2) X x :=
  ⟨τ.val.comp (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA), fun u hu =>
    τ.property _
      (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_boundary u hu))⟩

theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedQuadrilateralLoop_diagonal {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) (t : (unitInterval)) :
    tetrahedronShiftedQuadrilateralLoop τ ![t, t] = x :=
  τ.property _ (tetrahedronQuarterShift_oneSkeleton _ (tetrahedronQuadrilateralA_diagonal t))

def SecondHurewicz.SimplyConnected.quarterTurn : C(Fin 2 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u 1, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem SecondHurewicz.SimplyConnected.quarterTurn_apply (u : Fin 2 → (unitInterval)) :
    quarterTurn u = ![u 1, (unitInterval.symm) (u 0)] :=
  rfl

theorem SecondHurewicz.SimplyConnected.quarterTurn_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : quarterTurn u ∈ Cube.boundary (Fin 2) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨1, Or.inr (by simp [hi])⟩
    · exact ⟨0, Or.inl (by simpa using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨1, Or.inl (by simp [hi])⟩
    · exact ⟨0, Or.inr (by simpa using hi)⟩

def SecondHurewicz.SimplyConnected.rotatedSquareLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp quarterTurn, fun u hu => p.property _ (quarterTurn_boundary u hu)⟩

def SecondHurewicz.SimplyConnected.rotationVector (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, -v.1)

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationVector_norm (v : ℝ × ℝ) :
    ‖rotationVector v‖ = ‖v‖ := by simp [rotationVector, Prod.norm_def, max_comm]

def SecondHurewicz.SimplyConnected.rotationBlend (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * v.1 + t * v.2, (1 - t) * v.2 - t * v.1)

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationBlend_zero (v : ℝ × ℝ) : rotationBlend 0 v = v := by
  ext <;> simp [rotationBlend]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationBlend_one (v : ℝ × ℝ) :
    rotationBlend 1 v = rotationVector v := by ext <;> simp [rotationBlend, rotationVector]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationBlend_zero_vector (t : ℝ) :
    rotationBlend t 0 = 0 := by ext <;> simp [rotationBlend]

theorem SecondHurewicz.SimplyConnected.rotationBlend_ne_zero (t : ℝ) {v : ℝ × ℝ} (hv : v ≠ 0) :
    rotationBlend t v ≠ 0 := by
  intro h
  have h₁ : (1 - t) * v.1 + t * v.2 = 0 := congrArg Prod.fst h
  have h₂ : (1 - t) * v.2 - t * v.1 = 0 := congrArg Prod.snd h
  have hd : (1 - t) ^ 2 + t ^ 2 ≠ 0 := by
    have hp : 0 < (1 - t) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
    exact ne_of_gt hp
  have ha : ((1 - t) ^ 2 + t ^ 2) * v.1 = 0 := by linear_combination (1 - t) * h₁ - t * h₂
  have hb : ((1 - t) ^ 2 + t ^ 2) * v.2 = 0 := by linear_combination t * h₁ + (1 - t) * h₂
  apply hv
  exact Prod.ext (mul_eq_zero.mp ha |>.resolve_left hd) (mul_eq_zero.mp hb |>.resolve_left hd)

theorem SecondHurewicz.SimplyConnected.rotationBlend_continuous :
    Continuous (fun z : ℝ × (ℝ × ℝ) => rotationBlend z.1 z.2) := by
  unfold rotationBlend
  fun_prop

def SecondHurewicz.SimplyConnected.rotationCentered (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (2 * (u 0 : ℝ) - 1, 2 * (u 1 : ℝ) - 1)

theorem SecondHurewicz.SimplyConnected.rotationCentered_continuous :
    Continuous rotationCentered := by
  unfold rotationCentered
  fun_prop

theorem SecondHurewicz.SimplyConnected.rotationCentered_norm_le (u : Fin 2 → (unitInterval)) :
    ‖rotationCentered u‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  constructor <;> rw [Real.norm_eq_abs, abs_le]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 0).property.1, (u 0).property.2]
  · constructor <;> dsimp [rotationCentered] <;> linarith [(u 1).property.1, (u 1).property.2]

theorem SecondHurewicz.SimplyConnected.rotationCentered_norm_boundary (u : Fin 2 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 2)) : ‖rotationCentered u‖ = 1 := by
  apply le_antisymm (rotationCentered_norm_le u)
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 0 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)
  · fin_cases i
    · change u 0 = 1 at hi
      have hc : ‖(rotationCentered u).1‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_fst_le (rotationCentered u)
    · change u 1 = 1 at hi
      have hc : ‖(rotationCentered u).2‖ = 1 := by norm_num [rotationCentered, hi]
      exact hc ▸ norm_snd_le (rotationCentered u)

def SecondHurewicz.SimplyConnected.rotationDenominator (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ :=
  1 - ‖rotationCentered u‖ + ‖rotationBlend t (rotationCentered u)‖

theorem SecondHurewicz.SimplyConnected.rotationDenominator_pos (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : 0 < rotationDenominator t u := by
  by_cases hv : rotationCentered u = 0
  · simp [rotationDenominator, hv]
  · have hnorm : 0 < ‖rotationBlend t (rotationCentered u)‖ :=
      norm_pos_iff.mpr (rotationBlend_ne_zero t hv)
    have hle := rotationCentered_norm_le u
    unfold rotationDenominator
    linarith

theorem SecondHurewicz.SimplyConnected.rotationDenominator_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationDenominator z.1 z.2) := by
  unfold rotationDenominator
  apply Continuous.add
  · exact continuous_const.sub (rotationCentered_continuous.comp continuous_snd).norm
  · apply Continuous.norm
    exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

def SecondHurewicz.SimplyConnected.rotationNormalized (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ℝ × ℝ :=
  (rotationDenominator t u)⁻¹ • rotationBlend t (rotationCentered u)

theorem SecondHurewicz.SimplyConnected.rotationNormalized_continuous :
    Continuous
      (fun z : (unitInterval) × (Fin 2 → (unitInterval)) => rotationNormalized z.1 z.2) := by
  unfold rotationNormalized
  apply
    Continuous.smul (f := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      (rotationDenominator z.1 z.2)⁻¹) (g := fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
      rotationBlend z.1 (rotationCentered z.2))
  · exact
      rotationDenominator_continuous.inv₀ (fun z => ne_of_gt (rotationDenominator_pos z.1 z.2))
  · exact
      rotationBlend_continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (rotationCentered_continuous.comp continuous_snd))

theorem SecondHurewicz.SimplyConnected.rotationNormalized_norm_le (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) : ‖rotationNormalized t u‖ ≤ 1 := by
  have hd := rotationDenominator_pos t u
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [inv_mul_le_iff₀ hd, mul_one]
  unfold rotationDenominator
  linarith [rotationCentered_norm_le u]

theorem SecondHurewicz.SimplyConnected.rotationNormalized_norm_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ‖rotationNormalized t u‖ = 1 := by
  have hd := rotationDenominator_pos t u
  have he : rotationDenominator t u = ‖rotationBlend t (rotationCentered u)‖ := by
    simp [rotationDenominator, rotationCentered_norm_boundary u hu]
  rw [rotationNormalized, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
  rw [← he, inv_mul_cancel₀ (ne_of_gt hd)]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationNormalized_zero (u : Fin 2 → (unitInterval)) :
    rotationNormalized 0 u = rotationCentered u := by
  simp [rotationNormalized, rotationDenominator]

@[simp]
theorem SecondHurewicz.SimplyConnected.rotationNormalized_one (u : Fin 2 → (unitInterval)) :
    rotationNormalized 1 u = rotationVector (rotationCentered u) := by
  simp [rotationNormalized, rotationDenominator]

def SecondHurewicz.SimplyConnected.rotationUncenter (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) :
    Fin 2 → (unitInterval) :=
  ![⟨(v.1 + 1) / 2,
      by
      have h := abs_le.mp (show |v.1| ≤ 1 from (norm_fst_le v).trans hv)
      constructor <;> linarith⟩,
    ⟨(v.2 + 1) / 2,
      by
      have h := abs_le.mp (show |v.2| ≤ 1 from (norm_snd_le v).trans hv)
      constructor <;> linarith⟩]

theorem SecondHurewicz.SimplyConnected.rotationUncenter_congr {v w : ℝ × ℝ} {hv : ‖v‖ ≤ 1}
    {hw : ‖w‖ ≤ 1} (h : v = w) : rotationUncenter v hv = rotationUncenter w hw := by
  subst w
  rfl

theorem SecondHurewicz.SimplyConnected.rotationUncenter_centered (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationCentered u) (rotationCentered_norm_le u) = u := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> dsimp [rotationUncenter, rotationCentered] <;> ring

theorem SecondHurewicz.SimplyConnected.rotationUncenter_vector (u : Fin 2 → (unitInterval)) :
    rotationUncenter (rotationVector (rotationCentered u))
        (by simpa using rotationCentered_norm_le u) =
      quarterTurn u := by
  rw [quarterTurn_apply]
  funext i
  fin_cases i <;> apply Subtype.ext <;>
      dsimp [rotationUncenter, rotationVector, rotationCentered, unitInterval.symm] <;>
    ring

theorem SecondHurewicz.SimplyConnected.rotationUncenter_boundary (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1)
    (he : ‖v‖ = 1) : rotationUncenter v hv ∈ Cube.boundary (Fin 2) := by
  have hm : 1 ≤ Max.max |v.1| |v.2| := by simpa [Prod.norm_def, Real.norm_eq_abs] using he.ge
  rcases le_max_iff.mp hm with ha | hb
  · have hn : |v.1| = 1 := le_antisymm ((norm_fst_le v).trans hv) ha
    by_cases hp : 0 ≤ v.1
    · have h : v.1 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨0, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.1 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨0, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
  · have hn : |v.2| = 1 := le_antisymm ((norm_snd_le v).trans hv) hb
    by_cases hp : 0 ≤ v.2
    · have h : v.2 = 1 := by simpa [abs_of_nonneg hp] using hn
      refine ⟨1, Or.inr ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith
    · have h : v.2 = -1 := by
        rw [abs_of_neg (lt_of_not_ge hp)] at hn
        linarith
      refine ⟨1, Or.inl ?_⟩
      apply Subtype.ext
      dsimp [rotationUncenter]
      linarith

def SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap :
    C((unitInterval) × (Fin 2 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun z := rotationUncenter (rotationNormalized z.1 z.2) (rotationNormalized_norm_le z.1 z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).1 + 1) / 2)
      exact (rotationNormalized_continuous.fst.add continuous_const).div_const 2
    · apply Continuous.subtype_mk
      change
        Continuous
          (fun z : (unitInterval) × (Fin 2 → (unitInterval)) =>
            ((rotationNormalized z.1 z.2).2 + 1) / 2)
      exact (rotationNormalized_continuous.snd.add continuous_const).div_const 2

@[simp]
theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (0, u) = u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 0 u)
          (rotationNormalized_zero u)).trans
      (rotationUncenter_centered u)

@[simp]
theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_one (u : Fin 2 → (unitInterval)) :
    quarterTurnHomotopyMap (1, u) = quarterTurn u := by
  exact
    (rotationUncenter_congr (hv := rotationNormalized_norm_le 1 u)
          (rotationNormalized_one u)).trans
      (rotationUncenter_vector u)

theorem SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    quarterTurnHomotopyMap (t, u) ∈ Cube.boundary (Fin 2) :=
  rotationUncenter_boundary (rotationNormalized t u) (rotationNormalized_norm_le t u)
    (rotationNormalized_norm_boundary t u hu)

def SecondHurewicz.SimplyConnected.rotatedSquareLoop_homotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (rotatedSquareLoop p).val (Cube.boundary (Fin 2))
    where
  toFun z := p (quarterTurnHomotopyMap z)
  continuous_toFun := p.val.continuous.comp quarterTurnHomotopyMap.continuous
  map_zero_left u := congrArg p (quarterTurnHomotopyMap_zero u)
  map_one_left u := congrArg p (quarterTurnHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (quarterTurnHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

theorem SecondHurewicz.SimplyConnected.rotatedSquareLoop_class {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) : (⟦rotatedSquareLoop p⟧ : π_ 2 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 2 X x) = ⟦rotatedSquareLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (rotatedSquareLoop p) from ⟨rotatedSquareLoop_homotopy p⟩)
  exact h.symm

def SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralB :
    C(Fin 2 → (unitInterval), FirstHurewicz.Simplex 3) :=
  (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA).comp quarterTurn

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateral_perimeter
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u = tetrahedronQuadrilateralB u := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuarterShift_zero (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 0 = s 3 := rfl
  have tetrahedronQuarterShift_one (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 1 = s 0 := rfl
  have tetrahedronQuarterShift_two (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 2 = s 1 := rfl
  have tetrahedronQuarterShift_three (s : FirstHurewicz.Simplex 3) :
    tetrahedronQuarterShift s 3 = s 2 := rfl
  have tetrahedronQuadrilateralB_apply (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralB u =
      tetrahedronQuarterShift (tetrahedronQuadrilateralA ![u 1, (unitInterval.symm) (u 0)]) :=
    rfl
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA u j = tetrahedronQuadrilateralB u j
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 1).property.2, max_eq_right (u 1).property.2,
          min_eq_left (u 1).property.1, max_eq_right (u 1).property.1]
    · change u 1 = 0 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 0).property.1, max_eq_left (u 0).property.1, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_right (u 1).property.2, max_eq_left (u 1).property.2,
          min_eq_right (u 1).property.1, max_eq_left (u 1).property.1]
    · change u 1 = 1 at hi
      fin_cases j <;>
        simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
          tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three,
          tetrahedronQuarterShift_zero, tetrahedronQuarterShift_one, tetrahedronQuarterShift_two,
          tetrahedronQuarterShift_three, tetrahedronQuadrilateralB_apply, hi,
          min_eq_left (u 0).property.2, max_eq_right (u 0).property.2, (u 0).property.1]

def SecondHurewicz.SimplyConnected.tetrahedronFillingsHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (tetrahedronQuadrilateralLoop τ).val.HomotopyRel
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (tetrahedronQuadrilateralA p.2)
        (tetrahedronQuadrilateralB p.2))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap tetrahedronQuadrilateralA tetrahedronQuadrilateralB).continuous
  map_zero_left
    u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (tetrahedronQuadrilateralB u)
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu := by
    change τ.val (tetrahedronSimplexBlend t _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [← tetrahedronQuadrilateral_perimeter u hu, tetrahedronSimplexBlend_self]

theorem SecondHurewicz.SimplyConnected.tetrahedronFillings_homotopic {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    GenLoop.Homotopic (tetrahedronQuadrilateralLoop τ)
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)) :=
  ⟨tetrahedronFillingsHomotopy τ⟩

theorem SecondHurewicz.SimplyConnected.tetrahedronFillings_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTetrahedron x) :
    (⟦tetrahedronQuadrilateralLoop τ⟧ : π_ 2 X x) = ⟦tetrahedronShiftedQuadrilateralLoop τ⟧ :=
  (Quotient.sound (tetrahedronFillings_homotopic τ)).trans
    (rotatedSquareLoop_class (tetrahedronShiftedQuadrilateralLoop τ))

def SecondHurewicz.SimplyConnected.triangleCyclicPermutation :
    C(FirstHurewicz.Simplex 2, FirstHurewicz.Simplex 2)
    where
  toFun
    s :=
    ⟨![s 1, s 2, s 0], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + s 2) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

theorem SecondHurewicz.SimplyConnected.triangleCyclicPermutation_boundary
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ triangleBoundary) :
    triangleCyclicPermutation s ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨2, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩

def SecondHurewicz.SimplyConnected.cyclicBasedTriangle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) : BasedTriangle x :=
  ⟨τ.val.comp triangleCyclicPermutation, fun s hs =>
    τ.property _ (triangleCyclicPermutation_boundary s hs)⟩

theorem SecondHurewicz.SimplyConnected.cyclicTriangleQuotient_commonZero
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3,
      triangleCyclicPermutation (triangleCubeQuotient u) i = 0 ∧
        triangleCubeQuotient (quarterTurn u) i = 0 := by
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have triangleCyclicPermutation_zero (s : FirstHurewicz.Simplex 2) :
    triangleCyclicPermutation s 0 = s 1 := rfl
  have triangleCyclicPermutation_one (s : FirstHurewicz.Simplex 2) :
    triangleCyclicPermutation s 1 = s 2 := rfl
  have triangleCyclicPermutation_two (s : FirstHurewicz.Simplex 2) :
    triangleCyclicPermutation s 2 = s 0 := rfl
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_left (u 1).property.1, min_eq_left (u 1).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩
      · simp [triangleCubeQuotient_apply, triangleCyclicPermutation_one, hi,
          min_eq_right (u 0).property.1]
      · simp [triangleCubeQuotient_apply, hi, (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_two, hi,
          min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [triangleCubeQuotient_apply, triangleCyclicPermutation_zero, hi,
          min_eq_left (u 0).property.2]

theorem SecondHurewicz.SimplyConnected.cyclicTriangleQuotient_blend_boundary (t : (unitInterval))
    (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronSimplexBlend t (triangleCyclicPermutation (triangleCubeQuotient u))
        (triangleCubeQuotient (quarterTurn u)) ∈
      triangleBoundary := by
  obtain ⟨i, hi, hj⟩ := cyclicTriangleQuotient_commonZero u hu
  exact ⟨i, tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

def SecondHurewicz.SimplyConnected.cyclicTriangleLoopHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop (cyclicBasedTriangle τ)).val.HomotopyRel
      (rotatedSquareLoop (basedTriangleLoop τ)).val (Cube.boundary (Fin 2))
    where
  toFun
    p :=
    τ.val
      (tetrahedronSimplexBlend p.1 (triangleCyclicPermutation (triangleCubeQuotient p.2))
        (triangleCubeQuotient (quarterTurn p.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (tetrahedronSimplexBlendMap (triangleCyclicPermutation.comp triangleCubeQuotient)
          (triangleCubeQuotient.comp quarterTurn)).continuous
  map_zero_left
    u := by
    change
      τ.val (tetrahedronSimplexBlend 0 _ _) =
        τ.val (triangleCyclicPermutation (triangleCubeQuotient u))
    rw [tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (triangleCubeQuotient (quarterTurn u))
    rw [tetrahedronSimplexBlend_one]
  prop' t u
    hu :=
    (τ.property _ (cyclicTriangleQuotient_blend_boundary t u hu)).trans
      ((basedTriangleLoop (cyclicBasedTriangle τ)).property u hu).symm

@[simp]
theorem SecondHurewicz.SimplyConnected.basedTriangleClass_cyclic {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    basedTriangleClass (cyclicBasedTriangle τ) = basedTriangleClass τ := by
  have h :
    GenLoop.Homotopic (basedTriangleLoop (cyclicBasedTriangle τ))
      (rotatedSquareLoop (basedTriangleLoop τ)) :=
    ⟨cyclicTriangleLoopHomotopy τ⟩
  have he :
    (⟦basedTriangleLoop (cyclicBasedTriangle τ)⟧ : π_ 2 X x) =
      ⟦rotatedSquareLoop (basedTriangleLoop τ)⟧ :=
    Quotient.sound h
  exact congrArg Additive.ofMul (he.trans (rotatedSquareLoop_class (basedTriangleLoop τ)))

abbrev SecondHurewicz.SimplyConnected.SubdivisionSquare :=
  Fin 2 → (unitInterval)

theorem SecondHurewicz.SimplyConnected.subdivisionSquare_boundary_cases (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : u 0 = 0 ∨ u 0 = 1 ∨ u 1 = 0 ∨ u 1 = 1 := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

inductive SecondHurewicz.SimplyConnected.SubdivisionSameSide (a b : SubdivisionSquare) : Prop
  | zero (i : Fin 2) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 2) (ha : a i = 1) (hb : b i = 1)
  | diagonal (ha : a 0 = a 1) (hb : b 0 = b 1)

def SecondHurewicz.SimplyConnected.subdivisionBlend (t : (unitInterval))
    (a b : SubdivisionSquare) : SubdivisionSquare := fun i => Set.Icc.convexComb (a i) (b i) t

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionBlend_zero (a b : SubdivisionSquare) :
    subdivisionBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionBlend_one (a b : SubdivisionSquare) :
    subdivisionBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def SecondHurewicz.SimplyConnected.subdivisionBlendMap
    (f g : C(SubdivisionSquare, SubdivisionSquare)) :
    C((unitInterval) × SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := subdivisionBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

theorem SecondHurewicz.SimplyConnected.subdivisionOnDiagonal {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (a : SubdivisionSquare) (ha : a 0 = a 1) : p a = x := by
  have h : a = ![a 0, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact ha.symm
  exact (congrArg p h).trans (hd _)

theorem SecondHurewicz.SimplyConnected.subdivisionBlend_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    {a b : SubdivisionSquare} (h : SubdivisionSameSide a b) (t : (unitInterval)) :
    p (subdivisionBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
    apply p.property
    exact ⟨i, Or.inl (by simp [subdivisionBlend, ha, hb])⟩
  | one i ha hb =>
    apply p.property
    exact ⟨i, Or.inr (by simp [subdivisionBlend, ha, hb])⟩
  | diagonal ha hb =>
    apply subdivisionOnDiagonal p hd
    simp only [subdivisionBlend, ha, hb]

def SecondHurewicz.SimplyConnected.subdivisionPullbackLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp f, hf⟩

def SecondHurewicz.SimplyConnected.subdivisionLinearHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x)
    (f g : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 2), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 2), SubdivisionSameSide (f u) (g u)) :
    (subdivisionPullbackLoop p f hf).val.HomotopyRel (subdivisionPullbackLoop p g hg).val
      (Cube.boundary (Fin 2))
    where
  toFun u := p (subdivisionBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (subdivisionBlendMap f g).continuous
  map_zero_left
    u := by
    change p (subdivisionBlend 0 (f u) (g u)) = p (f u)
    rw [subdivisionBlend_zero]
  map_one_left
    u := by
    change p (subdivisionBlend 1 (f u) (g u)) = p (g u)
    rw [subdivisionBlend_one]
  prop' t u hu := (subdivisionBlend_based p hd (hfg u hu) t).trans (hf u hu).symm

def SecondHurewicz.SimplyConnected.subdivisionSubMin (u v : (unitInterval)) : (unitInterval) :=
  ⟨(u : ℝ) - Min.min (u : ℝ) (v : ℝ), sub_nonneg.mpr (min_le_left _ _),
    (sub_le_self _ (le_min u.property.1 v.property.1)).trans u.property.2⟩

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_zero_left (v : (unitInterval)) :
    subdivisionSubMin 0 v = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.1]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_zero_right (u : (unitInterval)) :
    subdivisionSubMin u 0 = u := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.1]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_one_left (v : (unitInterval)) :
    subdivisionSubMin 1 v = (unitInterval.symm) v := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.2]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionSubMin_one_right (u : (unitInterval)) :
    subdivisionSubMin u 1 = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.2]

def SecondHurewicz.SimplyConnected.subdivisionLowerProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, u 0 * u 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => u 0 * u 1
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp (continuous_apply 0)).mul
          (continuous_subtype_val.comp (continuous_apply 1))

def SecondHurewicz.SimplyConnected.subdivisionUpperProductMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

def SecondHurewicz.SimplyConnected.subdivisionUpperConeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0 * (unitInterval.symm) (u 1), Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => u 0 * (unitInterval.symm) (u 1)
      apply Continuous.subtype_mk
      change Continuous fun u : SubdivisionSquare => (u 0 : ℝ) * (1 - (u 1 : ℝ))
      fun_prop
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, Min.min (u 0) (u 1)]
  continuous_toFun := by fun_prop

def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![subdivisionSubMin (u 0) (u 1), u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => subdivisionSubMin (u 0) (u 1)
      unfold subdivisionSubMin
      fun_prop
    · exact continuous_apply 0

theorem SecondHurewicz.SimplyConnected.subdivisionLowerProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionLowerProductMap, h])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperProductMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionUpperProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperProductMap, h])
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperProductMap, h])⟩

theorem SecondHurewicz.SimplyConnected.subdivisionUpperConeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperConeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperConeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperConeMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩

theorem SecondHurewicz.SimplyConnected.subdivisionLowerTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperTriangleMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperTriangleMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩

def SecondHurewicz.SimplyConnected.subdivisionLowerProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerProductMap (subdivisionLowerProductMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperProductLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperProductMap (subdivisionUpperProductMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperConeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperConeMap (subdivisionUpperConeMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerTriangleMap (subdivisionLowerTriangleMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperTriangleMap (subdivisionUpperTriangleMap_based p hd)

theorem SecondHurewicz.SimplyConnected.subdivisionLowerProductTriangle_sides
    (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionLowerProductMap u) (subdivisionLowerTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .one 0 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .zero 1 (by simp [subdivisionLowerProductMap, h]) (by simp [subdivisionLowerTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionLowerProductMap, h])
        (by
          simp [subdivisionLowerTriangleMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperProductCone_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperProductMap u) (subdivisionUpperConeMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])
  · exact .one 1 (by simp [subdivisionUpperProductMap, h]) (by simp [subdivisionUpperConeMap, h])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperConeTriangle_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperConeMap u) (subdivisionUpperTriangleMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact .one 1 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])
  · exact
      .zero 0 (by simp [subdivisionUpperConeMap, h]) (by simp [subdivisionUpperTriangleMap, h])

def SecondHurewicz.SimplyConnected.subdivisionLowerTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionLowerProductLoop p hd).val.HomotopyRel (subdivisionLowerTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionLowerProductMap_based p hd)
    (subdivisionLowerTriangleMap_based p hd) subdivisionLowerProductTriangle_sides

def SecondHurewicz.SimplyConnected.subdivisionUpperConeHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperProductLoop p hd).val.HomotopyRel (subdivisionUpperConeLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperProductMap_based p hd)
    (subdivisionUpperConeMap_based p hd) subdivisionUpperProductCone_sides

def SecondHurewicz.SimplyConnected.subdivisionUpperTriangleHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperConeLoop p hd).val.HomotopyRel (subdivisionUpperTriangleLoop p hd).val
      (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperConeMap_based p hd)
    (subdivisionUpperTriangleMap_based p hd) subdivisionUpperConeTriangle_sides

theorem SecondHurewicz.SimplyConnected.subdivision_toLoop_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin 2) (a b : GenLoop (Fin 2) X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

theorem SecondHurewicz.SimplyConnected.subdivision_transAt_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin 2) {a b c d : GenLoop (Fin 2) X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [subdivision_toLoop_transAt, subdivision_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

noncomputable def SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate :
    C((unitInterval) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ))) p.1
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_apply (u v : (unitInterval)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1))
        (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ))) u :=
  rfl

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_zero (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 0) = 0 := by
  simp [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_one (u : (unitInterval)) :
    subdivisionWarpCoordinate (u, 1) = 1 := by
  norm_num [subdivisionWarpCoordinate, Set.projIcc, Set.Icc.convexComb]

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_le_half (u v : (unitInterval))
    (hv : (v : ℝ) ≤ 1 / 2) :
    subdivisionWarpCoordinate (u, v) = u * Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) := by
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hzero]
  apply Subtype.ext
  simp

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_le (u v : (unitInterval))
    (hv : 1 / 2 ≤ (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (2 * (v : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpCoordinate_apply, hone]
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  change (1 - (u : ℝ)) * _ + (u : ℝ) * 1 = (1 - _) * (u : ℝ) + _ * 1
  ring

theorem SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (u v : (unitInterval))
    (hv : 1 / 2 < (v : ℝ)) :
    subdivisionWarpCoordinate (u, v) =
      Set.Icc.convexComb u 1 (Set.projIcc 0 1 zero_le_one (2 * (v : ℝ) - 1)) :=
  subdivisionWarpCoordinate_of_half_le u v hv.le

def SecondHurewicz.SimplyConnected.subdivisionWarpMap : C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![u 0, subdivisionWarpCoordinate (u 0, u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => subdivisionWarpCoordinate (u 0, u 1)
      exact
        subdivisionWarpCoordinate.continuous.comp
          (show Continuous (fun u : SubdivisionSquare => (u 0, u 1)) from
            (continuous_apply 0).prodMk (continuous_apply 1))

theorem SecondHurewicz.SimplyConnected.subdivisionWarpMap_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : SubdivisionSameSide u (subdivisionWarpMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 0 h (by simp [subdivisionWarpMap, h])
  · exact .one 0 h (by simp [subdivisionWarpMap, h])
  · exact .zero 1 h (by simp [subdivisionWarpMap, h])
  · exact .one 1 h (by simp [subdivisionWarpMap, h])

theorem SecondHurewicz.SimplyConnected.subdivisionWarpMap_based {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (u : SubdivisionSquare) (hu : u ∈ Cube.boundary (Fin 2)) :
    p (subdivisionWarpMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionWarpMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionWarpMap, h])⟩

def SecondHurewicz.SimplyConnected.subdivisionWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionWarpMap (subdivisionWarpMap_based p)

def SecondHurewicz.SimplyConnected.subdivisionWarpHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    p.val.HomotopyRel (subdivisionWarpLoop p).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd (ContinuousMap.id _) subdivisionWarpMap p.property
    (subdivisionWarpMap_based p) subdivisionWarpMap_sides

theorem SecondHurewicz.SimplyConnected.subdivisionWarpLoop_eq_transAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionWarpLoop p =
      GenLoop.transAt (1 : Fin 2) (subdivisionLowerProductLoop p hd)
        (subdivisionUpperProductLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![u 0, subdivisionWarpCoordinate (u 0, u 1)] =
      if (u 1 : ℝ) ≤ 1 / 2 then
        subdivisionLowerProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ))))
      else
        subdivisionUpperProductLoop p hd
          (Function.update u 1 (Set.projIcc 0 1 zero_le_one (2 * (u 1 : ℝ) - 1)))
  split_ifs with h
  · simpa [subdivisionLowerProductLoop, subdivisionPullbackLoop, subdivisionLowerProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_le_half (u 0) (u 1) h)
  · simpa [subdivisionUpperProductLoop, subdivisionPullbackLoop, subdivisionUpperProductMap] using
      congrArg (fun v : (unitInterval) => p ![u 0, v])
        (subdivisionWarpCoordinate_of_half_lt (u 0) (u 1) (lt_of_not_ge h))

theorem SecondHurewicz.SimplyConnected.subdivision_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic p
      (GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
        (subdivisionUpperTriangleLoop p hd)) := by
  have hw : GenLoop.Homotopic p (subdivisionWarpLoop p) := ⟨subdivisionWarpHomotopy p hd⟩
  rw [subdivisionWarpLoop_eq_transAt p hd] at hw
  apply hw.trans
  apply subdivision_transAt_homotopic
  · exact ⟨subdivisionLowerTriangleHomotopy p hd⟩
  · exact ⟨(subdivisionUpperConeHomotopy p hd).trans (subdivisionUpperTriangleHomotopy p hd)⟩

theorem SecondHurewicz.SimplyConnected.subdivision_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦p⟧ : π_ 2 X x) =
      ((· * ·) : π_ 2 X x → π_ 2 X x → π_ 2 X x) ⟦subdivisionLowerTriangleLoop p hd⟧
        ⟦subdivisionUpperTriangleLoop p hd⟧ := by
  have h :
    (⟦p⟧ : π_ 2 X x) =
      (⟦GenLoop.transAt (1 : Fin 2) (subdivisionLowerTriangleLoop p hd)
            (subdivisionUpperTriangleLoop p hd)⟧ :
        π_ 2 X x) :=
    Quotient.sound (subdivision_homotopic p hd)
  exact
    h.trans
      ((HomotopyGroup.mul_spec (i := (1 : Fin 2)) (p := subdivisionUpperTriangleLoop p hd) (q :=
            subdivisionLowerTriangleLoop p hd)).symm.trans
        (mul_comm _ _))

theorem SecondHurewicz.SimplyConnected.subdivision_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· + ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivision_class p hd)

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_lower
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u) =
      FirstHurewicz.simplexFace 2 3 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![u 0, Min.min (u 0) (u 1)] j =
      (FirstHurewicz.simplexFace 2 3 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_three]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply]

theorem SecondHurewicz.SimplyConnected.tetrahedronQuadrilateralA_upper
    (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u) =
      FirstHurewicz.simplexFace 2 1 (triangleCubeQuotient u) := by
  have tetrahedronQuadrilateralA_zero (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_one (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_two (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 2 = Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have tetrahedronQuadrilateralA_three (u : Fin 2 → (unitInterval)) :
    tetrahedronQuadrilateralA u 3 = (u 1 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have triangleCubeQuotient_apply (t : Fin 2 → (unitInterval)) :
    triangleCubeQuotient t = triangleQuotient (t 0, t 1) := rfl
  have subdivisionSubMin_coe (u v : (unitInterval)) :
    (subdivisionSubMin u v : ℝ) = (u : ℝ) - Min.min (u : ℝ) (v : ℝ) := rfl
  have hm : (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) ≤ (u 0 : ℝ) :=
    sub_le_self _ (le_min (u 0).property.1 (u 1).property.1)
  apply Subtype.ext
  funext j
  change
    tetrahedronQuadrilateralA ![subdivisionSubMin (u 0) (u 1), u 0] j =
      (FirstHurewicz.simplexFace 2 1 (triangleCubeQuotient u) : Fin 4 → ℝ) j
  rw [simplexFace_two_one]
  fin_cases j <;>
    simp [tetrahedronQuadrilateralA_zero, tetrahedronQuadrilateralA_one,
      tetrahedronQuadrilateralA_two, tetrahedronQuadrilateralA_three, triangleCubeQuotient_apply,
      subdivisionSubMin_coe, min_eq_left hm, max_eq_right hm]

theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_face_three
    (s : FirstHurewicz.Simplex 2) :
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 3 s) = FirstHurewicz.simplexFace 2 0 s :=
  by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 3 s) j =
      (FirstHurewicz.simplexFace 2 0 s : Fin 4 → ℝ) j
  rw [simplexFace_two_zero]
  fin_cases j
  · exact FirstHurewicz.simplexFace_apply_self 2 3 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 3 s 2

theorem SecondHurewicz.SimplyConnected.tetrahedronQuarterShift_face_one
    (s : FirstHurewicz.Simplex 2) :
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 1 s) =
      FirstHurewicz.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) := by
  apply Subtype.ext
  funext j
  change
    tetrahedronQuarterShift (FirstHurewicz.simplexFace 2 1 s) j =
      (FirstHurewicz.simplexFace 2 2 (triangleCyclicPermutation (triangleCyclicPermutation s)) :
          Fin 4 → ℝ)
        j
  rw [simplexFace_two_two]
  fin_cases j
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 0
  · exact FirstHurewicz.simplexFace_apply_self 2 1 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 2 1 s 1

theorem SecondHurewicz.SimplyConnected.tetrahedronLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 3) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u)) =
      τ.val (FirstHurewicz.simplexFace 2 3 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower]

theorem SecondHurewicz.SimplyConnected.tetrahedronUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronQuadrilateralLoop τ)
        (tetrahedronQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 1) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u)) =
      τ.val (FirstHurewicz.simplexFace 2 1 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_upper]

theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedLowerLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionLowerTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (basedTetrahedronFace τ 0) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionLowerTriangleMap u))) =
      τ.val (FirstHurewicz.simplexFace 2 0 (triangleCubeQuotient u))
  rw [tetrahedronQuadrilateralA_lower, tetrahedronQuarterShift_face_three]

theorem SecondHurewicz.SimplyConnected.tetrahedronShiftedUpperLoop_eq_face {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    subdivisionUpperTriangleLoop (tetrahedronShiftedQuadrilateralLoop τ)
        (tetrahedronShiftedQuadrilateralLoop_diagonal τ) =
      basedTriangleLoop (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (tetrahedronQuarterShift (tetrahedronQuadrilateralA (subdivisionUpperTriangleMap u))) =
      τ.val
        (FirstHurewicz.simplexFace 2 2
          (triangleCyclicPermutation (triangleCyclicPermutation (triangleCubeQuotient u))))
  rw [tetrahedronQuadrilateralA_upper, tetrahedronQuarterShift_face_one]

theorem SecondHurewicz.SimplyConnected.basedTetrahedron_pair_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 3) +
        basedTriangleClass (basedTetrahedronFace τ 1) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass (basedTetrahedronFace τ 2) := by
  have hA :=
    subdivision_additiveClass (tetrahedronQuadrilateralLoop τ)
      (tetrahedronQuadrilateralLoop_diagonal τ)
  rw [tetrahedronLowerLoop_eq_face, tetrahedronUpperLoop_eq_face] at hA
  have hB :=
    subdivision_additiveClass (tetrahedronShiftedQuadrilateralLoop τ)
      (tetrahedronShiftedQuadrilateralLoop_diagonal τ)
  rw [tetrahedronShiftedLowerLoop_eq_face, tetrahedronShiftedUpperLoop_eq_face] at hB
  change
    Additive.ofMul (⟦tetrahedronShiftedQuadrilateralLoop τ⟧ : π_ 2 X x) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass
          (cyclicBasedTriangle (cyclicBasedTriangle (basedTetrahedronFace τ 2))) at hB
  simp only [basedTriangleClass_cyclic] at hB
  exact hA.symm.trans ((congrArg Additive.ofMul (tetrahedronFillings_class τ)).trans hB)

theorem SecondHurewicz.SimplyConnected.basedTetrahedron_boundary_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 0) -
            basedTriangleClass (basedTetrahedronFace τ 1) +
          basedTriangleClass (basedTetrahedronFace τ 2) -
        basedTriangleClass (basedTetrahedronFace τ 3) =
      0 := by
  calc
    _ =
        (basedTriangleClass (basedTetrahedronFace τ 0) +
            basedTriangleClass (basedTetrahedronFace τ 2)) -
          (basedTriangleClass (basedTetrahedronFace τ 3) +
            basedTriangleClass (basedTetrahedronFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedTetrahedron_pair_relation τ).symm

theorem SecondHurewicz.SimplyConnected.basedTetrahedron_signed_relation {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTetrahedron x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • basedTriangleClass (basedTetrahedronFace τ i) = 0 := by
  have h := basedTetrahedron_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

def SecondHurewicz.SimplyConnected.normalizedTetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) :
    BasedTetrahedron x :=
  BasedTetrahedron.ofFaces (normalizedTetrahedronMap x smp)
    (normalizedTetrahedronMap_face_boundary x smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTetrahedron_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) (i : Fin 4) :
    basedTetrahedronFace (normalizedTetrahedron x smp) i =
      normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i)) := by
  apply Subtype.ext
  exact normalizedTetrahedronMap_face x smp i

theorem SecondHurewicz.SimplyConnected.normalizedTriangle_boundary_relation {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 3) :
    ∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          basedTriangleClass (normalizedTriangle x (smp.comp (FirstHurewicz.simplexFace 2 i))) =
      0 := by
  simpa only [normalizedTetrahedron_face] using
    basedTetrahedron_signed_relation (normalizedTetrahedron x smp)

theorem PeriodTorusHigherHomology.formalBoundary_edge_simplex {V : Type*} (v : Fin 2 → V) :
    SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v) =
      SingularMayerVietoris.formalSimplex (fun _ : Fin 1 => v 1) -
        SingularMayerVietoris.formalSimplex (fun _ : Fin 1 => v 0) := by
  rw [SingularMayerVietoris.formalBoundary_simplex]
  change
    (∑ i : Fin 2, (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (v ∘ i.succAbove)) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul, ← sub_eq_add_neg]
  congr 1 <;> congr 1 <;> funext i <;> rw [Fin.eq_zero i] <;> rfl

theorem PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    formalPointCrossProduct q
        (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v)) d =
      SingularMayerVietoris.formalMap (fun w => (v 1, w)) (q + 1) d -
        SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  rw [formalBoundary_edge_simplex, map_sub, LinearMap.sub_apply,
    formalPointCrossProduct_simplex_left, formalPointCrossProduct_simplex_left]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.squareAffineTriangle (v : Fin 3 → Fin 2 × Fin 2) :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  ((FirstHurewicz.pathSimplex Path.id).prodMap (FirstHurewicz.pathSimplex Path.id)).comp
    (PeriodTorusHigherHomology.productAffineSimplex
      (fun i =>
        (SingularMayerVietoris.stdVertices 1 (v i).1,
          SingularMayerVietoris.stdVertices 1 (v i).2)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareAffineTriangle_fst_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : FirstHurewicz.Simplex 2) :
    ((squareAffineTriangle v s).1 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).1 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).1) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareAffineTriangle_snd_coe (v : Fin 3 → Fin 2 × Fin 2)
    (s : FirstHurewicz.Simplex 2) :
    ((squareAffineTriangle v s).2 : ℝ) =
      ∑ i, s i * SingularMayerVietoris.stdVertices 1 (v i).2 1 := by
  change
    SingularMayerVietoris.affineSimplex (fun i => SingularMayerVietoris.stdVertices 1 (v i).2) s
        1 =
      _
  exact SingularMayerVietoris.affineSimplex_coordinate _ _ _

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.lowerProductTriangle :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (1, 0), (1, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.upperProductTriangle :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 1), (1, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.leftProductDegenerate :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (0, 1)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.bottomProductDegenerate :
    C(FirstHurewicz.Simplex 2, (unitInterval) × (unitInterval)) :=
  squareAffineTriangle ![(0, 0), (0, 0), (1, 0)]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.lowerProductTriangle_fst (s : FirstHurewicz.Simplex 2) :
    ((lowerProductTriangle s).1 : ℝ) = s 1 + s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.lowerProductTriangle_snd (s : FirstHurewicz.Simplex 2) :
    ((lowerProductTriangle s).2 : ℝ) = s 2 := by
  simp [lowerProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.upperProductTriangle_fst (s : FirstHurewicz.Simplex 2) :
    ((upperProductTriangle s).1 : ℝ) = s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.upperProductTriangle_snd (s : FirstHurewicz.Simplex 2) :
    ((upperProductTriangle s).2 : ℝ) = s 1 + s 2 := by
  simp [upperProductTriangle, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.leftProductDegenerate_fst (s : FirstHurewicz.Simplex 2) :
    (leftProductDegenerate s).1 = 0 := by
  apply Subtype.ext
  simp [leftProductDegenerate, squareAffineTriangle_fst_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.bottomProductDegenerate_snd (s : FirstHurewicz.Simplex 2) :
    (bottomProductDegenerate s).2 = 0 := by
  apply Subtype.ext
  simp [bottomProductDegenerate, squareAffineTriangle_snd_coe, SingularMayerVietoris.stdVertices,
    stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.lowerSquareTriangle :
    C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp lowerProductTriangle

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def SecondHurewicz.SimplyConnected.upperSquareTriangle :
    C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp upperProductTriangle

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_zero (s : FirstHurewicz.Simplex 2) :
    (lowerSquareTriangle s 0 : ℝ) = s 1 + s 2 := by simp [lowerSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_one (s : FirstHurewicz.Simplex 2) :
    (lowerSquareTriangle s 1 : ℝ) = s 2 := by simp [lowerSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_zero (s : FirstHurewicz.Simplex 2) :
    (upperSquareTriangle s 0 : ℝ) = s 2 := by simp [upperSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_one (s : FirstHurewicz.Simplex 2) :
    (upperSquareTriangle s 1 : ℝ) = s 1 + s 2 := by simp [upperSquareTriangle]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.productSquareChain_four_triangles :
    SecondHurewicz.productSquareChain =
      FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
            FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate -
          FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle +
        FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 bottomProductDegenerate := by
  rw [SecondHurewicz.productSquareChain, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    PeriodTorusHigherHomology.formalBoundary_edge_simplex]
  simp only [map_sub, PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex]
  change
    (FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 lowerProductTriangle -
          FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 leftProductDegenerate) -
        (FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2 upperProductTriangle -
          FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2
            bottomProductDegenerate) =
      _
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareMap_leftProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (SecondHurewicz.squareMap p).comp leftProductDegenerate =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨0, Or.inl ?_⟩
  rw [SecondHurewicz.squareCoordinates_zero, leftProductDegenerate_fst]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareMap_bottomProductDegenerate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (SecondHurewicz.squareMap p).comp bottomProductDegenerate =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  apply GenLoop.boundary p
  refine ⟨1, Or.inl ?_⟩
  rw [SecondHurewicz.squareCoordinates_one, bottomProductDegenerate_snd]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem SecondHurewicz.SimplyConnected.squareChain_two_triangles {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    SecondHurewicz.squareChain p =
      FirstHurewicz.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
        FirstHurewicz.simplexChain X 2 (p.val.comp upperSquareTriangle) := by
  rw [SecondHurewicz.squareChain, SecondHurewicz.suspensionOne_toLoop,
    productSquareChain_four_triangles]
  simp only [map_add, map_sub, FirstHurewicz.inducedChain_simplex,
    squareMap_leftProductDegenerate, squareMap_bottomProductDegenerate]
  change
    (FirstHurewicz.simplexChain X 2 (p.val.comp lowerSquareTriangle) -
            FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x)) -
          FirstHurewicz.simplexChain X 2 (p.val.comp upperSquareTriangle) +
        FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      _
  abel

theorem SecondHurewicz.SimplyConnected.triangleQuotient_lowerProductTriangle :
    triangleQuotient.comp lowerProductTriangle = ContinuousMap.id (FirstHurewicz.Simplex 2) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + s 2) = 1 at hs
  have hle : s 2 ≤ s 1 + s 2 := le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  fin_cases i
  · change 1 - ((lowerProductTriangle s).1 : ℝ) = s 0
    rw [lowerProductTriangle_fst]
    linarith
  · change
      ((lowerProductTriangle s).1 : ℝ) -
          Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) =
        s 1
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]
    ring
  · change Min.min ((lowerProductTriangle s).1 : ℝ) ((lowerProductTriangle s).2 : ℝ) = s 2
    rw [lowerProductTriangle_fst, lowerProductTriangle_snd, min_eq_right hle]

theorem SecondHurewicz.SimplyConnected.triangleQuotient_upperProductTriangle_boundary
    (s : FirstHurewicz.Simplex 2) :
    triangleQuotient (upperProductTriangle s) ∈ triangleBoundary := by
  refine ⟨1, ?_⟩
  rw [triangleQuotient_one, upperProductTriangle_fst, upperProductTriangle_snd,
    min_eq_left (le_add_of_nonneg_left (stdSimplex.zero_le s 1)), sub_self]

theorem SecondHurewicz.SimplyConnected.basedTriangleLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) : (basedTriangleLoop τ).val.comp lowerSquareTriangle = τ.val := by
  change (SecondHurewicz.squareMap (basedTriangleLoop τ)).comp lowerProductTriangle = _
  rw [squareMap_basedTriangleLoop, ContinuousMap.comp_assoc,
    triangleQuotient_lowerProductTriangle, ContinuousMap.comp_id]

theorem SecondHurewicz.SimplyConnected.basedTriangleLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleLoop τ).val.comp upperSquareTriangle =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  change (SecondHurewicz.squareMap (basedTriangleLoop τ)).comp upperProductTriangle = _
  rw [squareMap_basedTriangleLoop]
  ext s
  exact τ.property _ (triangleQuotient_upperProductTriangle_boundary s)

theorem SecondHurewicz.SimplyConnected.squareChain_basedTriangleLoop {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.squareChain (basedTriangleLoop τ) =
      FirstHurewicz.simplexChain X 2 τ.val -
        FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x) := by
  rw [squareChain_two_triangles, basedTriangleLoop_lower, basedTriangleLoop_upper]

def SecondHurewicz.SimplyConnected.basedTriangleCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedTriangle x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 2
    (FirstHurewicz.simplexChain X 2 τ.val -
      FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x))
    (by
      rw [← squareChain_basedTriangleLoop]
      exact SecondHurewicz.squareChain_boundary (basedTriangleLoop τ))

@[simp]
theorem SecondHurewicz.SimplyConnected.basedTriangleCycle_val {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    (basedTriangleCycle τ).val =
      FirstHurewicz.simplexChain X 2 τ.val -
        FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x) :=
  rfl

theorem SecondHurewicz.SimplyConnected.hurewicz_basedTriangleClass {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedTriangle x) :
    SecondHurewicz.hurewiczMap x (basedTriangleClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (basedTriangleCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (SecondHurewicz.squareCycle (basedTriangleLoop τ)) =
      _
  congr 1
  apply Subtype.ext
  exact squareChain_basedTriangleLoop τ

def SecondHurewicz.SimplyConnected.secondHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : FirstHurewicz.Chains X 2 →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X 3, F (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (FirstHurewicz.singularComplex X) 2
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2).subtype)
    (fun b => hF b)

@[simp]
theorem SecondHurewicz.SimplyConnected.secondHomologyDesc_cycleClass {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : FirstHurewicz.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 3, F (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    secondHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (FirstHurewicz.singularComplex X) 2 _ _ c

theorem SecondHurewicz.SimplyConnected.comp_secondHomologyDesc_eq_id {X : Type}
    [TopologicalSpace X] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : FirstHurewicz.Chains X 2 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 3, F (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c) :
    g.comp (secondHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (FirstHurewicz.singularComplex X) 2
  intro c
  simpa only [LinearMap.comp_apply, secondHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

def SecondHurewicz.SimplyConnected.chainAugmentation (X : Type) [TopologicalSpace X] (n : ℕ) :
    FirstHurewicz.Chains X n →ₗ[ℤ] ℤ :=
  FirstHurewicz.chainLift X n fun _ => 1

@[simp]
theorem SecondHurewicz.SimplyConnected.chainAugmentation_simplex (X : Type) [TopologicalSpace X]
    (n : ℕ) (smp : FirstHurewicz.SingularSimplex X n) :
    chainAugmentation X n (FirstHurewicz.simplexChain X n smp) = 1 :=
  FirstHurewicz.chainLift_simplex X n _ smp

theorem SecondHurewicz.SimplyConnected.chainAugmentation_boundaryTwo (X : Type)
    [TopologicalSpace X] (c : FirstHurewicz.Chains X 2) :
    chainAugmentation X 1 (FirstHurewicz.boundaryTwo X c) = chainAugmentation X 2 c := by
  have h : (chainAugmentation X 1).comp (FirstHurewicz.boundaryTwo X) = chainAugmentation X 2 := by
    apply FirstHurewicz.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundaryTwo_simplex, map_add, map_sub,
      chainAugmentation_simplex, sub_self, zero_add]
  exact LinearMap.congr_fun h c

@[simp]
theorem SecondHurewicz.SimplyConnected.chainAugmentation_twoCycle (X : Type) [TopologicalSpace X]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    chainAugmentation X 2 c.1 = 0 := by
  rw [← chainAugmentation_boundaryTwo]
  have hc :=
    SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 2 c
  change FirstHurewicz.boundaryTwo X c.1 = 0 at hc
  rw [hc, map_zero]

theorem SecondHurewicz.SimplyConnected.chainLift_sub_constant (X : Type) [TopologicalSpace X]
    {M : Type} [AddCommGroup M] [Module ℤ M] (n : ℕ) (f : FirstHurewicz.SingularSimplex X n → M)
    (m : M) (c : FirstHurewicz.Chains X n) :
    FirstHurewicz.chainLift X n (fun smp => f smp - m) c =
      FirstHurewicz.chainLift X n f c - chainAugmentation X n c • m := by
  have h :
    FirstHurewicz.chainLift X n (fun smp => f smp - m) =
      FirstHurewicz.chainLift X n f -
        (LinearMap.toSpanSingleton ℤ M m).comp (chainAugmentation X n) := by
    apply FirstHurewicz.chainMap_ext X n
    intro smp
    simp only [FirstHurewicz.chainLift_simplex, LinearMap.sub_apply, LinearMap.comp_apply,
      chainAugmentation_simplex, LinearMap.toSpanSingleton_apply_one]
  exact
    (LinearMap.congr_fun h c).trans
      (congrArg (fun z : M => FirstHurewicz.chainLift X n f c - z)
        (int_smul_eq_zsmul (inferInstance : Module ℤ M) (chainAugmentation X n c) m))

theorem SecondHurewicz.SimplyConnected.chainLift_sub_constant_twoCycle (X : Type)
    [TopologicalSpace X] {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : FirstHurewicz.SingularSimplex X 2 → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    FirstHurewicz.chainLift X 2 (fun smp => f smp - m) c.1 = FirstHurewicz.chainLift X 2 f c.1 := by
  rw [chainLift_sub_constant, chainAugmentation_twoCycle, zero_smul, sub_zero]

def SecondHurewicz.SimplyConnected.triangleClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) : FirstHurewicz.Chains X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  FirstHurewicz.chainLift X 2 fun smp => basedTriangleClass (normalizedTriangle x smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.triangleClassOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) :
    triangleClassOperator x (FirstHurewicz.simplexChain X 2 smp) =
      basedTriangleClass (normalizedTriangle x smp) :=
  FirstHurewicz.chainLift_simplex X 2 _ smp

theorem SecondHurewicz.SimplyConnected.triangleClassOperator_boundary {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (b : FirstHurewicz.Chains X 3) :
    triangleClassOperator x (((FirstHurewicz.singularComplex X).d 3 2).hom b) = 0 := by
  have h : (triangleClassOperator x).comp ((FirstHurewicz.singularComplex X).d 3 2).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      triangleClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedTriangle_boundary_relation x smp
  exact LinearMap.congr_fun h b

def SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    FirstHurewicz.Chains X 2 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2 :=
  FirstHurewicz.chainLift X 2 fun smp => basedTriangleCycle (normalizedTriangle x smp)

@[simp]
theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_simplex {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (smp : FirstHurewicz.SingularSimplex X 2) :
    normalizedTriangleCycleOperator x (FirstHurewicz.simplexChain X 2 smp) =
      basedTriangleCycle (normalizedTriangle x smp) :=
  FirstHurewicz.chainLift_simplex X 2 _ smp

theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_val {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (c : FirstHurewicz.Chains X 2) :
    (normalizedTriangleCycleOperator x c).val =
      FirstHurewicz.chainLift X 2
        (fun smp =>
          FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val -
            FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2).subtype.comp
        (normalizedTriangleCycleOperator x) =
      FirstHurewicz.chainLift X 2
        (fun smp =>
          FirstHurewicz.simplexChain X 2 (normalizedTriangle x smp).val -
            FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x)) := by
    apply FirstHurewicz.chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, normalizedTriangleCycleOperator_simplex,
      Submodule.subtype_apply, basedTriangleCycle_val, FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

theorem SecondHurewicz.SimplyConnected.normalizedTriangleCycleOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    normalizedTriangleCycleOperator x c.val = normalizedTwoCycle x c := by
  apply Subtype.ext
  rw [normalizedTriangleCycleOperator_val, chainLift_sub_constant_twoCycle,
    normalizedTwoCycle_val]
  rfl

theorem SecondHurewicz.SimplyConnected.hurewiczMap_comp_triangleClassOperator {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (SecondHurewicz.hurewiczMap x).comp (triangleClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2).comp
        (normalizedTriangleCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 2
  intro smp
  simp only [LinearMap.comp_apply, triangleClassOperator_simplex,
    normalizedTriangleCycleOperator_simplex]
  exact hurewicz_basedTriangleClass (normalizedTriangle x smp)

theorem SecondHurewicz.SimplyConnected.hurewiczMap_triangleClassOperator_twoCycle {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    SecondHurewicz.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_triangleClassOperator x) c.val
  change
    SecondHurewicz.hurewiczMap x (triangleClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2
        (normalizedTriangleCycleOperator x c.val) at h
  rw [normalizedTriangleCycleOperator_twoCycle] at h
  exact h.trans (normalizedTwoCycle_class x c)

def SecondHurewicz.SimplyConnected.hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SingularMayerVietoris.SingularHomology X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  secondHomologyDesc (triangleClassOperator x) (triangleClassOperator_boundary x)

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 2) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 2 c) =
      triangleClassOperator x c.val :=
  secondHomologyDesc_cycleClass _ _ c

theorem SecondHurewicz.SimplyConnected.hurewiczMap_comp_hurewiczInverse {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (SecondHurewicz.hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_secondHomologyDesc_eq_id (triangleClassOperator x) (triangleClassOperator_boundary x)
    (SecondHurewicz.hurewiczMap x) (hurewiczMap_triangleClassOperator_twoCycle x)

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (c : SingularMayerVietoris.SingularHomology X 2) :
    SecondHurewicz.hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp lowerSquareTriangle) := by
  intro i
  change p (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨1, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (lowerSquareTriangle (stdSimplex.vertex (S := ℝ) i) 1 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_verticesBased {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    VerticesBased x 2 (p.val.comp upperSquareTriangle) := by
  intro i
  change p (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i)) = x
  apply GenLoop.boundary p
  refine ⟨0, ?_⟩
  by_cases hi : i = 2
  · right
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 1
    simp [hi, stdSimplex.vertex]
  · left
    apply Subtype.ext
    change (upperSquareTriangle (stdSimplex.vertex (S := ℝ) i) 0 : ℝ) = 0
    simp [hi, stdSimplex.vertex]

theorem SecondHurewicz.SimplyConnected.squareTriangles_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).comp (FirstHurewicz.simplexFace 1 1) =
      (p.val.comp upperSquareTriangle).comp (FirstHurewicz.simplexFace 1 1) := by
  apply ContinuousMap.ext
  intro s
  change
    p.val (lowerSquareTriangle (FirstHurewicz.simplexFace 1 1 s)) =
      p.val (upperSquareTriangle (FirstHurewicz.simplexFace 1 1 s))
  apply congrArg p.val
  funext i
  apply Subtype.ext
  fin_cases i
  · change
      (lowerSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 0 : ℝ) =
        (upperSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 0 : ℝ)
    rw [lowerSquareTriangle_zero, upperSquareTriangle_zero, FirstHurewicz.simplexFace_apply_self,
      zero_add]
  · change
      (lowerSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 1 : ℝ) =
        (upperSquareTriangle (FirstHurewicz.simplexFace 1 1 s) 1 : ℝ)
    rw [lowerSquareTriangle_one, upperSquareTriangle_one, FirstHurewicz.simplexFace_apply_self,
      zero_add]

theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_outerFace {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp lowerSquareTriangle).comp (FirstHurewicz.simplexFace 1 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (FirstHurewicz.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (FirstHurewicz.simplexFace 1 0 s) 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    have h1 : FirstHurewicz.simplexFace 1 0 s 1 = s 0 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 0
    have h2 : FirstHurewicz.simplexFace 1 0 s 2 = s 1 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (lowerSquareTriangle (FirstHurewicz.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle (FirstHurewicz.simplexFace 1 2 s) 1 : ℝ) = 0
    rw [lowerSquareTriangle_one, FirstHurewicz.simplexFace_apply_self]

theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_outerFace {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x) (i : Fin 3) (hi : i ≠ 1) :
    (p.val.comp upperSquareTriangle).comp (FirstHurewicz.simplexFace 1 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 1) x := by
  fin_cases i
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (FirstHurewicz.simplexFace 1 0 s)) = x
    apply GenLoop.boundary p
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (FirstHurewicz.simplexFace 1 0 s) 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    have h1 : FirstHurewicz.simplexFace 1 0 s 1 = s 0 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 0
    have h2 : FirstHurewicz.simplexFace 1 0 s 2 = s 1 :=
      FirstHurewicz.simplexFace_apply_succAbove 1 0 s 1
    rw [h1, h2]
    exact stdSimplex.add_eq_one s
  · exact (hi rfl).elim
  · apply ContinuousMap.ext
    intro s
    change p (upperSquareTriangle (FirstHurewicz.simplexFace 1 2 s)) = x
    apply GenLoop.boundary p
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle (FirstHurewicz.simplexFace 1 2 s) 0 : ℝ) = 0
    rw [upperSquareTriangle_zero, FirstHurewicz.simplexFace_apply_self]

theorem SecondHurewicz.SimplyConnected.lowerSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 1 : ℝ) ≤ t 0) : lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 0 : ℝ) = (t 0 : ℝ)
    rw [lowerSquareTriangle_zero, triangleQuotient_one, triangleQuotient_two]
    ring
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 1 : ℝ) = (t 1 : ℝ)
    rw [lowerSquareTriangle_one, triangleQuotient_two, min_eq_right h]

theorem SecondHurewicz.SimplyConnected.upperSquareTriangle_quotient (t : Fin 2 → (unitInterval))
    (h : (t 0 : ℝ) ≤ t 1) : upperSquareTriangle (triangleQuotient (t 1, t 0)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 0 : ℝ) = (t 0 : ℝ)
    rw [upperSquareTriangle_zero, triangleQuotient_two, min_eq_right h]
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 1 : ℝ) = (t 1 : ℝ)
    rw [upperSquareTriangle_one, triangleQuotient_one, triangleQuotient_two]
    ring

theorem SecondHurewicz.SimplyConnected.triangleQuotient_perimeter_of_le
    (z : (unitInterval) × (unitInterval)) (hper : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1)
    (hle : (z.2 : ℝ) ≤ z.1) : triangleQuotient z 0 = 0 ∨ triangleQuotient z 2 = 0 := by
  rcases hper with h | h | h | h
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_left z.2.property.1
  · left
    rw [triangleQuotient_zero, h]
    norm_num
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_right z.1.property.1
  · have hu : z.1 = 1 := Subtype.ext (le_antisymm z.1.property.2 (by simpa only [h] using hle))
    left
    rw [triangleQuotient_zero, hu]
    norm_num

theorem SecondHurewicz.SimplyConnected.cubeBoundary_productBoundary (t : Fin 2 → (unitInterval))
    (ht : t ∈ Cube.boundary (Fin 2)) : t 0 = 0 ∨ t 0 = 1 ∨ t 1 = 0 ∨ t 1 = 1 := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hi))

def SecondHurewicz.SimplyConnected.gluedTriangleHomotopyMap {X : Type} [TopologicalSpace X]
    (L U : C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) :
    C((unitInterval) × (Fin 2 → (unitInterval)), X)
    where
  toFun
    z :=
    if (z.2 1 : ℝ) ≤ z.2 0 then L (z.1, triangleQuotient (z.2 0, z.2 1))
    else U (z.1, triangleQuotient (z.2 1, z.2 0))
  continuous_toFun := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro z h
    have he : z.2 1 = z.2 0 := Subtype.ext h
    have hq : triangleQuotient (z.2 0, z.2 1) 1 = 0 := by
      simp only [triangleQuotient_one, he, min_self, sub_self]
    simpa only [he] using hdiag z.1 (triangleQuotient (z.2 0, z.2 1)) hq

theorem SecondHurewicz.SimplyConnected.gluedTriangleHomotopyMap_boundary {X : Type}
    [TopologicalSpace X] (L U : C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (x : X)
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x) (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x)
    (r : (unitInterval)) (t : Fin 2 → (unitInterval)) (ht : t ∈ Cube.boundary (Fin 2)) :
    gluedTriangleHomotopyMap L U hdiag (r, t) = x := by
  have hp := cubeBoundary_productBoundary t ht
  change (if (t 1 : ℝ) ≤ t 0 then _ else _) = x
  split_ifs with h
  · exact hL r _ (triangleQuotient_perimeter_of_le (t 0, t 1) hp h)
  · have hp' : t 1 = 0 ∨ t 1 = 1 ∨ t 0 = 0 ∨ t 0 = 1 := by
      rcases hp with hp | hp | hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inr (Or.inr hp))
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    exact hU r _ (triangleQuotient_perimeter_of_le (t 1, t 0) hp' (le_of_not_ge h))

def SecondHurewicz.SimplyConnected.gluedTriangleHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 2) X x}
    (L : (p.val.comp lowerSquareTriangle).Homotopy (q.val.comp lowerSquareTriangle))
    (U : (p.val.comp upperSquareTriangle).Homotopy (q.val.comp upperSquareTriangle))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel q.val (Cube.boundary (Fin 2))
    where
  toContinuousMap := gluedTriangleHomotopyMap L.toContinuousMap U.toContinuousMap hdiag
  map_zero_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = p.val t
    split_ifs with h
    · change L (0, triangleQuotient (t 0, t 1)) = p.val t
      rw [L.apply_zero]
      change p.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = p.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (0, triangleQuotient (t 1, t 0)) = p.val t
      rw [U.apply_zero]
      change p.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = p.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  map_one_left
    t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = q.val t
    split_ifs with h
    · change L (1, triangleQuotient (t 0, t 1)) = q.val t
      rw [L.apply_one]
      change q.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = q.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (1, triangleQuotient (t 1, t 0)) = q.val t
      rw [U.apply_one]
      change q.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = q.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  prop' r t
    ht :=
    (gluedTriangleHomotopyMap_boundary L.toContinuousMap U.toContinuousMap hdiag x hL hU r t
          ht).trans
      (GenLoop.boundary p t ht).symm

private theorem SecondHurewicz.SimplyConnected.basedTriangles_diagonal_mo1973_6743 {X : Type}
    [TopologicalSpace X] {x : X} (τ υ : BasedTriangle x) (s : FirstHurewicz.Simplex 2)
    (hs : s 1 = 0) : τ.val s = υ.val s :=
  (τ.property s ⟨1, hs⟩).trans (υ.property s ⟨1, hs⟩).symm

def SecondHurewicz.SimplyConnected.basedTrianglesLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ υ : BasedTriangle x) : GenLoop (Fin 2) X x :=
  ⟨(gluedTriangleHomotopyMap (τ.val.comp ContinuousMap.snd) (υ.val.comp ContinuousMap.snd)
          (fun _ => basedTriangles_diagonal_mo1973_6743 τ υ)).comp
      ⟨fun t => ((0 : (unitInterval)), t), by fun_prop⟩,
    by
    intro t ht
    exact
      gluedTriangleHomotopyMap_boundary _ _ (fun _ => basedTriangles_diagonal_mo1973_6743 τ υ) x
        (fun _ s hs => τ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩)))
        (fun _ s hs => υ.property s (hs.elim (fun h => ⟨0, h⟩) (fun h => ⟨2, h⟩))) 0 t ht⟩

@[simp]
theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_apply {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (t : Fin 2 → (unitInterval)) :
    basedTrianglesLoop τ υ t =
      if (t 1 : ℝ) ≤ t 0 then τ.val (triangleQuotient (t 0, t 1))
      else υ.val (triangleQuotient (t 1, t 0)) :=
  rfl

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_diagonal {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) (u : (unitInterval)) :
    basedTrianglesLoop τ υ (fun _ => u) = x := by
  rw [basedTrianglesLoop_apply, if_pos le_rfl]
  apply τ.property
  exact ⟨1, by simp only [triangleQuotient_one, min_self, sub_self]⟩

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_lower {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp lowerSquareTriangle = τ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (lowerSquareTriangle s) = τ.val s
  rw [basedTrianglesLoop_apply]
  have hle : (lowerSquareTriangle s 1 : ℝ) ≤ lowerSquareTriangle s 0 := by
    rw [lowerSquareTriangle_zero, lowerSquareTriangle_one]
    exact le_add_of_nonneg_left (stdSimplex.zero_le s 1)
  rw [if_pos hle]
  change
    τ.val (triangleQuotient ((lowerProductTriangle s).1, (lowerProductTriangle s).2)) = τ.val s
  exact congrArg τ.val (ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s)

private theorem SecondHurewicz.SimplyConnected.triangleQuotient_swapped_upper_mo1973_6748
    (s : FirstHurewicz.Simplex 2) :
    triangleQuotient (upperSquareTriangle s 1, upperSquareTriangle s 0) = s := by
  have hpair : (upperSquareTriangle s 1, upperSquareTriangle s 0) = lowerProductTriangle s := by
    apply Prod.ext <;> apply Subtype.ext
    · rw [upperSquareTriangle_one, lowerProductTriangle_fst]
    · rw [upperSquareTriangle_zero, lowerProductTriangle_snd]
  rw [hpair]
  exact ContinuousMap.congr_fun triangleQuotient_lowerProductTriangle s

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_upper {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    (basedTrianglesLoop τ υ).val.comp upperSquareTriangle = υ.val := by
  apply ContinuousMap.ext
  intro s
  change basedTrianglesLoop τ υ (upperSquareTriangle s) = υ.val s
  rw [basedTrianglesLoop_apply]
  split_ifs with h
  · have hs : s 1 = 0 := by
      rw [upperSquareTriangle_zero, upperSquareTriangle_one] at h
      exact le_antisymm (by linarith) (stdSimplex.zero_le s 1)
    have he : upperSquareTriangle s 0 = upperSquareTriangle s 1 := by
      apply Subtype.ext
      rw [upperSquareTriangle_zero, upperSquareTriangle_one, hs, zero_add]
    have hq : triangleQuotient (upperSquareTriangle s 0, upperSquareTriangle s 1) = s := by
      simpa only [he] using triangleQuotient_swapped_upper_mo1973_6748 s
    rw [hq]
    exact basedTriangles_diagonal_mo1973_6743 τ υ s hs
  · rw [triangleQuotient_swapped_upper_mo1973_6748]

def SecondHurewicz.SimplyConnected.basedTrianglesHomotopy {X : Type} [TopologicalSpace X] {x : X}
    {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  gluedTriangleHomotopy (L.cast rfl (basedTrianglesLoop_lower τ υ).symm)
    (U.cast rfl (basedTrianglesLoop_upper τ υ).symm) hdiag hL hU

theorem SecondHurewicz.SimplyConnected.triangleProperty_of_face
    {P : FirstHurewicz.Simplex 2 → Prop} (i : Fin 3)
    (h : ∀ u, P (FirstHurewicz.simplexFace 1 i u)) (s : FirstHurewicz.Simplex 2) (hs : s i = 0) :
    P s := by simpa only [simplexFace_inverse] using h (simplexFaceInverse 1 i ⟨s, hs⟩)

def SecondHurewicz.SimplyConnected.basedTrianglesHomotopy_of_faces {X : Type} [TopologicalSpace X]
    {x : X} {p : GenLoop (Fin 2) X x} (τ υ : BasedTriangle x)
    (L : (p.val.comp lowerSquareTriangle).Homotopy τ.val)
    (U : (p.val.comp upperSquareTriangle).Homotopy υ.val)
    (hdiag :
      ∀ r s, L (r, FirstHurewicz.simplexFace 1 1 s) = U (r, FirstHurewicz.simplexFace 1 1 s))
    (hL : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, L (r, FirstHurewicz.simplexFace 1 i s) = x)
    (hU : ∀ r (i : Fin 3), i ≠ 1 → ∀ s, U (r, FirstHurewicz.simplexFace 1 i s) = x) :
    p.val.HomotopyRel (basedTrianglesLoop τ υ).val (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy τ υ L U
    (fun r s hs => triangleProperty_of_face (P := fun s => L (r, s) = U (r, s)) 1 (hdiag r) s hs)
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => L (r, s) = x) 0 (hL r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => L (r, s) = x) 2 (hL r 2 (by decide)) s))
    (fun r s hs =>
      hs.elim (triangleProperty_of_face (P := fun s => U (r, s) = x) 0 (hU r 0 (by decide)) s)
        (triangleProperty_of_face (P := fun s => U (r, s) = x) 2 (hU r 2 (by decide)) s))

def SecondHurewicz.SimplyConnected.squareNormalizedLowerTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp lowerSquareTriangle)
    (lowerSquareTriangle_verticesBased p)

def SecondHurewicz.SimplyConnected.squareNormalizedUpperTriangle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) : BasedTriangle x :=
  edgeStraightenedTriangle x (p.val.comp upperSquareTriangle)
    (upperSquareTriangle_verticesBased p)

def SecondHurewicz.SimplyConnected.squareNormalizationTriangleHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(FirstHurewicz.Simplex 2, X))
    (h : VerticesBased x 2 smp) : smp.Homotopy (edgeStraightenedTriangle x smp h).val
    where
  toContinuousMap := triangleEdgeStraighteningHomotopy x smp
  map_zero_left := triangleEdgeStraighteningHomotopy_zero x smp
  map_one_left _ := rfl

def SecondHurewicz.SimplyConnected.squareLowerNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp lowerSquareTriangle).Homotopy (squareNormalizedLowerTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (lowerSquareTriangle_verticesBased p)

def SecondHurewicz.SimplyConnected.squareUpperNormalizationHomotopy {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (p.val.comp upperSquareTriangle).Homotopy (squareNormalizedUpperTriangle p).val :=
  squareNormalizationTriangleHomotopy _ (upperSquareTriangle_verticesBased p)

theorem SecondHurewicz.SimplyConnected.squareNormalization_edge_face {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (smp : C(FirstHurewicz.Simplex 2, X))
    (i : Fin 3) (r : (unitInterval)) (s : FirstHurewicz.Simplex 1) :
    triangleEdgeStraighteningHomotopy x smp (r, FirstHurewicz.simplexFace 1 i s) =
      edgeStraighteningHomotopy x (smp.comp (FirstHurewicz.simplexFace 1 i)) (r, s) :=
  DFunLike.congr_fun (triangleEdgeStraighteningHomotopy_face x smp i) (r, s)

theorem SecondHurewicz.SimplyConnected.squareNormalization_diagonal {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 1 s) =
      squareUpperNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 1 s) := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 1 s) =
      triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 1 s)
  rw [squareNormalization_edge_face, squareNormalization_edge_face, squareTriangles_diagonal]

theorem SecondHurewicz.SimplyConnected.squareLowerNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : FirstHurewicz.Simplex 1) :
    squareLowerNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp lowerSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, lowerSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

theorem SecondHurewicz.SimplyConnected.squareUpperNormalization_outerFace {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (r : (unitInterval)) (i : Fin 3) (hi : i ≠ 1) (s : FirstHurewicz.Simplex 1) :
    squareUpperNormalizationHomotopy p (r, FirstHurewicz.simplexFace 1 i s) = x := by
  change
    triangleEdgeStraighteningHomotopy x (p.val.comp upperSquareTriangle)
        (r, FirstHurewicz.simplexFace 1 i s) =
      x
  rw [squareNormalization_edge_face, upperSquareTriangle_outerFace p i hi,
    edgeStraighteningHomotopy_const]
  rfl

def SecondHurewicz.SimplyConnected.squareNormalizationHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)).val
      (Cube.boundary (Fin 2)) :=
  basedTrianglesHomotopy_of_faces (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p) (squareLowerNormalizationHomotopy p)
    (squareUpperNormalizationHomotopy p) (squareNormalization_diagonal p)
    (squareLowerNormalization_outerFace p) (squareUpperNormalization_outerFace p)

theorem SecondHurewicz.SimplyConnected.squareNormalization_homotopic {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    GenLoop.Homotopic p
      (basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)) :=
  ⟨squareNormalizationHomotopy p⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle :
    C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (squareAffineTriangle ![(0, 0), (1, 1), (0, 1)])

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_zero
    (s : FirstHurewicz.Simplex 2) : (subdivisionUpperPositiveSquareTriangle s 0 : ℝ) = s 1 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_fst_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

@[simp]
theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_one
    (s : FirstHurewicz.Simplex 2) :
    (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = s 1 + s 2 := by
  simp [subdivisionUpperPositiveSquareTriangle, squareAffineTriangle_snd_coe,
    SingularMayerVietoris.stdVertices, stdSimplex.vertex, Fin.sum_univ_succ, Pi.single_apply]

theorem SecondHurewicz.SimplyConnected.subdivisionTriangle_coordinate_sum
    (s : FirstHurewicz.Simplex 2) : s 0 + s 1 + s 2 = 1 := by
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  linarith

theorem SecondHurewicz.SimplyConnected.subdivisionLowerSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (lowerSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨0, Or.inr ?_⟩
    apply Subtype.ext
    change (lowerSquareTriangle s 0 : ℝ) = 1
    rw [lowerSquareTriangle_zero]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨1, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (upperSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (upperSquareTriangle s 1 : ℝ) = 1
    rw [upperSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveSquareTriangle_based {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ triangleBoundary) : p (subdivisionUpperPositiveSquareTriangle s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨1, Or.inr ?_⟩
    apply Subtype.ext
    change (subdivisionUpperPositiveSquareTriangle s 1 : ℝ) = 1
    rw [subdivisionUpperPositiveSquareTriangle_one]
    linarith [subdivisionTriangle_coordinate_sum s]
  · change s 1 = 0 at hi
    apply p.property
    refine ⟨0, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi
  · change s 2 = 0 at hi
    apply subdivisionOnDiagonal p hd
    apply Subtype.ext
    simp [hi]

def SecondHurewicz.SimplyConnected.subdivisionLowerBasedTriangle {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    BasedTriangle x :=
  ⟨p.val.comp lowerSquareTriangle, subdivisionLowerSquareTriangle_based p hd⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp upperSquareTriangle, subdivisionUpperNegativeSquareTriangle_based p hd⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperPositiveBasedTriangle {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : BasedTriangle x :=
  ⟨p.val.comp subdivisionUpperPositiveSquareTriangle,
    subdivisionUpperPositiveSquareTriangle_based p hd⟩

theorem SecondHurewicz.SimplyConnected.subdivisionLowerTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionLowerTriangleLoop p hd = basedTriangleLoop (subdivisionLowerBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change p ![u 0, Min.min (u 0) (u 1)] = p (lowerSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

theorem SecondHurewicz.SimplyConnected.subdivisionUpperTriangleLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperTriangleLoop p hd =
      basedTriangleLoop (subdivisionUpperPositiveBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![subdivisionSubMin (u 0) (u 1), u 0] =
      p (subdivisionUpperPositiveSquareTriangle (triangleQuotient (u 0, u 1)))
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp [subdivisionSubMin]

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeBasedTriangle_loop_apply {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : Fin 2 → (unitInterval)) :
    basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) u =
      p ![Min.min (u 0) (u 1), u 0] := by
  change p (upperSquareTriangle (triangleQuotient (u 0, u 1))) = p ![Min.min (u 0) (u 1), u 0]
  congr 1
  funext i
  fin_cases i <;> apply Subtype.ext <;> simp

theorem SecondHurewicz.SimplyConnected.subdivision_basedTriangleClass_sum {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) +
        basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) := by
  simpa only [subdivisionLowerTriangleLoop_eq_basedTriangleLoop,
    subdivisionUpperTriangleLoop_eq_basedTriangleLoop, basedTriangleClass] using
    subdivision_additiveClass p hd

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) (u 1), u 0]
  continuous_toFun := by fun_prop

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedMap :
    C(SubdivisionSquare, SubdivisionSquare)
    where
  toFun u := ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0]
  continuous_toFun := by fun_prop

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedMap_based {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeReversedMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact
      subdivisionOnDiagonal p hd _
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeLoop {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 2) X x) (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeMap (subdivisionUpperNegativeMap_based p hd)

def SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedLoop {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeReversedMap
    (subdivisionUpperNegativeReversedMap_based p hd)

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperTriangleMap u) (subdivisionUpperNegativeReversedMap u) :=
  by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact
      .zero 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .one 1 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact
      .diagonal (by simp [subdivisionUpperTriangleMap, h])
        (by
          simp [subdivisionUpperNegativeReversedMap, h,
            min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)])
  · exact
      .zero 0 (by simp [subdivisionUpperTriangleMap, h])
        (by simp [subdivisionUpperNegativeReversedMap, h])

def SecondHurewicz.SimplyConnected.subdivisionUpperOrientationHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (subdivisionUpperTriangleLoop p hd).val.HomotopyRel
      (subdivisionUpperNegativeReversedLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperTriangleMap_based p hd)
    (subdivisionUpperNegativeReversedMap_based p hd) subdivisionUpperOrientation_sides

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeReversedLoop_eq_symmAt {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeReversedLoop p hd =
      GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd) := by
  apply GenLoop.ext
  intro u
  change
    p ![Min.min (u 0) ((unitInterval.symm) (u 1)), u 0] =
      subdivisionUpperNegativeLoop p hd
        (fun j => if j = 1 then (unitInterval.symm) (u 1) else u j)
  simp [subdivisionUpperNegativeLoop, subdivisionPullbackLoop, subdivisionUpperNegativeMap]

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    GenLoop.Homotopic (subdivisionUpperTriangleLoop p hd)
      (GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)) := by
  rw [← subdivisionUpperNegativeReversedLoop_eq_symmAt]
  exact ⟨subdivisionUpperOrientationHomotopy p hd⟩

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_class {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((·⁻¹) : π_ 2 X x → π_ 2 X x) ⟦subdivisionUpperNegativeLoop p hd⟧ := by
  have h :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      (⟦GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)⟧ : π_ 2 X x) :=
    Quotient.sound (subdivisionUpperOrientation_homotopic p hd)
  exact
    h.trans
      (HomotopyGroup.inv_spec (i := (1 : Fin 2)) (p := subdivisionUpperNegativeLoop p hd)).symm

theorem SecondHurewicz.SimplyConnected.subdivisionUpperOrientation_additiveClass {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((-·) : Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivisionUpperOrientation_class p hd)

theorem SecondHurewicz.SimplyConnected.subdivision_eq_sub_of_eq_add {A : Type*} [AddGroup A]
    {a b c d : A} (h : a = b + c) (hc : c = -d) : a = b - d :=
  h.trans ((congrArg (fun z => b + z) hc).trans (sub_eq_add_neg b d).symm)

theorem SecondHurewicz.SimplyConnected.subdivisionUpperNegativeLoop_eq_basedTriangleLoop
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    subdivisionUpperNegativeLoop p hd =
      basedTriangleLoop (subdivisionUpperNegativeBasedTriangle p hd) := by
  apply GenLoop.ext
  intro u
  exact (subdivisionUpperNegativeBasedTriangle_loop_apply p hd u).symm

theorem SecondHurewicz.SimplyConnected.subdivisionUpperPositiveBasedTriangle_class_eq_neg
    {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    basedTriangleClass (subdivisionUpperPositiveBasedTriangle p hd) =
      -basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) := by
  unfold basedTriangleClass
  rw [← subdivisionUpperTriangleLoop_eq_basedTriangleLoop, ←
    subdivisionUpperNegativeLoop_eq_basedTriangleLoop]
  exact subdivisionUpperOrientation_additiveClass p hd

theorem SecondHurewicz.SimplyConnected.subdivision_basedTriangleClass_sub {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : (unitInterval), p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      basedTriangleClass (subdivisionLowerBasedTriangle p hd) -
        basedTriangleClass (subdivisionUpperNegativeBasedTriangle p hd) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_basedTriangleClass_sum p hd)
    (subdivisionUpperPositiveBasedTriangle_class_eq_neg p hd)

theorem SecondHurewicz.SimplyConnected.basedTrianglesLoop_class {X : Type} [TopologicalSpace X]
    {x : X} (τ υ : BasedTriangle x) :
    Additive.ofMul (⟦basedTrianglesLoop τ υ⟧ : π_ 2 X x) =
      basedTriangleClass τ - basedTriangleClass υ := by
  have hd : ∀ t : (unitInterval), basedTrianglesLoop τ υ ![t, t] = x := by
    intro t
    have he : (![t, t] : Fin 2 → (unitInterval)) = fun _ => t := by
      funext i
      fin_cases i <;> rfl
    rw [he, basedTrianglesLoop_diagonal]
  have hl : subdivisionLowerBasedTriangle (basedTrianglesLoop τ υ) hd = τ :=
    Subtype.ext (basedTrianglesLoop_lower τ υ)
  have hu : subdivisionUpperNegativeBasedTriangle (basedTrianglesLoop τ υ) hd = υ :=
    Subtype.ext (basedTrianglesLoop_upper τ υ)
  simpa only [hl, hu] using subdivision_basedTriangleClass_sub (basedTrianglesLoop τ υ) hd

theorem SecondHurewicz.SimplyConnected.squareNormalization_quotient {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    (⟦p⟧ : π_ 2 X x) =
      ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧ :=
  Quotient.sound (squareNormalization_homotopic p)

theorem SecondHurewicz.SimplyConnected.squareNormalization_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] {x : X} (p : GenLoop (Fin 2) X x) :
    basedTriangleClass (squareNormalizedLowerTriangle p) -
        basedTriangleClass (squareNormalizedUpperTriangle p) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  have h := congrArg Additive.ofMul (squareNormalization_quotient p)
  exact
    (basedTrianglesLoop_class (squareNormalizedLowerTriangle p)
          (squareNormalizedUpperTriangle p)).symm.trans
      h.symm

theorem SecondHurewicz.SimplyConnected.triangleClassOperator_squareChain {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    triangleClassOperator x (SecondHurewicz.squareChain p) = Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [squareChain_two_triangles, map_sub, triangleClassOperator_simplex,
    triangleClassOperator_simplex,
    normalizedTriangle_of_verticesBased x _ (lowerSquareTriangle_verticesBased p),
    normalizedTriangle_of_verticesBased x _ (upperSquareTriangle_verticesBased p)]
  exact squareNormalization_class p

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczInverse_hurewiczMap_mk {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczInverse x (SecondHurewicz.hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [SecondHurewicz.hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact triangleClassOperator_squareChain x p

@[simp]
theorem SecondHurewicz.SimplyConnected.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczInverse x (SecondHurewicz.hurewiczMap x a) = a := by
  change
    hurewiczInverse x (SecondHurewicz.hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem SecondHurewicz.SimplyConnected.hurewiczInverse_comp_hurewiczMap {X : Type}
    [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    (hurewiczInverse x).comp (SecondHurewicz.hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

def SecondHurewicz.SimplyConnected.hurewiczLinearEquiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    Additive (π_ 2 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 2 :=
  LinearEquiv.ofLinearMap (SecondHurewicz.hurewiczMap x) (hurewiczInverse x)
    (hurewiczMap_comp_hurewiczInverse x) (hurewiczInverse_comp_hurewiczMap x)

def SecondHurewicz.SimplyConnected.hurewiczPi2Equiv {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    π_ 2 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 2)
    where
  __ := SecondHurewicz.hurewiczPi2 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

theorem SphereHomology.unitSphere_piTwo_subsingleton (n : ℕ) (x : UnitSphere (n + 3)) :
    Subsingleton (π_ 2 (UnitSphere (n + 3)) x) := by
  let := unitSphere_homology_subsingleton (n + 2) 2 (by decide) (by omega)
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton

theorem ThirdHurewicz.gluedBoundaryMap_constant_value {X : Type} [TopologicalSpace X] {n : ℕ}
    (f : C(FirstHurewicz.Simplex n, X))
    (g : C((unitInterval) × SecondHurewicz.SimplyConnected.SimplexBoundary n, X))
    (h₀ : ∀ s, g (0, s) = f s.val) (x : X) (hf : ∀ s, f s = x) (hg : ∀ u, g u = x)
    (u : ↥(SecondHurewicz.SimplyConnected.bottomOrSide n)) :
    SecondHurewicz.SimplyConnected.gluedBoundaryMap f g h₀ u = x := by
  rcases u.property with hb | hs
  · have hu : u = SecondHurewicz.SimplyConnected.bottomInclusion n u.val.2 := by
      apply Subtype.ext
      exact Prod.ext hb rfl
    exact
      (congrArg (SecondHurewicz.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((SecondHurewicz.SimplyConnected.gluedBoundaryMap_bottomInclusion f g h₀ _).trans (hf _))
  · have hu : u = SecondHurewicz.SimplyConnected.sideInclusion n (u.val.1, ⟨u.val.2, hs⟩) := by
      apply Subtype.ext
      rfl
    exact
      (congrArg (SecondHurewicz.SimplyConnected.gluedBoundaryMap f g h₀) hu).trans
        ((SecondHurewicz.SimplyConnected.gluedBoundaryMap_sideInclusion f g h₀ _).trans (hg _))

theorem ThirdHurewicz.coherentFaceBoundaryHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hc :
      H' (ContinuousMap.const (FirstHurewicz.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex (n + 1)) x) :
    SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
        (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x) =
      ContinuousMap.const
        ((unitInterval) × SecondHurewicz.SimplyConnected.SimplexBoundary (n + 2)) x := by
  unfold SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy
  apply
    (SecondHurewicz.SimplyConnected.glueFaceHomotopies_unique _ _ (ContinuousMap.const _ x)
        ?_).symm
  intro i r s
  change x = H' (ContinuousMap.const (FirstHurewicz.Simplex (n + 1)) x) (r, s)
  rw [hc]
  rfl

theorem ThirdHurewicz.extendCoherentSimplexHomotopy_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp s, H' smp (0, s) = smp s) (x : X)
    (hc :
      H' (ContinuousMap.const (FirstHurewicz.Simplex (n + 1)) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex (n + 1)) x) :
    SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy H H' h h₀
        (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex (n + 2)) x := by
  unfold SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
  ext u
  change
    SecondHurewicz.SimplyConnected.gluedBoundaryMap
        (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x)
        (SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy H H' h
          (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x))
        (SecondHurewicz.SimplyConnected.coherentFaceBoundaryHomotopy_zero H H' h h₀
          (ContinuousMap.const (FirstHurewicz.Simplex (n + 2)) x))
        (SecondHurewicz.SimplyConnected.cylinderRetraction (n + 2) u) =
      x
  apply gluedBoundaryMap_constant_value _ _ _ x (fun _ => rfl)
  intro v
  exact
    congrArg
      (fun F : C((unitInterval) × SecondHurewicz.SimplyConnected.SimplexBoundary (n + 2), X) =>
        F v)
      (coherentFaceBoundaryHomotopy_const H H' h x hc)

@[simp]
theorem ThirdHurewicz.edgeTriangleHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x :=
  extendCoherentSimplexHomotopy_const (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 0)
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_zero x) x
    (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy_const x)

@[simp]
theorem ThirdHurewicz.edgeTetrahedronHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
  extendCoherentSimplexHomotopy_const (SecondHurewicz.SimplyConnected.edgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x) x
    (edgeTriangleHomotopy_const x)

def ThirdHurewicz.edgeFourSimplexHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) (smp : FirstHurewicz.SingularSimplex X 4) :
    C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x) smp

theorem ThirdHurewicz.edgeFourSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
      (edgeFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x)

def ThirdHurewicz.edgeNormalizedFourSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 4) :
    FirstHurewicz.SingularSimplex X 4 :=
  SecondHurewicz.SimplyConnected.timeSlice
    (edgeFourSimplexHomotopy x (SecondHurewicz.SimplyConnected.vertexNormalizedSimplex x 4 smp)) 1

theorem ThirdHurewicz.edgeNormalizedFourSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) :
    (edgeNormalizedFourSimplexMap x smp).comp (FirstHurewicz.simplexFace 3 i) =
      SecondHurewicz.SimplyConnected.normalizedTetrahedronMap x
        (smp.comp (FirstHurewicz.simplexFace 3 i)) := by
  change
    (SecondHurewicz.SimplyConnected.timeSlice
            (edgeFourSimplexHomotopy x
              (SecondHurewicz.SimplyConnected.vertexNormalizedSimplex x 4 smp))
            1).comp
        (FirstHurewicz.simplexFace 3 i) =
      _
  rw [SecondHurewicz.SimplyConnected.timeSlice_face (edgeFourSimplexHomotopy_face x),
    SecondHurewicz.SimplyConnected.vertexNormalizedSimplex_face]
  rfl

theorem ThirdHurewicz.triangleReturn_first_mem (s : FirstHurewicz.Simplex 2) :
    s 1 + Max.max (s 2 - s 0) 0 ∈ unitInterval := by
  constructor
  · exact add_nonneg (stdSimplex.zero_le s 1) (le_max_right _ _)
  · have hm : Max.max (s 2 - s 0) 0 ≤ s 2 :=
      max_le (sub_le_self _ (stdSimplex.zero_le s 0)) (stdSimplex.zero_le s 2)
    have h0 := stdSimplex.zero_le s 0
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    linarith

theorem ThirdHurewicz.triangleReturn_second_mem (s : FirstHurewicz.Simplex 2) :
    s 2 + Min.min (s 0) (s 2) ∈ unitInterval := by
  constructor
  · exact
      add_nonneg (stdSimplex.zero_le s 2)
        (le_min (stdSimplex.zero_le s 0) (stdSimplex.zero_le s 2))
  · have hm : Min.min (s 0) (s 2) ≤ s 0 := min_le_left _ _
    have h1 := stdSimplex.zero_le s 1
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + s 2) = 1 at hs
    linarith

def ThirdHurewicz.triangleCubicalReturn : C(FirstHurewicz.Simplex 2, Fin 2 → (unitInterval))
    where
  toFun
    s :=
    ![⟨s 1 + Max.max (s 2 - s 0) 0, triangleReturn_first_mem s⟩,
      ⟨s 2 + Min.min (s 0) (s 2), triangleReturn_second_mem s⟩]
  continuous_toFun := by
    have hc (j : Fin 3) : Continuous (fun s : FirstHurewicz.Simplex 2 => s j) :=
      (continuous_apply j).comp continuous_subtype_val
    apply continuous_pi
    intro i
    fin_cases i <;> apply Continuous.subtype_mk
    · change Continuous fun s : FirstHurewicz.Simplex 2 => s 1 + Max.max (s 2 - s 0) 0
      exact (hc 1).add (((hc 2).sub (hc 0)).max continuous_const)
    · change Continuous fun s : FirstHurewicz.Simplex 2 => s 2 + Min.min (s 0) (s 2)
      exact (hc 2).add ((hc 0).min (hc 2))

theorem ThirdHurewicz.triangleCubicalReturn_face_zero (s : FirstHurewicz.Simplex 2)
    (hs : s 0 = 0) : triangleCubicalReturn s 0 = 1 := by
  apply Subtype.ext
  change s 1 + Max.max (s 2 - s 0) 0 = 1
  rw [hs, sub_zero, max_eq_left (stdSimplex.zero_le s 2)]
  have hsum := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change s 0 + (s 1 + s 2) = 1 at hsum
  simpa only [hs, zero_add] using hsum

theorem ThirdHurewicz.triangleCubicalReturn_face_two (s : FirstHurewicz.Simplex 2)
    (hs : s 2 = 0) : triangleCubicalReturn s 1 = 0 := by
  apply Subtype.ext
  change s 2 + Min.min (s 0) (s 2) = 0
  rw [hs, min_eq_right (stdSimplex.zero_le s 0), zero_add]

theorem ThirdHurewicz.triangleCubicalReturn_face_one (s : FirstHurewicz.Simplex 2)
    (hs : s 1 = 0) : triangleCubicalReturn s 0 = 0 ∨ triangleCubicalReturn s 1 = 1 := by
  rcases le_total (s 2) (s 0) with h | h
  · left
    apply Subtype.ext
    change s 1 + Max.max (s 2 - s 0) 0 = 0
    rw [hs, max_eq_right (sub_nonpos.mpr h), zero_add]
  · right
    apply Subtype.ext
    change s 2 + Min.min (s 0) (s 2) = 1
    rw [min_eq_left h]
    have hsum := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
    change s 0 + (s 1 + s 2) = 1 at hsum
    linarith

theorem ThirdHurewicz.triangleCubicalReturn_boundary (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ SecondHurewicz.SimplyConnected.triangleBoundary) :
    triangleCubicalReturn s ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨0, Or.inr (triangleCubicalReturn_face_zero s hi)⟩
  · rcases triangleCubicalReturn_face_one s hi with h | h
    · exact ⟨0, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
  · exact ⟨1, Or.inl (triangleCubicalReturn_face_two s hi)⟩

theorem ThirdHurewicz.triangleCubicalReturn_quotient_zero (s : FirstHurewicz.Simplex 2)
    (i : Fin 3) (hi : s i = 0) :
    SecondHurewicz.SimplyConnected.triangleCubeQuotient (triangleCubicalReturn s) i = 0 := by
  fin_cases i
  · change 1 - (triangleCubicalReturn s 0 : ℝ) = 0
    rw [triangleCubicalReturn_face_zero s hi]
    norm_num
  · change
      (triangleCubicalReturn s 0 : ℝ) -
          Min.min (triangleCubicalReturn s 0 : ℝ) (triangleCubicalReturn s 1 : ℝ) =
        0
    rcases triangleCubicalReturn_face_one s hi with h | h
    · rw [h]
      change 0 - Min.min 0 (triangleCubicalReturn s 1 : ℝ) = 0
      rw [min_eq_left (triangleCubicalReturn s 1).property.1, sub_self]
    · rw [h]
      change (triangleCubicalReturn s 0 : ℝ) - Min.min (triangleCubicalReturn s 0 : ℝ) 1 = 0
      rw [min_eq_left (triangleCubicalReturn s 0).property.2, sub_self]
  · change Min.min (triangleCubicalReturn s 0 : ℝ) (triangleCubicalReturn s 1 : ℝ) = 0
    rw [triangleCubicalReturn_face_two s hi]
    change Min.min (triangleCubicalReturn s 0 : ℝ) 0 = 0
    exact min_eq_right (triangleCubicalReturn s 0).property.1

def ThirdHurewicz.triangleReturnComposition :
    C(FirstHurewicz.Simplex 2, FirstHurewicz.Simplex 2) :=
  SecondHurewicz.SimplyConnected.triangleCubeQuotient.comp triangleCubicalReturn

def ThirdHurewicz.triangleReturnInterpolation :
    C((unitInterval) × FirstHurewicz.Simplex 2, FirstHurewicz.Simplex 2) :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap
    (ContinuousMap.id (FirstHurewicz.Simplex 2)) triangleReturnComposition

@[simp]
theorem ThirdHurewicz.triangleReturnInterpolation_zero (s : FirstHurewicz.Simplex 2) :
    triangleReturnInterpolation (0, s) = s :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero s (triangleReturnComposition s)

@[simp]
theorem ThirdHurewicz.triangleReturnInterpolation_one (s : FirstHurewicz.Simplex 2) :
    triangleReturnInterpolation (1, s) = triangleReturnComposition s :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one s (triangleReturnComposition s)

theorem ThirdHurewicz.triangleReturnInterpolation_coordinate_zero (t : (unitInterval))
    (s : FirstHurewicz.Simplex 2) (i : Fin 3) (hi : s i = 0) :
    triangleReturnInterpolation (t, s) i = 0 :=
  SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t s
    (triangleReturnComposition s) i hi (triangleCubicalReturn_quotient_zero s i hi)

theorem ThirdHurewicz.triangleReturnInterpolation_boundary (t : (unitInterval))
    (s : FirstHurewicz.Simplex 2) (hs : s ∈ SecondHurewicz.SimplyConnected.triangleBoundary) :
    triangleReturnInterpolation (t, s) ∈ SecondHurewicz.SimplyConnected.triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, triangleReturnInterpolation_coordinate_zero t s i hi⟩

def ThirdHurewicz.triangleReturnHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (τ : SecondHurewicz.SimplyConnected.BasedTriangle x) :
    τ.val.HomotopyRel
      ((SecondHurewicz.SimplyConnected.basedTriangleLoop τ).val.comp triangleCubicalReturn)
      SecondHurewicz.SimplyConnected.triangleBoundary
    where
  toFun z := τ.val (triangleReturnInterpolation z)
  continuous_toFun := τ.val.continuous.comp triangleReturnInterpolation.continuous
  map_zero_left s := congrArg τ.val (triangleReturnInterpolation_zero s)
  map_one_left s := congrArg τ.val (triangleReturnInterpolation_one s)
  prop' t s
    hs :=
    (τ.property _ (triangleReturnInterpolation_boundary t s hs)).trans (τ.property s hs).symm

def ThirdHurewicz.nativeSquareNullHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    [hπ : Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin 2 → (unitInterval)) x) (Cube.boundary (Fin 2)) :=
  Classical.choice
    (show GenLoop.Homotopic p GenLoop.const from
      Quotient.exact (@Subsingleton.elim (π_ 2 X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

def ThirdHurewicz.nativeSquareNullHomotopy_comp {X : Type*} [TopologicalSpace X] {x : X}
    {A : Type*} [TopologicalSpace A] [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → (unitInterval))) (S : Set A) (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S
    where
  toFun z := nativeSquareNullHomotopy p (z.1, r z.2)
  continuous_toFun :=
    (nativeSquareNullHomotopy p).continuous.comp
      (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeSquareNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeSquareNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeSquareNullHomotopy p).eq_fst t (hr ha)

def ThirdHurewicz.triangleNullHomotopyUnnormalized {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
      SecondHurewicz.SimplyConnected.triangleBoundary :=
  ContinuousMap.HomotopyRel.trans (triangleReturnHomotopy τ)
    (nativeSquareNullHomotopy_comp (SecondHurewicz.SimplyConnected.basedTriangleLoop τ)
      triangleCubicalReturn SecondHurewicz.SimplyConnected.triangleBoundary
      (fun _ hs => triangleCubicalReturn_boundary _ hs))

def ThirdHurewicz.triangleNullHomotopy {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
      SecondHurewicz.SimplyConnected.triangleBoundary := by
  classical
    exact
    if h : τ = SecondHurewicz.SimplyConnected.constantBasedTriangle x then
      ContinuousMap.HomotopyRel.cast
        (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
          SecondHurewicz.SimplyConnected.triangleBoundary)
        (congrArg (fun υ : SecondHurewicz.SimplyConnected.BasedTriangle x => υ.val) h).symm rfl
    else triangleNullHomotopyUnnormalized τ

@[simp]
theorem ThirdHurewicz.triangleNullHomotopy_zero {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x)
    (s : FirstHurewicz.Simplex 2) : triangleNullHomotopy τ (0, s) = τ.val s :=
  (triangleNullHomotopy τ).apply_zero s

@[simp]
theorem ThirdHurewicz.triangleNullHomotopy_one {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ 2 X x)] (τ : SecondHurewicz.SimplyConnected.BasedTriangle x)
    (s : FirstHurewicz.Simplex 2) : triangleNullHomotopy τ (1, s) = x :=
  (triangleNullHomotopy τ).apply_one s

@[simp]
theorem ThirdHurewicz.triangleNullHomotopy_constant {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    triangleNullHomotopy (SecondHurewicz.SimplyConnected.constantBasedTriangle x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex 2) x)
        SecondHurewicz.SimplyConnected.triangleBoundary := by
  classical
  unfold triangleNullHomotopy
  rw [dif_pos rfl]
  rfl

@[simp]
theorem ThirdHurewicz.triangleNullHomotopy_constant_toContinuousMap {X : Type}
    [TopologicalSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (triangleNullHomotopy
          (SecondHurewicz.SimplyConnected.constantBasedTriangle x)).toContinuousMap =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x := by
  rw [triangleNullHomotopy_constant]
  rfl

def ThirdHurewicz.triangleStraighteningHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2) :
    C((unitInterval) × FirstHurewicz.Simplex 2, X) := by
  classical
    exact
    if h : ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary, smp s = x then
      (triangleNullHomotopy
          (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x)).toContinuousMap
    else SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2 smp

@[simp]
theorem ThirdHurewicz.triangleStraighteningHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2)
    (s : FirstHurewicz.Simplex 2) : triangleStraighteningHomotopy x smp (0, s) = smp s := by
  classical
  unfold triangleStraighteningHomotopy
  split
  · rename_i h
    exact triangleNullHomotopy_zero (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x) s
  · rfl

theorem ThirdHurewicz.triangleStraighteningHomotopy_one {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2)
    (h : ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary, smp s = x)
    (s : FirstHurewicz.Simplex 2) : triangleStraighteningHomotopy x smp (1, s) = x := by
  classical
  rw [triangleStraighteningHomotopy, dif_pos h]
  exact triangleNullHomotopy_one (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x) s

theorem ThirdHurewicz.triangleStraighteningHomotopy_boundary {X : Type} [TopologicalSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 2)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex 2)
    (hs : s ∈ SecondHurewicz.SimplyConnected.triangleBoundary) :
    triangleStraighteningHomotopy x smp (r, s) = smp s := by
  classical
  unfold triangleStraighteningHomotopy
  split
  · rename_i h
    exact
      (triangleNullHomotopy (⟨smp, h⟩ : SecondHurewicz.SimplyConnected.BasedTriangle x)).eq_fst r
        hs
  · rfl

@[simp]
theorem ThirdHurewicz.triangleStraighteningHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    triangleStraighteningHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x := by
  classical
  have h :
    ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
      (ContinuousMap.const (FirstHurewicz.Simplex 2) x) s = x :=
    fun _ _ => rfl
  rw [triangleStraighteningHomotopy, dif_pos h]
  exact triangleNullHomotopy_constant_toContinuousMap x

theorem ThirdHurewicz.triangleStraighteningHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 1
      (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1)
      (triangleStraighteningHomotopy x) := by
  intro smp i
  ext u
  change
    triangleStraighteningHomotopy x smp (u.1, FirstHurewicz.simplexFace 1 i u.2) =
      smp (FirstHurewicz.simplexFace 1 i u.2)
  exact
    triangleStraighteningHomotopy_boundary x smp u.1 _
      ⟨i, FirstHurewicz.simplexFace_apply_self 1 i u.2⟩

def ThirdHurewicz.threeSimplexBoundary : Set (FirstHurewicz.Simplex 3) :=
  {s | ∃ i, s i = 0}

def ThirdHurewicz.BasedThreeSimplex {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 3, X) // ∀ s ∈ threeSimplexBoundary, τ s = x }

def ThirdHurewicz.threeSimplexQuotient : C(Fin 3 → (unitInterval), FirstHurewicz.Simplex 3)
    where
  toFun
    u :=
    ⟨![1 - (u 0 : ℝ), (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        Min.min (u 0 : ℝ) (u 1 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)),
        Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ))],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (u 0).property.2
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_min_left _ (min_le_left _ _))
        · exact le_min (u 0).property.1 (le_min (u 1).property.1 (u 2).property.1)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem ThirdHurewicz.threeSimplexQuotient_zero (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 0 = 1 - (u 0 : ℝ) :=
  rfl

@[simp]
theorem ThirdHurewicz.threeSimplexQuotient_one (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) :=
  rfl

@[simp]
theorem ThirdHurewicz.threeSimplexQuotient_two (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 2 =
      Min.min (u 0 : ℝ) (u 1 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
  rfl

@[simp]
theorem ThirdHurewicz.threeSimplexQuotient_three (u : Fin 3 → (unitInterval)) :
    threeSimplexQuotient u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
  rfl

theorem ThirdHurewicz.threeSimplexQuotient_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : threeSimplexQuotient u ∈ threeSimplexBoundary := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      exact min_eq_left (le_min (u 1).property.1 (u 2).property.1)
    · change u 1 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      change Min.min (u 0 : ℝ) (Min.min (0 : ℝ) (u 2 : ℝ)) = 0
      rw [min_eq_left (u 2).property.1]
      exact min_eq_right (u 0).property.1
    · change u 2 = 0 at hi
      refine ⟨3, ?_⟩
      rw [threeSimplexQuotient_three, hi]
      change Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (0 : ℝ)) = 0
      rw [min_eq_right (u 1).property.1]
      exact min_eq_right (u 0).property.1
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨0, ?_⟩
      rw [threeSimplexQuotient_zero, hi]
      norm_num
    · change u 1 = 1 at hi
      refine ⟨1, ?_⟩
      rw [threeSimplexQuotient_one, hi]
      change (u 0 : ℝ) - Min.min (u 0 : ℝ) (1 : ℝ) = 0
      rw [min_eq_left (u 0).property.2, sub_self]
    · change u 2 = 1 at hi
      refine ⟨2, ?_⟩
      rw [threeSimplexQuotient_two, hi]
      change Min.min (u 0 : ℝ) (u 1 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (1 : ℝ)) = 0
      rw [min_eq_left (u 1).property.2, sub_self]

theorem ThirdHurewicz.threeSimplexQuotient_boundary_of_first_le (u : Fin 3 → (unitInterval))
    (h : (u 0 : ℝ) ≤ u 1) : threeSimplexQuotient u ∈ threeSimplexBoundary :=
  ⟨1, by rw [threeSimplexQuotient_one, min_eq_left h, sub_self]⟩

theorem ThirdHurewicz.threeSimplexQuotient_boundary_of_second_le (u : Fin 3 → (unitInterval))
    (h : (u 1 : ℝ) ≤ u 2) : threeSimplexQuotient u ∈ threeSimplexBoundary :=
  ⟨2, by rw [threeSimplexQuotient_two, min_eq_left h, sub_self]⟩

def ThirdHurewicz.basedThreeSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp threeSimplexQuotient, fun u hu => τ.property _ (threeSimplexQuotient_boundary u hu)⟩

def ThirdHurewicz.basedThreeSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : Additive (π_ 3 X x) :=
  Additive.ofMul (⟦basedThreeSimplexLoop τ⟧ : π_ 3 X x)

theorem ThirdHurewicz.basedThreeSimplex_face {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) (i : Fin 4) :
    τ.val.comp (FirstHurewicz.simplexFace 2 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, FirstHurewicz.simplexFace_apply_self 2 i s⟩

def ThirdHurewicz.constantBasedThreeSimplex {X : Type} [TopologicalSpace X] (x : X) :
    BasedThreeSimplex x :=
  ⟨ContinuousMap.const (FirstHurewicz.Simplex 3) x, fun _ _ => rfl⟩

def ThirdHurewicz.triangleThreeSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3) :
    C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1) (triangleStraighteningHomotopy x)
    (triangleStraighteningHomotopy_face x) (triangleStraighteningHomotopy_zero x) smp

@[simp]
theorem ThirdHurewicz.triangleThreeSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (s : FirstHurewicz.Simplex 3) : triangleThreeSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem ThirdHurewicz.triangleThreeSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 (triangleStraighteningHomotopy x)
      (triangleThreeSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1) (triangleStraighteningHomotopy x)
    (triangleStraighteningHomotopy_face x) (triangleStraighteningHomotopy_zero x)

@[simp]
theorem ThirdHurewicz.triangleThreeSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    triangleThreeSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
  extendCoherentSimplexHomotopy_const (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 1)
    (triangleStraighteningHomotopy x) (triangleStraighteningHomotopy_face x)
    (triangleStraighteningHomotopy_zero x) x (triangleStraighteningHomotopy_const x)

def ThirdHurewicz.triangleFourSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy (triangleStraighteningHomotopy x)
    (triangleThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy_face x)
    (triangleThreeSimplexHomotopy_zero x) smp

theorem ThirdHurewicz.triangleFourSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3 (triangleThreeSimplexHomotopy x)
      (triangleFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (triangleStraighteningHomotopy x) (triangleThreeSimplexHomotopy x)
    (triangleThreeSimplexHomotopy_face x) (triangleThreeSimplexHomotopy_zero x)

theorem ThirdHurewicz.triangleThreeSimplexHomotopy_one_face {X : Type} [TopologicalSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (smp.comp (FirstHurewicz.simplexFace 2 i)) s = x)
    (i : Fin 4) :
    (SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 1).comp
        (FirstHurewicz.simplexFace 2 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  rw [SecondHurewicz.SimplyConnected.timeSlice_face (triangleThreeSimplexHomotopy_face x)]
  ext s
  exact triangleStraighteningHomotopy_one x (smp.comp (FirstHurewicz.simplexFace 2 i)) (h i) s

theorem ThirdHurewicz.triangleThreeSimplexHomotopy_one_boundary {X : Type} [TopologicalSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (smp.comp (FirstHurewicz.simplexFace 2 i)) s = x)
    (s : FirstHurewicz.Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ :=
    SecondHurewicz.SimplyConnected.simplexBoundary_exists_face 2
      (⟨s, hs⟩ : SecondHurewicz.SimplyConnected.SimplexBoundary 3)
  have he : FirstHurewicz.simplexFace 2 i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(FirstHurewicz.Simplex 2, X) => f t)
      (triangleThreeSimplexHomotopy_one_face x smp h i)

def ThirdHurewicz.triangleStraightenedThreeSimplex {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3)
    (h :
      ∀ i : Fin 4,
        ∀ s ∈ SecondHurewicz.SimplyConnected.triangleBoundary,
          (smp.comp (FirstHurewicz.simplexFace 2 i)) s = x) :
    BasedThreeSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 1,
    triangleThreeSimplexHomotopy_one_boundary x smp h⟩

def ThirdHurewicz.normalizedThreeSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 3) :
    BasedThreeSimplex x :=
  triangleStraightenedThreeSimplex x
    (SecondHurewicz.SimplyConnected.normalizedTetrahedronMap x smp)
    (SecondHurewicz.SimplyConnected.normalizedTetrahedronMap_face_boundary x smp)

def ThirdHurewicz.normalizedFourSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) : FirstHurewicz.SingularSimplex X 4 :=
  SecondHurewicz.SimplyConnected.timeSlice
    (triangleFourSimplexHomotopy x (edgeNormalizedFourSimplexMap x smp)) 1

theorem ThirdHurewicz.normalizedFourSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) :
    (normalizedFourSimplexMap x smp).comp (FirstHurewicz.simplexFace 3 i) =
      (normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i))).val := by
  change
    (SecondHurewicz.SimplyConnected.timeSlice
            (triangleFourSimplexHomotopy x (edgeNormalizedFourSimplexMap x smp)) 1).comp
        (FirstHurewicz.simplexFace 3 i) =
      _
  rw [SecondHurewicz.SimplyConnected.timeSlice_face (triangleFourSimplexHomotopy_face x),
    edgeNormalizedFourSimplexMap_face]
  rfl

theorem ThirdHurewicz.normalizedFourSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) :
    normalizedFourSimplexMap x smp (FirstHurewicz.simplexFace 3 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 3, X) => f s)
      (normalizedFourSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i))).property s hs)

def ThirdHurewicz.threeSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.Chains X 3 →ₗ[ℤ] Additive (π_ 3 X x) :=
  FirstHurewicz.chainLift X 3 fun smp => basedThreeSimplexClass (normalizedThreeSimplex x smp)

@[simp]
theorem ThirdHurewicz.threeSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    threeSimplexClassOperator x (FirstHurewicz.simplexChain X 3 smp) =
      basedThreeSimplexClass (normalizedThreeSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 3 _ smp

def ThirdHurewicz.straightenedThreeCycle {X : Type} [TopologicalSpace X]
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (SecondHurewicz.SimplyConnected.simplexEndpointOperator 3 H₃ 1 c.1)
    (by
      rw [SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary 2 H₂ H₃ h,
        SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 3
          c,
        map_zero])

theorem ThirdHurewicz.straightenedThreeCycle_boundary {X : Type} [TopologicalSpace X]
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H₃ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom
        (SecondHurewicz.SimplyConnected.simplexPrismOperator 3 H₃ c.1) =
      (straightenedThreeCycle H₂ H₃ h c).1 - c.1 := by
  rw [SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary 2 H₂ H₃ h,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero 3 H₃ h₀,
    SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 3 c,
    map_zero, sub_zero]
  rfl

theorem ThirdHurewicz.straightenedThreeCycle_class {X : Type} [TopologicalSpace X]
    (H₂ : FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H₃ smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (straightenedThreeCycle H₂ H₃ h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 3 _
        _).mpr
  exact
    ⟨SecondHurewicz.SimplyConnected.simplexPrismOperator 3 H₃ c.1,
      straightenedThreeCycle_boundary H₂ H₃ h h₀ c⟩

def ThirdHurewicz.normalizedThreeChain {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] : FirstHurewicz.Chains X 3 →ₗ[ℤ] FirstHurewicz.Chains X 3 :=
  FirstHurewicz.chainLift X 3 fun smp =>
    FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val

@[simp]
theorem ThirdHurewicz.normalizedThreeChain_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    normalizedThreeChain x (FirstHurewicz.simplexChain X 3 smp) =
      FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val :=
  FirstHurewicz.chainLift_simplex X 3 _ smp

theorem ThirdHurewicz.normalizedThreeChain_eq {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    normalizedThreeChain x =
      (SecondHurewicz.SimplyConnected.simplexEndpointOperator 3 (triangleThreeSimplexHomotopy x)
            1).comp
        ((SecondHurewicz.SimplyConnected.simplexEndpointOperator 3
              (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x) 1).comp
          (SecondHurewicz.SimplyConnected.simplexEndpointOperator 3
            (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3) 1)) := by
  apply FirstHurewicz.chainMap_ext X 3
  intro smp
  simp only [normalizedThreeChain_simplex, LinearMap.comp_apply,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex]
  rfl

def ThirdHurewicz.vertexNormalizedThreeCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  straightenedThreeCycle (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face x 2) c

theorem ThirdHurewicz.vertexNormalizedThreeCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (vertexNormalizedThreeCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c :=
  straightenedThreeCycle_class _ _
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face x 2)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_timeSlice_zero x 3) c

def ThirdHurewicz.edgeNormalizedThreeCycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  straightenedThreeCycle (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)
    (vertexNormalizedThreeCycle x c)

theorem ThirdHurewicz.edgeNormalizedThreeCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (edgeNormalizedThreeCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  have h₀ :
    ∀ smp,
      SecondHurewicz.SimplyConnected.timeSlice
          (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x smp) 0 =
        smp := by
    intro smp
    ext s
    exact SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x smp s
  exact
    (straightenedThreeCycle_class _ _
          (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x) h₀
          (vertexNormalizedThreeCycle x c)).trans
      (vertexNormalizedThreeCycle_class x c)

def ThirdHurewicz.normalizedThreeCycle {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  straightenedThreeCycle (triangleStraighteningHomotopy x) (triangleThreeSimplexHomotopy x)
    (triangleThreeSimplexHomotopy_face x) (edgeNormalizedThreeCycle x c)

@[simp]
theorem ThirdHurewicz.normalizedThreeCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    (normalizedThreeCycle x c).val = normalizedThreeChain x c.val := by
  rw [normalizedThreeChain_eq]
  rfl

theorem ThirdHurewicz.normalizedThreeCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (normalizedThreeCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  have h₀ :
    ∀ smp,
      SecondHurewicz.SimplyConnected.timeSlice (triangleThreeSimplexHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleThreeSimplexHomotopy_zero x smp s
  exact
    (straightenedThreeCycle_class _ _ (triangleThreeSimplexHomotopy_face x) h₀
          (edgeNormalizedThreeCycle x c)).trans
      (edgeNormalizedThreeCycle_class x c)

theorem ThirdHurewicz.basedThreeSimplex_boundary {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (FirstHurewicz.simplexChain X 3 τ.val) = 0 := by
  change (FirstHurewicz.singularComplex X).d 3 2 (FirstHurewicz.simplexChain X 3 τ.val) = 0
  rw [FirstHurewicz.boundary_simplex]
  simp [basedThreeSimplex_face, Fin.sum_univ_succ]

def ThirdHurewicz.basedThreeSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : FirstHurewicz.Chains X 3 :=
  FirstHurewicz.simplexChain X 3 τ.val -
    FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)

theorem ThirdHurewicz.basedThreeSimplexChain_boundary {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (basedThreeSimplexChain τ) = 0 := by
  rw [basedThreeSimplexChain, map_sub, basedThreeSimplex_boundary]
  have hc := basedThreeSimplex_boundary (constantBasedThreeSimplex x)
  change
    ((FirstHurewicz.singularComplex X).d 3 2).hom
        (FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)) =
      0 at hc
  rw [hc, sub_self]

def ThirdHurewicz.basedThreeSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (basedThreeSimplexChain τ) (basedThreeSimplexChain_boundary τ)

@[simp]
theorem ThirdHurewicz.basedThreeSimplexCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    (basedThreeSimplexCycle τ).val =
      FirstHurewicz.simplexChain X 3 τ.val -
        FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) :=
  rfl

def ThirdHurewicz.thirdHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*} [AddCommGroup M]
    [Module ℤ M] (F : FirstHurewicz.Chains X 3 →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X 4, F (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X 3 →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (FirstHurewicz.singularComplex X) 3
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3).subtype)
    (fun b => hF b)

@[simp]
theorem ThirdHurewicz.thirdHomologyDesc_cycleClass {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : FirstHurewicz.Chains X 3 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 4, F (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    thirdHomologyDesc F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (FirstHurewicz.singularComplex X) 3 _ _ c

theorem ThirdHurewicz.comp_thirdHomologyDesc_eq_id {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (F : FirstHurewicz.Chains X 3 →ₗ[ℤ] M)
    (hF : ∀ b : FirstHurewicz.Chains X 4, F (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c) :
    g.comp (thirdHomologyDesc F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (FirstHurewicz.singularComplex X) 3
  intro c
  simpa only [LinearMap.comp_apply, thirdHomologyDesc_cycleClass, LinearMap.id_apply] using hg c

def ThirdHurewicz.constantThreeChain {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains X 3 :=
  FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)

def ThirdHurewicz.constantFourChain {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains X 4 :=
  FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x)

theorem ThirdHurewicz.boundaryThree_constantThreeChain {X : Type} [TopologicalSpace X] (x : X) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (constantThreeChain x) = 0 := by
  rw [constantThreeChain, FirstHurewicz.boundary_simplex]
  change
    (∑ i : Fin 4,
        (-1 : ℤ) ^ i.val •
          FirstHurewicz.simplexChain X 2 (ContinuousMap.const (FirstHurewicz.Simplex 2) x)) =
      0
  simp [Fin.sum_univ_succ]

theorem ThirdHurewicz.boundaryFour_constantFourChain {X : Type} [TopologicalSpace X] (x : X) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom (constantFourChain x) = constantThreeChain x := by
  rw [constantFourChain, FirstHurewicz.boundary_simplex]
  change (∑ i : Fin 5, (-1 : ℤ) ^ i.val • constantThreeChain x) = constantThreeChain x
  simp [Fin.sum_univ_succ]

def ThirdHurewicz.constantThreeCycle {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (constantThreeChain x) (boundaryThree_constantThreeChain x)

@[simp]
theorem ThirdHurewicz.constantThreeCycle_val {X : Type} [TopologicalSpace X] (x : X) :
    (constantThreeCycle x).1 = constantThreeChain x :=
  rfl

@[simp]
theorem ThirdHurewicz.constantThreeCycle_class {X : Type} [TopologicalSpace X] (x : X) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (constantThreeCycle x) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        3 _).mpr
  exact ⟨constantFourChain x, boundaryFour_constantFourChain x⟩

def ThirdHurewicz.normalizedThreeSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.Chains X 3 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  FirstHurewicz.chainLift X 3 fun smp => basedThreeSimplexCycle (normalizedThreeSimplex x smp)

@[simp]
theorem ThirdHurewicz.normalizedThreeSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    normalizedThreeSimplexCycleOperator x (FirstHurewicz.simplexChain X 3 smp) =
      basedThreeSimplexCycle (normalizedThreeSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 3 _ smp

theorem ThirdHurewicz.normalizedThreeSimplexCycleOperator_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (c : FirstHurewicz.Chains X 3) :
    (normalizedThreeSimplexCycleOperator x c).val =
      FirstHurewicz.chainLift X 3
        (fun smp =>
          FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val -
            FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3).subtype.comp
        (normalizedThreeSimplexCycleOperator x) =
      FirstHurewicz.chainLift X 3
        (fun smp =>
          FirstHurewicz.simplexChain X 3 (normalizedThreeSimplex x smp).val -
            FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)) := by
    apply FirstHurewicz.chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, normalizedThreeSimplexCycleOperator_simplex,
      Submodule.subtype_apply, basedThreeSimplexCycle_val, FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

theorem ThirdHurewicz.normalizedThreeSimplexCycleOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    normalizedThreeSimplexCycleOperator x c.val =
      normalizedThreeCycle x c -
        SecondHurewicz.SimplyConnected.chainAugmentation X 3 c.val • constantThreeCycle x := by
  apply Subtype.ext
  change
    (normalizedThreeSimplexCycleOperator x c.val).val =
      (normalizedThreeCycle x c).val -
        SecondHurewicz.SimplyConnected.chainAugmentation X 3 c.val • (constantThreeCycle x).val
  rw [normalizedThreeSimplexCycleOperator_val,
    SecondHurewicz.SimplyConnected.chainLift_sub_constant, normalizedThreeCycle_val,
    constantThreeCycle_val]
  rfl

theorem ThirdHurewicz.normalizedThreeSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (normalizedThreeSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  rw [normalizedThreeSimplexCycleOperator_cycle, map_sub, map_zsmul, constantThreeCycle_class,
    zsmul_zero, sub_zero, normalizedThreeCycle_class]

abbrev ThirdHurewicz.Geometry.Cube3 :=
  Fin 3 → (unitInterval)

def ThirdHurewicz.Geometry.cubeAffineSimplex {n : ℕ} (v : Fin (n + 1) → Cube3) :
    C(FirstHurewicz.Simplex n, Cube3)
    where
  toFun s
    i :=
    ⟨∑ j, s j * (v j i : ℝ), by
      constructor
      · exact Finset.sum_nonneg fun j _ => mul_nonneg (stdSimplex.zero_le s j) (v j i).property.1
      · calc
          ∑ j, s j * (v j i : ℝ) ≤ ∑ j, s j * 1 :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (v j i).property.2 (stdSimplex.zero_le s j)
          _ = 1 := by simp only [mul_one, stdSimplex.sum_eq_one]⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact
      continuous_finsetSum _ fun j _ =>
        ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

@[simp]
theorem ThirdHurewicz.Geometry.cubeAffineSimplex_coordinate {n : ℕ} (v : Fin (n + 1) → Cube3)
    (s : FirstHurewicz.Simplex n) (i : Fin 3) :
    (cubeAffineSimplex v s i : ℝ) = ∑ j, s j * (v j i : ℝ) :=
  rfl

theorem ThirdHurewicz.Geometry.cubeAffineSimplex_face {n : ℕ} (v : Fin (n + 2) → Cube3)
    (i : Fin (n + 2)) :
    (cubeAffineSimplex v).comp (FirstHurewicz.simplexFace n i) =
      cubeAffineSimplex (fun j => v (i.succAbove j)) := by
  ext s k
  change
    (∑ j : Fin (n + 2), FirstHurewicz.simplexFace n i s j * (v j k : ℝ)) =
      ∑ j : Fin (n + 1), s j * (v (i.succAbove j) k : ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [FirstHurewicz.simplexFace_apply_self, MulZeroClass.zero_mul,
    FirstHurewicz.simplexFace_apply_succAbove, zero_add]

theorem ThirdHurewicz.Geometry.cubeAffineSimplex_constant_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (i : Fin 3) (c : (unitInterval)) (h : ∀ j, v j i = c)
    (s : FirstHurewicz.Simplex n) : cubeAffineSimplex v s i = c := by
  apply Subtype.ext
  simp only [cubeAffineSimplex_coordinate, h, ← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

def ThirdHurewicz.Geometry.cubeVertex (e : Equiv.Perm (Fin 3)) (k : Fin 4) : Cube3 := fun i =>
  if (e.symm i).val < k.val then 1 else 0

def ThirdHurewicz.Geometry.cubeTetrahedron (e : Equiv.Perm (Fin 3)) :
    C(FirstHurewicz.Simplex 3, Cube3) :=
  cubeAffineSimplex (cubeVertex e)

@[simp]
theorem ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : (cubeTetrahedron e s (e 0) : ℝ) = s 1 + s 2 + s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ, add_assoc]

@[simp]
theorem ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : (cubeTetrahedron e s (e 1) : ℝ) = s 2 + s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ]

@[simp]
theorem ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : (cubeTetrahedron e s (e 2) : ℝ) = s 3 := by
  simp [cubeTetrahedron, cubeAffineSimplex_coordinate, cubeVertex, Fin.sum_univ_succ]

theorem ThirdHurewicz.Geometry.cubeTetrahedron_order_first (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : cubeTetrahedron e s (e 1) ≤ cubeTetrahedron e s (e 0) := by
  change (cubeTetrahedron e s (e 1) : ℝ) ≤ (cubeTetrahedron e s (e 0) : ℝ)
  rw [cubeTetrahedron_coordinate_one, cubeTetrahedron_coordinate_zero]
  linarith [stdSimplex.zero_le s 1]

theorem ThirdHurewicz.Geometry.cubeTetrahedron_order_second (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) : cubeTetrahedron e s (e 2) ≤ cubeTetrahedron e s (e 1) := by
  change (cubeTetrahedron e s (e 2) : ℝ) ≤ (cubeTetrahedron e s (e 1) : ℝ)
  rw [cubeTetrahedron_coordinate_two, cubeTetrahedron_coordinate_one]
  exact le_add_of_nonneg_left (stdSimplex.zero_le s 2)

theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_coordinate (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 0 s) (e 0) = 1 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (FirstHurewicz.simplexFace 2 0)) s (e 0) = 1
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  fin_cases j <;> simp [cubeVertex, Fin.succAbove]

theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_three_coordinate (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 3 s) (e 2) = 0 := by
  change ((cubeAffineSimplex (cubeVertex e)).comp (FirstHurewicz.simplexFace 2 3)) s (e 2) = 0
  rw [cubeAffineSimplex_face]
  apply cubeAffineSimplex_constant_coordinate
  intro j
  fin_cases j <;> simp [cubeVertex, Fin.succAbove]

theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_boundary (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 0 s) ∈ Cube.boundary (Fin 3) :=
  ⟨e 0, Or.inr (cubeTetrahedron_face_zero_coordinate e s)⟩

theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_three_boundary (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 2) :
    cubeTetrahedron e (FirstHurewicz.simplexFace 2 3 s) ∈ Cube.boundary (Fin 3) :=
  ⟨e 2, Or.inl (cubeTetrahedron_face_three_coordinate e s)⟩

theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_one_swap (e : Equiv.Perm (Fin 3)) :
    (cubeTetrahedron e).comp (FirstHurewicz.simplexFace 2 1) =
      (cubeTetrahedron ((Equiv.swap 0 1).trans e)).comp (FirstHurewicz.simplexFace 2 1) := by
  simp only [cubeTetrahedron, cubeAffineSimplex_face]
  congr 1
  funext j i
  obtain ⟨k, rfl⟩ := e.surjective i
  fin_cases j <;> fin_cases k <;> simp [cubeVertex, Equiv.swap_apply_def, Fin.succAbove]

theorem ThirdHurewicz.Geometry.cubeTetrahedron_face_two_swap (e : Equiv.Perm (Fin 3)) :
    (cubeTetrahedron e).comp (FirstHurewicz.simplexFace 2 2) =
      (cubeTetrahedron ((Equiv.swap 1 2).trans e)).comp (FirstHurewicz.simplexFace 2 2) := by
  simp only [cubeTetrahedron, cubeAffineSimplex_face]
  congr 1
  funext j i
  obtain ⟨k, rfl⟩ := e.surjective i
  fin_cases j <;> fin_cases k <;> simp [cubeVertex, Equiv.swap_apply_def, Fin.succAbove]

def ThirdHurewicz.Geometry.cubeOrientation (e : Equiv.Perm (Fin 3)) : ℤ :=
  Equiv.Perm.sign e

@[simp]
theorem ThirdHurewicz.Geometry.cubeOrientation_refl : cubeOrientation (Equiv.refl (Fin 3)) = 1 := by
  simp [cubeOrientation]

theorem ThirdHurewicz.Geometry.cubeOrientation_swap (e : Equiv.Perm (Fin 3)) {i j : Fin 3}
    (h : i ≠ j) : cubeOrientation ((Equiv.swap i j).trans e) = -cubeOrientation e := by
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap h]

theorem ThirdHurewicz.threeSimplex_coordinate_sum (s : FirstHurewicz.Simplex 3) :
    s 0 + (s 1 + s 2 + s 3) = 1 := by
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
  linarith

theorem ThirdHurewicz.threeSimplexQuotient_cubeTetrahedron_refl :
    threeSimplexQuotient.comp (Geometry.cubeTetrahedron (Equiv.refl (Fin 3))) =
      ContinuousMap.id (FirstHurewicz.Simplex 3) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  funext i
  have h₁ : s 2 + s 3 ≤ s 1 + s 2 + s 3 := by linarith [stdSimplex.zero_le s 1]
  have h₂ : s 3 ≤ s 2 + s 3 := le_add_of_nonneg_left (stdSimplex.zero_le s 2)
  have h₃ : s 3 ≤ s 1 + s 2 + s 3 := h₂.trans h₁
  have hu₀ := Geometry.cubeTetrahedron_coordinate_zero (Equiv.refl (Fin 3)) s
  have hu₁ := Geometry.cubeTetrahedron_coordinate_one (Equiv.refl (Fin 3)) s
  have hu₂ := Geometry.cubeTetrahedron_coordinate_two (Equiv.refl (Fin 3)) s
  change (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) = _ at hu₀
  change (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) = _ at hu₁
  change (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ) = _ at hu₂
  fin_cases i
  · change 1 - (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) = s 0
    rw [hu₀]
    linarith [threeSimplex_coordinate_sum s]
  · change
      (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ) -
          Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
            (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) =
        s 1
    rw [hu₀, hu₁, min_eq_right h₁]
    ring
  · change
      Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
            (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ) -
          Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
            (Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ)
              (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ)) =
        s 2
    rw [hu₀, hu₁, hu₂, min_eq_right h₁, min_eq_right h₂, min_eq_right h₃]
    ring
  · change
      Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 0 : ℝ)
          (Min.min (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 1 : ℝ)
            (Geometry.cubeTetrahedron (Equiv.refl (Fin 3)) s 2 : ℝ)) =
        s 3
    rw [hu₀, hu₁, hu₂, min_eq_right h₂, min_eq_right h₃]

theorem ThirdHurewicz.cubeTetrahedron_coordinates_antitone (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) :
    Antitone (fun i => (Geometry.cubeTetrahedron e s (e i) : ℝ)) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  fin_cases i
  · exact Geometry.cubeTetrahedron_order_first e s
  · exact Geometry.cubeTetrahedron_order_second e s

theorem ThirdHurewicz.cubeTetrahedron_coordinate_inversion (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (s : FirstHurewicz.Simplex 3) :
    (Geometry.cubeTetrahedron e s 0 : ℝ) ≤ Geometry.cubeTetrahedron e s 1 ∨
      (Geometry.cubeTetrahedron e s 1 : ℝ) ≤ Geometry.cubeTetrahedron e s 2 := by
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  have hu : StrictAnti (fun i => (Geometry.cubeTetrahedron e s i : ℝ)) := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    fin_cases i
    · exact lt_of_not_ge h₁
    · exact lt_of_not_ge h₂
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (cubeTetrahedron_coordinates_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

theorem ThirdHurewicz.threeSimplexQuotient_cubeTetrahedron_boundary (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (s : FirstHurewicz.Simplex 3) :
    threeSimplexQuotient (Geometry.cubeTetrahedron e s) ∈ threeSimplexBoundary := by
  rcases cubeTetrahedron_coordinate_inversion e he s with h | h
  · exact threeSimplexQuotient_boundary_of_first_le _ h
  · exact threeSimplexQuotient_boundary_of_second_le _ h

theorem ThirdHurewicz.basedThreeSimplexLoop_cubeTetrahedron_refl {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron (Equiv.refl (Fin 3))) = τ.val := by
  change (τ.val.comp threeSimplexQuotient).comp _ = _
  rw [ContinuousMap.comp_assoc, threeSimplexQuotient_cubeTetrahedron_refl, ContinuousMap.comp_id]

theorem ThirdHurewicz.basedThreeSimplexLoop_cubeTetrahedron_other {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) (e : Equiv.Perm (Fin 3)) (he : e ≠ Equiv.refl (Fin 3)) :
    (basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron e) =
      ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (threeSimplexQuotient_cubeTetrahedron_boundary e he s)

theorem ThirdHurewicz.threeCubeOrientation_sum :
    ∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e = 0 := by
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin 3) 1)) Geometry.cubeOrientation
  change
    (∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation ((Equiv.swap 0 1).trans e)) =
      ∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e at h
  simp_rw [Geometry.cubeOrientation_swap _ (by decide : (0 : Fin 3) ≠ 1)] at h
  rw [Finset.sum_neg_distrib] at h
  omega

theorem ThirdHurewicz.basedThreeSimplex_tetrahedronChain_sum {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    (∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e •
          FirstHurewicz.simplexChain X 3
            ((basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron e))) =
      basedThreeSimplexChain τ := by
  classical
  let c := FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)
  have heq (e : Equiv.Perm (Fin 3)) :
    Geometry.cubeOrientation e •
        FirstHurewicz.simplexChain X 3
          ((basedThreeSimplexLoop τ).val.comp (Geometry.cubeTetrahedron e)) =
      (if e = Equiv.refl (Fin 3) then basedThreeSimplexChain τ else 0) +
        Geometry.cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin 3)
    · subst e
      rw [basedThreeSimplexLoop_cubeTetrahedron_refl, Geometry.cubeOrientation_refl, one_smul,
        if_pos rfl, one_smul]
      change FirstHurewicz.simplexChain X 3 τ.val = (FirstHurewicz.simplexChain X 3 τ.val - c) + c
      abel
    · rw [basedThreeSimplexLoop_cubeTetrahedron_other τ e he, if_neg he, zero_add]
  calc
    _ =
        ∑ e : Equiv.Perm (Fin 3),
          ((if e = Equiv.refl (Fin 3) then basedThreeSimplexChain τ else 0) +
            Geometry.cubeOrientation e • c) :=
      Finset.sum_congr rfl (fun e _ => heq e)
    _ = basedThreeSimplexChain τ + (∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e) • c := by
      rw [Finset.sum_add_distrib]
      have hc :
        (∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin 3), Geometry.cubeOrientation e • c := by
        let f : ℤ →+ FirstHurewicz.Chains X 3 :=
          { toFun := fun n => n • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f Geometry.cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = basedThreeSimplexChain τ := by rw [threeCubeOrientation_sum, zero_smul, add_zero]

abbrev ThirdHurewicz.Remaining :=
  { j : Fin 3 // j ≠ 0 }

def ThirdHurewicz.remainingCoordinates : C(Fin 2 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
theorem ThirdHurewicz.remainingCoordinates_succ (u : Fin 2 → (unitInterval)) (i : Fin 2) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

theorem ThirdHurewicz.remainingCoordinates_boundary {u : Fin 2 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 2)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

abbrev ThirdHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

def ThirdHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 2 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

theorem ThirdHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 2 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 2)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

theorem ThirdHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] (x : X)
    (f : C((unitInterval), Fin 2 → (unitInterval))) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × (unitInterval)) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

def ThirdHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 2 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 3) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem ThirdHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 2 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem ThirdHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 2 → (unitInterval)))
    (i : Fin 2) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

def ThirdHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    C((unitInterval) × (Fin 2 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

theorem ThirdHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 3) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 2 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.squareSideLeft (t : (unitInterval)) :
    C((unitInterval), Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.squareSideRight (t : (unitInterval)) :
    C((unitInterval), Fin 2 → (unitInterval)) :=
  SecondHurewicz.squareCoordinates.comp (PeriodTorusHigherHomology.crossInsertRight t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.squareSideLeft_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (s : (unitInterval)) : squareSideLeft t s ∈ Cube.boundary (Fin 2) := by
  refine ⟨0, ?_⟩
  change
    SecondHurewicz.squareCoordinates (t, s) 0 = 0 ∨ SecondHurewicz.squareCoordinates (t, s) 0 = 1
  simpa only [SecondHurewicz.squareCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.squareSideRight_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (s : (unitInterval)) : squareSideRight t s ∈ Cube.boundary (Fin 2) := by
  refine ⟨1, ?_⟩
  change
    SecondHurewicz.squareCoordinates (s, t) 1 = 0 ∨ SecondHurewicz.squareCoordinates (s, t) 1 = 1
  simpa only [SecondHurewicz.squareCoordinates_one] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.fundamentalSquareChain_boundary :
    FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval)) SecondHurewicz.fundamentalSquareChain =
      FirstHurewicz.inducedChain (squareSideLeft 1) 1 SecondHurewicz.intervalChain -
          FirstHurewicz.inducedChain (squareSideLeft 0) 1 SecondHurewicz.intervalChain -
        (FirstHurewicz.inducedChain (squareSideRight 1) 1 SecondHurewicz.intervalChain -
          FirstHurewicz.inducedChain (squareSideRight 0) 1 SecondHurewicz.intervalChain) := by
  change
    ((FirstHurewicz.singularComplex (Fin 2 → (unitInterval))).d 2 1).hom
        (FirstHurewicz.inducedChain SecondHurewicz.squareCoordinates 2
          SecondHurewicz.productSquareChain) =
      _
  rw [← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain SecondHurewicz.squareCoordinates 1
        (FirstHurewicz.boundaryTwo ((unitInterval) × (unitInterval))
          SecondHurewicz.productSquareChain) =
      _
  rw [SecondHurewicz.productSquareChain_boundary]
  simp only [map_sub, squareSideLeft, squareSideRight, FirstHurewicz.inducedChain_comp,
    LinearMap.comp_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.evaluated_edge_boundaryMap {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (f : C((unitInterval), Fin 2 → (unitInterval))) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 1
          a (FirstHurewicz.inducedChain f 1 SecondHurewicz.intervalChain)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × (unitInterval)) x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (unitInterval) 1 a
          SecondHurewicz.intervalChain) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f 1 a
      SecondHurewicz.intervalChain
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 2).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 2))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.evaluated_triangle_boundaryMap {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2)
    (f : C((unitInterval), Fin 2 → (unitInterval))) (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 2 → (unitInterval)) 1 a
          (FirstHurewicz.inducedChain f 1 SecondHurewicz.intervalChain)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × (unitInterval)) x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (unitInterval) 1 a
          SecondHurewicz.intervalChain) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      1 a SecondHurewicz.intervalChain
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 3).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 3))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.evaluated_edge_squareBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 1
          a
          (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
            SecondHurewicz.fundamentalSquareChain)) =
      0 := by
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a (squareSideLeft t) (squareSideLeft_boundary t ht)
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a (squareSideRight t) (squareSideRight_boundary t ht)
  simp only [fundamentalSquareChain_boundary, map_sub, hL 1 (Or.inr rfl), hL 0 (Or.inl rfl),
    hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.evaluated_triangle_squareBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 2 → (unitInterval)) 1 a
          (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
            SecondHurewicz.fundamentalSquareChain)) =
      0 := by
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a (squareSideLeft t) (squareSideLeft_boundary t ht)
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a (squareSideRight t) (squareSideRight_boundary t ht)
  simp only [fundamentalSquareChain_boundary, map_sub, hL 1 (Or.inr rfl), hL 0 (Or.inl rfl),
    hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 3 :=
  (FirstHurewicz.inducedChain (evaluation x) 3).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 2)
      SecondHurewicz.fundamentalSquareChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem ThirdHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 2
          a SecondHurewicz.fundamentalSquareChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 4 :=
  (FirstHurewicz.inducedChain (evaluation x) 4).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 2 → (unitInterval))
        2)
      SecondHurewicz.fundamentalSquareChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem ThirdHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 2 → (unitInterval)) 2 a SecondHurewicz.fundamentalSquareChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.boundaryThree_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 3 2).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 1]
  change
    FirstHurewicz.inducedChain (evaluation x) 2
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 2 → (unitInterval)) 2 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            SecondHurewicz.fundamentalSquareChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 1
            a
            (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
              SecondHurewicz.fundamentalSquareChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_squareBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.boundaryFour_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 1]
  change
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 2 → (unitInterval)) 2
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a)
            SecondHurewicz.fundamentalSquareChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 2 → (unitInterval)) 1 a
            (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
              SecondHurewicz.fundamentalSquareChain)) =
      _
  rw [map_add, evaluated_triangle_squareBoundary_cancel, add_zero]
  rfl

def ThirdHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 3
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryThree_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
theorem ThirdHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

def ThirdHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 3 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
    (pathCubeCycle x p)

theorem ThirdHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundaryFour_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem ThirdHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 3 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem ThirdHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
theorem ThirdHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        3 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryFour_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

theorem ThirdHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundaryFour_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem ThirdHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 3 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 2 → (unitInterval))) 3 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 2
    SecondHurewicz.intervalChain SecondHurewicz.fundamentalSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 3 → (unitInterval)) 3 :=
  FirstHurewicz.inducedChain cubeCoordinates 3 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 3) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 3 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 3) p).toContinuousMap (ContinuousMap.id (Fin 2 → (unitInterval))) 2
      SecondHurewicz.intervalChain SecondHurewicz.fundamentalSquareChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 3).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 3) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 2 → (unitInterval))))
            3))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    FirstHurewicz.Chains X 3 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 3) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 3 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 3 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 3).comp (FirstHurewicz.inducedChain cubeCoordinates 3))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 3) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : SingularMayerVietoris.SingularHomology X 3 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 3) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 3) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 3) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 3) (GenLoop.const : GenLoop (Fin 3) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem ThirdHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 3) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    GenLoop.toLoop (0 : Fin 3) (GenLoop.transAt (0 : Fin 3) p q) =
      (GenLoop.toLoop (0 : Fin 3) p).trans (GenLoop.toLoop (0 : Fin 3) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 3))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 3)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 3) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

def ThirdHurewicz.Geometry.cubeBitVertex (v : Fin 3 → Fin 2) : Cube3 := fun i =>
  FirstHurewicz.pathSimplex Path.id (SingularMayerVietoris.stdVertices 1 (v i))

@[simp]
theorem ThirdHurewicz.Geometry.cubeBitVertex_coordinate (v : Fin 3 → Fin 2) (i : Fin 3) :
    (cubeBitVertex v i : ℝ) = SingularMayerVietoris.stdVertices 1 (v i) 1 :=
  rfl

@[simp]
theorem ThirdHurewicz.Geometry.cubeBitVertex_zero (v : Fin 3 → Fin 2) {i : Fin 3} (h : v i = 0) :
    cubeBitVertex v i = 0 := by simp [cubeBitVertex, h, SingularMayerVietoris.stdVertices]

@[simp]
theorem ThirdHurewicz.Geometry.cubeBitVertex_one (v : Fin 3 → Fin 2) {i : Fin 3} (h : v i = 1) :
    cubeBitVertex v i = 1 := by simp [cubeBitVertex, h, SingularMayerVietoris.stdVertices]

def ThirdHurewicz.Geometry.cubeTrianglePrism (v : Fin 3 → Fin 2 × Fin 2) :
    C(FirstHurewicz.Simplex 1 × FirstHurewicz.Simplex 2, Cube3) :=
  ThirdHurewicz.cubeCoordinates.comp
    ((FirstHurewicz.pathSimplex Path.id).prodMap
      (SecondHurewicz.squareCoordinates.comp
        (SecondHurewicz.SimplyConnected.squareAffineTriangle v)))

theorem ThirdHurewicz.Geometry.affineSimplex_comp_selectedVertices {m n p : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p) (a : Fin (m + 1) → Fin (n + 1)) :
    (SingularMayerVietoris.affineSimplex v).comp
        (SingularMayerVietoris.affineSimplex
          (fun j => SingularMayerVietoris.stdVertices n (a j))) =
      SingularMayerVietoris.affineSimplex (fun j => v (a j)) := by
  rw [SingularMayerVietoris.affineSimplex_comp]
  congr 1
  funext j
  exact SingularMayerVietoris.affineSimplex_vertex v (a j)

theorem ThirdHurewicz.Geometry.cubeTrianglePrism_affine {n : ℕ} (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin (n + 1) → Fin 2 × Fin 3) :
    (cubeTrianglePrism v).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun j =>
            (SingularMayerVietoris.stdVertices 1 (w j).1,
              SingularMayerVietoris.stdVertices 2 (w j).2))) =
      cubeAffineSimplex (fun j => cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2]) := by
  ext s i
  fin_cases i
  · change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (w j).1) s
          1 =
        _
    rw [SingularMayerVietoris.affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]
  · change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).1)
          (SingularMayerVietoris.affineSimplex
            (fun j => SingularMayerVietoris.stdVertices 2 (w j).2) s)
          1 =
        _
    change
      ((SingularMayerVietoris.affineSimplex
                (fun j => SingularMayerVietoris.stdVertices 1 (v j).1)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices 2 (w j).2)))
          s 1 =
        _
    rw [affineSimplex_comp_selectedVertices, SingularMayerVietoris.affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]
  · change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).2)
          (SingularMayerVietoris.affineSimplex
            (fun j => SingularMayerVietoris.stdVertices 2 (w j).2) s)
          1 =
        _
    change
      ((SingularMayerVietoris.affineSimplex
                (fun j => SingularMayerVietoris.stdVertices 1 (v j).2)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices 2 (w j).2)))
          s 1 =
        _
    rw [affineSimplex_comp_selectedVertices, SingularMayerVietoris.affineSimplex_coordinate]
    simp [cubeAffineSimplex_coordinate, cubeBitVertex_coordinate]

theorem ThirdHurewicz.Geometry.cubeAffineSimplex_boundary_of_coordinate {n : ℕ}
    (v : Fin (n + 1) → Cube3) (i : Fin 3) (h : (∀ j, v j i = 0) ∨ (∀ j, v j i = 1))
    (s : FirstHurewicz.Simplex n) : cubeAffineSimplex v s ∈ Cube.boundary (Fin 3) := by
  rcases h with h | h
  · exact ⟨i, Or.inl (cubeAffineSimplex_constant_coordinate v i 0 h s)⟩
  · exact ⟨i, Or.inr (cubeAffineSimplex_constant_coordinate v i 1 h s)⟩

theorem ThirdHurewicz.Geometry.loop_comp_cubeAffineSimplex_of_coordinate {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin 3) X x) (v : Fin (n + 1) → Cube3)
    (i : Fin 3) (h : (∀ j, v j i = 0) ∨ (∀ j, v j i = 1)) :
    p.val.comp (cubeAffineSimplex v) = ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (cubeAffineSimplex_boundary_of_coordinate v i h s)

private theorem ThirdHurewicz.CubeSubdivision.formalEdgeCrossProduct_one_expansion_mo1973_7080
    {V W : Type*} (v : Fin 2 → V) (w : Fin 2 → W) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1)] -
            SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1)] -
          SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 1), (v 1, w 1)] +
        SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 1, w 0)] := by
  rw [PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    PeriodTorusHigherHomology.formalBoundary_edge_simplex]
  simp only [map_sub, PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex]
  have hv₀ : (fun i : Fin 2 => (v 0, w i)) = ![(v 0, w 0), (v 0, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun i : Fin 2 => (v 1, w i)) = ![(v 1, w 0), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  have hw₀ : (fun i : Fin 2 => (v i, w 0)) = ![(v 0, w 0), (v 1, w 0)] := by
    funext i
    fin_cases i <;> rfl
  have hw₁ : (fun i : Fin 2 => (v i, w 1)) = ![(v 0, w 1), (v 1, w 1)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv₀, hv₁, hw₀, hw₁]
  abel

theorem ThirdHurewicz.CubeSubdivision.formalBoundary_triangle_simplex {W : Type*}
    (w : Fin 3 → W) :
    SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex ![w 1, w 2] -
          SingularMayerVietoris.formalSimplex ![w 0, w 2] +
        SingularMayerVietoris.formalSimplex ![w 0, w 1] := by
  have h₀ : w ∘ (0 : Fin 3).succAbove = ![w 1, w 2] := by
    funext i
    fin_cases i <;> rfl
  have h₁ : w ∘ (1 : Fin 3).succAbove = ![w 0, w 2] := by
    funext i
    fin_cases i <;> rfl
  have h₂ : w ∘ (2 : Fin 3).succAbove = ![w 0, w 1] := by
    funext i
    fin_cases i <;> rfl
  rw [SingularMayerVietoris.formalBoundary_simplex]
  change
    (∑ i : Fin 3, (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (w ∘ i.succAbove)) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num only [Fin.val_zero, Fin.val_succ, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul]
  change
    SingularMayerVietoris.formalSimplex (w ∘ (0 : Fin 3).succAbove) +
        (-SingularMayerVietoris.formalSimplex (w ∘ (1 : Fin 3).succAbove) +
          SingularMayerVietoris.formalSimplex (w ∘ (2 : Fin 3).succAbove)) =
      _
  rw [h₀, h₁, h₂]
  abel

theorem ThirdHurewicz.CubeSubdivision.formalEdgeCrossProduct_two_expansion {V W : Type*}
    (v : Fin 2 → V) (w : Fin 3 → W) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct 2 (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 1, w 0), (v 1, w 1), (v 1, w 2)] -
                            SingularMayerVietoris.formalSimplex
                              ![(v 0, w 0), (v 0, w 1), (v 1, w 1), (v 1, w 2)] +
                          SingularMayerVietoris.formalSimplex
                            ![(v 0, w 0), (v 0, w 1), (v 0, w 2), (v 1, w 2)] -
                        SingularMayerVietoris.formalSimplex
                          ![(v 0, w 0), (v 0, w 0), (v 0, w 1), (v 0, w 2)] +
                      SingularMayerVietoris.formalSimplex
                        ![(v 0, w 0), (v 0, w 1), (v 0, w 1), (v 0, w 2)] -
                    SingularMayerVietoris.formalSimplex
                      ![(v 0, w 0), (v 0, w 1), (v 0, w 1), (v 1, w 1)] +
                  SingularMayerVietoris.formalSimplex
                    ![(v 0, w 0), (v 0, w 0), (v 1, w 0), (v 1, w 2)] -
                SingularMayerVietoris.formalSimplex
                  ![(v 0, w 0), (v 0, w 0), (v 0, w 0), (v 0, w 2)] -
              SingularMayerVietoris.formalSimplex
                ![(v 0, w 0), (v 0, w 0), (v 0, w 2), (v 1, w 2)] -
            SingularMayerVietoris.formalSimplex
              ![(v 0, w 0), (v 0, w 0), (v 1, w 0), (v 1, w 1)] +
          SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 0), (v 0, w 1)] +
        SingularMayerVietoris.formalSimplex ![(v 0, w 0), (v 0, w 0), (v 0, w 1), (v 1, w 1)] := by
  rw [PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary,
    formalBoundary_triangle_simplex]
  simp only [map_add, map_sub, formalEdgeCrossProduct_one_expansion_mo1973_7080,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex]
  have hv₀ : (fun i : Fin 3 => (v 0, w i)) = ![(v 0, w 0), (v 0, w 1), (v 0, w 2)] := by
    funext i
    fin_cases i <;> rfl
  have hv₁ : (fun i : Fin 3 => (v 1, w i)) = ![(v 1, w 0), (v 1, w 1), (v 1, w 2)] := by
    funext i
    fin_cases i <;> rfl
  simp only [Function.comp_def, hv₀, hv₁, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.Fin.cons_vecCons]
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.CubeSubdivision.prismSimplex (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) : C(FirstHurewicz.Simplex 3, ThirdHurewicz.Geometry.Cube3) :=
  ThirdHurewicz.Geometry.cubeAffineSimplex
    (fun j => ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2])

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.CubeSubdivision.prismSimplexChain (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) : FirstHurewicz.Chains ThirdHurewicz.Geometry.Cube3 3 :=
  FirstHurewicz.simplexChain ThirdHurewicz.Geometry.Cube3 3 (prismSimplex v w)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.CubeSubdivision.prismRealization (v : Fin 3 → Fin 2 × Fin 2) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin 3) 4 →ₗ[ℤ]
      FirstHurewicz.Chains ThirdHurewicz.Geometry.Cube3 3 :=
  (FirstHurewicz.inducedChain (ThirdHurewicz.Geometry.cubeTrianglePrism v) 3).comp
    ((PeriodTorusHigherHomology.productAffineChainMap 1 2 3).comp
      (SingularMayerVietoris.formalMap
        (fun z : Fin 2 × Fin 3 =>
          (SingularMayerVietoris.stdVertices 1 z.1, SingularMayerVietoris.stdVertices 2 z.2))
        4))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem ThirdHurewicz.CubeSubdivision.prismRealization_simplex (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) :
    prismRealization v (SingularMayerVietoris.formalSimplex w) = prismSimplexChain v w := by
  simp only [prismRealization, LinearMap.comp_apply, SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex]
  change
    FirstHurewicz.simplexChain ThirdHurewicz.Geometry.Cube3 3
        ((ThirdHurewicz.Geometry.cubeTrianglePrism v).comp
          (PeriodTorusHigherHomology.productAffineSimplex
            (fun j =>
              (SingularMayerVietoris.stdVertices 1 (w j).1,
                SingularMayerVietoris.stdVertices 2 (w j).2)))) =
      _
  rw [ThirdHurewicz.Geometry.cubeTrianglePrism_affine]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def ThirdHurewicz.CubeSubdivision.intervalTriangleChain (v : Fin 3 → Fin 2 × Fin 2) :
    FirstHurewicz.Chains ThirdHurewicz.Geometry.Cube3 3 :=
  FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 3
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 2
      SecondHurewicz.intervalChain
      (FirstHurewicz.inducedChain SecondHurewicz.squareCoordinates 2
        (FirstHurewicz.simplexChain ((unitInterval) × (unitInterval)) 2
          (SecondHurewicz.SimplyConnected.squareAffineTriangle v))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.CubeSubdivision.intervalTriangleChain_eq_prismRealization
    (v : Fin 3 → Fin 2 × Fin 2) :
    intervalTriangleChain v =
      prismRealization v
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 2
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 3 => j))) := by
  have h :=
    PeriodTorusHigherHomology.formalMap_edgeCrossProduct (SingularMayerVietoris.stdVertices 1)
      (SingularMayerVietoris.stdVertices 2) 2
      (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
      (SingularMayerVietoris.formalSimplex (fun j : Fin 3 => j))
  simp only [SingularMayerVietoris.formalMap_simplex, Function.comp_def] at h
  rw [intervalTriangleChain, FirstHurewicz.inducedChain_simplex, SecondHurewicz.intervalChain,
    FirstHurewicz.pathChain, PeriodTorusHigherHomology.crossProductEdge_simplex]
  change
    ((FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 3).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (SecondHurewicz.squareCoordinates.comp
                (SecondHurewicz.SimplyConnected.squareAffineTriangle v)))
            3))
        (PeriodTorusHigherHomology.productAffineChainMap 1 2 3
          (PeriodTorusHigherHomology.formalEdgeCrossProduct 2
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2)))) =
      _
  rw [← FirstHurewicz.inducedChain_comp, ← h]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.CubeSubdivision.intervalTriangleChain_twelve_tetrahedra
    (v : Fin 3 → Fin 2 × Fin 2) :
    intervalTriangleChain v =
      prismSimplexChain v ![(0, 0), (1, 0), (1, 1), (1, 2)] -
                            prismSimplexChain v ![(0, 0), (0, 1), (1, 1), (1, 2)] +
                          prismSimplexChain v ![(0, 0), (0, 1), (0, 2), (1, 2)] -
                        prismSimplexChain v ![(0, 0), (0, 0), (0, 1), (0, 2)] +
                      prismSimplexChain v ![(0, 0), (0, 1), (0, 1), (0, 2)] -
                    prismSimplexChain v ![(0, 0), (0, 1), (0, 1), (1, 1)] +
                  prismSimplexChain v ![(0, 0), (0, 0), (1, 0), (1, 2)] -
                prismSimplexChain v ![(0, 0), (0, 0), (0, 0), (0, 2)] -
              prismSimplexChain v ![(0, 0), (0, 0), (0, 2), (1, 2)] -
            prismSimplexChain v ![(0, 0), (0, 0), (1, 0), (1, 1)] +
          prismSimplexChain v ![(0, 0), (0, 0), (0, 0), (0, 1)] +
        prismSimplexChain v ![(0, 0), (0, 0), (0, 1), (1, 1)] := by
  rw [intervalTriangleChain_eq_prismRealization]
  have h :=
    congrArg (prismRealization v)
      (formalEdgeCrossProduct_two_expansion (fun i : Fin 2 => i) (fun j : Fin 3 => j))
  simpa only [map_sub, map_add, prismRealization_simplex] using h

def ThirdHurewicz.Geometry.cubePermutation : Fin 6 → Equiv.Perm (Fin 3) :=
  ![1, Equiv.swap 1 2, Equiv.swap 0 1, (Equiv.swap 0 1).trans (Equiv.swap 1 2),
    (Equiv.swap 1 2).trans (Equiv.swap 0 1), Equiv.swap 0 2]

theorem ThirdHurewicz.Geometry.cubePermutation_injective : Function.Injective cubePermutation := by
  decide

theorem ThirdHurewicz.Geometry.cubePermutation_bijective : Function.Bijective cubePermutation := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨cubePermutation_injective, by norm_num [Fintype.card_perm, Nat.factorial]⟩

theorem ThirdHurewicz.Geometry.sum_cubePermutations {A : Type*} [AddCommMonoid A]
    (f : Equiv.Perm (Fin 3) → A) :
    ∑ e, f e =
      f 1 + f (Equiv.swap 1 2) + f (Equiv.swap 0 1) +
            f ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) +
          f ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) +
        f (Equiv.swap 0 2) := by
  rw [← cubePermutation_bijective.sum_comp f]
  simp [cubePermutation, Fin.sum_univ_succ, add_assoc]

theorem ThirdHurewicz.Geometry.cubeOrientation_cubePermutation (i : Fin 6) :
    cubeOrientation (cubePermutation i) = ![1, -1, -1, 1, 1, -1] i := by
  fin_cases i <;>
    simp [cubePermutation, cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap']

theorem ThirdHurewicz.Geometry.sum_oriented_cubePermutations {A : Type*} [AddCommGroup A]
    (f : Equiv.Perm (Fin 3) → A) :
    ∑ e, cubeOrientation e • f e =
      f 1 - f (Equiv.swap 1 2) - f (Equiv.swap 0 1) +
            f ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) +
          f ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) -
        f (Equiv.swap 0 2) := by
  rw [sum_cubePermutations]
  simp [cubeOrientation, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap', sub_eq_add_neg, add_assoc]

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_lower_zero :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron 1 := by
  change
    ThirdHurewicz.Geometry.cubeAffineSimplex _ =
      ThirdHurewicz.Geometry.cubeAffineSimplex
        (ThirdHurewicz.Geometry.cubeVertex (Equiv.refl (Fin 3)))
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices]

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_lower_one :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 1) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_lower_two :
    prismSimplex ![(0, 0), (1, 0), (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_upper_zero :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 1 2) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_upper_one :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 0 1).trans (Equiv.swap 1 2)) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_upper_two :
    prismSimplex ![(0, 0), (0, 1), (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)] =
      ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 2) := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j i
  fin_cases j <;> fin_cases i <;>
    simp [ThirdHurewicz.Geometry.cubeBitVertex, ThirdHurewicz.Geometry.cubeVertex,
      SingularMayerVietoris.stdVertices, Equiv.swap_apply_def]

theorem ThirdHurewicz.CubeSubdivision.loop_prismSimplex_of_coordinate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) (i : Fin 3)
    (h :
      (∀ j, ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 0) ∨
        (∀ j,
          ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x :=
  ThirdHurewicz.Geometry.loop_comp_cubeAffineSimplex_of_coordinate p _ i h

theorem ThirdHurewicz.CubeSubdivision.induced_prismSimplexChain_of_coordinate {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) (i : Fin 3)
    (h :
      (∀ j, ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 0) ∨
        (∀ j,
          ThirdHurewicz.Geometry.cubeBitVertex ![(w j).1, (v (w j).2).1, (v (w j).2).2] i = 1)) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain v w) =
      FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) := by
  rw [prismSimplexChain, FirstHurewicz.inducedChain_simplex,
    loop_prismSimplex_of_coordinate p v w i h]

theorem ThirdHurewicz.CubeSubdivision.loop_prismSimplex_of_fst {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : (∀ j, (v j).1 = 0) ∨ (∀ j, (v j).1 = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  apply loop_prismSimplex_of_coordinate p v w 1
  rcases h with h | h
  · exact Or.inl fun j => ThirdHurewicz.Geometry.cubeBitVertex_zero _ (i := 1) (h (w j).2)
  · exact Or.inr fun j => ThirdHurewicz.Geometry.cubeBitVertex_one _ (i := 1) (h (w j).2)

theorem ThirdHurewicz.CubeSubdivision.loop_prismSimplex_of_snd {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2) (w : Fin 4 → Fin 2 × Fin 3)
    (h : (∀ j, (v j).2 = 0) ∨ (∀ j, (v j).2 = 1)) :
    p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  apply loop_prismSimplex_of_coordinate p v w 2
  rcases h with h | h
  · exact Or.inl fun j => ThirdHurewicz.Geometry.cubeBitVertex_zero _ (i := 2) (h (w j).2)
  · exact Or.inr fun j => ThirdHurewicz.Geometry.cubeBitVertex_one _ (i := 2) (h (w j).2)

private theorem
  ThirdHurewicz.CubeSubdivision.induced_intervalTriangleChain_of_constant_mo1973_7106 {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (h : ∀ w, p.val.comp (prismSimplex v w) = ContinuousMap.const (FirstHurewicz.Simplex 3) x) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain v) = 0 := by
  rw [intervalTriangleChain_twelve_tetrahedra]
  simp only [map_add, map_sub, prismSimplexChain, FirstHurewicz.inducedChain_simplex, h]
  abel

theorem ThirdHurewicz.CubeSubdivision.induced_intervalTriangleChain_of_fst {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (h : (∀ j, (v j).1 = 0) ∨ (∀ j, (v j).1 = 1)) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain v) = 0 :=
  induced_intervalTriangleChain_of_constant_mo1973_7106 p v fun w =>
    loop_prismSimplex_of_fst p v w h

theorem ThirdHurewicz.CubeSubdivision.induced_intervalTriangleChain_of_snd {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (v : Fin 3 → Fin 2 × Fin 2)
    (h : (∀ j, (v j).2 = 0) ∨ (∀ j, (v j).2 = 1)) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain v) = 0 :=
  induced_intervalTriangleChain_of_constant_mo1973_7106 p v fun w =>
    loop_prismSimplex_of_snd p v w h

theorem ThirdHurewicz.CubeSubdivision.prismSimplex_endpoints_eq (b c : Fin 2 × Fin 2)
    (w : Fin 4 → Fin 2 × Fin 3) (h : ∀ j, (w j).2 = 0 ∨ (w j).2 = 2) :
    prismSimplex ![(0, 0), b, (1, 1)] w = prismSimplex ![(0, 0), c, (1, 1)] w := by
  apply congrArg ThirdHurewicz.Geometry.cubeAffineSimplex
  funext j
  rcases h j with hj | hj <;> simp [hj]

def ThirdHurewicz.CubeSubdivision.diagonalPrismPrincipal {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (b : Fin 2 × Fin 2) : FirstHurewicz.Chains X 3 :=
  FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (1, 0), (1, 1), (1, 2)]) -
      FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (0, 1), (1, 1), (1, 2)]) +
    FirstHurewicz.inducedChain p.val 3
      (prismSimplexChain ![(0, 0), b, (1, 1)] ![(0, 0), (0, 1), (0, 2), (1, 2)])

def ThirdHurewicz.CubeSubdivision.prismCommonCorrection {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : FirstHurewicz.Chains X 3 :=
  FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] ![(0, 0), (0, 0), (1, 0), (1, 2)]) -
      FirstHurewicz.inducedChain p.val 3
        (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] ![(0, 0), (0, 0), (0, 2), (1, 2)]) -
    FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x)

theorem ThirdHurewicz.CubeSubdivision.induced_diagonalPrism_eq_principal_add_correction {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (b : Fin 2 × Fin 2)
    (hb : b.1 = 0 ∨ b.2 = 0) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain ![(0, 0), b, (1, 1)]) =
      diagonalPrismPrincipal p b + prismCommonCorrection p := by
  have htime (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).1 = 0) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
      FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) := by
    apply induced_prismSimplexChain_of_coordinate p _ w 0
    left
    intro j
    simp [ThirdHurewicz.Geometry.cubeBitVertex, SingularMayerVietoris.stdVertices, hw j]
  have hside (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).2 = 0 ∨ (w j).2 = 1) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
      FirstHurewicz.simplexChain X 3 (ContinuousMap.const (FirstHurewicz.Simplex 3) x) := by
    rcases hb with hb | hb
    · apply induced_prismSimplexChain_of_coordinate p _ w 1
      left
      intro j
      rcases hw j with hj | hj <;>
        simp [ThirdHurewicz.Geometry.cubeBitVertex, SingularMayerVietoris.stdVertices, hj, hb]
    · apply induced_prismSimplexChain_of_coordinate p _ w 2
      left
      intro j
      rcases hw j with hj | hj <;>
        simp [ThirdHurewicz.Geometry.cubeBitVertex, SingularMayerVietoris.stdVertices, hj, hb]
  have hdiag (w : Fin 4 → Fin 2 × Fin 3) (hw : ∀ j, (w j).2 = 0 ∨ (w j).2 = 2) :
    FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), b, (1, 1)] w) =
      FirstHurewicz.inducedChain p.val 3 (prismSimplexChain ![(0, 0), (0, 0), (1, 1)] w) := by
    simp only [prismSimplexChain, prismSimplex_endpoints_eq b (0, 0) w hw]
  rw [intervalTriangleChain_twelve_tetrahedra]
  simp only [map_add, map_sub]
  rw [htime ![(0, 0), (0, 0), (0, 1), (0, 2)] (by intro j; fin_cases j <;> rfl),
    htime ![(0, 0), (0, 1), (0, 1), (0, 2)] (by intro j; fin_cases j <;> rfl),
    hside ![(0, 0), (0, 1), (0, 1), (1, 1)] (by intro j; fin_cases j <;> simp),
    hdiag ![(0, 0), (0, 0), (1, 0), (1, 2)] (by intro j; fin_cases j <;> simp),
    htime ![(0, 0), (0, 0), (0, 0), (0, 2)] (by intro j; fin_cases j <;> rfl),
    hdiag ![(0, 0), (0, 0), (0, 2), (1, 2)] (by intro j; fin_cases j <;> simp),
    hside ![(0, 0), (0, 0), (1, 0), (1, 1)] (by intro j; fin_cases j <;> simp),
    htime ![(0, 0), (0, 0), (0, 0), (0, 1)] (by intro j; fin_cases j <;> rfl),
    hside ![(0, 0), (0, 0), (0, 1), (1, 1)] (by intro j; fin_cases j <;> simp)]
  unfold diagonalPrismPrincipal prismCommonCorrection
  abel

theorem ThirdHurewicz.CubeSubdivision.induced_diagonalPrism_sub {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) :
    FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain ![(0, 0), (1, 0), (1, 1)]) -
        FirstHurewicz.inducedChain p.val 3 (intervalTriangleChain ![(0, 0), (0, 1), (1, 1)]) =
      diagonalPrismPrincipal p (1, 0) - diagonalPrismPrincipal p (0, 1) := by
  rw [induced_diagonalPrism_eq_principal_add_correction p (1, 0) (Or.inr rfl),
    induced_diagonalPrism_eq_principal_add_correction p (0, 1) (Or.inl rfl)]
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.CubeSubdivision.fundamentalCubeChain_four_prisms :
    ThirdHurewicz.fundamentalCubeChain =
      intervalTriangleChain ![(0, 0), (1, 0), (1, 1)] -
            intervalTriangleChain ![(0, 0), (0, 0), (0, 1)] -
          intervalTriangleChain ![(0, 0), (0, 1), (1, 1)] +
        intervalTriangleChain ![(0, 0), (0, 0), (1, 0)] := by
  rw [ThirdHurewicz.fundamentalCubeChain, ThirdHurewicz.productCubeChain,
    SecondHurewicz.fundamentalSquareChain,
    SecondHurewicz.SimplyConnected.productSquareChain_four_triangles]
  simp only [map_add, map_sub]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.CubeSubdivision.induced_fundamentalCubeChain_eq_principal {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) :
    FirstHurewicz.inducedChain p.val 3 ThirdHurewicz.fundamentalCubeChain =
      diagonalPrismPrincipal p (1, 0) - diagonalPrismPrincipal p (0, 1) := by
  rw [fundamentalCubeChain_four_prisms]
  simp only [map_add, map_sub]
  rw [induced_intervalTriangleChain_of_fst p ![(0, 0), (0, 0), (0, 1)]
      (Or.inl (by intro j; fin_cases j <;> rfl)),
    induced_intervalTriangleChain_of_snd p ![(0, 0), (0, 0), (1, 0)]
      (Or.inl (by intro j; fin_cases j <;> rfl)),
    sub_zero, add_zero]
  exact induced_diagonalPrism_sub p

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.CubeSubdivision.cubeChain_six_tetrahedra {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) :
    ThirdHurewicz.cubeChain p =
      FirstHurewicz.simplexChain X 3 (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron 1)) -
                FirstHurewicz.simplexChain X 3
                  (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 1))) +
              FirstHurewicz.simplexChain X 3
                (p.val.comp
                  (ThirdHurewicz.Geometry.cubeTetrahedron
                    ((Equiv.swap 1 2).trans (Equiv.swap 0 1)))) -
            FirstHurewicz.simplexChain X 3
              (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 1 2))) +
          FirstHurewicz.simplexChain X 3
            (p.val.comp
              (ThirdHurewicz.Geometry.cubeTetrahedron
                ((Equiv.swap 0 1).trans (Equiv.swap 1 2)))) -
        FirstHurewicz.simplexChain X 3
          (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron (Equiv.swap 0 2))) := by
  rw [ThirdHurewicz.cubeChain_eq_induced, induced_fundamentalCubeChain_eq_principal]
  simp only [diagonalPrismPrincipal, prismSimplexChain, FirstHurewicz.inducedChain_simplex,
    prismSimplex_lower_zero, prismSimplex_lower_one, prismSimplex_lower_two,
    prismSimplex_upper_zero, prismSimplex_upper_one, prismSimplex_upper_two]
  abel

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem ThirdHurewicz.CubeSubdivision.cubeChain_eq_sum_tetrahedra {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) :
    ThirdHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 3),
        ThirdHurewicz.Geometry.cubeOrientation e •
          FirstHurewicz.simplexChain X 3
            (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) := by
  rw [cubeChain_six_tetrahedra, ThirdHurewicz.Geometry.sum_oriented_cubePermutations]
  abel

def ThirdHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 3 X x → SingularMayerVietoris.SingularHomology X 3 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

def ThirdHurewicz.hurewiczPi3 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 3 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 3)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 3 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 3)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 3) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

def ThirdHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 3 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3
    where
  toFun := (hurewiczPi3 x).toAdditiveLeft
  map_add' := (hurewiczPi3 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi3 x).toAdditiveLeft ℤ ℤ n a

theorem ThirdHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 3) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 3 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (cubeCycle p) :=
  rfl

theorem ThirdHurewicz.cubeChain_basedThreeSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : cubeChain (basedThreeSimplexLoop τ) = basedThreeSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_tetrahedra, basedThreeSimplex_tetrahedronChain_sum]

theorem ThirdHurewicz.cubeCycle_basedThreeSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : cubeCycle (basedThreeSimplexLoop τ) = basedThreeSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedThreeSimplexLoop τ

theorem ThirdHurewicz.hurewicz_basedThreeSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    hurewiczMap x (basedThreeSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (basedThreeSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (cubeCycle (basedThreeSimplexLoop τ)) =
      _
  rw [cubeCycle_basedThreeSimplexLoop]

theorem ThirdHurewicz.hurewiczMap_comp_threeSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (hurewiczMap x).comp (threeSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3).comp
        (normalizedThreeSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 3
  intro smp
  simp only [LinearMap.comp_apply, threeSimplexClassOperator_simplex,
    normalizedThreeSimplexCycleOperator_simplex]
  exact hurewicz_basedThreeSimplexClass (normalizedThreeSimplex x smp)

theorem ThirdHurewicz.hurewiczMap_threeSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    hurewiczMap x (threeSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_threeSimplexClassOperator x) c.val
  change
    hurewiczMap x (threeSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3
        (normalizedThreeSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedThreeSimplexCycleOperator_class x c)

def ThirdHurewicz.fourSimplexTwoSkeleton : Set (FirstHurewicz.Simplex 4) :=
  {s | ∃ i j : Fin 5, i ≠ j ∧ s i = 0 ∧ s j = 0}

def ThirdHurewicz.BasedFourSimplex {X : Type} [TopologicalSpace X] (x : X) :=
  { τ : C(FirstHurewicz.Simplex 4, X) // ∀ s ∈ fourSimplexTwoSkeleton, τ s = x }

theorem ThirdHurewicz.simplexFace_threeSimplexBoundary (i : Fin 5) (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : FirstHurewicz.simplexFace 3 i s ∈ fourSimplexTwoSkeleton := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, FirstHurewicz.simplexFace_apply_self 3 i s,
      (FirstHurewicz.simplexFace_apply_succAbove 3 i s j).trans hj⟩

def ThirdHurewicz.basedFourSimplexFace {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (i : Fin 5) : BasedThreeSimplex x :=
  ⟨τ.val.comp (FirstHurewicz.simplexFace 3 i), fun s hs =>
    τ.property _ (simplexFace_threeSimplexBoundary i s hs)⟩

def ThirdHurewicz.BasedFourSimplex.ofFaces {X : Type} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 4, X))
    (h :
      ∀ i : Fin 5,
        ∀ s ∈ ThirdHurewicz.threeSimplexBoundary,
          (τ.comp (FirstHurewicz.simplexFace 3 i)) s = x) :
    ThirdHurewicz.BasedFourSimplex x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 3 i ⟨s, hi⟩
    have ht : t ∈ ThirdHurewicz.threeSimplexBoundary := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (FirstHurewicz.simplexFace 3 i t) = x at he
    rw [show FirstHurewicz.simplexFace 3 i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse 3 i ⟨s, hi⟩] at he
    exact he⟩

def ThirdHurewicz.normalizedFourSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    BasedFourSimplex x :=
  BasedFourSimplex.ofFaces (normalizedFourSimplexMap x smp)
    (normalizedFourSimplexMap_face_boundary x smp)

@[simp]
theorem ThirdHurewicz.normalizedFourSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (i : Fin 5) :
    basedFourSimplexFace (normalizedFourSimplex x smp) i =
      normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i)) := by
  apply Subtype.ext
  exact normalizedFourSimplexMap_face x smp i

theorem ThirdHurewicz.fourSimplex_three_order_cases (a b c : ℝ) :
    (a ≤ b ∧ b ≤ c) ∨
      (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨ (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact Or.inl ⟨hab, hbc⟩
    · rcases le_total a c with hac | hca
      · exact Or.inr (Or.inl ⟨hac, hcb⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hca, hab⟩))))
  · rcases le_total a c with hac | hca
    · exact Or.inr (Or.inr (Or.inl ⟨hba, hac⟩))
    · rcases le_total b c with hbc | hcb
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hbc, hca⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hcb, hba⟩))))

theorem ThirdHurewicz.fourSimplex_coordinates_sum_A (a b c : ℝ) :
    (1 - Max.max a b) + (a - Min.min a (Max.max b c)) + (b - Min.min b c) +
          (Min.min b c - Min.min a (Min.min b c)) +
        Min.min a c =
      1 := by
  rcases fourSimplex_three_order_cases a b c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    have h₃ := h₁.trans h₂
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring

theorem ThirdHurewicz.fourSimplex_coordinates_sum_B (a b c : ℝ) :
    (a - Min.min a b) + (1 - Max.max a (Max.max b c)) + (b - Min.min b c) +
          Min.min a (Min.min b c) +
        (c - Min.min a c) =
      1 := by
  rcases fourSimplex_three_order_cases a b c with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    have h₃ := h₁.trans h₂
    simp_all only [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
    ring

def ThirdHurewicz.fourSimplexFillA : C(Fin 3 → (unitInterval), FirstHurewicz.Simplex 4)
    where
  toFun
    u :=
    ⟨![1 - Max.max (u 0 : ℝ) (u 1 : ℝ),
        (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)),
        (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ),
        Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)),
        Min.min (u 0 : ℝ) (u 2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (max_le (u 0).property.2 (u 1).property.2)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact sub_nonneg.mpr (min_le_right _ _)
        · exact le_min (u 0).property.1 (u 2).property.1
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        simpa only [add_assoc] using fourSimplex_coordinates_sum_A (u 0) (u 1) (u 2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

def ThirdHurewicz.fourSimplexFillB : C(Fin 3 → (unitInterval), FirstHurewicz.Simplex 4)
    where
  toFun
    u :=
    ⟨![(u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ),
        1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)),
        (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ), Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)),
        (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ)],
      by
      constructor
      · intro i
        fin_cases i
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact
            sub_nonneg.mpr (max_le (u 0).property.2 (max_le (u 1).property.2 (u 2).property.2))
        · exact sub_nonneg.mpr (min_le_left _ _)
        · exact le_min (u 0).property.1 (le_min (u 1).property.1 (u 2).property.1)
        · exact sub_nonneg.mpr (min_le_right _ _)
      · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one]
        simpa only [add_assoc] using fourSimplex_coordinates_sum_B (u 0) (u 1) (u 2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

def ThirdHurewicz.fourSimplexReflectFirst : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![(unitInterval.symm) (u 0), u 1, u 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem ThirdHurewicz.fourSimplexReflectFirst_involutive (u : Fin 3 → (unitInterval)) :
    fourSimplexReflectFirst (fourSimplexReflectFirst u) = u := by
  funext i
  fin_cases i <;> simp [fourSimplexReflectFirst]

theorem ThirdHurewicz.fourSimplexReflectFirst_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : fourSimplexReflectFirst u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact ⟨0, Or.inr (by simp [fourSimplexReflectFirst, hi])⟩
    · exact ⟨1, Or.inl (by simpa [fourSimplexReflectFirst] using hi)⟩
    · exact ⟨2, Or.inl (by simpa [fourSimplexReflectFirst] using hi)⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact ⟨0, Or.inl (by simp [fourSimplexReflectFirst, hi])⟩
    · exact ⟨1, Or.inr (by simpa [fourSimplexReflectFirst] using hi)⟩
    · exact ⟨2, Or.inr (by simpa [fourSimplexReflectFirst] using hi)⟩

theorem ThirdHurewicz.fourSimplexFill_first_zero (u : Fin 3 → (unitInterval)) (hu : u 0 = 0) :
    fourSimplexFillA u 1 = 0 ∧
      fourSimplexFillA u 4 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 4 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    min_eq_left ((u 1).property.1.trans (le_max_left _ (u 2 : ℝ))), min_eq_left (u 2).property.1,
    max_eq_left (max_le (u 1).property.2 (u 2).property.2), min_eq_right (u 2).property.2]

theorem ThirdHurewicz.fourSimplexFill_first_one (u : Fin 3 → (unitInterval)) (hu : u 0 = 1) :
    fourSimplexFillA u 0 = 0 ∧
      fourSimplexFillA u 3 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 0 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    max_eq_left (u 1).property.2,
    min_eq_right ((min_le_left (u 1 : ℝ) (u 2 : ℝ)).trans (u 1).property.2),
    min_eq_left (u 1).property.1, min_eq_left (le_min (u 1).property.1 (u 2).property.1)]

theorem ThirdHurewicz.fourSimplexFill_second_zero (u : Fin 3 → (unitInterval)) (hu : u 1 = 0) :
    fourSimplexFillA u 2 = 0 ∧
      fourSimplexFillA u 3 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 2 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    min_eq_left (u 2).property.1, min_eq_right (u 0).property.1, (u 0).property.2]

theorem ThirdHurewicz.fourSimplexFill_second_one (u : Fin 3 → (unitInterval)) (hu : u 1 = 1) :
    fourSimplexFillA u 0 = 0 ∧
      fourSimplexFillA u 1 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 0 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    max_eq_right (u 0).property.2, max_eq_left (u 2).property.2, min_eq_left (u 0).property.2,
    min_eq_left (sub_le_self 1 (u 0).property.1), max_eq_right (sub_le_self 1 (u 0).property.1)]

theorem ThirdHurewicz.fourSimplexFill_third_zero (u : Fin 3 → (unitInterval)) (hu : u 2 = 0) :
    fourSimplexFillA u 3 = 0 ∧
      fourSimplexFillA u 4 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 3 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 4 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    min_eq_right (u 1).property.1, min_eq_right (u 0).property.1, (u 0).property.2]

theorem ThirdHurewicz.fourSimplexFill_third_one (u : Fin 3 → (unitInterval)) (hu : u 2 = 1) :
    fourSimplexFillA u 1 = 0 ∧
      fourSimplexFillA u 2 = 0 ∧
        fourSimplexFillB (fourSimplexReflectFirst u) 1 = 0 ∧
          fourSimplexFillB (fourSimplexReflectFirst u) 2 = 0 := by
  simp [fourSimplexFillA, fourSimplexFillB, fourSimplexReflectFirst, DFunLike.coe, hu,
    max_eq_right (u 1).property.2, min_eq_left (u 0).property.2, min_eq_left (u 1).property.2,
    max_eq_right (sub_le_self 1 (u 0).property.1)]

theorem ThirdHurewicz.fourSimplexFill_boundary_common_zeros (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i j : Fin 5,
      i ≠ j ∧
        fourSimplexFillA u i = 0 ∧
          fourSimplexFillA u j = 0 ∧
            fourSimplexFillB (fourSimplexReflectFirst u) i = 0 ∧
              fourSimplexFillB (fourSimplexReflectFirst u) j = 0 := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · exact ⟨1, 4, by decide, fourSimplexFill_first_zero u hi⟩
    · exact ⟨2, 3, by decide, fourSimplexFill_second_zero u hi⟩
    · exact ⟨3, 4, by decide, fourSimplexFill_third_zero u hi⟩
  · fin_cases i
    · exact ⟨0, 3, by decide, fourSimplexFill_first_one u hi⟩
    · exact ⟨0, 1, by decide, fourSimplexFill_second_one u hi⟩
    · exact ⟨1, 2, by decide, fourSimplexFill_third_one u hi⟩

theorem ThirdHurewicz.fourSimplexFillA_first_eq_second (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 1) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩
  · simp [fourSimplexFillA, DFunLike.coe, hu]
  · simp [fourSimplexFillA, DFunLike.coe, hu]

theorem ThirdHurewicz.fourSimplexFillA_first_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 2) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  refine ⟨1, 3, by decide, ?_, ?_⟩
  · simp [fourSimplexFillA, DFunLike.coe, hu]
  · simp [fourSimplexFillA, DFunLike.coe, hu]

theorem ThirdHurewicz.fourSimplexFillA_second_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 1 = u 2) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 0 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨1, 2, by decide, ?_, ?_⟩
    · simp [fourSimplexFillA, DFunLike.coe, hu, min_eq_left h]
    · simp [fourSimplexFillA, DFunLike.coe, hu]
  · refine ⟨2, 3, by decide, ?_, ?_⟩
    · simp [fourSimplexFillA, DFunLike.coe, hu]
    · simp [fourSimplexFillA, DFunLike.coe, hu, min_eq_right h]

theorem ThirdHurewicz.fourSimplexFillB_first_eq_second (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 1) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 1 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu]
    · simp [fourSimplexFillB, DFunLike.coe, min_eq_left h]
  · refine ⟨0, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu]
    · simp [fourSimplexFillB, DFunLike.coe, hu, min_eq_right h]

theorem ThirdHurewicz.fourSimplexFillB_first_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 0 = u 2) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 2 : ℝ) (u 1 : ℝ) with h | h
  · refine ⟨0, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu, min_eq_left h]
    · simp [fourSimplexFillB, DFunLike.coe, hu]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, min_eq_left h]
    · simp [fourSimplexFillB, DFunLike.coe, hu]

theorem ThirdHurewicz.fourSimplexFillB_second_eq_third (u : Fin 3 → (unitInterval))
    (hu : u 1 = u 2) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  rcases le_total (u 0 : ℝ) (u 2 : ℝ) with h | h
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu, min_eq_left h]
    · simp [fourSimplexFillB, DFunLike.coe, hu]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · simp [fourSimplexFillB, DFunLike.coe, hu]
    · simp [fourSimplexFillB, DFunLike.coe, min_eq_right h]

theorem ThirdHurewicz.fourSimplexFillA_internal (u : Fin 3 → (unitInterval)) (i j : Fin 3)
    (hij : i ≠ j) (hu : u i = u j) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fourSimplexFillA_first_eq_second u hu
  · exact fourSimplexFillA_first_eq_third u hu
  · exact fourSimplexFillA_first_eq_second u hu.symm
  · exact (hij rfl).elim
  · exact fourSimplexFillA_second_eq_third u hu
  · exact fourSimplexFillA_first_eq_third u hu.symm
  · exact fourSimplexFillA_second_eq_third u hu.symm
  · exact (hij rfl).elim

theorem ThirdHurewicz.fourSimplexFillB_internal (u : Fin 3 → (unitInterval)) (i j : Fin 3)
    (hij : i ≠ j) (hu : u i = u j) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact fourSimplexFillB_first_eq_second u hu
  · exact fourSimplexFillB_first_eq_third u hu
  · exact fourSimplexFillB_first_eq_second u hu.symm
  · exact (hij rfl).elim
  · exact fourSimplexFillB_second_eq_third u hu
  · exact fourSimplexFillB_first_eq_third u hu.symm
  · exact fourSimplexFillB_second_eq_third u hu.symm
  · exact (hij rfl).elim

theorem ThirdHurewicz.fourSimplexFillA_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : fourSimplexFillA u ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, hi, hj, _, _⟩ := fourSimplexFill_boundary_common_zeros u hu
  exact ⟨i, j, hij, hi, hj⟩

theorem ThirdHurewicz.fourSimplexFillB_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : fourSimplexFillB u ∈ fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, _, _, hi, hj⟩ :=
    fourSimplexFill_boundary_common_zeros (fourSimplexReflectFirst u)
      (fourSimplexReflectFirst_boundary u hu)
  exact
    ⟨i, j, hij, by simpa only [fourSimplexReflectFirst_involutive] using hi, by
      simpa only [fourSimplexReflectFirst_involutive] using hj⟩

theorem ThirdHurewicz.fourSimplexFill_blend_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend t (fourSimplexFillA u)
        (fourSimplexFillB (fourSimplexReflectFirst u)) ∈
      fourSimplexTwoSkeleton := by
  obtain ⟨i, j, hij, hai, haj, hbi, hbj⟩ := fourSimplexFill_boundary_common_zeros u hu
  exact
    ⟨i, j, hij,
      SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ i hai hbi,
      SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ j haj hbj⟩

abbrev ThirdHurewicz.NativeCube :=
  Fin 3 → (unitInterval)

def ThirdHurewicz.nativeCubeClass {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : Additive (π_ 3 X x) :=
  Additive.ofMul (⟦p⟧ : π_ 3 X x)

theorem ThirdHurewicz.nativeCubeClass_homotopic {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 3) X x} (h : GenLoop.Homotopic p q) :
    nativeCubeClass p = nativeCubeClass q :=
  congrArg (fun a : π_ 3 X x => Additive.ofMul a) (Quotient.sound h)

theorem ThirdHurewicz.nativeCubeClass_transAt {X : Type*} [TopologicalSpace X] {x : X} (i : Fin 3)
    (p q : GenLoop (Fin 3) X x) :
    nativeCubeClass (GenLoop.transAt i p q) = nativeCubeClass p + nativeCubeClass q :=
  congrArg Additive.ofMul
    ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans (mul_comm _ _))

theorem ThirdHurewicz.nativeCubeClass_symmAt {X : Type*} [TopologicalSpace X] {x : X} (i : Fin 3)
    (p : GenLoop (Fin 3) X x) : nativeCubeClass (GenLoop.symmAt i p) = -nativeCubeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

def ThirdHurewicz.NativeCubeInternalBased {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : Prop :=
  ∀ u : NativeCube, ∀ i j : Fin 3, i ≠ j → u i = u j → p u = x

inductive ThirdHurewicz.NativeCubeSameFlat (a b : NativeCube) : Prop
  | zero (i : Fin 3) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 3) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : Fin 3) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

def ThirdHurewicz.nativeCubeBlend (t : (unitInterval)) (a b : NativeCube) : NativeCube := fun i =>
  Set.Icc.convexComb (a i) (b i) t

@[simp]
theorem ThirdHurewicz.nativeCubeBlend_zero (a b : NativeCube) : nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
theorem ThirdHurewicz.nativeCubeBlend_one (a b : NativeCube) : nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def ThirdHurewicz.nativeCubeBlendMap (f g : C(NativeCube, NativeCube)) :
    C((unitInterval) × NativeCube, NativeCube)
    where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

theorem ThirdHurewicz.nativeCubeBlend_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) {a b : NativeCube}
    (h : NativeCubeSameFlat a b) (t : (unitInterval)) : p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb => exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb => exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb => exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

def ThirdHurewicz.nativeCubePullbackLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (f : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp f, hf⟩

def ThirdHurewicz.nativeCubeLinearHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (f g : C(NativeCube, NativeCube))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 3), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel (nativeCubePullbackLoop p g hg).val
      (Cube.boundary (Fin 3))
    where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left
    u := by
    change p (nativeCubeBlend 0 (f u) (g u)) = p (f u)
    rw [nativeCubeBlend_zero]
  map_one_left
    u := by
    change p (nativeCubeBlend 1 (f u) (g u)) = p (g u)
    rw [nativeCubeBlend_one]
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

def ThirdHurewicz.fourSimplexLoopA {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp fourSimplexFillA, fun u hu => τ.property _ (fourSimplexFillA_boundary u hu)⟩

def ThirdHurewicz.fourSimplexLoopB {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : GenLoop (Fin 3) X x :=
  ⟨τ.val.comp fourSimplexFillB, fun u hu => τ.property _ (fourSimplexFillB_boundary u hu)⟩

theorem ThirdHurewicz.fourSimplexLoopA_internal {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (u : Fin 3 → (unitInterval)) (i j : Fin 3) (hij : i ≠ j)
    (hu : u i = u j) : fourSimplexLoopA τ u = x :=
  τ.property _ (fourSimplexFillA_internal u i j hij hu)

theorem ThirdHurewicz.fourSimplexLoopB_internal {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (u : Fin 3 → (unitInterval)) (i j : Fin 3) (hij : i ≠ j)
    (hu : u i = u j) : fourSimplexLoopB τ u = x :=
  τ.property _ (fourSimplexFillB_internal u i j hij hu)

theorem ThirdHurewicz.fourSimplexReflectFirst_eq_update (u : Fin 3 → (unitInterval)) :
    fourSimplexReflectFirst u = Function.update u 0 ((unitInterval.symm) (u 0)) := by
  funext i
  fin_cases i <;> simp [fourSimplexReflectFirst]

def ThirdHurewicz.fourSimplexFillingsHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    (fourSimplexLoopA τ).val.HomotopyRel (GenLoop.symmAt 0 (fourSimplexLoopB τ)).val
      (Cube.boundary (Fin 3))
    where
  toFun
    p :=
    τ.val
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend p.1 (fourSimplexFillA p.2)
        (fourSimplexFillB (fourSimplexReflectFirst p.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap fourSimplexFillA
          (fourSimplexFillB.comp fourSimplexReflectFirst)).continuous
  map_zero_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 0 _ _) =
        τ.val (fourSimplexFillA u)
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 1 _ _) =
        τ.val (fourSimplexFillB (Function.update u 0 ((unitInterval.symm) (u 0))))
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one,
      fourSimplexReflectFirst_eq_update]
  prop' t u
    hu :=
    (τ.property _ (fourSimplexFill_blend_boundary t u hu)).trans
      ((fourSimplexLoopA τ).property u hu).symm

theorem ThirdHurewicz.fourSimplexFillings_additiveClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopA τ) = -nativeCubeClass (fourSimplexLoopB τ) :=
  (nativeCubeClass_homotopic ⟨fourSimplexFillingsHomotopy τ⟩).trans
    (nativeCubeClass_symmAt 0 (fourSimplexLoopB τ))

def ThirdHurewicz.nativeCubeTetrahedronQuotient (e : Equiv.Perm (Fin 3)) :
    C(NativeCube, NativeCube) :=
  (Geometry.cubeTetrahedron e).comp threeSimplexQuotient

@[simp]
theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_coordinate_zero (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeCubeTetrahedronQuotient e u (e 0) = u 0 := by
  apply Subtype.ext
  change (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 0) : ℝ) = (u 0 : ℝ)
  rw [Geometry.cubeTetrahedron_coordinate_zero, threeSimplexQuotient_one,
    threeSimplexQuotient_two, threeSimplexQuotient_three]
  ring

@[simp]
theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_coordinate_one (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeCubeTetrahedronQuotient e u (e 1) = Min.min (u 0) (u 1) := by
  apply Subtype.ext
  change
    (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 1) : ℝ) = Min.min (u 0 : ℝ) (u 1 : ℝ)
  rw [Geometry.cubeTetrahedron_coordinate_one, threeSimplexQuotient_two,
    threeSimplexQuotient_three]
  exact sub_add_cancel _ _

@[simp]
theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_coordinate_two (e : Equiv.Perm (Fin 3))
    (u : NativeCube) :
    nativeCubeTetrahedronQuotient e u (e 2) = Min.min (u 0) (Min.min (u 1) (u 2)) := by
  apply Subtype.ext
  change
    (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 2) : ℝ) =
      Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ))
  rw [Geometry.cubeTetrahedron_coordinate_two, threeSimplexQuotient_three]

theorem ThirdHurewicz.nativeCubeTetrahedron_coordinate_sum (s : FirstHurewicz.Simplex 3) :
    s 0 + s 1 + s 2 + s 3 = 1 := by
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
  linarith

theorem ThirdHurewicz.nativeCubeTetrahedron_based {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    p (Geometry.cubeTetrahedron e s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨e 0, Or.inr ?_⟩
    apply Subtype.ext
    change (Geometry.cubeTetrahedron e s (e 0) : ℝ) = 1
    rw [Geometry.cubeTetrahedron_coordinate_zero]
    linarith [nativeCubeTetrahedron_coordinate_sum s]
  · change s 1 = 0 at hi
    apply hp _ (e 0) (e 1) (e.injective.ne (by decide))
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply hp _ (e 1) (e 2) (e.injective.ne (by decide))
    apply Subtype.ext
    simp [hi]
  · change s 3 = 0 at hi
    apply p.property
    refine ⟨e 2, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

def ThirdHurewicz.nativeBasedCubeTetrahedron {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    BasedThreeSimplex x :=
  ⟨p.val.comp (Geometry.cubeTetrahedron e), nativeCubeTetrahedron_based p hp e⟩

theorem ThirdHurewicz.nativeCubeTetrahedronQuotient_based {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeTetrahedronQuotient e u) = x :=
  nativeCubeTetrahedron_based p hp e _ (threeSimplexQuotient_boundary u hu)

def ThirdHurewicz.fourSimplexTetrahedronA {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  nativeBasedCubeTetrahedron (fourSimplexLoopA τ) (fourSimplexLoopA_internal τ) e

def ThirdHurewicz.fourSimplexTetrahedronB {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  nativeBasedCubeTetrahedron (fourSimplexLoopB τ) (fourSimplexLoopB_internal τ) e

theorem ThirdHurewicz.fourSimplexTetrahedron_coordinate_perm (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) (i : Fin 3) :
    (Geometry.cubeTetrahedron e s i : ℝ) = ![s 1 + s 2 + s 3, s 2 + s 3, s 3] (e.symm i) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  fin_cases j <;> simp

theorem ThirdHurewicz.fourSimplexTetrahedron_zero_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s i : ℝ) =
      ![s 1 + s 2 + s 3, s 2 + s 3, s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  rfl

theorem ThirdHurewicz.fourSimplexTetrahedron_one_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s i : ℝ) =
      ![s 1 + s 2 + s 3, s 3, s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

theorem ThirdHurewicz.fourSimplexTetrahedron_two_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s i : ℝ) =
      ![s 2 + s 3, s 1 + s 2 + s 3, s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

theorem ThirdHurewicz.fourSimplexTetrahedron_three_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s i : ℝ) =
      ![s 2 + s 3, s 3, s 1 + s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

theorem ThirdHurewicz.fourSimplexTetrahedron_four_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s i : ℝ) =
      ![s 3, s 1 + s 2 + s 3, s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

theorem ThirdHurewicz.fourSimplexTetrahedron_five_coordinate (s : FirstHurewicz.Simplex 3)
    (i : Fin 3) :
    (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s i : ℝ) =
      ![s 3, s 2 + s 3, s 1 + s 2 + s 3] i := by
  rw [fourSimplexTetrahedron_coordinate_perm]
  fin_cases i <;> simp [Geometry.cubePermutation, Equiv.swap_apply_def]

theorem ThirdHurewicz.fourSimplexTetrahedron_tail_le_middle (s : FirstHurewicz.Simplex 3) :
    s 3 ≤ s 2 + s 3 :=
  le_add_of_nonneg_left (stdSimplex.zero_le s 2)

theorem ThirdHurewicz.fourSimplexTetrahedron_middle_le_first (s : FirstHurewicz.Simplex 3) :
    s 2 + s 3 ≤ s 1 + s 2 + s 3 := by linarith [stdSimplex.zero_le s 1]

theorem ThirdHurewicz.fourSimplexTetrahedron_tail_le_first (s : FirstHurewicz.Simplex 3) :
    s 3 ≤ s 1 + s 2 + s 3 :=
  (fourSimplexTetrahedron_tail_le_middle s).trans (fourSimplexTetrahedron_middle_le_first s)

theorem ThirdHurewicz.fourSimplexTetrahedron_sum (s : FirstHurewicz.Simplex 3) :
    s 0 + s 1 + s 2 + s 3 = 1 := by
  have h := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at h
  linarith

theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_zero (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s) : Fin 5 → ℝ) =
      ![s 0, s 1, s 2, 0, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_zero_coordinate,
      min_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_zero (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s) : Fin 5 → ℝ) =
      ![s 1, s 0, s 2, s 3, 0] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_zero_coordinate,
      min_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_one (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s) : Fin 5 → ℝ) =
      ![s 0, s 1, 0, 0, s 2 + s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_one_coordinate,
      max_eq_left hca, min_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_one (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s) : Fin 5 → ℝ) =
      ![s 1 + s 2, s 0, 0, s 3, 0] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_one_coordinate,
      min_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_two (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s) : Fin 5 → ℝ) =
      ![s 0, 0, s 1 + s 2, 0, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_two_coordinate,
      max_eq_left hca, min_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_two (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s) : Fin 5 → ℝ) =
      ![0, s 0, s 1 + s 2, s 3, 0] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_two_coordinate,
      max_eq_left hca, min_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_three (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s) : Fin 5 → ℝ) =
      ![s 0 + s 1, 0, 0, 0, s 2 + s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_three_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_three (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s) : Fin 5 → ℝ) =
      ![s 2, s 0, 0, s 3, s 1] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_three_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_four (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s) : Fin 5 → ℝ) =
      ![s 0, 0, s 1, s 2, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_four_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_four (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s) : Fin 5 → ℝ) =
      ![0, s 0, s 1, s 3, s 2] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_four_coordinate,
      min_eq_left hca, max_eq_right hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillA_tetrahedron_five (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s) : Fin 5 → ℝ) =
      ![s 0 + s 1, 0, 0, s 2, s 3] := by
  have fourSimplexFillA_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 0 = 1 - Max.max (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillA_one (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 1 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillA_two (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillA_three (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 3 =
      Min.min (u 1 : ℝ) (u 2 : ℝ) - Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) :=
    rfl
  have fourSimplexFillA_four (u : Fin 3 → unitInterval) :
    fourSimplexFillA u 4 = Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillA_zero, fourSimplexFillA_one, fourSimplexFillA_two,
      fourSimplexFillA_three, fourSimplexFillA_four, fourSimplexTetrahedron_five_coordinate,
      min_eq_left hca]
  all_goals linarith

theorem ThirdHurewicz.fourSimplexFillB_tetrahedron_five (s : FirstHurewicz.Simplex 3) :
    (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s) : Fin 5 → ℝ) =
      ![0, s 0, 0, s 3, s 1 + s 2] := by
  have fourSimplexFillB_zero (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 0 = (u 0 : ℝ) - Min.min (u 0 : ℝ) (u 1 : ℝ) := rfl
  have fourSimplexFillB_one (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 1 = 1 - Max.max (u 0 : ℝ) (Max.max (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_two (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 2 = (u 1 : ℝ) - Min.min (u 1 : ℝ) (u 2 : ℝ) := rfl
  have fourSimplexFillB_three (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 3 = Min.min (u 0 : ℝ) (Min.min (u 1 : ℝ) (u 2 : ℝ)) := rfl
  have fourSimplexFillB_four (u : Fin 3 → unitInterval) :
    fourSimplexFillB u 4 = (u 2 : ℝ) - Min.min (u 0 : ℝ) (u 2 : ℝ) := rfl
  have hca := fourSimplexTetrahedron_tail_le_first s
  have hs := fourSimplexTetrahedron_sum s
  funext i
  fin_cases i <;>
    simp [fourSimplexFillB_zero, fourSimplexFillB_one, fourSimplexFillB_two,
      fourSimplexFillB_three, fourSimplexFillB_four, fourSimplexTetrahedron_five_coordinate,
      max_eq_right hca, min_eq_left hca]
  all_goals linarith

theorem ThirdHurewicz.simplexFace_three_zero (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 0 s : Fin 5 → ℝ) = ![0, s 0, s 1, s 2, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_self 3 0 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 0 s 3

theorem ThirdHurewicz.simplexFace_three_one (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 1 s : Fin 5 → ℝ) = ![s 0, 0, s 1, s 2, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 0
  · exact FirstHurewicz.simplexFace_apply_self 3 1 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 1 s 3

theorem ThirdHurewicz.simplexFace_three_two (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 2 s : Fin 5 → ℝ) = ![s 0, s 1, 0, s 2, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 1
  · exact FirstHurewicz.simplexFace_apply_self 3 2 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 2 s 3

theorem ThirdHurewicz.simplexFace_three_three (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 3 s : Fin 5 → ℝ) = ![s 0, s 1, s 2, 0, s 3] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 2
  · exact FirstHurewicz.simplexFace_apply_self 3 3 s
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 3 s 3

theorem ThirdHurewicz.simplexFace_three_four (s : FirstHurewicz.Simplex 3) :
    (FirstHurewicz.simplexFace 3 4 s : Fin 5 → ℝ) = ![s 0, s 1, s 2, s 3, 0] := by
  funext i
  fin_cases i
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 0
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 1
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 2
  · exact FirstHurewicz.simplexFace_apply_succAbove 3 4 s 3
  · exact FirstHurewicz.simplexFace_apply_self 3 4 s

theorem ThirdHurewicz.fourSimplexTetrahedronA_zero {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 0) = basedFourSimplexFace τ 3 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s)) =
      τ.val (FirstHurewicz.simplexFace 3 3 s)
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillA_tetrahedron_zero s).trans (simplexFace_three_three s).symm

theorem ThirdHurewicz.fourSimplexTetrahedronA_one {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 1) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s)) = x
  apply τ.property
  exact
    ⟨2, 3, by decide, (congrFun (fourSimplexFillA_tetrahedron_one s) 2).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_one s) 3).trans rfl⟩

theorem ThirdHurewicz.fourSimplexTetrahedronA_two {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 2) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s)) = x
  apply τ.property
  exact
    ⟨1, 3, by decide, (congrFun (fourSimplexFillA_tetrahedron_two s) 1).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_two s) 3).trans rfl⟩

theorem ThirdHurewicz.fourSimplexTetrahedronA_three {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 3) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s)) = x
  apply τ.property
  exact
    ⟨1, 2, by decide, (congrFun (fourSimplexFillA_tetrahedron_three s) 1).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_three s) 2).trans rfl⟩

theorem ThirdHurewicz.fourSimplexTetrahedronA_four {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 4) = basedFourSimplexFace τ 1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s)) =
      τ.val (FirstHurewicz.simplexFace 3 1 s)
  apply congrArg τ.val
  apply Subtype.ext
  exact (fourSimplexFillA_tetrahedron_four s).trans (simplexFace_three_one s).symm

theorem ThirdHurewicz.fourSimplexTetrahedronA_five {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronA τ (Geometry.cubePermutation 5) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillA (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s)) = x
  apply τ.property
  exact
    ⟨1, 2, by decide, (congrFun (fourSimplexFillA_tetrahedron_five s) 1).trans rfl,
      (congrFun (fourSimplexFillA_tetrahedron_five s) 2).trans rfl⟩

def ThirdHurewicz.cubeThirdCycle : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![u 1, u 2, u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

theorem ThirdHurewicz.cubeThirdCycle_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : cubeThirdCycle u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact ⟨2, by simpa [cubeThirdCycle] using hi⟩
  · exact ⟨0, by simpa [cubeThirdCycle] using hi⟩
  · exact ⟨1, by simpa [cubeThirdCycle] using hi⟩

def ThirdHurewicz.cubeThirdCyclicReverse : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![u 1, u 2, (unitInterval.symm) (u 0)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

theorem ThirdHurewicz.cubeThirdCyclicReverse_boundary (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) : cubeThirdCyclicReverse u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · change u 0 = 0 ∨ u 0 = 1 at hi
    rcases hi with hi | hi
    · exact ⟨2, Or.inr (by simp [cubeThirdCyclicReverse, hi])⟩
    · exact ⟨2, Or.inl (by simp [cubeThirdCyclicReverse, hi])⟩
  · exact ⟨0, by simpa [cubeThirdCyclicReverse] using hi⟩
  · exact ⟨1, by simpa [cubeThirdCyclicReverse] using hi⟩

def ThirdHurewicz.cyclicThreeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp cubeThirdCycle, fun u hu => p.property _ (cubeThirdCycle_boundary u hu)⟩

def ThirdHurewicz.cyclicReverseThreeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp cubeThirdCyclicReverse, fun u hu =>
    p.property _ (cubeThirdCyclicReverse_boundary u hu)⟩

theorem ThirdHurewicz.cubeInsert01_boundary (a : Fin 2 → (unitInterval)) (b : (unitInterval))
    (ha : a ∈ Cube.boundary (Fin 2)) : ![a 0, a 1, b] ∈ Cube.boundary (Fin 3) := by
  rcases ha with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa using hi⟩
  · exact ⟨1, by simpa using hi⟩

theorem ThirdHurewicz.cubeInsert12_boundary (a : (unitInterval)) (b : Fin 2 → (unitInterval))
    (hb : b ∈ Cube.boundary (Fin 2)) : ![a, b 0, b 1] ∈ Cube.boundary (Fin 3) := by
  rcases hb with ⟨i, hi⟩
  fin_cases i
  · exact ⟨1, by simpa using hi⟩
  · exact ⟨2, by simpa using hi⟩

def ThirdHurewicz.cubeQuarter01HomotopyMap :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun
    z :=
    ![SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 0, z.2 1]) 0,
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 0, z.2 1]) 1, z.2 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem ThirdHurewicz.cubeQuarter01HomotopyMap_zero (u : Fin 3 → (unitInterval)) :
    cubeQuarter01HomotopyMap (0, u) = u := by
  funext i
  fin_cases i <;> simp [cubeQuarter01HomotopyMap]

@[simp]
theorem ThirdHurewicz.cubeQuarter01HomotopyMap_one (u : Fin 3 → (unitInterval)) :
    cubeQuarter01HomotopyMap (1, u) = ![u 1, (unitInterval.symm) (u 0), u 2] := by
  funext i
  fin_cases i <;> simp [cubeQuarter01HomotopyMap]

theorem ThirdHurewicz.cubeQuarter01HomotopyMap_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeQuarter01HomotopyMap (t, u) ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact
      cubeInsert01_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 0, u 1])
          ⟨0, by simpa using hi⟩)
  · exact
      cubeInsert01_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 0, u 1])
          ⟨1, by simpa using hi⟩)
  · exact ⟨2, by simpa [cubeQuarter01HomotopyMap] using hi⟩

def ThirdHurewicz.cubeQuarter12HomotopyMap :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun
    z :=
    ![z.2 0, SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 1, z.2 2]) 0,
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, ![z.2 1, z.2 2]) 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem ThirdHurewicz.cubeQuarter12HomotopyMap_zero (u : Fin 3 → (unitInterval)) :
    cubeQuarter12HomotopyMap (0, u) = u := by
  funext i
  fin_cases i <;> simp [cubeQuarter12HomotopyMap]

@[simp]
theorem ThirdHurewicz.cubeQuarter12HomotopyMap_one (u : Fin 3 → (unitInterval)) :
    cubeQuarter12HomotopyMap (1, u) = ![u 0, u 2, (unitInterval.symm) (u 1)] := by
  funext i
  fin_cases i <;> simp [cubeQuarter12HomotopyMap]

theorem ThirdHurewicz.cubeQuarter12HomotopyMap_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeQuarter12HomotopyMap (t, u) ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · exact ⟨0, by simpa [cubeQuarter12HomotopyMap] using hi⟩
  · exact
      cubeInsert12_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 1, u 2])
          ⟨0, by simpa using hi⟩)
  · exact
      cubeInsert12_boundary _ _
        (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (![u 1, u 2])
          ⟨1, by simpa using hi⟩)

def ThirdHurewicz.cubeThirdCycleHomotopyMap :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval)) :=
  cubeQuarter12HomotopyMap.comp ⟨fun z => (z.1, cubeQuarter01HomotopyMap z), by fun_prop⟩

@[simp]
theorem ThirdHurewicz.cubeThirdCycleHomotopyMap_zero (u : Fin 3 → (unitInterval)) :
    cubeThirdCycleHomotopyMap (0, u) = u := by
  change cubeQuarter12HomotopyMap (0, cubeQuarter01HomotopyMap (0, u)) = u
  rw [cubeQuarter01HomotopyMap_zero, cubeQuarter12HomotopyMap_zero]

@[simp]
theorem ThirdHurewicz.cubeThirdCycleHomotopyMap_one (u : Fin 3 → (unitInterval)) :
    cubeThirdCycleHomotopyMap (1, u) = cubeThirdCycle u := by
  change cubeQuarter12HomotopyMap (1, cubeQuarter01HomotopyMap (1, u)) = _
  rw [cubeQuarter01HomotopyMap_one, cubeQuarter12HomotopyMap_one]
  simp [cubeThirdCycle]

theorem ThirdHurewicz.cubeThirdCycleHomotopyMap_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    cubeThirdCycleHomotopyMap (t, u) ∈ Cube.boundary (Fin 3) :=
  cubeQuarter12HomotopyMap_boundary t _ (cubeQuarter01HomotopyMap_boundary t u hu)

def ThirdHurewicz.cyclicThreeLoop_homotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : p.val.HomotopyRel (cyclicThreeLoop p).val (Cube.boundary (Fin 3))
    where
  toFun z := p (cubeThirdCycleHomotopyMap z)
  continuous_toFun := p.val.continuous.comp cubeThirdCycleHomotopyMap.continuous
  map_zero_left u := congrArg p (cubeThirdCycleHomotopyMap_zero u)
  map_one_left u := congrArg p (cubeThirdCycleHomotopyMap_one u)
  prop' t u
    hu := (p.property _ (cubeThirdCycleHomotopyMap_boundary t u hu)).trans (p.property u hu).symm

theorem ThirdHurewicz.cyclicThreeLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : (⟦cyclicThreeLoop p⟧ : π_ 3 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 3 X x) = ⟦cyclicThreeLoop p⟧ :=
    Quotient.sound
      (show GenLoop.Homotopic p (cyclicThreeLoop p) from ⟨cyclicThreeLoop_homotopy p⟩)
  exact h.symm

theorem ThirdHurewicz.cyclicReverseThreeLoop_eq {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    cyclicReverseThreeLoop p = cyclicThreeLoop (GenLoop.symmAt (2 : Fin 3) p) := by
  apply GenLoop.ext
  intro u
  change
    p ![u 1, u 2, (unitInterval.symm) (u 0)] =
      p
        (fun j =>
          if j = (2 : Fin 3) then (unitInterval.symm) (![u 1, u 2, u 0] 2)
          else ![u 1, u 2, u 0] j)
  congr 1
  funext i
  fin_cases i <;> simp

theorem ThirdHurewicz.cyclicReverseThreeLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) :
    (⟦cyclicReverseThreeLoop p⟧ : π_ 3 X x) = ((·⁻¹) : π_ 3 X x → π_ 3 X x) ⟦p⟧ := by
  rw [cyclicReverseThreeLoop_eq, cyclicThreeLoop_class]
  exact (HomotopyGroup.inv_spec (i := (2 : Fin 3)) (p := p)).symm

def ThirdHurewicz.threeSimplexCycle : C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 1, s 2, s 3, s 0], by
      constructor
      · intro i
        fin_cases i <;> exact stdSimplex.zero_le s _
      · have hs := stdSimplex.sum_eq_one s
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_apply 1).comp continuous_subtype_val
    · exact (continuous_apply 2).comp continuous_subtype_val
    · exact (continuous_apply 3).comp continuous_subtype_val
    · exact (continuous_apply 0).comp continuous_subtype_val

theorem ThirdHurewicz.threeSimplexCycle_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexCycle s ∈ threeSimplexBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨3, hi⟩
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨2, hi⟩

def ThirdHurewicz.basedThreeSimplexVertexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexCycle, fun s hs => τ.property _ (threeSimplexCycle_boundary s hs)⟩

theorem ThirdHurewicz.threeSimplexCycle_quotient_commonZero (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i : Fin 4,
      threeSimplexCycle (threeSimplexQuotient u) i = 0 ∧
        threeSimplexQuotient (cubeThirdCyclicReverse u) i = 0 := by
  have threeSimplexCycle_zero (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 0 = s 1 := rfl
  have threeSimplexCycle_one (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 1 = s 2 := rfl
  have threeSimplexCycle_two (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 2 = s 3 := rfl
  have threeSimplexCycle_three (s : FirstHurewicz.Simplex 3) : threeSimplexCycle s 3 = s 0 := rfl
  have cubeThirdCyclicReverse_apply (u : Fin 3 → (unitInterval)) :
    cubeThirdCyclicReverse u = ![u 1, u 2, (unitInterval.symm) (u 0)] := rfl
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      refine ⟨2, ?_, ?_⟩
      · simp [threeSimplexCycle_two, hi, min_eq_left (le_min (u 1).property.1 (u 2).property.1)]
      · simp [cubeThirdCyclicReverse_apply, hi, min_eq_left (u 2).property.2]
    · change u 1 = 0 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_one, cubeThirdCyclicReverse_apply, hi,
          min_eq_left (u 2).property.1, min_eq_right (u 0).property.1]
    · change u 2 = 0 at hi
      refine ⟨2, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_two, cubeThirdCyclicReverse_apply, hi,
          min_eq_right (u 1).property.1, min_eq_right (u 0).property.1,
          min_eq_left (sub_nonneg.mpr (u 0).property.2)]
  · fin_cases i
    · change u 0 = 1 at hi
      refine ⟨3, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_three, cubeThirdCyclicReverse_apply, hi,
          min_eq_right (u 2).property.1, min_eq_right (u 1).property.1]
    · change u 1 = 1 at hi
      refine ⟨0, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_zero, cubeThirdCyclicReverse_apply, hi,
          min_eq_left (u 0).property.2]
    · change u 2 = 1 at hi
      refine ⟨1, ?_, ?_⟩ <;>
        simp [threeSimplexCycle_one, cubeThirdCyclicReverse_apply, hi,
          min_eq_left (u 1).property.2]

theorem ThirdHurewicz.threeSimplexCycle_quotient_blend_boundary (t : (unitInterval))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend t
        (threeSimplexCycle (threeSimplexQuotient u))
        (threeSimplexQuotient (cubeThirdCyclicReverse u)) ∈
      threeSimplexBoundary := by
  obtain ⟨i, hi, hj⟩ := threeSimplexCycle_quotient_commonZero u hu
  exact ⟨i, SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ i hi hj⟩

def ThirdHurewicz.basedThreeSimplexVertexCycle_loopHomotopy {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)).val.HomotopyRel
      (cyclicReverseThreeLoop (basedThreeSimplexLoop τ)).val (Cube.boundary (Fin 3))
    where
  toFun
    z :=
    τ.val
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend z.1
        (threeSimplexCycle (threeSimplexQuotient z.2))
        (threeSimplexQuotient (cubeThirdCyclicReverse z.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap
          (threeSimplexCycle.comp threeSimplexQuotient)
          (threeSimplexQuotient.comp cubeThirdCyclicReverse)).continuous
  map_zero_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 0 _ _) =
        τ.val (threeSimplexCycle (threeSimplexQuotient u))
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero]
  map_one_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 1 _ _) =
        τ.val (threeSimplexQuotient (cubeThirdCyclicReverse u))
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one]
  prop' t u
    hu :=
    (τ.property _ (threeSimplexCycle_quotient_blend_boundary t u hu)).trans
      ((basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)).property u hu).symm

@[simp]
theorem ThirdHurewicz.basedThreeSimplexVertexCycle_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexVertexCycle τ) = -basedThreeSimplexClass τ := by
  have h :
    GenLoop.Homotopic (basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ))
      (cyclicReverseThreeLoop (basedThreeSimplexLoop τ)) :=
    ⟨basedThreeSimplexVertexCycle_loopHomotopy τ⟩
  have he :
    (⟦basedThreeSimplexLoop (basedThreeSimplexVertexCycle τ)⟧ : π_ 3 X x) =
      ⟦cyclicReverseThreeLoop (basedThreeSimplexLoop τ)⟧ :=
    Quotient.sound h
  exact
    congrArg Additive.ofMul (he.trans (cyclicReverseThreeLoop_class (basedThreeSimplexLoop τ)))

def ThirdHurewicz.threeSimplexSwapLast : C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3)
    where
  toFun
    s :=
    ⟨![s 0, s 1, s 3, s 2], by
      constructor
      · intro i
        fin_cases i <;> exact s.property.1 _
      · have hs := s.property.2
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one] at hs ⊢
        change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
        simpa only [add_comm (s 2) (s 3)] using hs⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 0
      exact (continuous_apply 0).comp continuous_subtype_val
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 1
      exact (continuous_apply 1).comp continuous_subtype_val
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 3
      exact (continuous_apply 3).comp continuous_subtype_val
    · change Continuous fun s : FirstHurewicz.Simplex 3 => s 2
      exact (continuous_apply 2).comp continuous_subtype_val

theorem ThirdHurewicz.threeSimplexSwapLast_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexSwapLast s ∈ threeSimplexBoundary := by
  obtain ⟨i, hi⟩ := hs
  fin_cases i
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨3, hi⟩
  · exact ⟨2, hi⟩

def ThirdHurewicz.cubeThirdLastReverse : C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u := ![u 0, u 1, (unitInterval.symm) (u 2)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp]
theorem ThirdHurewicz.cubeThirdLastReverse_zero (u : Fin 3 → (unitInterval)) :
    cubeThirdLastReverse u 0 = u 0 :=
  rfl

@[simp]
theorem ThirdHurewicz.cubeThirdLastReverse_one (u : Fin 3 → (unitInterval)) :
    cubeThirdLastReverse u 1 = u 1 :=
  rfl

@[simp]
theorem ThirdHurewicz.cubeThirdLastReverse_two (u : Fin 3 → (unitInterval)) :
    cubeThirdLastReverse u 2 = (unitInterval.symm) (u 2) :=
  rfl

theorem ThirdHurewicz.threeSimplexSwapLast_commonZero (u : Fin 3 → (unitInterval))
    (hu : u ∈ Cube.boundary (Fin 3)) :
    ∃ i : Fin 4,
      threeSimplexSwapLast (threeSimplexQuotient u) i = 0 ∧
        threeSimplexQuotient (cubeThirdLastReverse u) i = 0 := by
  have threeSimplexSwapLast_zero (s : FirstHurewicz.Simplex 3) : threeSimplexSwapLast s 0 = s 0 :=
    rfl
  have threeSimplexSwapLast_one (s : FirstHurewicz.Simplex 3) : threeSimplexSwapLast s 1 = s 1 :=
    rfl
  have threeSimplexSwapLast_two (s : FirstHurewicz.Simplex 3) : threeSimplexSwapLast s 2 = s 3 :=
    rfl
  have threeSimplexSwapLast_three (s : FirstHurewicz.Simplex 3) :
    threeSimplexSwapLast s 3 = s 2 := rfl
  rcases hu with ⟨j, hj | hj⟩
  · fin_cases j
    · change u 0 = 0 at hj
      refine ⟨1, ?_, ?_⟩
      · simp [threeSimplexSwapLast_one, hj, min_eq_left (u 1).property.1]
      · simp [hj, min_eq_left (u 1).property.1]
    · change u 1 = 0 at hj
      refine ⟨2, ?_, ?_⟩
      · simp [threeSimplexSwapLast_two, hj, min_eq_left (u 2).property.1,
          min_eq_right (u 0).property.1]
      · simp only [threeSimplexQuotient_two, cubeThirdLastReverse_zero, cubeThirdLastReverse_one,
          cubeThirdLastReverse_two, hj]
        change
          Min.min (u 0 : ℝ) 0 - Min.min (u 0 : ℝ) (Min.min 0 ((unitInterval.symm) (u 2) : ℝ)) = 0
        rw [min_eq_right (u 0).property.1, min_eq_left ((unitInterval.symm) (u 2)).property.1,
          min_eq_right (u 0).property.1, sub_self]
    · change u 2 = 0 at hj
      refine ⟨2, ?_, ?_⟩
      · simp [threeSimplexSwapLast_two, hj, min_eq_right (u 1).property.1,
          min_eq_right (u 0).property.1]
      · simp [hj, min_eq_left (u 1).property.2]
  · fin_cases j
    · change u 0 = 1 at hj
      exact ⟨0, by simp [threeSimplexSwapLast_zero, hj], by simp [hj]⟩
    · change u 1 = 1 at hj
      exact
        ⟨1, by simp [threeSimplexSwapLast_one, hj, min_eq_left (u 0).property.2], by
          simp [hj, min_eq_left (u 0).property.2]⟩
    · change u 2 = 1 at hj
      refine ⟨3, ?_, ?_⟩
      · simp [threeSimplexSwapLast_three, hj, min_eq_left (u 1).property.2]
      · simp [hj, min_eq_right (u 1).property.1, min_eq_right (u 0).property.1]

def ThirdHurewicz.basedThreeSimplexSwapLast {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexSwapLast, fun s hs => τ.property _ (threeSimplexSwapLast_boundary s hs)⟩

theorem ThirdHurewicz.symmAt_last_apply {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (u : Fin 3 → (unitInterval)) :
    GenLoop.symmAt (2 : Fin 3) p u = p (cubeThirdLastReverse u) := by
  change p (fun j => if j = (2 : Fin 3) then (unitInterval.symm) (u 2) else u j) = _
  congr 1
  funext j
  fin_cases j <;> rfl

def ThirdHurewicz.basedThreeSimplexSwapLast_loopHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)).val.HomotopyRel
      (GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ)).val (Cube.boundary (Fin 3))
    where
  toFun
    z :=
    τ.val
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend z.1
        (threeSimplexSwapLast (threeSimplexQuotient z.2))
        (threeSimplexQuotient (cubeThirdLastReverse z.2)))
  continuous_toFun :=
    τ.val.continuous.comp
      (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlendMap
          (threeSimplexSwapLast.comp threeSimplexQuotient)
          (threeSimplexQuotient.comp cubeThirdLastReverse)).continuous
  map_zero_left
    u := by
    change τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 0 _ _) = _
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero]
    rfl
  map_one_left
    u := by
    change
      τ.val (SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend 1 _ _) =
        GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ) u
    rw [SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_one, symmAt_last_apply]
    rfl
  prop' t u
    hu := by
    obtain ⟨i, ha, hb⟩ := threeSimplexSwapLast_commonZero u hu
    exact
      (τ.property _
            ⟨i,
              SecondHurewicz.SimplyConnected.tetrahedronSimplexBlend_zero_coordinate t _ _ i ha
                hb⟩).trans
        ((basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)).property u hu).symm

theorem ThirdHurewicz.basedThreeSimplexSwapLast_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexSwapLast τ) = -basedThreeSimplexClass τ := by
  have h :
    (⟦basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)⟧ : π_ 3 X x) =
      ⟦GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ)⟧ :=
    Quotient.sound ⟨basedThreeSimplexSwapLast_loopHomotopy τ⟩
  exact
    congrArg Additive.ofMul
      (h.trans (HomotopyGroup.inv_spec (i := (2 : Fin 3)) (p := basedThreeSimplexLoop τ)).symm)

def ThirdHurewicz.threeSimplexSwapFirst : C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3) :=
  threeSimplexCycle.comp
    (threeSimplexCycle.comp
      (threeSimplexSwapLast.comp (threeSimplexCycle.comp threeSimplexCycle)))

theorem ThirdHurewicz.threeSimplexSwapFirst_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexSwapFirst s ∈ threeSimplexBoundary :=
  threeSimplexCycle_boundary _
    (threeSimplexCycle_boundary _
      (threeSimplexSwapLast_boundary _
        (threeSimplexCycle_boundary _ (threeSimplexCycle_boundary _ hs))))

def ThirdHurewicz.threeSimplexVertexOrder1302 :
    C(FirstHurewicz.Simplex 3, FirstHurewicz.Simplex 3) :=
  threeSimplexCycle.comp (threeSimplexSwapLast.comp threeSimplexCycle)

theorem ThirdHurewicz.threeSimplexVertexOrder1302_boundary (s : FirstHurewicz.Simplex 3)
    (hs : s ∈ threeSimplexBoundary) : threeSimplexVertexOrder1302 s ∈ threeSimplexBoundary :=
  threeSimplexCycle_boundary _ (threeSimplexSwapLast_boundary _ (threeSimplexCycle_boundary _ hs))

def ThirdHurewicz.basedThreeSimplexSwapFirst {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexSwapFirst, fun s hs =>
    τ.property _ (threeSimplexSwapFirst_boundary s hs)⟩

theorem ThirdHurewicz.basedThreeSimplexSwapFirst_word {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexSwapFirst τ =
      basedThreeSimplexVertexCycle
        (basedThreeSimplexVertexCycle
          (basedThreeSimplexSwapLast
            (basedThreeSimplexVertexCycle (basedThreeSimplexVertexCycle τ)))) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rfl

@[simp]
theorem ThirdHurewicz.basedThreeSimplexSwapFirst_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexSwapFirst τ) = -basedThreeSimplexClass τ := by
  rw [basedThreeSimplexSwapFirst_word]
  simp only [basedThreeSimplexVertexCycle_class, basedThreeSimplexSwapLast_class, neg_neg]

def ThirdHurewicz.basedThreeSimplexVertexOrder1302 {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedThreeSimplex x) : BasedThreeSimplex x :=
  ⟨τ.val.comp threeSimplexVertexOrder1302, fun s hs =>
    τ.property _ (threeSimplexVertexOrder1302_boundary s hs)⟩

theorem ThirdHurewicz.basedThreeSimplexVertexOrder1302_word {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    basedThreeSimplexVertexOrder1302 τ =
      basedThreeSimplexVertexCycle (basedThreeSimplexSwapLast (basedThreeSimplexVertexCycle τ)) :=
  by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rfl

@[simp]
theorem ThirdHurewicz.basedThreeSimplexVertexOrder1302_class {X : Type} [TopologicalSpace X]
    {x : X} (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexVertexOrder1302 τ) = -basedThreeSimplexClass τ := by
  rw [basedThreeSimplexVertexOrder1302_word]
  simp only [basedThreeSimplexVertexCycle_class, basedThreeSimplexSwapLast_class, neg_neg]

theorem ThirdHurewicz.fourSimplexTetrahedronB_zero {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 0) =
      basedThreeSimplexSwapFirst (basedFourSimplexFace τ 4) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 0) s)) =
      τ.val (FirstHurewicz.simplexFace 3 4 (threeSimplexSwapFirst s))
  apply congrArg τ.val
  apply Subtype.ext
  exact
    (fourSimplexFillB_tetrahedron_zero s).trans
      (simplexFace_three_four (threeSimplexSwapFirst s)).symm

theorem ThirdHurewicz.fourSimplexTetrahedronB_one {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 1) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 1) s)) = x
  apply τ.property
  exact
    ⟨2, 4, by decide, (congrFun (fourSimplexFillB_tetrahedron_one s) 2).trans rfl,
      (congrFun (fourSimplexFillB_tetrahedron_one s) 4).trans rfl⟩

theorem ThirdHurewicz.fourSimplexTetrahedronB_two {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 2) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 2) s)) = x
  apply τ.property
  exact
    ⟨0, 4, by decide, (congrFun (fourSimplexFillB_tetrahedron_two s) 0).trans rfl,
      (congrFun (fourSimplexFillB_tetrahedron_two s) 4).trans rfl⟩

theorem ThirdHurewicz.fourSimplexTetrahedronB_three {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 3) =
      basedThreeSimplexVertexOrder1302 (basedFourSimplexFace τ 2) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 3) s)) =
      τ.val (FirstHurewicz.simplexFace 3 2 (threeSimplexVertexOrder1302 s))
  apply congrArg τ.val
  apply Subtype.ext
  exact
    (fourSimplexFillB_tetrahedron_three s).trans
      (simplexFace_three_two (threeSimplexVertexOrder1302 s)).symm

theorem ThirdHurewicz.fourSimplexTetrahedronB_four {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 4) =
      basedThreeSimplexSwapLast (basedFourSimplexFace τ 0) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change
    τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 4) s)) =
      τ.val (FirstHurewicz.simplexFace 3 0 (threeSimplexSwapLast s))
  apply congrArg τ.val
  apply Subtype.ext
  exact
    (fourSimplexFillB_tetrahedron_four s).trans
      (simplexFace_three_zero (threeSimplexSwapLast s)).symm

theorem ThirdHurewicz.fourSimplexTetrahedronB_five {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    fourSimplexTetrahedronB τ (Geometry.cubePermutation 5) = constantBasedThreeSimplex x := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  change τ.val (fourSimplexFillB (Geometry.cubeTetrahedron (Geometry.cubePermutation 5) s)) = x
  apply τ.property
  exact
    ⟨0, 2, by decide, (congrFun (fourSimplexFillB_tetrahedron_five s) 0).trans rfl,
      (congrFun (fourSimplexFillB_tetrahedron_five s) 2).trans rfl⟩

theorem ThirdHurewicz.fourSimplexTetrahedraA_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronA τ e) =
      basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) := by
  have hconstant : basedThreeSimplexClass (constantBasedThreeSimplex x) = 0 := rfl
  rw [←
    Geometry.cubePermutation_bijective.sum_comp
      (fun e =>
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronA τ e))]
  simp [hconstant, Fin.sum_univ_succ, Geometry.cubeOrientation_cubePermutation,
    fourSimplexTetrahedronA_zero, fourSimplexTetrahedronA_one, fourSimplexTetrahedronA_two,
    fourSimplexTetrahedronA_three, fourSimplexTetrahedronA_four, fourSimplexTetrahedronA_five]

theorem ThirdHurewicz.fourSimplexTetrahedraB_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronB τ e) =
      -(basedThreeSimplexClass (basedFourSimplexFace τ 4) +
            basedThreeSimplexClass (basedFourSimplexFace τ 2) +
          basedThreeSimplexClass (basedFourSimplexFace τ 0)) := by
  have hconstant : basedThreeSimplexClass (constantBasedThreeSimplex x) = 0 := rfl
  rw [←
    Geometry.cubePermutation_bijective.sum_comp
      (fun e =>
        Geometry.cubeOrientation e • basedThreeSimplexClass (fourSimplexTetrahedronB τ e))]
  simp [hconstant, Fin.sum_univ_succ, Geometry.cubeOrientation_cubePermutation, add_assoc,
    fourSimplexTetrahedronB_zero, fourSimplexTetrahedronB_one, fourSimplexTetrahedronB_two,
    fourSimplexTetrahedronB_three, fourSimplexTetrahedronB_four, fourSimplexTetrahedronB_five,
    basedThreeSimplexSwapLast_class]
  abel

def ThirdHurewicz.nativeDuffyCubeCanonical : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, u 0 * u 1 * u 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact
        ((continuous_subtype_val.comp (continuous_apply 0)).mul
              (continuous_subtype_val.comp (continuous_apply 1))).subtype_mk
          _
    · exact
        (((continuous_subtype_val.comp (continuous_apply 0)).mul
                  (continuous_subtype_val.comp (continuous_apply 1))).mul
              (continuous_subtype_val.comp (continuous_apply 2))).subtype_mk
          _

def ThirdHurewicz.nativeDuffyCube (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube)
    where
  toFun u i := nativeDuffyCubeCanonical u (e.symm i)
  continuous_toFun :=
    continuous_pi fun i => (continuous_apply (e.symm i)).comp nativeDuffyCubeCanonical.continuous

theorem ThirdHurewicz.nativeDuffyCube_apply (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (i : Fin 3) : nativeDuffyCube e u i = ![u 0, u 0 * u 1, u 0 * u 1 * u 2] (e.symm i) :=
  rfl

@[simp]
theorem ThirdHurewicz.nativeDuffyCube_coordinate_zero (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCube e u (e 0) = u 0 := by simp [nativeDuffyCube_apply]

@[simp]
theorem ThirdHurewicz.nativeDuffyCube_coordinate_one (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCube e u (e 1) = u 0 * u 1 := by simp [nativeDuffyCube_apply]

@[simp]
theorem ThirdHurewicz.nativeDuffyCube_coordinate_two (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCube e u (e 2) = u 0 * u 1 * u 2 := by simp [nativeDuffyCube_apply]

theorem ThirdHurewicz.nativeDuffyCube_boundary (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin 3) ∨
      ∃ i j : Fin 3, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  rcases hu with ⟨j, hj⟩
  fin_cases j
  · change u 0 = 0 ∨ u 0 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 0, Or.inl (by simpa using hj)⟩
    · exact Or.inl ⟨e 0, Or.inr (by simpa using hj)⟩
  · change u 1 = 0 ∨ u 1 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 1, Or.inl (by simp [hj])⟩
    · exact Or.inr ⟨e 0, e 1, e.injective.ne (by decide), by simp [hj]⟩
  · change u 2 = 0 ∨ u 2 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 2, Or.inl (by simp [hj])⟩
    · exact Or.inr ⟨e 1, e 2, e.injective.ne (by decide), by simp [hj]⟩

theorem ThirdHurewicz.nativeDuffyCube_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

def ThirdHurewicz.nativeDuffyCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

def ThirdHurewicz.nativeCubePair (i j : Fin 3) : C(Fin 3 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

def ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap (i j : Fin 3) :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 3 → (unitInterval))
    where
  toFun z
    k :=
    if k = i then
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 0
    else
      if k = j then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 1
      else z.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases hi : k = i
    · simp only [if_pos hi]
      exact
        (continuous_apply (0 : Fin 2)).comp
          (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
            (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
    · by_cases hj : k = j
      · simp only [if_neg hi, if_pos hj]
        exact
          (continuous_apply (1 : Fin 2)).comp
            (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
              (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
      · simp only [if_neg hi, if_neg hj]
        exact (continuous_apply k).comp continuous_snd

@[simp]
theorem ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap_zero (i j : Fin 3)
    (u : Fin 3 → (unitInterval)) : nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change
    (if k = i then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
      else
        if k = j then
          SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 1
        else u k) =
      u k
  simp only [SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

@[simp]
theorem ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap_one (i j : Fin 3)
    (u : Fin 3 → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) = fun k =>
      if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

theorem ThirdHurewicz.nativeCubeQuarterTurnHomotopyMap_boundary (i j : Fin 3) (hij : i ≠ j)
    (t : (unitInterval)) (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary (Fin 3) := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary (Fin 3) := by
    obtain ⟨k, hk⟩ :=
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (nativeCubePair i j u) h
    fin_cases k
    · exact ⟨i, by simpa [nativeCubeQuarterTurnHomotopyMap] using hk⟩
    · exact ⟨j, by simpa [nativeCubeQuarterTurnHomotopyMap, hij.symm] using hk⟩
  obtain ⟨k, hk⟩ := hu
  by_cases hi : k = i
  · subst k
    exact hp ⟨0, by simpa [nativeCubePair] using hk⟩
  · by_cases hj : k = j
    · subst k
      exact hp ⟨1, by simpa [nativeCubePair] using hk⟩
    · exact ⟨k, by simpa [nativeCubeQuarterTurnHomotopyMap, hi, hj] using hk⟩

def ThirdHurewicz.nativeCubeQuarterTurnLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) : GenLoop (Fin 3) X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp
        ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
          (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp]
theorem ThirdHurewicz.nativeCubeQuarterTurnLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) (u : Fin 3 → (unitInterval)) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

def ThirdHurewicz.nativeCubeQuarterTurnHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary (Fin 3))
    where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u
    hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

theorem ThirdHurewicz.nativeCubeQuarterTurnLoop_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : π_ 3 X x) = ⟦p⟧ := by
  exact
    (Quotient.sound
        (show GenLoop.Homotopic p (nativeCubeQuarterTurnLoop p i j hij) from
          ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩)).symm

theorem ThirdHurewicz.nativeCubeQuarterTurnLoop_additiveClass {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    Additive.ofMul (⟦nativeCubeQuarterTurnLoop p i j hij⟧ : π_ 3 X x) =
      Additive.ofMul (⟦p⟧ : π_ 3 X x) :=
  congrArg Additive.ofMul (nativeCubeQuarterTurnLoop_class p i j hij)

def ThirdHurewicz.permuteCubeCoordinates (e : Equiv.Perm (Fin 3)) :
    C(Fin 3 → (unitInterval), Fin 3 → (unitInterval))
    where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

theorem ThirdHurewicz.permuteCubeCoordinates_boundary (e : Equiv.Perm (Fin 3))
    (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    permuteCubeCoordinates e u ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

def ThirdHurewicz.permuteCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) : GenLoop (Fin 3) X x :=
  ⟨p.val.comp (permuteCubeCoordinates e), fun u hu =>
    p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp]
theorem ThirdHurewicz.permuteCubeLoop_one {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

theorem ThirdHurewicz.permuteCubeLoop_mul {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e f : Equiv.Perm (Fin 3)) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

theorem ThirdHurewicz.nativeCubeQuarterTurnLoop_eq_symmAt_permute {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeQuarterTurnLoop p i j hij = GenLoop.symmAt i (permuteCubeLoop p (Equiv.swap i j)) :=
  by
  apply GenLoop.ext
  intro u
  rw [nativeCubeQuarterTurnLoop_apply]
  change
    p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) =
      p
        (fun k =>
          if Equiv.swap i j k = i then (unitInterval.symm) (u i) else u (Equiv.swap i j k))
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem ThirdHurewicz.nativeCubeClass_quarterTurn {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeCubeClass p :=
  nativeCubeQuarterTurnLoop_additiveClass p i j hij

theorem ThirdHurewicz.permuteCubeLoop_swap_additiveClass {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i j : Fin 3) (hij : i ≠ j) :
    nativeCubeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeCubeClass p := by
  have h := nativeCubeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeCubeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

theorem ThirdHurewicz.permuteCubeLoop_additiveClass {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    nativeCubeClass (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeCubeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

def ThirdHurewicz.nativeCubeCycle120 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

def ThirdHurewicz.nativeCubeCycle201 : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2 * Equiv.swap 0 1

@[fun_prop]
theorem ThirdHurewicz.nativeInterval_continuous_mul {Y : Type*} [TopologicalSpace Y]
    {f g : Y → (unitInterval)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => f y * g y := by
  apply Continuous.subtype_mk
  exact hf.subtype_val.mul hg.subtype_val

@[fun_prop]
theorem ThirdHurewicz.nativeInterval_continuous_convexComb {Y : Type*} [TopologicalSpace Y]
    {f g t : Y → (unitInterval)} (hf : Continuous f) (hg : Continuous g) (ht : Continuous t) :
    Continuous fun y => Set.Icc.convexComb (f y) (g y) (t y) := by
  apply Continuous.subtype_mk
  exact
    ((continuous_const.sub ht.subtype_val).mul hf.subtype_val).add
      (ht.subtype_val.mul hg.subtype_val)

def ThirdHurewicz.nativeLowerPrismMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, u 2]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeUpperPrismMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1), u 2]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeMiddleChamberMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, u 0 * Set.Icc.convexComb (u 1) 1 (u 2)]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeHighChamberMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, u 0 * u 1, Set.Icc.convexComb (u 0) 1 (u 2)]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeUpperLowChamberMap : C(NativeCube, NativeCube)
    where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1), u 0 * u 2]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeUpperMiddleChamberMap : C(NativeCube, NativeCube)
    where
  toFun
    u :=
    ![u 0, Set.Icc.convexComb (u 0) 1 (u 1),
      Set.Icc.convexComb (u 0) (Set.Icc.convexComb (u 0) 1 (u 1)) (u 2)]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeUpperHighChamberMap : C(NativeCube, NativeCube)
    where
  toFun
    u :=
    ![u 0, Set.Icc.convexComb (u 0) 1 (u 1),
      Set.Icc.convexComb (Set.Icc.convexComb (u 0) 1 (u 1)) 1 (u 2)]
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeOrderedDuffyMap (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp]
theorem ThirdHurewicz.nativeOrderedDuffyMap_swap12 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 1 2) u = ![u 0, u 0 * u 2 * u 1, u 0 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem ThirdHurewicz.nativeOrderedDuffyMap_cycle201 (u : NativeCube) :
    nativeOrderedDuffyMap nativeCubeCycle201 u = ![u 2 * u 0, u 2 * u 0 * u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem ThirdHurewicz.nativeOrderedDuffyMap_swap01 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 0 1) u = ![u 1 * u 0, u 1, u 1 * u 0 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem ThirdHurewicz.nativeOrderedDuffyMap_cycle120 (u : NativeCube) :
    nativeOrderedDuffyMap nativeCubeCycle120 u = ![u 1 * u 2 * u 0, u 1, u 1 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem ThirdHurewicz.nativeOrderedDuffyMap_swap02 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 0 2) u = ![u 2 * u 1 * u 0, u 2 * u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

theorem ThirdHurewicz.nativeMiddleChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeMiddleChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 1 2) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .zero 1 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 1 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .one 0 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])

theorem ThirdHurewicz.nativeHighChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeHighChamberMap u) (nativeOrderedDuffyMap (nativeCubeCycle201) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .zero 1 (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 0 2 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .one 2 (by simp [nativeHighChamberMap, hi]) (by simp [hi])

theorem ThirdHurewicz.nativeUpperLowChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperLowChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 0 1) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .zero 2 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .one 1 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])

theorem ThirdHurewicz.nativeUpperMiddleChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperMiddleChamberMap u)
      (nativeOrderedDuffyMap nativeCubeCycle120 u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .one 1 (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])

theorem ThirdHurewicz.nativeUpperHighChamber_flats (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperHighChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 0 2) u) :=
  by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .one 2 (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])

theorem ThirdHurewicz.nativeCubeMap_based_of_commonLeft {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) {f g : C(NativeCube, NativeCube)}
    (h : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (f u) = x := by
  simpa only [nativeCubeBlend_zero] using nativeCubeBlend_based p hp (h u hu) 0

theorem ThirdHurewicz.nativeDuffyCube_tetrahedron_sameFlat (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeTetrahedronQuotient e u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero (e 0) (by simp [hi]) (by simp [hi])
    · change u 1 = 0 at hi
      refine .zero (e 1) (by simp [hi]) ?_
      simp [hi]
    · change u 2 = 0 at hi
      refine .zero (e 2) (by simp [hi]) ?_
      simp [hi]
  · fin_cases i
    · change u 0 = 1 at hi
      exact .one (e 0) (by simp [hi]) (by simp [hi])
    · change u 1 = 1 at hi
      refine .equal (e 0) (e 1) (e.injective.ne (by decide)) (by simp [hi]) ?_
      simp [hi, min_eq_left (show u 0 ≤ (1 : (unitInterval)) from (u 0).property.2)]
    · change u 2 = 1 at hi
      refine .equal (e 1) (e 2) (e.injective.ne (by decide)) (by simp [hi]) ?_
      simp [hi, min_eq_left (show u 1 ≤ (1 : (unitInterval)) from (u 1).property.2)]

def ThirdHurewicz.nativeDuffyCubeTetrahedronHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e)).val (Cube.boundary (Fin 3)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeTetrahedronQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeTetrahedronQuotient_based p hp e)
    (nativeDuffyCube_tetrahedron_sameFlat e)

theorem ThirdHurewicz.nativeDuffyCube_homotopic_basedThreeSimplexLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin 3)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e)) :=
  ⟨nativeDuffyCubeTetrahedronHomotopy p hp e⟩

theorem ThirdHurewicz.nativeDuffyCubeClass_eq_basedThreeSimplexClass {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin 3)) :
    nativeCubeClass (nativeDuffyCubeLoop p hp e) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  nativeCubeClass_homotopic (nativeDuffyCube_homotopic_basedThreeSimplexLoop p hp e)

def ThirdHurewicz.nativeCubeOrderedDuffyHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3)) (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin 3)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (fun u hu => nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)) hfg

theorem ThirdHurewicz.nativeCubeClass_commonOrderedDuffy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3)) (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeCubeClass (nativeDuffyCubeLoop p hp e) :=
  (nativeCubeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp f e hf hfg⟩).trans
    (permuteCubeLoop_additiveClass (nativeDuffyCubeLoop p hp e) e)

theorem ThirdHurewicz.nativeCubeClass_commonOrderedTetrahedron {Y : Type} [TopologicalSpace Y]
    {y : Y} (p : GenLoop (Fin 3) Y y) (hp : NativeCubeInternalBased p)
    (f : C(NativeCube, NativeCube)) (e : Equiv.Perm (Fin 3))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = y)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) := by
  simpa only [nativeDuffyCubeClass_eq_basedThreeSimplexClass, Geometry.cubeOrientation] using
    nativeCubeClass_commonOrderedDuffy p hp f e hf hfg

theorem ThirdHurewicz.nativeLowerPrismMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeLowerPrismMap u) = x := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact p.property _ ⟨0, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
    · change u 1 = 0 at hi
      exact p.property _ ⟨1, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
    · change u 2 = 0 at hi
      exact p.property _ ⟨2, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact p.property _ ⟨0, Or.inr (by simp [nativeLowerPrismMap, hi])⟩
    · change u 1 = 1 at hi
      exact hp _ 0 1 (by decide) (by simp [nativeLowerPrismMap, hi])
    · change u 2 = 1 at hi
      exact p.property _ ⟨2, Or.inr (by simp [nativeLowerPrismMap, hi])⟩

theorem ThirdHurewicz.nativeUpperPrismMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeUpperPrismMap u) = x := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact p.property _ ⟨0, Or.inl (by simp [nativeUpperPrismMap, hi])⟩
    · change u 1 = 0 at hi
      exact hp _ 0 1 (by decide) (by simp [nativeUpperPrismMap, hi])
    · change u 2 = 0 at hi
      exact p.property _ ⟨2, Or.inl (by simp [nativeUpperPrismMap, hi])⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact p.property _ ⟨0, Or.inr (by simp [nativeUpperPrismMap, hi])⟩
    · change u 1 = 1 at hi
      exact p.property _ ⟨1, Or.inr (by simp [nativeUpperPrismMap, hi])⟩
    · change u 2 = 1 at hi
      exact p.property _ ⟨2, Or.inr (by simp [nativeUpperPrismMap, hi])⟩

def ThirdHurewicz.nativeLowerPrismLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeLowerPrismMap (nativeLowerPrismMap_based p hp)

def ThirdHurewicz.nativeUpperPrismLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperPrismMap (nativeUpperPrismMap_based p hp)

def ThirdHurewicz.nativeMiddleChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeMiddleChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeMiddleChamber_flats)

def ThirdHurewicz.nativeHighChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeHighChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeHighChamber_flats)

def ThirdHurewicz.nativeUpperLowChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperLowChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperLowChamber_flats)

def ThirdHurewicz.nativeUpperMiddleChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperMiddleChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperMiddleChamber_flats)

def ThirdHurewicz.nativeUpperHighChamberLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperHighChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperHighChamber_flats)

def ThirdHurewicz.nativeCubeRecoveryPermutation : Fin 6 → Equiv.Perm (Fin 3) :=
  Geometry.cubePermutation ∘ Equiv.swap 2 3

theorem ThirdHurewicz.nativeCubeRecoveryPermutation_apply (i : Fin 6) :
    nativeCubeRecoveryPermutation i =
      ![1, Equiv.swap 1 2, nativeCubeCycle201, Equiv.swap 0 1, nativeCubeCycle120, Equiv.swap 0 2]
        i := by fin_cases i <;> rfl

theorem ThirdHurewicz.nativeCubeRecoveryPermutation_bijective :
    Function.Bijective nativeCubeRecoveryPermutation :=
  Geometry.cubePermutation_bijective.comp (Equiv.swap 2 3).bijective

@[simp]
theorem ThirdHurewicz.cubeOrientation_nativeCubeCycle120 :
    Geometry.cubeOrientation nativeCubeCycle120 = 1 := by
  simp [Geometry.cubeOrientation, nativeCubeCycle120, Equiv.Perm.sign_swap']

@[simp]
theorem ThirdHurewicz.cubeOrientation_nativeCubeCycle201 :
    Geometry.cubeOrientation nativeCubeCycle201 = 1 := by
  simp [Geometry.cubeOrientation, nativeCubeCycle201, Equiv.Perm.sign_swap']

theorem ThirdHurewicz.sum_nativeCubeRecoveryPermutations {A : Type*} [AddCommMonoid A]
    (F : Equiv.Perm (Fin 3) → A) :
    ∑ e, F e =
      F 1 + F (Equiv.swap 1 2) + F nativeCubeCycle201 + F (Equiv.swap 0 1) +
          F nativeCubeCycle120 +
        F (Equiv.swap 0 2) := by
  rw [← nativeCubeRecoveryPermutation_bijective.sum_comp F]
  simp [nativeCubeRecoveryPermutation_apply, Fin.sum_univ_succ, add_assoc]

theorem ThirdHurewicz.sum_oriented_nativeCubeRecoveryPermutations {A : Type*} [AddCommGroup A]
    (F : Equiv.Perm (Fin 3) → A) :
    ∑ e, Geometry.cubeOrientation e • F e =
      F 1 - F (Equiv.swap 1 2) + F nativeCubeCycle201 - F (Equiv.swap 0 1) +
          F nativeCubeCycle120 -
        F (Equiv.swap 0 2) := by
  rw [sum_nativeCubeRecoveryPermutations]
  simp [Geometry.cubeOrientation, nativeCubeCycle120, nativeCubeCycle201, Equiv.Perm.sign_swap',
    sub_eq_add_neg]

theorem ThirdHurewicz.nativeMiddleChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeMiddleChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 1 2)) := by
  simpa [nativeMiddleChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeMiddleChamberMap (Equiv.swap 1 2)
      (nativeCubeMap_based_of_commonLeft p hp nativeMiddleChamber_flats) nativeMiddleChamber_flats

theorem ThirdHurewicz.nativeHighChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeHighChamberLoop p hp) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp nativeCubeCycle201) := by
  simpa [nativeHighChamberLoop] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeHighChamberMap nativeCubeCycle201
      (nativeCubeMap_based_of_commonLeft p hp nativeHighChamber_flats) nativeHighChamber_flats

theorem ThirdHurewicz.nativeUpperLowChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperLowChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 0 1)) := by
  simpa [nativeUpperLowChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperLowChamberMap (Equiv.swap 0 1)
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperLowChamber_flats)
      nativeUpperLowChamber_flats

theorem ThirdHurewicz.nativeUpperMiddleChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperMiddleChamberLoop p hp) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp nativeCubeCycle120) := by
  simpa [nativeUpperMiddleChamberLoop] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperMiddleChamberMap nativeCubeCycle120
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperMiddleChamber_flats)
      nativeUpperMiddleChamber_flats

theorem ThirdHurewicz.nativeUpperHighChamberLoop_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperHighChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 0 2)) := by
  simpa [nativeUpperHighChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperHighChamberMap (Equiv.swap 0 2)
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperHighChamber_flats)
      nativeUpperHighChamber_flats

def ThirdHurewicz.NativeCubeCutIndependent (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    Prop :=
  ∀ u v, a (Function.update u i v) = a u

def ThirdHurewicz.NativeCubeCutBased {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval))) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

def ThirdHurewicz.nativeCubeCutLowerMap (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (a u * u i)
  continuous_toFun :=
    continuous_id.update i
      (((continuous_subtype_val.comp a.continuous).mul
            (continuous_subtype_val.comp (continuous_apply i))).subtype_mk
        _)

def ThirdHurewicz.nativeCubeCutMiddleMap (i : Fin 3) (a b : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

def ThirdHurewicz.nativeCubeCutUpperMap (i : Fin 3) (b : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (b u) 1 (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (b.continuous.prodMk (continuous_const.prodMk (continuous_apply i))))

theorem ThirdHurewicz.nativeCubeCutLowerMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutLowerMap i a u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · exact p.property _ ⟨i, Or.inl (by simp [nativeCubeCutLowerMap, hj])⟩
    · simpa [nativeCubeCutLowerMap, hj] using ha u
  · exact p.property _ ⟨j, by simpa [nativeCubeCutLowerMap, hji] using hj⟩

theorem ThirdHurewicz.nativeCubeCutMiddleMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeCubeCutMiddleMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [nativeCubeCutMiddleMap, hj] using ha u
    · simpa [nativeCubeCutMiddleMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [nativeCubeCutMiddleMap, hji] using hj⟩

theorem ThirdHurewicz.nativeCubeCutUpperMap_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (b : C(NativeCube, (unitInterval)))
    (hb : NativeCubeCutBased p i b) (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutUpperMap i b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [nativeCubeCutUpperMap, hj] using hb u
    · exact p.property _ ⟨i, Or.inr (by simp [nativeCubeCutUpperMap, hj])⟩
  · exact p.property _ ⟨j, by simpa [nativeCubeCutUpperMap, hji] using hj⟩

def ThirdHurewicz.nativeCubeCutLowerLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutLowerMap i a) (nativeCubeCutLowerMap_based p i a ha)

def ThirdHurewicz.nativeCubeCutMiddleLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutMiddleMap i a b)
    (nativeCubeCutMiddleMap_based p i a b ha hb)

def ThirdHurewicz.nativeCubeCutUpperLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (b : C(NativeCube, (unitInterval)))
    (hb : NativeCubeCutBased p i b) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutUpperMap i b) (nativeCubeCutUpperMap_based p i b hb)

@[simp]
theorem ThirdHurewicz.nativeCubeCutLowerLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (u : NativeCube) :
    nativeCubeCutLowerLoop p i a ha u = p (Function.update u i (a u * u i)) :=
  rfl

@[simp]
theorem ThirdHurewicz.nativeCubeCutMiddleLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b) (u : NativeCube) :
    nativeCubeCutMiddleLoop p i a b ha hb u =
      p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) :=
  rfl

@[simp]
theorem ThirdHurewicz.nativeCubeCutUpperLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (b : C(NativeCube, (unitInterval)))
    (hb : NativeCubeCutBased p i b) (u : NativeCube) :
    nativeCubeCutUpperLoop p i b hb u =
      p (Function.update u i (Set.Icc.convexComb (b u) 1 (u i))) :=
  rfl

def ThirdHurewicz.nativeCubeCutCoordinateMap (i : Fin 3) (w : C(NativeCube, (unitInterval))) :
    C(NativeCube, NativeCube)
    where
  toFun u := Function.update u i (w u)
  continuous_toFun := continuous_id.update i w.continuous

theorem ThirdHurewicz.nativeCubeCutCoordinateMap_boundary (i : Fin 3)
    (w : C(NativeCube, (unitInterval))) (hzero : ∀ u, u i = 0 → w u = 0)
    (hone : ∀ u, u i = 1 → w u = 1) (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeCubeCutCoordinateMap i w u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · exact ⟨i, Or.inl (by simp [nativeCubeCutCoordinateMap, hzero u hj])⟩
    · exact ⟨i, Or.inr (by simp [nativeCubeCutCoordinateMap, hone u hj])⟩
  · exact ⟨j, by simpa [nativeCubeCutCoordinateMap, hji] using hj⟩

def ThirdHurewicz.nativeCubeCutCoordinateLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (w : C(NativeCube, (unitInterval)))
    (hzero : ∀ u, u i = 0 → w u = 0) (hone : ∀ u, u i = 1 → w u = 1) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutCoordinateMap i w)
    (fun u hu => p.property _ (nativeCubeCutCoordinateMap_boundary i w hzero hone u hu))

def ThirdHurewicz.nativeCubeCutCoordinateHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (w : C(NativeCube, (unitInterval)))
    (hzero : ∀ u, u i = 0 → w u = 0) (hone : ∀ u, u i = 1 → w u = 1) :
    p.val.HomotopyRel (nativeCubeCutCoordinateLoop p i w hzero hone).val (Cube.boundary (Fin 3))
    where
  toFun v := p (Function.update v.2 i (Set.Icc.convexComb (v.2 i) (w v.2) v.1))
  continuous_toFun :=
    p.val.continuous.comp
      (continuous_snd.update i
        (Set.Icc.continuous_convexComb_prod.comp
          (((continuous_apply i).comp continuous_snd).prodMk
            ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left u := by simp
  map_one_left
    u := by
    change
      p (Function.update u i (Set.Icc.convexComb (u i) (w u) 1)) = p (Function.update u i (w u))
    rw [Set.Icc.convexComb_one]
  prop' t u
    hu := by
    rw [p.property u hu]
    apply p.property
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · exact ⟨i, Or.inl (by simp [hj, hzero u hj])⟩
      · exact ⟨i, Or.inr (by simp [hj, hone u hj])⟩
    · exact ⟨j, by simpa [hji] using hj⟩

def ThirdHurewicz.nativeCubeCutTwoWarpCoordinate (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    C(NativeCube, (unitInterval))
    where
  toFun u := SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate (a u, u i)
  continuous_toFun :=
    SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate.continuous.comp
      (a.continuous.prodMk (continuous_apply i))

theorem ThirdHurewicz.nativeCubeCutTwoWarpCoordinate_zero (i : Fin 3)
    (a : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 0) :
    nativeCubeCutTwoWarpCoordinate i a u = 0 := by simp [nativeCubeCutTwoWarpCoordinate, hu]

theorem ThirdHurewicz.nativeCubeCutTwoWarpCoordinate_one (i : Fin 3)
    (a : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 1) :
    nativeCubeCutTwoWarpCoordinate i a u = 1 := by simp [nativeCubeCutTwoWarpCoordinate, hu]

def ThirdHurewicz.nativeCubeCutTwoWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval))) :
    GenLoop (Fin 3) X x :=
  nativeCubeCutCoordinateLoop p i (nativeCubeCutTwoWarpCoordinate i a)
    (nativeCubeCutTwoWarpCoordinate_zero i a) (nativeCubeCutTwoWarpCoordinate_one i a)

theorem ThirdHurewicz.nativeCubeCutTwoWarpLoop_eq_transAt {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (haInd : NativeCubeCutIndependent i a) :
    nativeCubeCutTwoWarpLoop p i a =
      GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutUpperLoop p i a ha) := by
  apply GenLoop.ext
  intro u
  change
    p
        (Function.update u i
          (SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate (a u, u i))) =
      if (u i : ℝ) ≤ 1 / 2 then
        nativeCubeCutLowerLoop p i a ha
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        nativeCubeCutUpperLoop p i a ha
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))
  split_ifs with h
  · rw [nativeCubeCutLowerLoop_apply, haInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_le_half (a u) (u i) h)
  · rw [nativeCubeCutUpperLoop_apply, haInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (SecondHurewicz.SimplyConnected.subdivisionWarpCoordinate_of_half_lt (a u) (u i)
          (lt_of_not_ge h))

theorem ThirdHurewicz.nativeCubeCutTwo_homotopic {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (haInd : NativeCubeCutIndependent i a) :
    GenLoop.Homotopic p
      (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutUpperLoop p i a ha)) := by
  have h : GenLoop.Homotopic p (nativeCubeCutTwoWarpLoop p i a) :=
    ⟨nativeCubeCutCoordinateHomotopy p i (nativeCubeCutTwoWarpCoordinate i a)
        (nativeCubeCutTwoWarpCoordinate_zero i a) (nativeCubeCutTwoWarpCoordinate_one i a)⟩
  rwa [nativeCubeCutTwoWarpLoop_eq_transAt p i a ha haInd] at h

theorem ThirdHurewicz.nativeCubeCutTwo_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (haInd : NativeCubeCutIndependent i a) :
    nativeCubeClass p =
      nativeCubeClass (nativeCubeCutLowerLoop p i a ha) +
        nativeCubeClass (nativeCubeCutUpperLoop p i a ha) :=
  (nativeCubeClass_homotopic (nativeCubeCutTwo_homotopic p i a ha haInd)).trans
    (nativeCubeClass_transAt i _ _)

def ThirdHurewicz.subdivisionWarpThreeCoordinate :
    C(((unitInterval) × (unitInterval)) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb (p.1.1 * Set.projIcc 0 1 zero_le_one (4 * (p.2 : ℝ)))
      (Set.Icc.convexComb p.1.2 1 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1)))
      (Set.projIcc 0 1 zero_le_one (4 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_apply (a b w : (unitInterval)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb (a * Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)))
        (Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)))
        (Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1)) :=
  rfl

@[simp]
theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_zero (a b : (unitInterval)) :
    subdivisionWarpThreeCoordinate ((a, b), 0) = 0 := by
  norm_num [subdivisionWarpThreeCoordinate, Set.projIcc, Set.Icc.convexComb]

@[simp]
theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_one (a b : (unitInterval)) :
    subdivisionWarpThreeCoordinate ((a, b), 1) = 1 := by
  norm_num [subdivisionWarpThreeCoordinate, Set.projIcc, Set.Icc.convexComb]

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_le_quarter (a b w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 4) :
    subdivisionWarpThreeCoordinate ((a, b), w) = a * Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)) := by
  have hz : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hz, Set.Icc.convexComb_zero]

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_quarter_le_of_le_half
    (a b w : (unitInterval)) (hl : 1 / 4 ≤ (w : ℝ)) (hu : (w : ℝ) ≤ 1 / 2) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  have hzero : Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hone, hzero, mul_one, Set.Icc.convexComb_zero]

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_half_le (a b w : (unitInterval))
    (hw : 1 / 2 ≤ (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) := by
  have hone : Set.projIcc 0 1 zero_le_one (4 * (w : ℝ) - 1) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [subdivisionWarpThreeCoordinate_apply, hone, Set.Icc.convexComb_one]

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_of_half_lt (a b w : (unitInterval))
    (hw : 1 / 2 < (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) :=
  subdivisionWarpThreeCoordinate_of_half_le a b w hw.le

theorem ThirdHurewicz.subdivisionWarpThree_clip_two_coe (w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 2) : (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) = 2 * (w : ℝ) := by
  have hmem : 2 * (w : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [w.property.1], by linarith⟩
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hmem)

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_nested_lower (a b w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 2) (hi : (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) ≤ 1 / 2) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      a * Set.projIcc 0 1 zero_le_one (2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ)) := by
  have hc := subdivisionWarpThree_clip_two_coe w hw
  have hquarter : (w : ℝ) ≤ 1 / 4 := by rw [hc] at hi; linarith
  have he : 2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) = 4 * (w : ℝ) := by rw [hc]; ring
  rw [he]
  exact subdivisionWarpThreeCoordinate_of_le_quarter a b w hquarter

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_nested_middle (a b w : (unitInterval))
    (hw : (w : ℝ) ≤ 1 / 2) (hi : 1 / 2 < (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb a b
        (Set.projIcc 0 1 zero_le_one (2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) - 1)) :=
  by
  have hc := subdivisionWarpThree_clip_two_coe w hw
  have hquarter : 1 / 4 ≤ (w : ℝ) := by rw [hc] at hi; linarith
  have he : 2 * (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ)) : ℝ) - 1 = 4 * (w : ℝ) - 1 := by
    rw [hc]; ring
  rw [he]
  exact subdivisionWarpThreeCoordinate_of_quarter_le_of_le_half a b w hquarter hw

theorem ThirdHurewicz.subdivisionWarpThreeCoordinate_nested_upper (a b w : (unitInterval))
    (hw : 1 / 2 < (w : ℝ)) :
    subdivisionWarpThreeCoordinate ((a, b), w) =
      Set.Icc.convexComb b 1 (Set.projIcc 0 1 zero_le_one (2 * (w : ℝ) - 1)) :=
  subdivisionWarpThreeCoordinate_of_half_lt a b w hw

def ThirdHurewicz.nativeCubeCutThreeWarpCoordinate (i : Fin 3)
    (a b : C(NativeCube, (unitInterval))) : C(NativeCube, (unitInterval))
    where
  toFun u := subdivisionWarpThreeCoordinate ((a u, b u), u i)
  continuous_toFun :=
    subdivisionWarpThreeCoordinate.continuous.comp
      ((a.continuous.prodMk b.continuous).prodMk (continuous_apply i))

theorem ThirdHurewicz.nativeCubeCutThreeWarpCoordinate_zero (i : Fin 3)
    (a b : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 0) :
    nativeCubeCutThreeWarpCoordinate i a b u = 0 := by simp [nativeCubeCutThreeWarpCoordinate, hu]

theorem ThirdHurewicz.nativeCubeCutThreeWarpCoordinate_one (i : Fin 3)
    (a b : C(NativeCube, (unitInterval))) (u : NativeCube) (hu : u i = 1) :
    nativeCubeCutThreeWarpCoordinate i a b u = 1 := by simp [nativeCubeCutThreeWarpCoordinate, hu]

def ThirdHurewicz.nativeCubeCutThreeWarpLoop {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval))) :
    GenLoop (Fin 3) X x :=
  nativeCubeCutCoordinateLoop p i (nativeCubeCutThreeWarpCoordinate i a b)
    (nativeCubeCutThreeWarpCoordinate_zero i a b) (nativeCubeCutThreeWarpCoordinate_one i a b)

theorem ThirdHurewicz.nativeCubeCutThreeWarpLoop_eq_transAt {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b)
    (haInd : NativeCubeCutIndependent i a) (hbInd : NativeCubeCutIndependent i b) :
    nativeCubeCutThreeWarpLoop p i a b =
      GenLoop.transAt i
        (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
          (nativeCubeCutMiddleLoop p i a b ha hb))
        (nativeCubeCutUpperLoop p i b hb) := by
  apply GenLoop.ext
  intro u
  change
    p (Function.update u i (subdivisionWarpThreeCoordinate ((a u, b u), u i))) =
      if (u i : ℝ) ≤ 1 / 2 then
        (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
            (nativeCubeCutMiddleLoop p i a b ha hb))
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        nativeCubeCutUpperLoop p i b hb
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))
  split_ifs with h
  · change
      p (Function.update u i (subdivisionWarpThreeCoordinate ((a u, b u), u i))) =
        if
            ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ) ≤
              1 / 2 then
          nativeCubeCutLowerLoop p i a ha
            (Function.update (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i
              (Set.projIcc 0 1 zero_le_one
                (2 *
                  ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ))))
        else
          nativeCubeCutMiddleLoop p i a b ha hb
            (Function.update (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i
              (Set.projIcc 0 1 zero_le_one
                (2 * ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ) -
                  1)))
    simp only [Function.update_self]
    split_ifs with hi
    · simp only [nativeCubeCutLowerLoop_apply, Function.update_self, Function.update_idem]
      rw [haInd u _]
      exact
        congrArg (fun v => p (Function.update u i v))
          (subdivisionWarpThreeCoordinate_nested_lower (a u) (b u) (u i) h hi)
    · simp only [nativeCubeCutMiddleLoop_apply, Function.update_self, Function.update_idem]
      rw [haInd u _, hbInd u _]
      exact
        congrArg (fun v => p (Function.update u i v))
          (subdivisionWarpThreeCoordinate_nested_middle (a u) (b u) (u i) h (lt_of_not_ge hi))
  · rw [nativeCubeCutUpperLoop_apply, hbInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (subdivisionWarpThreeCoordinate_nested_upper (a u) (b u) (u i) (lt_of_not_ge h))

theorem ThirdHurewicz.nativeCubeCutThree_homotopic {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b)
    (haInd : NativeCubeCutIndependent i a) (hbInd : NativeCubeCutIndependent i b) :
    GenLoop.Homotopic p
      (GenLoop.transAt i
        (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
          (nativeCubeCutMiddleLoop p i a b ha hb))
        (nativeCubeCutUpperLoop p i b hb)) := by
  have h : GenLoop.Homotopic p (nativeCubeCutThreeWarpLoop p i a b) :=
    ⟨nativeCubeCutCoordinateHomotopy p i (nativeCubeCutThreeWarpCoordinate i a b)
        (nativeCubeCutThreeWarpCoordinate_zero i a b)
        (nativeCubeCutThreeWarpCoordinate_one i a b)⟩
  rwa [nativeCubeCutThreeWarpLoop_eq_transAt p i a b ha hb haInd hbInd] at h

theorem ThirdHurewicz.nativeCubeCutThree_class {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (i : Fin 3) (a b : C(NativeCube, (unitInterval)))
    (ha : NativeCubeCutBased p i a) (hb : NativeCubeCutBased p i b)
    (haInd : NativeCubeCutIndependent i a) (hbInd : NativeCubeCutIndependent i b) :
    nativeCubeClass p =
      nativeCubeClass (nativeCubeCutLowerLoop p i a ha) +
          nativeCubeClass (nativeCubeCutMiddleLoop p i a b ha hb) +
        nativeCubeClass (nativeCubeCutUpperLoop p i b hb) := by
  rw [nativeCubeClass_homotopic (nativeCubeCutThree_homotopic p i a b ha hb haInd hbInd),
    nativeCubeClass_transAt, nativeCubeClass_transAt]

def ThirdHurewicz.nativePrismFirstCut : C(NativeCube, (unitInterval)) :=
  ⟨fun u => u 0, continuous_apply 0⟩

def ThirdHurewicz.nativeLowerPrismCut : C(NativeCube, (unitInterval))
    where
  toFun u := u 0 * u 1
  continuous_toFun := by fun_prop

def ThirdHurewicz.nativeUpperPrismCut : C(NativeCube, (unitInterval))
    where
  toFun u := Set.Icc.convexComb (u 0) 1 (u 1)
  continuous_toFun := by fun_prop

theorem ThirdHurewicz.nativePrismFirstCut_independent (i : Fin 3) (hi : i ≠ 0) :
    NativeCubeCutIndependent i nativePrismFirstCut := by
  intro u v
  simp [nativePrismFirstCut, hi.symm]

theorem ThirdHurewicz.nativeLowerPrismCut_independent :
    NativeCubeCutIndependent 2 nativeLowerPrismCut := by
  intro u v
  simp [nativeLowerPrismCut]

theorem ThirdHurewicz.nativeUpperPrismCut_independent :
    NativeCubeCutIndependent 2 nativeUpperPrismCut := by
  intro u v
  simp [nativeUpperPrismCut]

theorem ThirdHurewicz.nativeInterval_convexComb_mul (a b t : (unitInterval)) :
    Set.Icc.convexComb (a * b) a t = a * Set.Icc.convexComb b 1 t := by
  apply Subtype.ext
  change
    (1 - (t : ℝ)) * ((a : ℝ) * (b : ℝ)) + (t : ℝ) * (a : ℝ) =
      (a : ℝ) * ((1 - (t : ℝ)) * (b : ℝ) + (t : ℝ) * 1)
  ring

theorem ThirdHurewicz.nativePrismFirstCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased p 1 nativePrismFirstCut := by
  intro u
  exact hp _ 0 1 (by decide) (by simp [nativePrismFirstCut])

theorem ThirdHurewicz.nativeLowerPrismCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut := by
  intro u
  change p (nativeLowerPrismMap (Function.update u 2 (u 0 * u 1))) = x
  exact hp _ 1 2 (by decide) (by simp [nativeLowerPrismMap])

theorem ThirdHurewicz.nativeLowerPrismFirstCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeLowerPrismLoop p hp) 2 nativePrismFirstCut := by
  intro u
  change p (nativeLowerPrismMap (Function.update u 2 (u 0))) = x
  exact hp _ 0 2 (by decide) (by simp [nativeLowerPrismMap])

theorem ThirdHurewicz.nativeUpperPrismFirstCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut := by
  intro u
  change p (nativeUpperPrismMap (Function.update u 2 (u 0))) = x
  exact hp _ 0 2 (by decide) (by simp [nativeUpperPrismMap])

theorem ThirdHurewicz.nativeUpperPrismCut_based {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeUpperPrismLoop p hp) 2 nativeUpperPrismCut := by
  intro u
  change p (nativeUpperPrismMap (Function.update u 2 (Set.Icc.convexComb (u 0) 1 (u 1)))) = x
  exact hp _ 1 2 (by decide) (by simp [nativeUpperPrismMap])

theorem ThirdHurewicz.nativeCubeCutLowerLoop_eq_lowerPrism {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp) =
      nativeLowerPrismLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeCubeCutUpperLoop_eq_upperPrism {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp) =
      nativeUpperPrismLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeCubeClass_prisms {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass p =
      nativeCubeClass (nativeLowerPrismLoop p hp) + nativeCubeClass (nativeUpperPrismLoop p hp) :=
  by
  simpa only [nativeCubeCutLowerLoop_eq_lowerPrism p hp,
    nativeCubeCutUpperLoop_eq_upperPrism p hp] using
    nativeCubeCutTwo_class p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp)
      (nativePrismFirstCut_independent 1 (by decide))

theorem ThirdHurewicz.nativeLowerPrismCutLowerLoop_eq_duffy {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut
        (nativeLowerPrismCut_based p hp) =
      nativeDuffyCubeLoop p hp 1 := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeLowerPrismCutMiddleLoop_eq_middle {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutMiddleLoop (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut nativePrismFirstCut
        (nativeLowerPrismCut_based p hp) (nativeLowerPrismFirstCut_based p hp) =
      nativeMiddleChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  change
    p ![u 0, u 0 * u 1, Set.Icc.convexComb (u 0 * u 1) (u 0) (u 2)] =
      p ![u 0, u 0 * u 1, u 0 * Set.Icc.convexComb (u 1) 1 (u 2)]
  rw [nativeInterval_convexComb_mul]

theorem ThirdHurewicz.nativeLowerPrismCutUpperLoop_eq_high {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop (nativeLowerPrismLoop p hp) 2 nativePrismFirstCut
        (nativeLowerPrismFirstCut_based p hp) =
      nativeHighChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeLowerPrismClass_eq {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeLowerPrismLoop p hp) =
      nativeCubeClass (nativeDuffyCubeLoop p hp 1) +
          nativeCubeClass (nativeMiddleChamberLoop p hp) +
        nativeCubeClass (nativeHighChamberLoop p hp) := by
  simpa only [nativeLowerPrismCutLowerLoop_eq_duffy, nativeLowerPrismCutMiddleLoop_eq_middle,
    nativeLowerPrismCutUpperLoop_eq_high] using
    nativeCubeCutThree_class (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut nativePrismFirstCut
      (nativeLowerPrismCut_based p hp) (nativeLowerPrismFirstCut_based p hp)
      nativeLowerPrismCut_independent (nativePrismFirstCut_independent 2 (by decide))

theorem ThirdHurewicz.nativeUpperPrismCutLowerLoop_eq_lower {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut
        (nativeUpperPrismFirstCut_based p hp) =
      nativeUpperLowChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeUpperPrismCutMiddleLoop_eq_middle {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutMiddleLoop (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut nativeUpperPrismCut
        (nativeUpperPrismFirstCut_based p hp) (nativeUpperPrismCut_based p hp) =
      nativeUpperMiddleChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeUpperPrismCutUpperLoop_eq_upper {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop (nativeUpperPrismLoop p hp) 2 nativeUpperPrismCut
        (nativeUpperPrismCut_based p hp) =
      nativeUpperHighChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem ThirdHurewicz.nativeUpperPrismClass_eq {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperPrismLoop p hp) =
      nativeCubeClass (nativeUpperLowChamberLoop p hp) +
          nativeCubeClass (nativeUpperMiddleChamberLoop p hp) +
        nativeCubeClass (nativeUpperHighChamberLoop p hp) := by
  simpa only [nativeUpperPrismCutLowerLoop_eq_lower, nativeUpperPrismCutMiddleLoop_eq_middle,
    nativeUpperPrismCutUpperLoop_eq_upper] using
    nativeCubeCutThree_class (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut nativeUpperPrismCut
      (nativeUpperPrismFirstCut_based p hp) (nativeUpperPrismCut_based p hp)
      (nativePrismFirstCut_independent 2 (by decide)) nativeUpperPrismCut_independent

theorem ThirdHurewicz.nativeCubeClass_eq_sum_tetrahedra {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    nativeCubeClass p =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  by
  rw [sum_oriented_nativeCubeRecoveryPermutations, nativeCubeClass_prisms p hp,
    nativeLowerPrismClass_eq, nativeUpperPrismClass_eq,
    nativeDuffyCubeClass_eq_basedThreeSimplexClass, nativeMiddleChamberLoop_class,
    nativeHighChamberLoop_class, nativeUpperLowChamberLoop_class,
    nativeUpperMiddleChamberLoop_class, nativeUpperHighChamberLoop_class]
  simp only [sub_eq_add_neg, add_assoc]

theorem ThirdHurewicz.nativeCubeSubdivision_class {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ 3 X x) =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  nativeCubeClass_eq_sum_tetrahedra p hp

theorem ThirdHurewicz.nativeCubeSubdivision_homotopy_class {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 3) X x) (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 3)))
    (hq : NativeCubeInternalBased q) :
    nativeCubeClass p =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron q hq e) :=
  (nativeCubeClass_homotopic ⟨H⟩).trans (nativeCubeClass_eq_sum_tetrahedra q hq)

theorem ThirdHurewicz.fourSimplexLoopA_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopA τ) =
      basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) :=
  (nativeCubeSubdivision_class (fourSimplexLoopA τ) (fourSimplexLoopA_internal τ)).trans
    (fourSimplexTetrahedraA_sum τ)

theorem ThirdHurewicz.fourSimplexLoopB_class {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopB τ) =
      -(basedThreeSimplexClass (basedFourSimplexFace τ 4) +
            basedThreeSimplexClass (basedFourSimplexFace τ 2) +
          basedThreeSimplexClass (basedFourSimplexFace τ 0)) :=
  (nativeCubeSubdivision_class (fourSimplexLoopB τ) (fourSimplexLoopB_internal τ)).trans
    (fourSimplexTetrahedraB_sum τ)

theorem ThirdHurewicz.basedFourSimplex_pair_relation {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) =
      basedThreeSimplexClass (basedFourSimplexFace τ 4) +
          basedThreeSimplexClass (basedFourSimplexFace τ 2) +
        basedThreeSimplexClass (basedFourSimplexFace τ 0) := by
  have h := fourSimplexFillings_additiveClass τ
  rw [fourSimplexLoopA_class, fourSimplexLoopB_class, neg_neg] at h
  exact h

theorem ThirdHurewicz.basedFourSimplex_boundary_relation {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    basedThreeSimplexClass (basedFourSimplexFace τ 0) -
              basedThreeSimplexClass (basedFourSimplexFace τ 1) +
            basedThreeSimplexClass (basedFourSimplexFace τ 2) -
          basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 4) =
      0 := by
  calc
    _ =
        (basedThreeSimplexClass (basedFourSimplexFace τ 4) +
              basedThreeSimplexClass (basedFourSimplexFace τ 2) +
            basedThreeSimplexClass (basedFourSimplexFace τ 0)) -
          (basedThreeSimplexClass (basedFourSimplexFace τ 3) +
            basedThreeSimplexClass (basedFourSimplexFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedFourSimplex_pair_relation τ).symm

theorem ThirdHurewicz.basedFourSimplex_signed_relation {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    ∑ i : Fin 5, (-1 : ℤ) ^ i.val • basedThreeSimplexClass (basedFourSimplexFace τ i) = 0 := by
  have h := basedFourSimplex_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

theorem ThirdHurewicz.normalizedThreeSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    ∑ i : Fin 5,
        (-1 : ℤ) ^ i.val •
          basedThreeSimplexClass
            (normalizedThreeSimplex x (smp.comp (FirstHurewicz.simplexFace 3 i))) =
      0 := by
  simpa only [normalizedFourSimplex_face] using
    basedFourSimplex_signed_relation (normalizedFourSimplex x smp)

theorem ThirdHurewicz.threeSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (b : FirstHurewicz.Chains X 4) :
    threeSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 4 3).hom b) = 0 := by
  have h : (threeSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 4 3).hom = 0 :=
    by
    apply FirstHurewicz.chainMap_ext X 4
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      threeSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedThreeSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

def ThirdHurewicz.cylinderHomotopy {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    (H : C((unitInterval) × A, X)) :
    ContinuousMap.Homotopy (SecondHurewicz.SimplyConnected.timeSlice H 0)
      (SecondHurewicz.SimplyConnected.timeSlice H 1)
    where
  toContinuousMap := H
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem ThirdHurewicz.homotopyTrans_compContinuousMap {A B X : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace X] {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (f : C(B, A)) :
    (F.trans G).toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap f) =
      ((F.compContinuousMap f).trans (G.compContinuousMap f)).toContinuousMap := by
  ext z
  change (F.trans G) (z.1, f z.2) = ((F.compContinuousMap f).trans (G.compContinuousMap f)) z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

theorem ThirdHurewicz.homotopyTrans_const {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (x : X)
    (hF : F.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x)
    (hG : G.toContinuousMap = ContinuousMap.const ((unitInterval) × A) x) :
    (F.trans G).toContinuousMap = ContinuousMap.const ((unitInterval) × A) x := by
  ext z
  change (F.trans G) z = x
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

theorem ThirdHurewicz.homotopyTrans_congr {A X : Type} [TopologicalSpace A] [TopologicalSpace X]
    {f₀ f₁ f₂ g₀ g₁ g₂ : C(A, X)} (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (F' : g₀.Homotopy g₁)
    (G' : g₁.Homotopy g₂) (hF : F.toContinuousMap = F'.toContinuousMap)
    (hG : G.toContinuousMap = G'.toContinuousMap) :
    (F.trans G).toContinuousMap = (F'.trans G').toContinuousMap := by
  ext z
  change (F.trans G) z = (F'.trans G') z
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact ContinuousMap.congr_fun hF _
  · exact ContinuousMap.congr_fun hG _

def ThirdHurewicz.simplexFamilyHomotopy {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (h₀ : ∀ smp s, H smp (0, s) = smp s) (smp : FirstHurewicz.SingularSimplex X n) :
    smp.Homotopy (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1) :=
  (cylinderHomotopy (H smp)).cast (by ext s; exact h₀ smp s) rfl

def ThirdHurewicz.composeSimplexHomotopies {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) : C((unitInterval) × FirstHurewicz.Simplex n, X) :=
  ((simplexFamilyHomotopy H hH₀ smp).trans
      (simplexFamilyHomotopy G hG₀
        (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1))).toContinuousMap

@[simp]
theorem ThirdHurewicz.composeSimplexHomotopies_zero {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) (s : FirstHurewicz.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (0, s) = smp s :=
  ContinuousMap.Homotopy.apply_zero _ s

@[simp]
theorem ThirdHurewicz.composeSimplexHomotopies_one {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) (s : FirstHurewicz.Simplex n) :
    composeSimplexHomotopies H G hH₀ hG₀ smp (1, s) =
      G (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1) (1, s) :=
  ContinuousMap.Homotopy.apply_one _ s

@[simp]
theorem ThirdHurewicz.timeSlice_composeSimplexHomotopies_one {X : Type} [TopologicalSpace X]
    {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (smp : FirstHurewicz.SingularSimplex X n) :
    SecondHurewicz.SimplyConnected.timeSlice (composeSimplexHomotopies H G hH₀ hG₀ smp) 1 =
      SecondHurewicz.SimplyConnected.timeSlice
        (G (SecondHurewicz.SimplyConnected.timeSlice (H smp) 1)) 1 := by
  ext s
  exact composeSimplexHomotopies_one H G hH₀ hG₀ smp s

theorem ThirdHurewicz.composeSimplexHomotopies_face {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' G' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s)
    (hH'₀ : ∀ smp s, H' smp (0, s) = smp s) (hG'₀ : ∀ smp s, G' smp (0, s) = smp s)
    (hH : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hG : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n G G') :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n
      (composeSimplexHomotopies H G hH₀ hG₀) (composeSimplexHomotopies H' G' hH'₀ hG'₀) := by
  intro smp i
  unfold composeSimplexHomotopies
  rw [homotopyTrans_compContinuousMap]
  apply homotopyTrans_congr
  · change
      (H' smp).comp ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i)) =
        H (smp.comp (FirstHurewicz.simplexFace n i))
    exact hH smp i
  · change
      (G' (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)).comp
          ((ContinuousMap.id (unitInterval)).prodMap (FirstHurewicz.simplexFace n i)) =
        G
          (SecondHurewicz.SimplyConnected.timeSlice (H (smp.comp (FirstHurewicz.simplexFace n i)))
            1)
    rw [hG (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1) i,
      SecondHurewicz.SimplyConnected.timeSlice_face hH smp i 1]

theorem ThirdHurewicz.composeSimplexHomotopies_const {X : Type} [TopologicalSpace X] {n : ℕ}
    (H G : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hH₀ : ∀ smp s, H smp (0, s) = smp s) (hG₀ : ∀ smp s, G smp (0, s) = smp s) (x : X)
    (hH :
      H (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hG :
      G (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x) :
    composeSimplexHomotopies H G hH₀ hG₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  have h₁ :
    SecondHurewicz.SimplyConnected.timeSlice (H (ContinuousMap.const (FirstHurewicz.Simplex n) x))
        1 =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
    rw [hH]
    rfl
  unfold composeSimplexHomotopies
  apply homotopyTrans_const
  · exact hH
  · change
      G
          (SecondHurewicz.SimplyConnected.timeSlice
            (H (ContinuousMap.const (FirstHurewicz.Simplex n) x)) 1) =
        _
    rw [h₁]
    exact hG

def ThirdHurewicz.vertexEdgeTriangleHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X) :=
  composeSimplexHomotopies (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x)

def ThirdHurewicz.vertexEdgeThreeSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  composeSimplexHomotopies (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x)

@[simp]
theorem ThirdHurewicz.vertexEdgeTriangleHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 2)
    (s : FirstHurewicz.Simplex 2) : vertexEdgeTriangleHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp]
theorem ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3)
    (s : FirstHurewicz.Simplex 3) : vertexEdgeThreeSimplexHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem ThirdHurewicz.vertexEdgeHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 (vertexEdgeTriangleHomotopy x)
      (vertexEdgeThreeSimplexHomotopy x) :=
  composeSimplexHomotopies_face (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 3)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_face x 2)
    (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_face x)

@[simp]
theorem ThirdHurewicz.vertexEdgeTriangleHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) :
    vertexEdgeTriangleHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x :=
  composeSimplexHomotopies_const (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy x)
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 2)
    (SecondHurewicz.SimplyConnected.triangleEdgeStraighteningHomotopy_zero x) x
    (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const x 2)
    (edgeTriangleHomotopy_const x)

@[simp]
theorem ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) (smp : FirstHurewicz.SingularSimplex X 3) :
    SecondHurewicz.SimplyConnected.timeSlice (vertexEdgeThreeSimplexHomotopy x smp) 1 =
      SecondHurewicz.SimplyConnected.normalizedTetrahedronMap x smp := by
  rw [vertexEdgeThreeSimplexHomotopy, timeSlice_composeSimplexHomotopies_one]
  rfl

def ThirdHurewicz.normalizationTriangleHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.SingularSimplex X 2 → C((unitInterval) × FirstHurewicz.Simplex 2, X) :=
  composeSimplexHomotopies (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x)

def ThirdHurewicz.normalizationThreeSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  composeSimplexHomotopies (vertexEdgeThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy x)
    (vertexEdgeThreeSimplexHomotopy_zero x) (triangleThreeSimplexHomotopy_zero x)

@[simp]
theorem ThirdHurewicz.normalizationThreeSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) (s : FirstHurewicz.Simplex 3) :
    normalizationThreeSimplexHomotopy x smp (0, s) = smp s :=
  composeSimplexHomotopies_zero _ _ _ _ smp s

theorem ThirdHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 (normalizationTriangleHomotopy x)
      (normalizationThreeSimplexHomotopy x) :=
  composeSimplexHomotopies_face (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeThreeSimplexHomotopy x) (triangleThreeSimplexHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x)
    (vertexEdgeThreeSimplexHomotopy_zero x) (triangleThreeSimplexHomotopy_zero x)
    (vertexEdgeHomotopy_face x) (triangleThreeSimplexHomotopy_face x)

@[simp]
theorem ThirdHurewicz.normalizationTriangleHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    normalizationTriangleHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x :=
  composeSimplexHomotopies_const (vertexEdgeTriangleHomotopy x) (triangleStraighteningHomotopy x)
    (vertexEdgeTriangleHomotopy_zero x) (triangleStraighteningHomotopy_zero x) x
    (vertexEdgeTriangleHomotopy_const x) (triangleStraighteningHomotopy_const x)

@[simp]
theorem ThirdHurewicz.normalizationThreeSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationThreeSimplexHomotopy x smp) 1 =
      (normalizedThreeSimplex x smp).val := by
  rw [normalizationThreeSimplexHomotopy, timeSlice_composeSimplexHomotopies_one,
    vertexEdgeThreeSimplexHomotopy_endpoint]
  rfl

abbrev ThirdHurewicz.CubeTriangulation.SortedCoordinates {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) (e : Equiv.Perm (Fin 3)) : Prop :=
  u (e 2) ≤ u (e 1) ∧ u (e 1) ≤ u (e 0)

theorem ThirdHurewicz.CubeTriangulation.exists_sortedPermutation {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) : ∃ e : Equiv.Perm (Fin 3), SortedCoordinates u e := by
  rcases le_total (u 0) (u 1) with h01 | h10
  · rcases le_total (u 1) (u 2) with h12 | h21
    · refine ⟨Equiv.swap 0 2, ?_⟩
      simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h01 h12
    · rcases le_total (u 0) (u 2) with h02 | h20
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 0 2), ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h02 h21
      · refine ⟨Equiv.swap 0 1, ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h20 h01
  · rcases le_total (u 0) (u 2) with h02 | h20
    · refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), ?_⟩
      simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h10 h02
    · rcases le_total (u 1) (u 2) with h12 | h21
      · refine ⟨Equiv.swap 1 2, ?_⟩
        simpa [SortedCoordinates, Equiv.swap_apply_def] using And.intro h12 h20
      · exact ⟨Equiv.refl (Fin 3), h21, h10⟩

def ThirdHurewicz.CubeTriangulation.cubeOrderedRegion (e : Equiv.Perm (Fin 3)) :
    Set ThirdHurewicz.Geometry.Cube3 :=
  {u | SortedCoordinates u e}

theorem ThirdHurewicz.CubeTriangulation.continuous_cubeCoordinate (i : Fin 3) :
    Continuous (fun u : ThirdHurewicz.Geometry.Cube3 => (u i : ℝ)) :=
  continuous_subtype_val.comp (continuous_apply i)

def ThirdHurewicz.CubeTriangulation.cubeBarycentric (e : Equiv.Perm (Fin 3))
    (u : ThirdHurewicz.Geometry.Cube3) : Fin 4 → ℝ :=
  ![1 - (u (e 0) : ℝ), (u (e 0) : ℝ) - u (e 1), (u (e 1) : ℝ) - u (e 2), (u (e 2) : ℝ)]

theorem ThirdHurewicz.CubeTriangulation.cubeBarycentric_nonneg (e : Equiv.Perm (Fin 3))
    (u : ThirdHurewicz.Geometry.Cube3) (h : SortedCoordinates u e) (i : Fin 4) :
    0 ≤ cubeBarycentric e u i := by
  fin_cases i
  · exact sub_nonneg.mpr (u (e 0)).property.2
  · exact sub_nonneg.mpr h.2
  · exact sub_nonneg.mpr h.1
  · exact (u (e 2)).property.1

theorem ThirdHurewicz.CubeTriangulation.cubeBarycentric_sum (e : Equiv.Perm (Fin 3))
    (u : ThirdHurewicz.Geometry.Cube3) : ∑ i, cubeBarycentric e u i = 1 := by
  simp [cubeBarycentric, Fin.sum_univ_succ]

def ThirdHurewicz.CubeTriangulation.cubeTetrahedronInverse (e : Equiv.Perm (Fin 3)) :
    C(↥(cubeOrderedRegion e), FirstHurewicz.Simplex 3)
    where
  toFun
    u :=
    ⟨cubeBarycentric e u.val,
      ⟨cubeBarycentric_nonneg e u.val u.property, cubeBarycentric_sum e u.val⟩⟩
  continuous_toFun := by
    have hc (i : Fin 3) : Continuous (fun u : ↥(cubeOrderedRegion e) => (u.val i : ℝ)) :=
      (continuous_cubeCoordinate i).comp continuous_subtype_val
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const.sub (hc (e 0))
    · exact (hc (e 0)).sub (hc (e 1))
    · exact (hc (e 1)).sub (hc (e 2))
    · exact hc (e 2)

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_sorted (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) :
    SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s) e :=
  ⟨ThirdHurewicz.Geometry.cubeTetrahedron_order_second e s,
    ThirdHurewicz.Geometry.cubeTetrahedron_order_first e s⟩

@[simp]
theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_inverse (e : Equiv.Perm (Fin 3))
    (u : ↥(cubeOrderedRegion e)) :
    ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) = u.val := by
  funext k
  obtain ⟨j, rfl⟩ := e.surjective k
  apply Subtype.ext
  fin_cases j
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) (e 0) : ℝ) =
        (u.val (e 0) : ℝ)
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero]
    change
      ((u.val (e 0) : ℝ) - u.val (e 1)) + ((u.val (e 1) : ℝ) - u.val (e 2)) + u.val (e 2) =
        (u.val (e 0) : ℝ)
    ring
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) (e 1) : ℝ) =
        (u.val (e 1) : ℝ)
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one]
    change ((u.val (e 1) : ℝ) - u.val (e 2)) + u.val (e 2) = (u.val (e 1) : ℝ)
    ring
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e (cubeTetrahedronInverse e u) (e 2) : ℝ) =
        (u.val (e 2) : ℝ)
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two]
    rfl

@[simp]
theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedronInverse_tetrahedron
    (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3) :
    cubeTetrahedronInverse e
        ⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩ =
      s := by
  apply Subtype.ext
  funext i
  change cubeBarycentric e (ThirdHurewicz.Geometry.cubeTetrahedron e s) i = s i
  fin_cases i
  · change 1 - (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) = s 0
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero]
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
    linarith
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) -
          ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) =
        s 1
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero,
      ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one]
    ring
  · change
      (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) : ℝ) -
          ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) =
        s 2
    rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one,
      ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two]
    ring
  · change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) : ℝ) = s 3
    exact ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two e s

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_injective (e : Equiv.Perm (Fin 3)) :
    Function.Injective (ThirdHurewicz.Geometry.cubeTetrahedron e) := by
  intro s t h
  have hh :
    (⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, cubeTetrahedron_sorted e s⟩ :
        ↥(cubeOrderedRegion e)) =
      ⟨ThirdHurewicz.Geometry.cubeTetrahedron e t, cubeTetrahedron_sorted e t⟩ :=
    Subtype.ext h
  simpa only [cubeTetrahedronInverse_tetrahedron] using congrArg (cubeTetrahedronInverse e) hh

theorem ThirdHurewicz.CubeTriangulation.exists_cubeTetrahedron
    (u : ThirdHurewicz.Geometry.Cube3) :
    ∃ e : Equiv.Perm (Fin 3),
      ∃ s : FirstHurewicz.Simplex 3, ThirdHurewicz.Geometry.cubeTetrahedron e s = u := by
  obtain ⟨e, he⟩ := exists_sortedPermutation u
  exact ⟨e, cubeTetrahedronInverse e ⟨u, he⟩, cubeTetrahedron_inverse e ⟨u, he⟩⟩

def ThirdHurewicz.CubeTriangulation.cubeTetrahedronCylinder (e : Equiv.Perm (Fin 3)) :
    C((unitInterval) × FirstHurewicz.Simplex 3, (unitInterval) × ThirdHurewicz.Geometry.Cube3) :=
  (ContinuousMap.id (unitInterval)).prodMap (ThirdHurewicz.Geometry.cubeTetrahedron e)

def ThirdHurewicz.CubeTriangulation.cubeCylinderCover :
    C((Σ _e : Equiv.Perm (Fin 3), (unitInterval) × FirstHurewicz.Simplex 3),
      (unitInterval) × ThirdHurewicz.Geometry.Cube3)
    where
  toFun a := cubeTetrahedronCylinder a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeTetrahedronCylinder e).continuous

theorem ThirdHurewicz.CubeTriangulation.cubeCylinderCover_surjective :
    Function.Surjective cubeCylinderCover := by
  rintro ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeTetrahedron u
  exact ⟨⟨e, (r, s)⟩, rfl⟩

theorem ThirdHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap :
    Topology.IsQuotientMap cubeCylinderCover :=
  Topology.IsQuotientMap.of_surjective_continuous cubeCylinderCover_surjective
    cubeCylinderCover.continuous

def ThirdHurewicz.CubeGluing.CubeCompatible {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin 3)) (s t : FirstHurewicz.Simplex 3),
    ThirdHurewicz.Geometry.cubeTetrahedron e s = ThirdHurewicz.Geometry.cubeTetrahedron f t →
      ∀ r : (unitInterval), F e (r, s) = F f (r, t)

def ThirdHurewicz.CubeGluing.cubeFamilyMap {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X)) :
    C((Σ _e : Equiv.Perm (Fin 3), (unitInterval) × FirstHurewicz.Simplex 3), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

theorem ThirdHurewicz.CubeGluing.cubeFamilyMap_factorsThrough {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F) ThirdHurewicz.CubeTriangulation.cubeCylinderCover :=
  by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs :
    ThirdHurewicz.Geometry.cubeTetrahedron e s = ThirdHurewicz.Geometry.cubeTetrahedron f t :=
    congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

def ThirdHurewicz.CubeGluing.glueCubeHomotopies {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) : C((unitInterval) × ThirdHurewicz.Geometry.Cube3, X) :=
  ThirdHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap.lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp]
theorem ThirdHurewicz.CubeGluing.glueCubeHomotopies_cell {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) :
    glueCubeHomotopies F hF (r, ThirdHurewicz.Geometry.cubeTetrahedron e s) = F e (r, s) :=
  DFunLike.congr_fun
    (ThirdHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap.lift_comp (cubeFamilyMap F)
      (cubeFamilyMap_factorsThrough F hF))
    ⟨e, (r, s)⟩

theorem ThirdHurewicz.CubeGluing.glueCubeHomotopies_time {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) (r : (unitInterval)) (g : ThirdHurewicz.Geometry.Cube3 → X)
    (h :
      ∀ (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3),
        F e (r, s) = g (ThirdHurewicz.Geometry.cubeTetrahedron e s))
    (u : ThirdHurewicz.Geometry.Cube3) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := ThirdHurewicz.CubeTriangulation.exists_cubeTetrahedron u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

theorem ThirdHurewicz.CubeGluing.glueCubeHomotopies_zero {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin 3) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hF : CubeCompatible F) (g : C(ThirdHurewicz.Geometry.Cube3, X))
    (h :
      ∀ (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3),
        F e (0, s) = g (ThirdHurewicz.Geometry.cubeTetrahedron e s))
    (u : ThirdHurewicz.Geometry.Cube3) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_mem_boundary_iff (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) :
    ThirdHurewicz.Geometry.cubeTetrahedron e s ∈ Cube.boundary (Fin 3) ↔ s 0 = 0 ∨ s 3 = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    have h0 := stdSimplex.zero_le s 0
    have h1 := stdSimplex.zero_le s 1
    have h2 := stdSimplex.zero_le s 2
    have h3 := stdSimplex.zero_le s 3
    have hs := stdSimplex.sum_eq_one s
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
    fin_cases j
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) = 0 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero] at hr
        linarith
      · left
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) : ℝ) = 1 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero] at hr
        linarith
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) : ℝ) = 0 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one] at hr
        linarith
      · left
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) : ℝ) = 1 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one] at hr
        linarith
    · rcases hi with hi | hi
      · right
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) : ℝ) = 0 at hr
        rwa [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two] at hr
      · left
        have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) hi
        change (ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2) : ℝ) = 1 at hr
        rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two] at hr
        linarith
  · rintro (hs | hs)
    · have ht :=
        ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_boundary e
          (SecondHurewicz.SimplyConnected.simplexFaceInverse 2 0 ⟨s, hs⟩)
      simpa only [SecondHurewicz.SimplyConnected.simplexFace_inverse] using ht
    · have ht :=
        ThirdHurewicz.Geometry.cubeTetrahedron_face_three_boundary e
          (SecondHurewicz.SimplyConnected.simplexFaceInverse 2 3 ⟨s, hs⟩)
      simpa only [SecondHurewicz.SimplyConnected.simplexFace_inverse] using ht

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_first (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3)
    (h :
      ThirdHurewicz.Geometry.cubeTetrahedron e s (e 0) =
        ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1)) :
    s 1 = 0 := by
  have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_zero,
    ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one] at hr
  linarith

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_second (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3)
    (h :
      ThirdHurewicz.Geometry.cubeTetrahedron e s (e 1) =
        ThirdHurewicz.Geometry.cubeTetrahedron e s (e 2)) :
    s 2 = 0 := by
  have hr := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_one,
    ThirdHurewicz.Geometry.cubeTetrahedron_coordinate_two] at hr
  linarith

theorem ThirdHurewicz.CubeGluing.cubeOriginal_face_zero {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 0) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  exact GenLoop.boundary p _ (ThirdHurewicz.Geometry.cubeTetrahedron_face_zero_boundary e s)

theorem ThirdHurewicz.CubeGluing.cubeOriginal_face_three {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 3) =
      ContinuousMap.const (FirstHurewicz.Simplex 2) x := by
  ext s
  exact GenLoop.boundary p _ (ThirdHurewicz.Geometry.cubeTetrahedron_face_three_boundary e s)

theorem ThirdHurewicz.CubeGluing.cubeOriginal_face_one_swap {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 1) =
      (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 0 1).trans e))).comp
        (FirstHurewicz.simplexFace 2 1) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(FirstHurewicz.Simplex 2, ThirdHurewicz.Geometry.Cube3) => p.val.comp f)
      (ThirdHurewicz.Geometry.cubeTetrahedron_face_one_swap e)

theorem ThirdHurewicz.CubeGluing.cubeOriginal_face_two_swap {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp (FirstHurewicz.simplexFace 2 2) =
      (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 1 2).trans e))).comp
        (FirstHurewicz.simplexFace 2 2) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg (fun f : C(FirstHurewicz.Simplex 2, ThirdHurewicz.Geometry.Cube3) => p.val.comp f)
      (ThirdHurewicz.Geometry.cubeTetrahedron_face_two_swap e)

theorem ThirdHurewicz.CubeGluing.coherentCubeCell_face {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (i : Fin 4) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 2) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))
        (r, FirstHurewicz.simplexFace 2 i s) =
      H₂
        ((p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)).comp
          (FirstHurewicz.simplexFace 2 i))
        (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) i) (r, s)

theorem ThirdHurewicz.CubeGluing.coherentCubeCell_one_swap {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) (hs : s 1 = 0) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) =
      H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 0 1).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 1 ⟨s, hs⟩
  have ht : FirstHurewicz.simplexFace 2 1 t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse 2 1 ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₂ H₃ hface, coherentCubeCell_face H₂ H₃ hface,
    cubeOriginal_face_one_swap]

theorem ThirdHurewicz.CubeGluing.coherentCubeCell_two_swap {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) (hs : s 2 = 0) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) =
      H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron ((Equiv.swap 1 2).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 2 ⟨s, hs⟩
  have ht : FirstHurewicz.simplexFace 2 2 t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse 2 2 ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₂ H₃ hface, coherentCubeCell_face H₂ H₃ hface,
    cubeOriginal_face_two_swap]

theorem ThirdHurewicz.CubeGluing.coherentCubeCell_boundary {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3)
    (hs : ThirdHurewicz.Geometry.cubeTetrahedron e s ∈ Cube.boundary (Fin 3)) :
    H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) = x := by
  rcases (ThirdHurewicz.CubeTriangulation.cubeTetrahedron_mem_boundary_iff e s).mp hs with hs | hs
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 0 ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace 2 0 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse 2 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₂ H₃ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse 2 3 ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace 2 3 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse 2 3 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₂ H₃ hface, cubeOriginal_face_three, hconst]
    rfl

theorem ThirdHurewicz.CubeTriangulation.SortedCoordinates.le_first {α : Type*} [LinearOrder α]
    {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : ThirdHurewicz.CubeTriangulation.SortedCoordinates u e) (i : Fin 3) : u i ≤ u (e 0) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  fin_cases j
  · exact le_rfl
  · exact he.2
  · exact he.1.trans he.2

theorem ThirdHurewicz.CubeTriangulation.sorted_first_value_eq {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : u (e 0) = u (f 0) :=
  le_antisymm (hf.le_first (e 0)) (he.le_first (f 0))

theorem ThirdHurewicz.CubeTriangulation.SortedCoordinates.swap01 {α : Type*} [LinearOrder α]
    {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : ThirdHurewicz.CubeTriangulation.SortedCoordinates u e) (ht : u (e 0) = u (e 1)) :
    ThirdHurewicz.CubeTriangulation.SortedCoordinates u ((Equiv.swap 0 1).trans e) := by
  simpa [ThirdHurewicz.CubeTriangulation.SortedCoordinates, Equiv.swap_apply_def] using
    And.intro (he.1.trans he.2) ht.le

theorem ThirdHurewicz.CubeTriangulation.SortedCoordinates.swap12 {α : Type*} [LinearOrder α]
    {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : ThirdHurewicz.CubeTriangulation.SortedCoordinates u e) (ht : u (e 1) = u (e 2)) :
    ThirdHurewicz.CubeTriangulation.SortedCoordinates u ((Equiv.swap 1 2).trans e) := by
  simpa [ThirdHurewicz.CubeTriangulation.SortedCoordinates, Equiv.swap_apply_def] using
    And.intro ht.le (he.1.trans he.2)

private theorem ThirdHurewicz.CubeTriangulation.permutation_ext_zero_one_mo1973_7620
    {e f : Equiv.Perm (Fin 3)} (h0 : e 0 = f 0) (h1 : e 1 = f 1) : e = f := by
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · obtain ⟨j, hj⟩ := f.surjective (e 2)
    fin_cases j
    · exact ((by decide : (0 : Fin 3) ≠ 2) (e.injective (h0.trans hj))).elim
    · exact ((by decide : (1 : Fin 3) ≠ 2) (e.injective (h1.trans hj))).elim
    · exact hj.symm

private theorem ThirdHurewicz.CubeTriangulation.eq_of_sorted_same_first_mo1973_7621 {α : Type*}
    [LinearOrder α] (u : Fin 3 → α) {A : Type*} (F : Equiv.Perm (Fin 3) → A)
    (h12 : ∀ e, SortedCoordinates u e → u (e 1) = u (e 2) → F e = F ((Equiv.swap 1 2).trans e))
    {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e) (hf : SortedCoordinates u f)
    (h0 : e 0 = f 0) : F e = F f := by
  obtain ⟨i, hi⟩ := e.surjective (f 1)
  fin_cases i
  · exact ((by decide : (0 : Fin 3) ≠ 1) (f.injective (h0.symm.trans hi))).elim
  · exact congrArg F (permutation_ext_zero_one_mo1973_7620 h0 hi)
  · have hp : (Equiv.swap 1 2).trans e = f :=
      permutation_ext_zero_one_mo1973_7620 (by simpa [Equiv.swap_apply_def] using h0)
        (by simpa [Equiv.swap_apply_def] using hi)
    have hrev : u (e 1) ≤ u (e 2) := by
      have hh := hf.1
      rw [← hp] at hh
      simpa [Equiv.swap_apply_def] using hh
    exact (h12 e he (le_antisymm hrev he.1)).trans (congrArg F hp)

theorem ThirdHurewicz.CubeTriangulation.eq_of_sorted_adjacent {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) {A : Type*} (F : Equiv.Perm (Fin 3) → A)
    (h01 : ∀ e, SortedCoordinates u e → u (e 0) = u (e 1) → F e = F ((Equiv.swap 0 1).trans e))
    (h12 : ∀ e, SortedCoordinates u e → u (e 1) = u (e 2) → F e = F ((Equiv.swap 1 2).trans e))
    {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    F e = F f := by
  obtain ⟨i, hi⟩ := e.surjective (f 0)
  fin_cases i
  · exact eq_of_sorted_same_first_mo1973_7621 u F h12 he hf hi
  · change e 1 = f 0 at hi
    have ht : u (e 0) = u (e 1) := by
      rw [hi]
      exact sorted_first_value_eq u he hf
    have hg := he.swap01 ht
    have hg0 : ((Equiv.swap 0 1).trans e) 0 = f 0 := by simpa [Equiv.swap_apply_def] using hi
    exact (h01 e he ht).trans (eq_of_sorted_same_first_mo1973_7621 u F h12 hg hf hg0)
  · change e 2 = f 0 at hi
    have ht : u (e 0) = u (e 2) := by
      rw [hi]
      exact sorted_first_value_eq u he hf
    have ht12 : u (e 1) = u (e 2) := le_antisymm (he.2.trans ht.le) he.1
    have hg := he.swap12 ht12
    have ht01 : u (((Equiv.swap 1 2).trans e) 0) = u (((Equiv.swap 1 2).trans e) 1) := by
      simpa [Equiv.swap_apply_def] using ht
    have hh := hg.swap01 ht01
    have hh0 : ((Equiv.swap 0 1).trans ((Equiv.swap 1 2).trans e)) 0 = f 0 := by
      simpa [Equiv.swap_apply_def] using hi
    exact
      (h12 e he ht12).trans
        ((h01 _ hg ht01).trans (eq_of_sorted_same_first_mo1973_7621 u F h12 hh hf hh0))

theorem ThirdHurewicz.CubeTriangulation.sorted_values_eq {α : Type*} [LinearOrder α]
    (u : Fin 3 → α) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : ∀ i : Fin 3, u (e i) = u (f i) := by
  have hfun : (fun i => u (e i)) = (fun i => u (f i)) :=
    eq_of_sorted_adjacent u (fun g i => u (g i))
      (fun g _ ht => by
        funext i
        fin_cases i <;> simp [Equiv.swap_apply_def, ht])
      (fun g _ ht => by
        funext i
        fin_cases i <;> simp [Equiv.swap_apply_def, ht])
      he hf
  exact congrFun hfun

theorem ThirdHurewicz.CubeTriangulation.cubeBarycentric_eq_of_sorted
    (u : ThirdHurewicz.Geometry.Cube3) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : cubeBarycentric e u = cubeBarycentric f u := by
  simp only [cubeBarycentric, sorted_values_eq u he hf 0, sorted_values_eq u he hf 1,
    sorted_values_eq u he hf 2]

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedronInverse_sorted_eq
    (u : ThirdHurewicz.Geometry.Cube3) {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) :
    cubeTetrahedronInverse e ⟨u, he⟩ = cubeTetrahedronInverse f ⟨u, hf⟩ :=
  Subtype.ext (cubeBarycentric_eq_of_sorted u he hf)

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_eq_of_sorted (e f : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3)
    (hf : SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s) f) :
    ThirdHurewicz.Geometry.cubeTetrahedron f s = ThirdHurewicz.Geometry.cubeTetrahedron e s := by
  have hp : cubeTetrahedronInverse f ⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, hf⟩ = s :=
    (cubeTetrahedronInverse_sorted_eq (ThirdHurewicz.Geometry.cubeTetrahedron e s) hf
          (cubeTetrahedron_sorted e s)).trans
      (cubeTetrahedronInverse_tetrahedron e s)
  simpa only [hp] using cubeTetrahedron_inverse f ⟨ThirdHurewicz.Geometry.cubeTetrahedron e s, hf⟩

theorem ThirdHurewicz.CubeTriangulation.cubeTetrahedron_overlap_preimage
    (e f : Equiv.Perm (Fin 3)) (s t : FirstHurewicz.Simplex 3)
    (h :
      ThirdHurewicz.Geometry.cubeTetrahedron e s = ThirdHurewicz.Geometry.cubeTetrahedron f t) :
    s = t := by
  have hf : SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s) f := by
    rw [h]
    exact cubeTetrahedron_sorted f t
  exact cubeTetrahedron_injective f ((cubeTetrahedron_eq_of_sorted e f s hf).trans h)

theorem ThirdHurewicz.CubeGluing.coherentCubeFamily_compatible {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) :
    CubeCompatible (fun e => H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))) := by
  intro e f s t h r
  have hst := ThirdHurewicz.CubeTriangulation.cubeTetrahedron_overlap_preimage e f s t h
  subst t
  have hf :
    ThirdHurewicz.CubeTriangulation.SortedCoordinates (ThirdHurewicz.Geometry.cubeTetrahedron e s)
      f := by
    rw [h]
    exact ThirdHurewicz.CubeTriangulation.cubeTetrahedron_sorted f s
  apply
    ThirdHurewicz.CubeTriangulation.eq_of_sorted_adjacent
      (ThirdHurewicz.Geometry.cubeTetrahedron e s)
      (fun g => H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron g)) (r, s)) ?_ ?_
      (ThirdHurewicz.CubeTriangulation.cubeTetrahedron_sorted e s) hf
  · intro g hg ht
    apply coherentCubeCell_one_swap H₂ H₃ hface p g r s
    apply ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_first g s
    simpa only [ThirdHurewicz.CubeTriangulation.cubeTetrahedron_eq_of_sorted e g s hg] using ht
  · intro g hg ht
    apply coherentCubeCell_two_swap H₂ H₃ hface p g r s
    apply ThirdHurewicz.CubeTriangulation.cubeTetrahedron_tie_second g s
    simpa only [ThirdHurewicz.CubeTriangulation.cubeTetrahedron_eq_of_sorted e g s hg] using ht

def ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) : C((unitInterval) × ThirdHurewicz.Geometry.Cube3, X) :=
  glueCubeHomotopies (fun e => H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)))
    (coherentCubeFamily_compatible H₂ H₃ hface p)

@[simp]
theorem ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap_cell {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex 3) :
    coherentCubeHomotopyMap H₂ H₃ hface p (r, ThirdHurewicz.Geometry.cubeTetrahedron e s) =
      H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

theorem ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap_zero {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex 3, X)) (s : FirstHurewicz.Simplex 3),
        H₃ smp (0, s) = smp s)
    (p : GenLoop (Fin 3) X x) (u : ThirdHurewicz.Geometry.Cube3) :
    coherentCubeHomotopyMap H₂ H₃ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e)) s) u

theorem ThirdHurewicz.CubeGluing.coherentCubeHomotopyMap_boundary {X : Type} [TopologicalSpace X]
    {x : X} (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (r : (unitInterval)) (u : ThirdHurewicz.Geometry.Cube3)
    (hu : u ∈ Cube.boundary (Fin 3)) : coherentCubeHomotopyMap H₂ H₃ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := ThirdHurewicz.CubeTriangulation.exists_cubeTetrahedron u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₂ H₃ hface hconst p e r s hu

def ThirdHurewicz.CubeGluing.coherentCubeEndpoint {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (coherentCubeHomotopyMap H₂ H₃ hface p) 1, fun u hu =>
    coherentCubeHomotopyMap_boundary H₂ H₃ hface hconst p 1 u hu⟩

theorem ThirdHurewicz.CubeGluing.coherentCubeEndpoint_cell {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (coherentCubeEndpoint H₂ H₃ hface hconst p).val.comp
        (ThirdHurewicz.Geometry.cubeTetrahedron e) =
      SecondHurewicz.SimplyConnected.timeSlice
        (H₃ (p.val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₂ H₃ hface p e 1 s

def ThirdHurewicz.CubeGluing.coherentCubeHomotopy {X : Type} [TopologicalSpace X] {x : X}
    (H₂ : C(FirstHurewicz.Simplex 2, X) → C((unitInterval) × FirstHurewicz.Simplex 2, X))
    (H₃ : C(FirstHurewicz.Simplex 3, X) → C((unitInterval) × FirstHurewicz.Simplex 3, X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 2 H₂ H₃)
    (hconst :
      H₂ (ContinuousMap.const (FirstHurewicz.Simplex 2) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 2) x)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex 3, X)) (s : FirstHurewicz.Simplex 3),
        H₃ smp (0, s) = smp s)
    (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₂ H₃ hface hconst p).val (Cube.boundary (Fin 3))
    where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₂ H₃ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₂ H₃ hface hzero p
      map_one_left _ := rfl }
  prop' r u
    hu :=
    (coherentCubeHomotopyMap_boundary H₂ H₃ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

theorem ThirdHurewicz.cubeTetrahedron_coordinate_equality_boundary (e : Equiv.Perm (Fin 3))
    (s : FirstHurewicz.Simplex 3) (i j : Fin 3) (hij : i ≠ j)
    (hu : Geometry.cubeTetrahedron e s i = Geometry.cubeTetrahedron e s j) :
    s ∈ threeSimplexBoundary := by
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  have hab : a ≠ b := fun h => hij (congrArg e h)
  have hcoords :
    (fun k : Fin 3 => (Geometry.cubeTetrahedron e s (e k) : ℝ)) =
      ![s 1 + s 2 + s 3, s 2 + s 3, s 3] := by
    funext k
    fin_cases k
    · exact Geometry.cubeTetrahedron_coordinate_zero e s
    · exact Geometry.cubeTetrahedron_coordinate_one e s
    · exact Geometry.cubeTetrahedron_coordinate_two e s
  have hv := congrArg (fun t : (unitInterval) => (t : ℝ)) hu
  change
    (fun k : Fin 3 => (Geometry.cubeTetrahedron e s (e k) : ℝ)) a =
      (fun k : Fin 3 => (Geometry.cubeTetrahedron e s (e k) : ℝ)) b at hv
  rw [hcoords] at hv
  fin_cases a <;> fin_cases b
  all_goals try exact (hab rfl).elim
  all_goals
    dsimp at hv
    first
    | exact ⟨1, by linarith [stdSimplex.zero_le s 1, stdSimplex.zero_le s 2]⟩
    | exact ⟨2, by linarith [stdSimplex.zero_le s 1, stdSimplex.zero_le s 2]⟩

def ThirdHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  CubeGluing.coherentCubeEndpoint (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) p

theorem ThirdHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (normalizedCube x p).val.comp (Geometry.cubeTetrahedron e) =
      (normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e))).val := by
  exact
    (CubeGluing.coherentCubeEndpoint_cell (normalizationTriangleHomotopy x)
          (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
          (normalizationTriangleHomotopy_const x) p e).trans
      (normalizationThreeSimplexHomotopy_endpoint x _)

def ThirdHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 3)) :=
  CubeGluing.coherentCubeHomotopy (normalizationTriangleHomotopy x)
    (normalizationThreeSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationTriangleHomotopy_const x) (normalizationThreeSimplexHomotopy_zero x) p

theorem ThirdHurewicz.normalizedCube_cell_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) (s : FirstHurewicz.Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    normalizedCube x p (Geometry.cubeTetrahedron e s) = x := by
  have h := congrArg (fun f : C(FirstHurewicz.Simplex 3, X) => f s) (normalizedCube_cell x p e)
  exact
    h.trans ((normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e))).property s hs)

theorem ThirdHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    NativeCubeInternalBased (normalizedCube x p) := by
  intro u i j hij hu
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeTetrahedron u
  exact
    normalizedCube_cell_boundary x p e s
      (cubeTetrahedron_coordinate_equality_boundary e s i j hij hu)

theorem ThirdHurewicz.threeSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    threeSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 3),
        Geometry.cubeOrientation e •
          basedThreeSimplexClass
            (normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_tetrahedra]
  simp only [map_sum, map_zsmul, threeSimplexClassOperator_simplex]

theorem ThirdHurewicz.normalizedCube_tetrahedron {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) :
    nativeBasedCubeTetrahedron (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedThreeSimplex x (p.val.comp (Geometry.cubeTetrahedron e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

theorem ThirdHurewicz.threeSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    threeSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 3 X x) := by
  have h :=
    nativeCubeSubdivision_homotopy_class p (normalizedCube x p) (normalizationCubeHomotopy x p)
      (normalizedCube_internalBased x p)
  simp only [normalizedCube_tetrahedron] at h
  exact (threeSimplexClassOperator_cubeChain_sum x p).trans h.symm

def ThirdHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] :
    SingularMayerVietoris.SingularHomology X 3 →ₗ[ℤ] Additive (π_ 3 X x) :=
  thirdHomologyDesc (threeSimplexClassOperator x) (threeSimplexClassOperator_boundary x)

@[simp]
theorem ThirdHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 3) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 3 c) =
      threeSimplexClassOperator x c.val :=
  thirdHomologyDesc_cycleClass _ _ c

theorem ThirdHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_thirdHomologyDesc_eq_id (threeSimplexClassOperator x)
    (threeSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_threeSimplexClassOperator_cycle x)

@[simp]
theorem ThirdHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (c : SingularMayerVietoris.SingularHomology X 3) : hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp]
theorem ThirdHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 3) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 3 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 3 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact threeSimplexClassOperator_cubeChain x p

@[simp]
theorem ThirdHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] (a : Additive (π_ 3 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem ThirdHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

def ThirdHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    Additive (π_ 3 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 3 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x) (hurewiczMap_comp_hurewiczInverse x)
    (hurewiczInverse_comp_hurewiczMap x)

def ThirdHurewicz.hurewiczPi3Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] :
    π_ 3 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 3)
    where
  __ := hurewiczPi3 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

@[simp]
theorem FourthHurewicz.lowerThreeSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    ThirdHurewicz.normalizationThreeSimplexHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x := by
  have hVE :
    ThirdHurewicz.vertexEdgeThreeSimplexHomotopy x
        (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
    ThirdHurewicz.composeSimplexHomotopies_const
      (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy x 3)
      (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy x)
      (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_zero x 3)
      (SecondHurewicz.SimplyConnected.tetrahedronEdgeStraighteningHomotopy_zero x) x
      (SecondHurewicz.SimplyConnected.vertexStraighteningHomotopy_const x 3)
      (ThirdHurewicz.edgeTetrahedronHomotopy_const x)
  exact
    ThirdHurewicz.composeSimplexHomotopies_const (ThirdHurewicz.vertexEdgeThreeSimplexHomotopy x)
      (ThirdHurewicz.triangleThreeSimplexHomotopy x)
      (ThirdHurewicz.vertexEdgeThreeSimplexHomotopy_zero x)
      (ThirdHurewicz.triangleThreeSimplexHomotopy_zero x) x hVE
      (ThirdHurewicz.triangleThreeSimplexHomotopy_const x)

def FourthHurewicz.lowerFourSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) : C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x) smp

@[simp]
theorem FourthHurewicz.lowerFourSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (s : FirstHurewicz.Simplex 4) :
    lowerFourSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FourthHurewicz.lowerFourSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)

@[simp]
theorem FourthHurewicz.lowerFourSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    lowerFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (ThirdHurewicz.normalizationTriangleHomotopy x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (ThirdHurewicz.normalizationHomotopy_face x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x) x (lowerThreeSimplexHomotopy_const x)

def FourthHurewicz.lowerFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x) smp

@[simp]
theorem FourthHurewicz.lowerFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (s : FirstHurewicz.Simplex 5) :
    lowerFiveSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FourthHurewicz.lowerFiveSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (lowerFourSimplexHomotopy x)
      (lowerFiveSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x)

@[simp]
theorem FourthHurewicz.lowerFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] :
    lowerFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (ThirdHurewicz.normalizationThreeSimplexHomotopy x) (lowerFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_face x) (lowerFourSimplexHomotopy_zero x) x
    (lowerFourSimplexHomotopy_const x)

def HigherHurewicz.nativeCubeNullHomotopy {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    [hπ : Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin n → (unitInterval)) x) (Cube.boundary (Fin n)) :=
  Classical.choice
    (show GenLoop.Homotopic p GenLoop.const from
      Quotient.exact (@Subsingleton.elim (π_ n X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

def HigherHurewicz.nativeCubeNullHomotopy_comp {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    {A : Type*} [TopologicalSpace A] [Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → (unitInterval))) (S : Set A) (hr : Set.MapsTo r S (Cube.boundary (Fin n))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S
    where
  toFun z := nativeCubeNullHomotopy p (z.1, r z.2)
  continuous_toFun :=
    (nativeCubeNullHomotopy p).continuous.comp
      (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeCubeNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeCubeNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeCubeNullHomotopy p).eq_fst t (hr ha)

def HigherHurewicz.basedSimplexNativeLoop {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp ⟨(simplexCubeHomeomorph n).symm, (simplexCubeHomeomorph n).symm.continuous⟩,
    fun u hu => τ.property _ ((simplexCubeHomeomorph_symm_boundary_iff n u).mpr hu)⟩

theorem HigherHurewicz.basedSimplexNativeLoop_comp_homeomorph {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X} (τ : BasedSimplex n x) :
    (basedSimplexNativeLoop τ).val.comp
        ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩ =
      τ.val := by
  apply ContinuousMap.ext
  intro s
  change τ.val ((simplexCubeHomeomorph n).symm (simplexCubeHomeomorph n s)) = τ.val s
  rw [Homeomorph.symm_apply_apply]

def HigherHurewicz.simplexNullHomotopyUnnormalized {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) :=
  ContinuousMap.HomotopyRel.cast
    (nativeCubeNullHomotopy_comp (basedSimplexNativeLoop τ)
      ⟨simplexCubeHomeomorph n, (simplexCubeHomeomorph n).continuous⟩
      (SecondHurewicz.SimplyConnected.simplexBoundary n)
      (fun s hs => (simplexCubeHomeomorph_boundary_iff n s).mpr hs))
    (basedSimplexNativeLoop_comp_homeomorph τ) rfl

def HigherHurewicz.simplexNullHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) :
    τ.val.HomotopyRel (ContinuousMap.const (FirstHurewicz.Simplex n) x)
      (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
    exact
    if h : τ = constantBasedSimplex n x then
      ContinuousMap.HomotopyRel.cast
        (ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex n) x)
          (SecondHurewicz.SimplyConnected.simplexBoundary n))
        (congrArg (fun υ : BasedSimplex n x => υ.val) h).symm rfl
    else simplexNullHomotopyUnnormalized τ

@[simp]
theorem HigherHurewicz.simplexNullHomotopy_zero {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : FirstHurewicz.Simplex n) :
    simplexNullHomotopy τ (0, s) = τ.val s :=
  (simplexNullHomotopy τ).apply_zero s

@[simp]
theorem HigherHurewicz.simplexNullHomotopy_one {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    [Subsingleton (π_ n X x)] (τ : BasedSimplex n x) (s : FirstHurewicz.Simplex n) :
    simplexNullHomotopy τ (1, s) = x :=
  (simplexNullHomotopy τ).apply_one s

@[simp]
theorem HigherHurewicz.simplexNullHomotopy_constant {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexNullHomotopy (constantBasedSimplex n x) =
      ContinuousMap.HomotopyRel.refl (ContinuousMap.const (FirstHurewicz.Simplex n) x)
        (SecondHurewicz.SimplyConnected.simplexBoundary n) := by
  classical
  unfold simplexNullHomotopy
  rw [dif_pos rfl]
  rfl

@[simp]
theorem HigherHurewicz.simplexNullHomotopy_constant_toContinuousMap {X : Type}
    [TopologicalSpace X] (n : ℕ) (x : X) [Subsingleton (π_ n X x)] :
    (simplexNullHomotopy (constantBasedSimplex n x)).toContinuousMap =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  rw [simplexNullHomotopy_constant]
  rfl

def HigherHurewicz.simplexStraighteningHomotopy {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n) :
    C((unitInterval) × FirstHurewicz.Simplex n, X) := by
  classical
    exact
    if h : ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, smp s = x then
      (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).toContinuousMap
    else SecondHurewicz.SimplyConnected.stationarySimplexHomotopy n smp

@[simp]
theorem HigherHurewicz.simplexStraighteningHomotopy_zero {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n)
    (s : FirstHurewicz.Simplex n) : simplexStraighteningHomotopy n x smp (0, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact simplexNullHomotopy_zero (⟨smp, h⟩ : BasedSimplex n x) s
  · rfl

theorem HigherHurewicz.simplexStraighteningHomotopy_one {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n)
    (h : ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, smp s = x)
    (s : FirstHurewicz.Simplex n) : simplexStraighteningHomotopy n x smp (1, s) = x := by
  classical
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_one (⟨smp, h⟩ : BasedSimplex n x) s

theorem HigherHurewicz.simplexStraighteningHomotopy_boundary {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) [Subsingleton (π_ n X x)] (smp : FirstHurewicz.SingularSimplex X n)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    simplexStraighteningHomotopy n x smp (r, s) = smp s := by
  classical
  unfold simplexStraighteningHomotopy
  split
  · rename_i h
    exact (simplexNullHomotopy (⟨smp, h⟩ : BasedSimplex n x)).eq_fst r hs
  · rfl

@[simp]
theorem HigherHurewicz.simplexStraighteningHomotopy_const {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ n X x)] :
    simplexStraighteningHomotopy n x (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x := by
  classical
  have h :
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n,
      (ContinuousMap.const (FirstHurewicz.Simplex n) x) s = x :=
    fun _ _ => rfl
  rw [simplexStraighteningHomotopy, dif_pos h]
  exact simplexNullHomotopy_constant_toContinuousMap n x

theorem HigherHurewicz.simplexStraighteningHomotopy_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) [Subsingleton (π_ (n + 1) X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n
      (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy n)
      (simplexStraighteningHomotopy (n + 1) x) := by
  intro smp i
  ext u
  change
    simplexStraighteningHomotopy (n + 1) x smp (u.1, FirstHurewicz.simplexFace n i u.2) =
      smp (FirstHurewicz.simplexFace n i u.2)
  exact
    simplexStraighteningHomotopy_boundary (n + 1) x smp u.1 _
      ⟨i, FirstHurewicz.simplexFace_apply_self n i u.2⟩

def FourthHurewicz.threeFourSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) smp

@[simp]
theorem FourthHurewicz.threeFourSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 4)
    (s : FirstHurewicz.Simplex 4) : threeFourSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FourthHurewicz.threeFourSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)

@[simp]
theorem FourthHurewicz.threeFourSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    threeFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 2)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 2 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 3 x)

def FourthHurewicz.threeFiveSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x) smp

@[simp]
theorem FourthHurewicz.threeFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] (smp : FirstHurewicz.SingularSimplex X 5)
    (s : FirstHurewicz.Simplex 5) : threeFiveSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FourthHurewicz.threeFiveSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (threeFourSimplexHomotopy x)
      (threeFiveSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x)

@[simp]
theorem FourthHurewicz.threeFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 3 X x)] :
    threeFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (threeFourSimplexHomotopy x)
    (threeFourSimplexHomotopy_face x) (threeFourSimplexHomotopy_zero x) x
    (threeFourSimplexHomotopy_const x)

def FourthHurewicz.normalizationThreeSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.SingularSimplex X 3 → C((unitInterval) × FirstHurewicz.Simplex 3, X) :=
  ThirdHurewicz.composeSimplexHomotopies (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x)

def FourthHurewicz.normalizationFourSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.SingularSimplex X 4 → C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerFourSimplexHomotopy x) (threeFourSimplexHomotopy x)
    (lowerFourSimplexHomotopy_zero x) (threeFourSimplexHomotopy_zero x)

def FourthHurewicz.normalizationFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.SingularSimplex X 5 → C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerFiveSimplexHomotopy x) (threeFiveSimplexHomotopy x)
    (lowerFiveSimplexHomotopy_zero x) (threeFiveSimplexHomotopy_zero x)

@[simp]
theorem FourthHurewicz.normalizationFourSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) (s : FirstHurewicz.Simplex 4) :
    normalizationFourSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp]
theorem FourthHurewicz.normalizationFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (s : FirstHurewicz.Simplex 5) :
    normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

theorem FourthHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 3
      (normalizationThreeSimplexHomotopy x) (normalizationFourSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x) (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x) (lowerFourSimplexHomotopy_face x)
    (threeFourSimplexHomotopy_face x)

theorem FourthHurewicz.normalizationFiveHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFiveSimplexHomotopy x) (threeFiveSimplexHomotopy x)
    (lowerFourSimplexHomotopy_zero x) (threeFourSimplexHomotopy_zero x)
    (lowerFiveSimplexHomotopy_zero x) (threeFiveSimplexHomotopy_zero x)
    (lowerFiveSimplexHomotopy_face x) (threeFiveSimplexHomotopy_face x)

@[simp]
theorem FourthHurewicz.normalizationThreeSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    normalizationThreeSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 3) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 3) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (ThirdHurewicz.normalizationThreeSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 3 x)
    (ThirdHurewicz.normalizationThreeSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 3 x) x (lowerThreeSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 3 x)

@[simp]
theorem FourthHurewicz.normalizationFourSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    normalizationFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerFourSimplexHomotopy x)
    (threeFourSimplexHomotopy x) (lowerFourSimplexHomotopy_zero x)
    (threeFourSimplexHomotopy_zero x) x (lowerFourSimplexHomotopy_const x)
    (threeFourSimplexHomotopy_const x)

@[simp]
theorem FourthHurewicz.normalizationFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (lowerFiveSimplexHomotopy x)
    (threeFiveSimplexHomotopy x) (lowerFiveSimplexHomotopy_zero x)
    (threeFiveSimplexHomotopy_zero x) x (lowerFiveSimplexHomotopy_const x)
    (threeFiveSimplexHomotopy_const x)

@[simp]
theorem FourthHurewicz.normalizationThreeSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 3) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationThreeSimplexHomotopy x smp) 1 =
      ContinuousMap.const (FirstHurewicz.Simplex 3) x := by
  rw [normalizationThreeSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    ThirdHurewicz.normalizationThreeSimplexHomotopy_endpoint]
  ext s
  exact
    HigherHurewicz.simplexStraighteningHomotopy_one 3 x
      (ThirdHurewicz.normalizedThreeSimplex x smp).val
      (ThirdHurewicz.normalizedThreeSimplex x smp).property s

def HigherHurewicz.SimplexGeometry.prefixMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  (Finset.univ.filter fun i : Fin n => i.val < k).inf u

@[simp]
theorem HigherHurewicz.SimplexGeometry.prefixMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    prefixMinimum u 0 = 1 := by
  simp [prefixMinimum]
  rfl

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (prefixMinimum u) := by
  intro k l hkl
  apply Finset.inf_mono
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hkl

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_le_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) (i : Fin n) (hi : i.val < k) : prefixMinimum u k ≤ u i :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_succ {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k < n) : prefixMinimum u (k + 1) = Min.min (prefixMinimum u k) (u ⟨k, hk⟩) := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixMinimum
  rw [hs, Finset.inf_insert]
  exact min_comm _ _

theorem HigherHurewicz.SimplexGeometry.continuous_prefixMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => prefixMinimum u k) :=
  Continuous.finset_inf_apply (fun i _ => continuous_apply i)

def HigherHurewicz.SimplexGeometry.extendedMinimum {n : ℕ} (u : Fin n → (unitInterval)) (k : ℕ) :
    (unitInterval) :=
  if k ≤ n then prefixMinimum u k else 0

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_of_le {n : ℕ} (u : Fin n → (unitInterval))
    (k : ℕ) (hk : k ≤ n) : extendedMinimum u k = prefixMinimum u k :=
  if_pos hk

@[simp]
theorem HigherHurewicz.SimplexGeometry.extendedMinimum_zero {n : ℕ} (u : Fin n → (unitInterval)) :
    extendedMinimum u 0 = 1 := by simp [extendedMinimum]

@[simp]
theorem HigherHurewicz.SimplexGeometry.extendedMinimum_last_succ {n : ℕ}
    (u : Fin n → (unitInterval)) : extendedMinimum u (n + 1) = 0 := by simp [extendedMinimum]

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) : Antitone (extendedMinimum u) := by
  intro k l hkl
  by_cases hl : l ≤ n
  · have hk := hkl.trans hl
    simpa only [extendedMinimum, if_pos hk, if_pos hl] using prefixMinimum_antitone u hkl
  · rw [show extendedMinimum u l = 0 from if_neg hl]
    exact bot_le

theorem HigherHurewicz.SimplexGeometry.continuous_extendedMinimum (n k : ℕ) :
    Continuous (fun u : Fin n → (unitInterval) => extendedMinimum u k) := by
  by_cases hk : k ≤ n
  · simpa only [extendedMinimum, if_pos hk] using continuous_prefixMinimum n k
  · simpa only [extendedMinimum, if_neg hk] using
      (continuous_const : Continuous (fun _ : Fin n → (unitInterval) => (0 : (unitInterval))))

def HigherHurewicz.SimplexGeometry.simplexQuotient (n : ℕ) :
    C(Fin n → (unitInterval), FirstHurewicz.Simplex n)
    where
  toFun
    u :=
    ⟨fun i => (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ),
      by
      constructor
      · intro i
        exact sub_nonneg.mpr (extendedMinimum_antitone u (Nat.le_succ i.val))
      · calc
          (∑ i : Fin (n + 1),
                ((extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ))) =
              ∑ i ∈ Finset.range (n + 1),
                ((extendedMinimum u i : ℝ) - (extendedMinimum u (i + 1) : ℝ)) :=
            Fin.sum_univ_eq_sum_range
              (fun k : ℕ => (extendedMinimum u k : ℝ) - (extendedMinimum u (k + 1) : ℝ)) (n + 1)
          _ = (extendedMinimum u 0 : ℝ) - (extendedMinimum u (n + 1) : ℝ) :=
            (Finset.sum_range_sub' _ _)
          _ = 1 := by simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact
      (continuous_subtype_val.comp (continuous_extendedMinimum n i.val)).sub
        (continuous_subtype_val.comp (continuous_extendedMinimum n (i.val + 1)))

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_apply {n : ℕ} (u : Fin n → (unitInterval))
    (i : Fin (n + 1)) :
    simplexQuotient n u i = (extendedMinimum u i.val : ℝ) - (extendedMinimum u (i.val + 1) : ℝ) :=
  rfl

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) :
    simplexQuotient n u i.castSucc =
      (prefixMinimum u i.val : ℝ) - (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [simplexQuotient_apply]
  exact
    congrArg₂ (fun a b : (unitInterval) => (a : ℝ) - (b : ℝ))
      (extendedMinimum_of_le u i.val i.isLt.le) (extendedMinimum_of_le u (i.val + 1) i.isLt)

@[simp]
theorem HigherHurewicz.SimplexGeometry.simplexQuotient_last {n : ℕ} (u : Fin n → (unitInterval)) :
    simplexQuotient n u (Fin.last n) = (prefixMinimum u n : ℝ) := by
  rw [simplexQuotient_apply]
  simp only [Fin.val_last, extendedMinimum_last_succ, extendedMinimum_of_le u n le_rfl]
  exact sub_zero _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hp : prefixMinimum u n = 0 :=
    le_antisymm (hi ▸ prefixMinimum_le_coordinate u n i i.isLt) bot_le
  exact ⟨Fin.last n, by rw [simplexQuotient_last, hp]; rfl⟩

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨i.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : u ∈ Cube.boundary (Fin n)) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact simplexQuotient_boundary_of_zero u i hi
  · exact simplexQuotient_boundary_of_one u i hi

def HigherHurewicz.SimplexGeometry.BasedSimplex (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(FirstHurewicz.Simplex n, X) //
    ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n, τ s = x }

def HigherHurewicz.SimplexGeometry.basedSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp (simplexQuotient n), fun u hu => τ.property _ (simplexQuotient_boundary u hu)⟩

def HigherHurewicz.SimplexGeometry.basedSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex n x) : Additive (π_ n X x) :=
  Additive.ofMul (⟦basedSimplexLoop τ⟧ : π_ n X x)

theorem HigherHurewicz.SimplexGeometry.basedSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplex (n + 1) x) (i : Fin (n + 2)) :
    τ.val.comp (FirstHurewicz.simplexFace n i) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, FirstHurewicz.simplexFace_apply_self n i s⟩

abbrev FourthHurewicz.fourSimplexBoundary : Set (FirstHurewicz.Simplex 4) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 4

abbrev FourthHurewicz.BasedFourSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 4 x

abbrev FourthHurewicz.basedFourSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : GenLoop (Fin 4) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

abbrev FourthHurewicz.basedFourSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : Additive (π_ 4 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

theorem FourthHurewicz.basedFourSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) (i : Fin 5) :
    τ.val.comp (FirstHurewicz.simplexFace 3 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 3) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

theorem HigherHurewicz.simplexEndpoint_face_constant {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1).comp (FirstHurewicz.simplexFace n i) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x :=
  (SecondHurewicz.SimplyConnected.timeSlice_face hface smp i 1).trans (hone _)

theorem HigherHurewicz.simplexEndpoint_boundary {X : Type} [TopologicalSpace X] {n : ℕ}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H') (x : X)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) (s : FirstHurewicz.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ :=
    SecondHurewicz.SimplyConnected.simplexBoundary_exists_face n
      (⟨s, hs⟩ : SecondHurewicz.SimplyConnected.SimplexBoundary (n + 1))
  have he : FirstHurewicz.simplexFace n i t = s := congrArg Subtype.val ht
  rw [← he]
  exact
    congrArg (fun f : C(FirstHurewicz.Simplex n, X) => f t)
      (simplexEndpoint_face_constant H H' hface x hone smp i)

def FourthHurewicz.normalizedFourSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) : BasedFourSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (normalizationFourSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationThreeSimplexHomotopy x)
      (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationThreeSimplexHomotopy_endpoint x) smp⟩

theorem FourthHurewicz.normalizationFourSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFourSimplexHomotopy x smp) 1 =
      (normalizedFourSimplex x smp).val :=
  rfl

def FourthHurewicz.normalizedFiveSimplexMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : FirstHurewicz.SingularSimplex X 5 :=
  SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1

theorem FourthHurewicz.normalizedFiveSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (i : Fin 6) :
    (normalizedFiveSimplexMap x smp).comp (FirstHurewicz.simplexFace 4 i) =
      (normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i))).val :=
  SecondHurewicz.SimplyConnected.timeSlice_face (normalizationFiveHomotopy_face x) smp i 1

theorem FourthHurewicz.normalizedFiveSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (i : Fin 6) (s : FirstHurewicz.Simplex 4)
    (hs : s ∈ fourSimplexBoundary) :
    normalizedFiveSimplexMap x smp (FirstHurewicz.simplexFace 4 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 4, X) => f s)
      (normalizedFiveSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i))).property s hs)

def FourthHurewicz.fourSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.Chains X 4 →ₗ[ℤ] Additive (π_ 4 X x) :=
  FirstHurewicz.chainLift X 4 fun smp => basedFourSimplexClass (normalizedFourSimplex x smp)

@[simp]
theorem FourthHurewicz.fourSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    fourSimplexClassOperator x (FirstHurewicz.simplexChain X 4 smp) =
      basedFourSimplexClass (normalizedFourSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 4 _ smp

def HigherHurewicz.straightenedCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) (n + 1)
    (SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1)
    (by
      have hc : ((FirstHurewicz.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
        exact
          SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X)
            (n + 1) c
      rw [Nat.add_sub_cancel,
        SecondHurewicz.SimplyConnected.simplexEndpointOperator_boundary n H H' h, hc, map_zero])

@[simp]
theorem HigherHurewicz.straightenedCycle_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    (straightenedCycle n H H' h c).1 =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c.1 :=
  rfl

theorem HigherHurewicz.straightenedCycle_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 2) (n + 1)).hom
        (SecondHurewicz.SimplyConnected.simplexPrismOperator (n + 1) H' c.1) =
      (straightenedCycle n H H' h c).1 - c.1 := by
  have hc : ((FirstHurewicz.singularComplex X).d (n + 1) n).hom c.1 = 0 := by
    exact
      SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X)
        (n + 1) c
  rw [SecondHurewicz.SimplyConnected.simplexPrismOperator_boundary n H H' h,
    SecondHurewicz.SimplyConnected.simplexEndpointOperator_zero (n + 1) H' h₀, hc, map_zero,
    sub_zero]
  rfl

theorem HigherHurewicz.straightenedCycle_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (h : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        (straightenedCycle n H H' h c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        c := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X)
        (n + 1) _ _).mpr
  exact
    ⟨SecondHurewicz.SimplyConnected.simplexPrismOperator (n + 1) H' c.1,
      straightenedCycle_boundary n H H' h h₀ c⟩

def FourthHurewicz.normalizedFourChain {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.Chains X 4 →ₗ[ℤ] FirstHurewicz.Chains X 4 :=
  FirstHurewicz.chainLift X 4 fun smp =>
    FirstHurewicz.simplexChain X 4 (normalizedFourSimplex x smp).val

def FourthHurewicz.normalizedFourCycle {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  HigherHurewicz.straightenedCycle 3 (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) c

@[simp]
theorem FourthHurewicz.normalizedFourCycle_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    (normalizedFourCycle x c).val = normalizedFourChain x c.val :=
  rfl

theorem FourthHurewicz.normalizedFourCycle_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (normalizedFourCycle x c) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c := by
  apply
    HigherHurewicz.straightenedCycle_class 3 (normalizationThreeSimplexHomotopy x)
      (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) _ c
  intro smp
  ext s
  exact normalizationFourSimplexHomotopy_zero x smp s

def HigherHurewicz.singularHomologyDesc {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : FirstHurewicz.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X (n + 1),
        F (((FirstHurewicz.singularComplex X).d (n + 1) n).hom b) = 0) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] M :=
  PeriodTorusHigherHomology.homologyDesc (FirstHurewicz.singularComplex X) n
    (F.comp
      (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n).subtype)
    (fun b => hF b)

@[simp]
theorem HigherHurewicz.singularHomologyDesc_cycleClass {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : FirstHurewicz.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X (n + 1),
        F (((FirstHurewicz.singularComplex X).d (n + 1) n).hom b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    singularHomologyDesc n F hF
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n c) =
      F c.1 :=
  PeriodTorusHigherHomology.homologyDesc_cycleClass (FirstHurewicz.singularComplex X) n _ _ c

theorem HigherHurewicz.comp_singularHomologyDesc_eq_id {X : Type} [TopologicalSpace X] {M : Type*}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (F : FirstHurewicz.Chains X n →ₗ[ℤ] M)
    (hF :
      ∀ b : FirstHurewicz.Chains X (n + 1),
        F (((FirstHurewicz.singularComplex X).d (n + 1) n).hom b) = 0)
    (g : M →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n)
    (hg :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n,
        g (F c.1) =
          SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n c) :
    g.comp (singularHomologyDesc n F hF) = LinearMap.id := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (FirstHurewicz.singularComplex X) n
  intro c
  simpa only [LinearMap.comp_apply, singularHomologyDesc_cycleClass, LinearMap.id_apply] using
    hg c

theorem HigherHurewicz.boundarySignSum_even (n : ℕ) (hn : Even (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 1 := by
  rw [Fin.sum_neg_one_pow]
  have h : ¬Even (n + 2) := Nat.not_even_iff_odd.mpr hn.add_one
  exact if_neg h

theorem HigherHurewicz.boundarySignSum_odd (n : ℕ) (hn : Odd (n + 1)) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) = 0 := by
  rw [Fin.sum_neg_one_pow]
  have h : Even (n + 2) := hn.add_one
  exact if_pos h

def HigherHurewicz.constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X) :
    FirstHurewicz.Chains X n :=
  FirstHurewicz.simplexChain X n (ContinuousMap.const (FirstHurewicz.Simplex n) x)

theorem HigherHurewicz.boundary_constantSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) • constantSimplexChain n x := by
  rw [constantSimplexChain, FirstHurewicz.boundary_simplex]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • constantSimplexChain n x) = _
  exact
    (map_sum (zmultiplesHom (FirstHurewicz.Chains X n) (constantSimplexChain n x))
        (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val) Finset.univ).symm

theorem HigherHurewicz.boundary_constantSimplexChain_even {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Even (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) =
      constantSimplexChain n x := by
  rw [boundary_constantSimplexChain, boundarySignSum_even n hn, one_smul]

theorem HigherHurewicz.boundary_constantSimplexChain_odd {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (hn : Odd (n + 1)) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (constantSimplexChain (n + 1) x) = 0 := by
  rw [boundary_constantSimplexChain, boundarySignSum_odd n hn, zero_smul]

theorem HigherHurewicz.constantSimplexChain_cycle_condition {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X) (hn : Odd n) :
    ((FirstHurewicz.singularComplex X).d n (n - 1)).hom (constantSimplexChain n x) = 0 := by
  cases n with
  | zero => simp at hn
  | succ n => exact boundary_constantSimplexChain_odd n x hn

def HigherHurewicz.constantSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) n
    (constantSimplexChain n x) (constantSimplexChain_cycle_condition n x hn)

@[simp]
theorem HigherHurewicz.constantSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) : (constantSimplexCycle n x hn).1 = constantSimplexChain n x :=
  rfl

@[simp]
theorem HigherHurewicz.constantSimplexCycle_class {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (hn : Odd n) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
        (constantSimplexCycle n x hn) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        n _).mpr
  exact ⟨constantSimplexChain (n + 1) x, boundary_constantSimplexChain_even n x hn.add_one⟩

def HigherHurewicz.correctedSimplexChain {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : FirstHurewicz.SingularSimplex X n) : FirstHurewicz.Chains X n :=
  FirstHurewicz.simplexChain X n smp - constantSimplexChain n x

theorem HigherHurewicz.correctedSimplexChain_boundary {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (FirstHurewicz.simplexFace n i) =
          ContinuousMap.const (FirstHurewicz.Simplex n) x) :
    ((FirstHurewicz.singularComplex X).d (n + 1) n).hom (correctedSimplexChain (n + 1) x smp) =
      0 := by
  rw [correctedSimplexChain, map_sub, constantSimplexChain, FirstHurewicz.boundary_simplex,
    FirstHurewicz.boundary_simplex]
  simp only [hfaces, ContinuousMap.const_comp, sub_self]

def HigherHurewicz.correctedSimplexCycle {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (FirstHurewicz.simplexFace n i) =
          ContinuousMap.const (FirstHurewicz.Simplex n) x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) (n + 1)
    (correctedSimplexChain (n + 1) x smp) (correctedSimplexChain_boundary n x smp hfaces)

@[simp]
theorem HigherHurewicz.correctedSimplexCycle_val {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (smp : FirstHurewicz.SingularSimplex X (n + 1))
    (hfaces :
      ∀ i : Fin (n + 2),
        smp.comp (FirstHurewicz.simplexFace n i) =
          ContinuousMap.const (FirstHurewicz.Simplex n) x) :
    (correctedSimplexCycle n x smp hfaces).1 =
      FirstHurewicz.simplexChain X (n + 1) smp - constantSimplexChain (n + 1) x :=
  rfl

def FourthHurewicz.basedFourSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : FirstHurewicz.Chains X 4 :=
  HigherHurewicz.correctedSimplexChain 4 x τ.val

@[simp]
theorem FourthHurewicz.basedFourSimplexChain_eq {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    basedFourSimplexChain τ =
      FirstHurewicz.simplexChain X 4 τ.val -
        FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x) :=
  rfl

def FourthHurewicz.basedFourSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  HigherHurewicz.correctedSimplexCycle 3 x τ.val (basedFourSimplex_face τ)

@[simp]
theorem FourthHurewicz.basedFourSimplexCycle_val {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : (basedFourSimplexCycle τ).1 = basedFourSimplexChain τ :=
  rfl

theorem HigherHurewicz.chainAugmentation_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (c : FirstHurewicz.Chains X (n + 1)) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n
        (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c := by
  have h :
    (SecondHurewicz.SimplyConnected.chainAugmentation X n).comp
        ((FirstHurewicz.singularComplex X).d (n + 1) n).hom =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) •
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      SecondHurewicz.SimplyConnected.chainAugmentation_simplex, LinearMap.smul_apply,
      zsmul_eq_mul, mul_one, Int.cast_id]
  exact LinearMap.congr_fun h c

theorem HigherHurewicz.chainAugmentation_boundary_even (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even (n + 1)) (c : FirstHurewicz.Chains X (n + 1)) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n
        (((FirstHurewicz.singularComplex X).d (n + 1) n).hom c) =
      SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c := by
  rw [chainAugmentation_boundary, boundarySignSum_even n hn, one_smul]

theorem HigherHurewicz.chainAugmentation_evenCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (hn : Even n) (hpos : 0 < n)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SecondHurewicz.SimplyConnected.chainAugmentation X n c.1 = 0 := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ n =>
    rw [← chainAugmentation_boundary_even X n hn]
    have hc : ((FirstHurewicz.singularComplex X).d (n + 1) n).hom c.1 = 0 :=
      SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X)
        (n + 1) c
    rw [hc, map_zero]

theorem HigherHurewicz.chainLift_sub_constant_evenCycle (X : Type) [TopologicalSpace X] {M : Type}
    [AddCommGroup M] [Module ℤ M] (n : ℕ) (hn : Even n) (hpos : 0 < n)
    (f : FirstHurewicz.SingularSimplex X n → M) (m : M)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.chainLift X n (fun smp => f smp - m) c.1 = FirstHurewicz.chainLift X n f c.1 := by
  rw [SecondHurewicz.SimplyConnected.chainLift_sub_constant,
    chainAugmentation_evenCycle X n hn hpos, zero_smul, sub_zero]

def FourthHurewicz.normalizedFourSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    FirstHurewicz.Chains X 4 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  FirstHurewicz.chainLift X 4 fun smp => basedFourSimplexCycle (normalizedFourSimplex x smp)

@[simp]
theorem FourthHurewicz.normalizedFourSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 4) :
    normalizedFourSimplexCycleOperator x (FirstHurewicz.simplexChain X 4 smp) =
      basedFourSimplexCycle (normalizedFourSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 4 _ smp

theorem FourthHurewicz.normalizedFourSimplexCycleOperator_val {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : FirstHurewicz.Chains X 4) :
    (normalizedFourSimplexCycleOperator x c).val =
      FirstHurewicz.chainLift X 4
        (fun smp =>
          FirstHurewicz.simplexChain X 4 (normalizedFourSimplex x smp).val -
            FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x))
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4).subtype.comp
        (normalizedFourSimplexCycleOperator x) =
      FirstHurewicz.chainLift X 4
        (fun smp =>
          FirstHurewicz.simplexChain X 4 (normalizedFourSimplex x smp).val -
            FirstHurewicz.simplexChain X 4 (ContinuousMap.const (FirstHurewicz.Simplex 4) x)) := by
    apply FirstHurewicz.chainMap_ext X 4
    intro smp
    simp only [LinearMap.comp_apply, normalizedFourSimplexCycleOperator_simplex,
      Submodule.subtype_apply, basedFourSimplexCycle_val, basedFourSimplexChain_eq,
      FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

theorem FourthHurewicz.normalizedFourSimplexCycleOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    normalizedFourSimplexCycleOperator x c.val = normalizedFourCycle x c := by
  apply Subtype.ext
  rw [normalizedFourSimplexCycleOperator_val,
    HigherHurewicz.chainLift_sub_constant_evenCycle X 4 (by decide) (by decide),
    normalizedFourCycle_val]
  rfl

theorem FourthHurewicz.normalizedFourSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (normalizedFourSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c := by
  rw [normalizedFourSimplexCycleOperator_cycle, normalizedFourCycle_class]

theorem HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : Fin n → (unitInterval)) (i : Fin n) :
    (HigherHurewicz.CubeTriangulation.cubeSimplex e (simplexQuotient n u) (e i) : ℝ) =
      (prefixMinimum u (i.val + 1) : ℝ) := by
  rw [HigherHurewicz.CubeTriangulation.cubeSimplex_coordinate]
  have h :=
    HigherHurewicz.CubeTriangulation.sum_fin_differences_tail (n + 1)
      (fun k : Fin (n + 2) => (extendedMinimum u k.val : ℝ)) i.succ
  simpa only [simplexQuotient_apply, Fin.val_castSucc, Fin.val_succ, Nat.succ_le_iff,
    Fin.val_last, extendedMinimum_last_succ, show ((0 : (unitInterval)) : ℝ) = 0 from rfl,
    sub_zero, extendedMinimum_of_le u (i.val + 1) i.isLt] using h

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) (i : Fin n) :
    prefixMinimum u (i.val + 1) = u i := by
  apply le_antisymm (prefixMinimum_le_coordinate u (i.val + 1) i (Nat.lt_succ_self _))
  unfold prefixMinimum
  apply Finset.le_inf
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hu (Nat.le_of_lt_succ hj)

theorem HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_of_antitone {n : ℕ}
    (u : Fin n → (unitInterval)) (hu : Antitone u) :
    HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n)) (simplexQuotient n u) = u :=
  by
  funext i
  apply Subtype.ext
  simpa only [Equiv.refl_apply, prefixMinimum_of_antitone u hu i] using
    cubeSimplex_quotient_coordinate (Equiv.refl (Fin n)) u i

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_refl (n : ℕ) :
    (simplexQuotient n).comp (HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      ContinuousMap.id (FirstHurewicz.Simplex n) := by
  apply ContinuousMap.ext
  intro s
  apply HigherHurewicz.CubeTriangulation.cubeSimplex_injective (Equiv.refl (Fin n))
  exact
    cubeSimplex_quotient_of_antitone _
      (HigherHurewicz.CubeTriangulation.cubeSimplex_antitone (Equiv.refl (Fin n)) s)

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_boundary_of_coordinate_le {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hu : u i ≤ u j) :
    simplexQuotient n u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  refine ⟨j.castSucc, ?_⟩
  rw [simplexQuotient_castSucc, prefixMinimum_succ u j.val j.isLt]
  have hp : prefixMinimum u j.val ≤ u j := (prefixMinimum_le_coordinate u j.val i hij).trans hu
  rw [min_eq_left hp]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.cubeSimplex_coordinate_inversion {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : FirstHurewicz.Simplex n) :
    ∃ i j : Fin n,
      i < j ∧
        HigherHurewicz.CubeTriangulation.cubeSimplex e s i ≤
          HigherHurewicz.CubeTriangulation.cubeSimplex e s j := by
  by_contra h
  have hu : StrictAnti (HigherHurewicz.CubeTriangulation.cubeSimplex e s) := by
    intro i j hij
    exact lt_of_not_ge (fun hle => h ⟨i, j, hij, hle⟩)
  have hm : Monotone e := by
    intro i j hij
    exact hu.le_iff_ge.mp (HigherHurewicz.CubeTriangulation.cubeSimplex_antitone e s hij)
  apply he
  apply Equiv.ext
  intro i
  exact (hm.strictMono_of_injective e.injective).apply_eq

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeSimplex_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (he : e ≠ Equiv.refl (Fin n)) (s : FirstHurewicz.Simplex n) :
    simplexQuotient n (HigherHurewicz.CubeTriangulation.cubeSimplex e s) ∈
      SecondHurewicz.SimplyConnected.simplexBoundary n := by
  obtain ⟨i, j, hij, hu⟩ := cubeSimplex_coordinate_inversion e he s
  exact simplexQuotient_boundary_of_coordinate_le _ i j hij hu

theorem HigherHurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_refl {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) :
    (basedSimplexLoop τ).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex (Equiv.refl (Fin n))) =
      τ.val := by
  change (τ.val.comp (simplexQuotient n)).comp _ = _
  rw [ContinuousMap.comp_assoc, simplexQuotient_cubeSimplex_refl, ContinuousMap.comp_id]

theorem HigherHurewicz.SimplexGeometry.basedSimplexLoop_cubeSimplex_other {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex n x) (e : Equiv.Perm (Fin n))
    (he : e ≠ Equiv.refl (Fin n)) :
    (basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ (simplexQuotient_cubeSimplex_boundary e he s)

theorem HigherHurewicz.SimplexGeometry.cubeOrientation_sum (n : ℕ) :
    ∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e = 0 := by
  have hij : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
  have h :=
    Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (n + 2)) 1))
      (HigherHurewicz.CubeTriangulation.cubeOrientation (n := n + 2))
  change
    (∑ e : Equiv.Perm (Fin (n + 2)),
        HigherHurewicz.CubeTriangulation.cubeOrientation ((Equiv.swap 0 1).trans e)) =
      ∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e at h
  simp_rw [HigherHurewicz.CubeTriangulation.cubeOrientation_swap _ hij] at h
  rw [Finset.sum_neg_distrib] at h
  omega

theorem HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplex (n + 2) x) :
    (∑ e : Equiv.Perm (Fin (n + 2)),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X (n + 2)
            ((basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      HigherHurewicz.correctedSimplexChain (n + 2) x τ.val := by
  classical
  let c := HigherHurewicz.constantSimplexChain (n + 2) x
  have heq (e : Equiv.Perm (Fin (n + 2))) :
    HigherHurewicz.CubeTriangulation.cubeOrientation e •
        FirstHurewicz.simplexChain X (n + 2)
          ((basedSimplexLoop τ).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      (if e = Equiv.refl (Fin (n + 2)) then HigherHurewicz.correctedSimplexChain (n + 2) x τ.val
        else 0) +
        HigherHurewicz.CubeTriangulation.cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin (n + 2))
    · subst e
      rw [basedSimplexLoop_cubeSimplex_refl,
        HigherHurewicz.CubeTriangulation.cubeOrientation_refl, one_smul, if_pos rfl, one_smul]
      change
        FirstHurewicz.simplexChain X (n + 2) τ.val =
          (FirstHurewicz.simplexChain X (n + 2) τ.val - c) + c
      exact (sub_add_cancel _ _).symm
    · rw [basedSimplexLoop_cubeSimplex_other τ e he, if_neg he, zero_add]
      rfl
  calc
    _ =
        ∑ e : Equiv.Perm (Fin (n + 2)),
          ((if e = Equiv.refl (Fin (n + 2)) then
              HigherHurewicz.correctedSimplexChain (n + 2) x τ.val
            else 0) +
            HigherHurewicz.CubeTriangulation.cubeOrientation e • c) :=
      Finset.sum_congr rfl (fun e _ => heq e)
    _ =
        HigherHurewicz.correctedSimplexChain (n + 2) x τ.val +
          (∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e) •
            c := by
      rw [Finset.sum_add_distrib]
      have hc :
        (∑ e : Equiv.Perm (Fin (n + 2)), HigherHurewicz.CubeTriangulation.cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin (n + 2)),
            HigherHurewicz.CubeTriangulation.cubeOrientation e • c := by
        let f : ℤ →+ FirstHurewicz.Chains X (n + 2) :=
          { toFun := fun k => k • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f HigherHurewicz.CubeTriangulation.cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = HigherHurewicz.correctedSimplexChain (n + 2) x τ.val := by
      rw [cubeOrientation_sum n, zero_smul, add_zero]

theorem FourthHurewicz.basedFourSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    (∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 4
            ((basedFourSimplexLoop τ).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedFourSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum τ

theorem FourthHurewicz.CubeSubdivision.signed_sum_eq_zero_of_swap_invariant {n : ℕ} {A : Type*}
    [AddCommGroup A] (i j : Fin n) (hij : i ≠ j) (f : Equiv.Perm (Fin n) → A)
    (hf : ∀ e, f ((Equiv.swap i j).trans e) = f e) :
    ∑ e, HigherHurewicz.CubeTriangulation.cubeOrientation e • f e = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [HigherHurewicz.CubeTriangulation.cubeOrientation_swap e hij, hf, neg_smul, add_neg_cancel]
  · intro e _ he
    have h := congrArg (fun k : Equiv.Perm (Fin n) => k i) he
    have h' : e j = e i := by simpa using h
    exact hij (e.injective h').symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    simp

theorem FourthHurewicz.CubeSubdivision.signed_sum_constant_eq_zero {n : ℕ} [Nontrivial (Fin n)]
    {A : Type*} [AddCommGroup A] (a : A) :
    ∑ e : Equiv.Perm (Fin n), HigherHurewicz.CubeTriangulation.cubeOrientation e • a = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  exact signed_sum_eq_zero_of_swap_invariant i j hij (fun _ => a) (fun _ => rfl)

def FourthHurewicz.CubeSubdivision.prismCubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) : HigherHurewicz.CubeTriangulation.CubeN (n + 1) :=
  Fin.cases (FirstHurewicz.pathSimplex Path.id (SingularMayerVietoris.stdVertices 1 z.1))
    (HigherHurewicz.CubeTriangulation.cubeVertex e z.2)

@[simp]
theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_succ {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) (i : Fin n) :
    prismCubeVertex e z i.succ = HigherHurewicz.CubeTriangulation.cubeVertex e z.2 i :=
  rfl

def FourthHurewicz.CubeSubdivision.prismCubeSimplex {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    C(FirstHurewicz.Simplex m, HigherHurewicz.CubeTriangulation.CubeN (n + 1)) :=
  HigherHurewicz.CubeTriangulation.cubeAffineSimplex (fun j => prismCubeVertex e (v j))

theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_swap_of_ne {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (z : Fin 2 × Fin (n + 2))
    (hz : z.2 ≠ i.succ.castSucc) :
    prismCubeVertex e z = prismCubeVertex ((Equiv.swap i.castSucc i.succ).trans e) z := by
  funext coord
  refine Fin.cases ?_ (fun k => ?_) coord
  · rfl
  · exact congrFun (HigherHurewicz.CubeTriangulation.cubeVertex_swap_of_ne e i z.2 hz) k

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_swap_of_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    prismCubeSimplex e v = prismCubeSimplex ((Equiv.swap i.castSucc i.succ).trans e) v := by
  apply congrArg HigherHurewicz.CubeTriangulation.cubeAffineSimplex
  funext j
  exact prismCubeVertex_swap_of_ne e i (v j) (hv j)

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_zero_of_left_zero {m n : ℕ}
    (e : Equiv.Perm (Fin n)) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) (hv : ∀ j, (v j).1 = 0)
    (s : FirstHurewicz.Simplex m) : prismCubeSimplex e v s 0 = 0 := by
  apply HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp [prismCubeVertex, hv j, SingularMayerVietoris.stdVertices]

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_zero_of_last_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ Fin.last (n + 1)) (s : FirstHurewicz.Simplex m) :
    prismCubeSimplex e v s (e (Fin.last n)).succ = 0 := by
  apply HigherHurewicz.CubeTriangulation.cubeAffineSimplex_constant_coordinate
  intro j
  simp only [prismCubeVertex_succ, HigherHurewicz.CubeTriangulation.cubeVertex,
    Equiv.symm_apply_apply, Fin.val_last]
  apply if_neg
  have hne : (v j).2.val ≠ n + 1 := by
    intro h
    exact hv j (Fin.ext h)
  have hlt := (v j).2.isLt
  omega

def FourthHurewicz.CubeSubdivision.prismCubeRealization {X : Type} [TopologicalSpace X] {n : ℕ}
    (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) (e : Equiv.Perm (Fin n)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      FirstHurewicz.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp]
theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    prismCubeRealization p e m (SingularMayerVietoris.formalSimplex v) =
      FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

def FourthHurewicz.CubeSubdivision.orientedPrismRealization {X : Type} [TopologicalSpace X]
    {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) (m : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ]
      FirstHurewicz.Chains X m :=
  SingularMayerVietoris.formalLift fun v =>
    ∑ e : Equiv.Perm (Fin n),
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp]
theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_simplex {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    orientedPrismRealization p m (SingularMayerVietoris.formalSimplex v) =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  SingularMayerVietoris.formalLift_simplex _ _

abbrev FourthHurewicz.Remaining :=
  { j : Fin 4 // j ≠ 0 }

def FourthHurewicz.remainingCoordinates : C(Fin 3 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
theorem FourthHurewicz.remainingCoordinates_succ (u : Fin 3 → (unitInterval)) (i : Fin 3) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

theorem FourthHurewicz.remainingCoordinates_boundary {u : Fin 3 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 3)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

abbrev FourthHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

def FourthHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 3 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

theorem FourthHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 3 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 3)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

theorem FourthHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (x : X) (f : C(A, Fin 3 → (unitInterval)))
    (hf : ∀ a, f a ∈ Cube.boundary (Fin 3)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

def FourthHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 3 → (unitInterval)), Fin 4 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 4) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem FourthHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 3 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem FourthHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 3 → (unitInterval)))
    (i : Fin 3) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

def FourthHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    C((unitInterval) × (Fin 3 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

theorem FourthHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 4) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 3 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

theorem FourthHurewicz.CubeSubdivision.cubeCoordinates_boundary_right (s : (unitInterval))
    {u : Fin 3 → (unitInterval)} (hu : u ∈ Cube.boundary (Fin 3)) :
    FourthHurewicz.cubeCoordinates (s, u) ∈ Cube.boundary (Fin 4) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [FourthHurewicz.cubeCoordinates_succ] using hi⟩

def FourthHurewicz.CubeSubdivision.curryLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    GenLoop (Fin 3) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((FourthHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry,
    by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

def FourthHurewicz.CubeSubdivision.evalLeft (X : Type) [TopologicalSpace X] :
    C((unitInterval) × C((unitInterval), X), X)
    where
  toFun z := z.2 z.1
  continuous_toFun := by fun_prop

theorem FourthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    (evalLeft X).comp ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      FourthHurewicz.cubeMap p := by
  ext z
  rfl

theorem FourthHurewicz.CubeSubdivision.cubeAffineSimplex_comp {k m n : ℕ}
    (v : Fin (n + 1) → HigherHurewicz.CubeTriangulation.CubeN k)
    (w : Fin (m + 1) → FirstHurewicz.Simplex n) :
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex w) =
      HigherHurewicz.CubeTriangulation.cubeAffineSimplex
        (fun j => HigherHurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) := by
  ext t i
  change
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v
          (SingularMayerVietoris.affineSimplex w t) i :
        ℝ) =
      (HigherHurewicz.CubeTriangulation.cubeAffineSimplex
          (fun j => HigherHurewicz.CubeTriangulation.cubeAffineSimplex v (w j)) t i :
        ℝ)
  simp only [HigherHurewicz.CubeTriangulation.cubeAffineSimplex_coordinate,
    SingularMayerVietoris.affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem FourthHurewicz.CubeSubdivision.cubeAffineSimplex_comp_selectedVertices {k m n : ℕ}
    (v : Fin (n + 1) → HigherHurewicz.CubeTriangulation.CubeN k) (a : Fin (m + 1) → Fin (n + 1)) :
    (HigherHurewicz.CubeTriangulation.cubeAffineSimplex v).comp
        (SingularMayerVietoris.affineSimplex
          (fun j => SingularMayerVietoris.stdVertices n (a j))) =
      HigherHurewicz.CubeTriangulation.cubeAffineSimplex (fun j => v (a j)) := by
  rw [cubeAffineSimplex_comp]
  simp only [HigherHurewicz.CubeTriangulation.cubeAffineSimplex_vertex]

def FourthHurewicz.CubeSubdivision.prismCubeMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(FirstHurewicz.Simplex 1 × FirstHurewicz.Simplex n,
      HigherHurewicz.CubeTriangulation.CubeN (n + 1))
    where
  toFun
    z :=
    Fin.cases (FirstHurewicz.pathSimplex Path.id z.1)
      (HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (FirstHurewicz.pathSimplex Path.id).continuous.comp continuous_fst
    · exact
        (continuous_apply j).comp
          ((HigherHurewicz.CubeTriangulation.cubeSimplex e).continuous.comp continuous_snd)

theorem FourthHurewicz.CubeSubdivision.prismCubeMap_affine {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    (prismCubeMap e).comp
        (PeriodTorusHigherHomology.productAffineSimplex
          (fun j =>
            (SingularMayerVietoris.stdVertices 1 (v j).1,
              SingularMayerVietoris.stdVertices n (v j).2))) =
      prismCubeSimplex e v := by
  apply ContinuousMap.ext
  intro t
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply Subtype.ext
    change
      SingularMayerVietoris.affineSimplex (fun j => SingularMayerVietoris.stdVertices 1 (v j).1) t
          1 =
        ∑ j, t j * SingularMayerVietoris.stdVertices 1 (v j).1 1
    exact SingularMayerVietoris.affineSimplex_coordinate _ _ _
  · change
      ((HigherHurewicz.CubeTriangulation.cubeAffineSimplex
                (HigherHurewicz.CubeTriangulation.cubeVertex e)).comp
            (SingularMayerVietoris.affineSimplex
              (fun j => SingularMayerVietoris.stdVertices n (v j).2)))
          t k =
        _
    rw [cubeAffineSimplex_comp_selectedVertices]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.remainingCubeSideFirst (t : (unitInterval)) :
    C(Fin 2 → (unitInterval), Fin 3 → (unitInterval)) :=
  ThirdHurewicz.cubeCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.remainingCubeSide (f : C((unitInterval), Fin 2 → (unitInterval))) :
    C((unitInterval) × (unitInterval), Fin 3 → (unitInterval)) :=
  ThirdHurewicz.cubeCoordinates.comp ((ContinuousMap.id (unitInterval)).prodMap f)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.remainingCubeSideFirst_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (u : Fin 2 → (unitInterval)) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 3) := by
  refine ⟨0, ?_⟩
  change ThirdHurewicz.cubeCoordinates (t, u) 0 = 0 ∨ ThirdHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [ThirdHurewicz.cubeCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.remainingCubeSide_boundary (f : C((unitInterval), Fin 2 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 2)) (z : (unitInterval) × (unitInterval)) :
    remainingCubeSide f z ∈ Cube.boundary (Fin 3) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change
    ThirdHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
      ThirdHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [ThirdHurewicz.cubeCoordinates_succ] using hi

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.remainingCubeSide_chain (f : C((unitInterval), Fin 2 → (unitInterval))) :
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 1
          SecondHurewicz.intervalChain
          (FirstHurewicz.inducedChain f 1 SecondHurewicz.intervalChain)) =
      FirstHurewicz.inducedChain (remainingCubeSide f) 2 SecondHurewicz.productSquareChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f 1
      SecondHurewicz.intervalChain SecondHurewicz.intervalChain
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (unitInterval)).prodMap f) 2))
        SecondHurewicz.productSquareChain =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.remainingCubeChain_boundary :
    ((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
        ThirdHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (remainingCubeSideFirst 1) 2
            SecondHurewicz.fundamentalSquareChain -
          FirstHurewicz.inducedChain (remainingCubeSideFirst 0) 2
            SecondHurewicz.fundamentalSquareChain -
        (FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideLeft 1)) 2
              SecondHurewicz.productSquareChain -
            FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideLeft 0)) 2
              SecondHurewicz.productSquareChain -
          (FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideRight 1)) 2
              SecondHurewicz.productSquareChain -
            FirstHurewicz.inducedChain (remainingCubeSide (ThirdHurewicz.squareSideRight 0)) 2
              SecondHurewicz.productSquareChain)) := by
  have hpoint (t : (unitInterval)) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 2 → (unitInterval)) 2
        (FirstHurewicz.pointChain t) SecondHurewicz.fundamentalSquareChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 2
        SecondHurewicz.fundamentalSquareChain := by
    rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : (unitInterval)) :
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 2
          SecondHurewicz.fundamentalSquareChain) =
      FirstHurewicz.inducedChain (remainingCubeSideFirst t) 2
        SecondHurewicz.fundamentalSquareChain := by
    rw [remainingCubeSideFirst, FirstHurewicz.inducedChain_comp]
    rfl
  rw [ThirdHurewicz.fundamentalCubeChain, ← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (((FirstHurewicz.singularComplex ((unitInterval) × (Fin 2 → (unitInterval)))).d 3 2).hom
          (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 2
            SecondHurewicz.intervalChain SecondHurewicz.fundamentalSquareChain)) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 1]
  change
    FirstHurewicz.inducedChain ThirdHurewicz.cubeCoordinates 2
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 2 → (unitInterval)) 2
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain)
            SecondHurewicz.fundamentalSquareChain -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 2 → (unitInterval)) 1
            SecondHurewicz.intervalChain
            (FirstHurewicz.boundaryTwo (Fin 2 → (unitInterval))
              SecondHurewicz.fundamentalSquareChain)) =
      _
  rw [SecondHurewicz.intervalChain_boundary, ThirdHurewicz.fundamentalSquareChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.evaluated_edge_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (b : FirstHurewicz.Chains A 2) (f : C(A, Fin 3 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 3)) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 2
          a (FirstHurewicz.inducedChain f 2 b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) A 2 a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f 2 a
      b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 3).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 3))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.evaluated_triangle_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2)
    (b : FirstHurewicz.Chains A 2) (f : C(A, Fin 3 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 3)) :
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 3 → (unitInterval)) 2 a (FirstHurewicz.inducedChain f 2 b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) A 2 a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      2 a b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 4).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) 4))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.evaluated_edge_cubeBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 2
          a
          (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
            ThirdHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.fundamentalSquareChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideLeft t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideRight t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.evaluated_triangle_cubeBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 3 → (unitInterval)) 2 a
          (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
            ThirdHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.fundamentalSquareChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideLeft t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideLeft_boundary t ht))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a SecondHurewicz.productSquareChain
      (remainingCubeSide (ThirdHurewicz.squareSideRight t))
      (remainingCubeSide_boundary _ (ThirdHurewicz.squareSideRight_boundary t ht))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl), hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 4 :=
  (FirstHurewicz.inducedChain (evaluation x) 4).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 3)
      ThirdHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem FourthHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 3
          a ThirdHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 5 :=
  (FirstHurewicz.inducedChain (evaluation x) 5).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 3 → (unitInterval))
        3)
      ThirdHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem FourthHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 3 → (unitInterval)) 3 a ThirdHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.boundaryFour_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 4 3).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 2]
  change
    FirstHurewicz.inducedChain (evaluation x) 3
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 3 → (unitInterval)) 3 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            ThirdHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 2
            a
            (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
              ThirdHurewicz.fundamentalCubeChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_cubeBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.boundaryFive_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 2]
  change
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 3 → (unitInterval)) 3
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) ThirdHurewicz.fundamentalCubeChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 3 → (unitInterval)) 2 a
            (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
              ThirdHurewicz.fundamentalCubeChain)) =
      _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

def FourthHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 4
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryFour_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
theorem FourthHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

def FourthHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 4 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
    (pathCubeCycle x p)

theorem FourthHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundaryFive_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem FourthHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 4 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem FourthHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
theorem FourthHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        4 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundaryFive_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

theorem FourthHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundaryFive_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add,
    map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem FourthHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 4 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 3 → (unitInterval))) 4 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 3
    SecondHurewicz.intervalChain ThirdHurewicz.fundamentalCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 4 → (unitInterval)) 4 :=
  FirstHurewicz.inducedChain cubeCoordinates 4 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 4) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 4 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 4) p).toContinuousMap (ContinuousMap.id (Fin 3 → (unitInterval))) 3
      SecondHurewicz.intervalChain ThirdHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 4).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 4) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 3 → (unitInterval))))
            4))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    FirstHurewicz.Chains X 4 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 4) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 4 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 4 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 4).comp (FirstHurewicz.inducedChain cubeCoordinates 4))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 4) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) : SingularMayerVietoris.SingularHomology X 4 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 4) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 4) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 4) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 4) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 4) (GenLoop.const : GenLoop (Fin 4) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem FourthHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 4) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 4) X x) :
    GenLoop.toLoop (0 : Fin 4) (GenLoop.transAt (0 : Fin 4) p q) =
      (GenLoop.toLoop (0 : Fin 4) p).trans (GenLoop.toLoop (0 : Fin 4) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 4))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 4)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 4) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 4) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.evalLeft_crossProductEdge_curryLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) (n : ℕ)
    (b : FirstHurewicz.Chains (Fin 3 → (unitInterval)) n) :
    FirstHurewicz.inducedChain (evalLeft X) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain (curryLoop p).val n b)) =
      FirstHurewicz.inducedChain (FourthHurewicz.cubeMap p) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) n
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval))
      (curryLoop p).val n SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evalLeft X) (n + 1)).comp
          (FirstHurewicz.inducedChain
            ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) (n + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evalLeft_comp_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.cubeChain_eq_curriedCrossProduct {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      FirstHurewicz.inducedChain (evalLeft X) 4
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 3
          SecondHurewicz.intervalChain (ThirdHurewicz.cubeChain (curryLoop p))) := by
  rw [ThirdHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    FourthHurewicz.cubeChain_eq_induced, FourthHurewicz.fundamentalCubeChain]
  change
    (FirstHurewicz.inducedChain p.val 4)
        ((FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 4)
          FourthHurewicz.productCubeChain) =
      (FirstHurewicz.inducedChain (p.val.comp FourthHurewicz.cubeCoordinates) 4)
        FourthHurewicz.productCubeChain
  rw [FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FourthHurewicz.CubeSubdivision.intervalTetrahedronChain {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) : FirstHurewicz.Chains X 4 :=
  FirstHurewicz.inducedChain (evalLeft X) 4
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 3
      SecondHurewicz.intervalChain
      (FirstHurewicz.simplexChain C((unitInterval), X) 3
        ((curryLoop p).val.comp (ThirdHurewicz.Geometry.cubeTetrahedron e))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.intervalTetrahedronChain_eq_original {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) :
    intervalTetrahedronChain p e =
      FirstHurewicz.inducedChain (FourthHurewicz.cubeMap p) 4
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 3
          SecondHurewicz.intervalChain
          (FirstHurewicz.simplexChain (Fin 3 → (unitInterval)) 3
            (ThirdHurewicz.Geometry.cubeTetrahedron e))) := by
  rw [intervalTetrahedronChain, ← FirstHurewicz.inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_prisms {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 3),
        ThirdHurewicz.Geometry.cubeOrientation e • intervalTetrahedronChain p e := by
  rw [cubeChain_eq_curriedCrossProduct, ThirdHurewicz.CubeSubdivision.cubeChain_eq_sum_tetrahedra]
  simp only [map_sum, map_zsmul, intervalTetrahedronChain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_eq_induced {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) :
    prismCubeRealization p e m =
      (FirstHurewicz.inducedChain (p.comp (prismCubeMap e)) m).comp
        ((PeriodTorusHigherHomology.productAffineChainMap 1 n m).comp
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.stdVertices 1) (SingularMayerVietoris.stdVertices n))
            (m + 1))) := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  simp only [prismCubeRealization_simplex, LinearMap.comp_apply,
    SingularMayerVietoris.formalMap_simplex,
    PeriodTorusHigherHomology.productAffineChainMap_simplex, FirstHurewicz.inducedChain_simplex]
  apply congrArg (FirstHurewicz.simplexChain X m)
  change
    p.comp (prismCubeSimplex e v) =
      p.comp
        ((prismCubeMap e).comp
          (PeriodTorusHigherHomology.productAffineSimplex
            (fun j =>
              (SingularMayerVietoris.stdVertices 1 (v j).1,
                SingularMayerVietoris.stdVertices n (v j).2))))
  rw [prismCubeMap_affine]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) :
    prismCubeRealization p e (n + 1)
        (PeriodTorusHigherHomology.formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 1) => j))) =
      FirstHurewicz.inducedChain (p.comp (prismCubeMap e)) (n + 1)
        (PeriodTorusHigherHomology.productAffineChainMap 1 n (n + 1)
          (PeriodTorusHigherHomology.formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) := by
  rw [prismCubeRealization_eq_induced]
  simp only [LinearMap.comp_apply]
  rw [PeriodTorusHigherHomology.formalMap_edgeCrossProduct]
  simp only [SingularMayerVietoris.formalMap_simplex, Function.comp_def]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.prismCubeMap_three (e : Equiv.Perm (Fin 3)) :
    FourthHurewicz.cubeCoordinates.comp
        ((FirstHurewicz.pathSimplex Path.id).prodMap (ThirdHurewicz.Geometry.cubeTetrahedron e)) =
      prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact FourthHurewicz.cubeCoordinates_zero _
  · change
      FourthHurewicz.cubeCoordinates
          (FirstHurewicz.pathSimplex Path.id z.1, ThirdHurewicz.Geometry.cubeTetrahedron e z.2)
          j.succ =
        _
    rw [FourthHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FourthHurewicz.CubeSubdivision.intervalTetrahedronChain_eq_prismCubeRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 3)) :
    intervalTetrahedronChain p e =
      prismCubeRealization p.val e 4
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 3
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 4 => j))) := by
  rw [intervalTetrahedronChain_eq_original, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex, prismCubeRealization_edgeCrossProduct]
  change
    ((FirstHurewicz.inducedChain (FourthHurewicz.cubeMap p) 4).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (ThirdHurewicz.Geometry.cubeTetrahedron e))
            4))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  change
    FirstHurewicz.inducedChain
        (p.val.comp
          (FourthHurewicz.cubeCoordinates.comp
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (ThirdHurewicz.Geometry.cubeTetrahedron e))))
        4 _ =
      _
  rw [prismCubeMap_three]

theorem PeriodTorusHigherHomology.formalPointCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} (q : ℕ) {c : SingularMayerVietoris.FormalChains V 1}
    {d : SingularMayerVietoris.FormalChains W (q + 1)}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported S 1)
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1)) :
    formalPointCrossProduct q c d ∈
      SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1) := by
  apply
    SingularMayerVietoris.formalLinearMap_mem_of_supported ((formalPointCrossProduct q).flip d)
      (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 1)) hc
  intro v hv
  change formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d ∈ _
  rw [formalPointCrossProduct_simplex_left]
  exact
    SingularMayerVietoris.formalMap_mem_supported (S := T) (T := S ×ˢ T) (fun w => (v 0, w))
      (fun _ hw => ⟨hv 0, hw⟩) hd

theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_mem_supported {V W : Type*} {S : Set V}
    {T : Set W} :
    ∀ (q : ℕ) {c : SingularMayerVietoris.FormalChains V 2}
      {d : SingularMayerVietoris.FormalChains W (q + 1)},
      c ∈ SingularMayerVietoris.formalChainsSupported S 2 →
        d ∈ SingularMayerVietoris.formalChainsSupported T (q + 1) →
          formalEdgeCrossProduct q c d ∈
            SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 2) := by
  intro q
  induction q with
  | zero =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported (formalEdgeCrossProduct 0 c)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) 2) hd
    intro w hw
    rw [formalEdgeCrossProduct_zero_simplex_right]
    exact
      SingularMayerVietoris.formalMap_mem_supported (S := S) (T := S ×ˢ T) (fun v => (v, w 0))
        (fun _ hv => ⟨hv, hw 0⟩) hc
  | succ q ih =>
    intro c d hc hd
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        ((formalEdgeCrossProduct (q + 1)).flip d)
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hc
    intro v hv
    change formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v) d ∈ _
    apply
      SingularMayerVietoris.formalLinearMap_mem_of_supported
        (formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v))
        (SingularMayerVietoris.formalChainsSupported (S ×ˢ T) (q + 3)) hd
    intro w hw
    rw [formalEdgeCrossProduct_simplex_succ]
    apply
      SingularMayerVietoris.formalCone_mem_supported (show (v 0, w 0) ∈ S ×ˢ T from ⟨hv 0, hw 0⟩)
    apply Submodule.sub_mem
    · exact
        formalPointCrossProduct_mem_supported (q + 1)
          (SingularMayerVietoris.formalBoundary_mem_supported 1
            (SingularMayerVietoris.formalSimplex_mem_supported hv))
          (SingularMayerVietoris.formalSimplex_mem_supported hw)
    · exact
        ih (SingularMayerVietoris.formalSimplex_mem_supported hv)
          (SingularMayerVietoris.formalBoundary_mem_supported (q + 1)
            (SingularMayerVietoris.formalSimplex_mem_supported hw))

def FourthHurewicz.CubeSubdivision.badPrism (q m : ℕ) :
    Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m) :=
  SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ⊔
    ⨆ i : { i : Fin (q + 1) // i ≠ 0 },
      SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i.val} m

theorem FourthHurewicz.CubeSubdivision.mem_badPrism_of_left_zero {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_left hc

theorem FourthHurewicz.CubeSubdivision.mem_badPrism_of_omit {q m : ℕ} (i : Fin (q + 1))
    (hi : i ≠ 0) {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m}
    (hc : c ∈ SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m) : c ∈ badPrism q m :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ⟨i, hi⟩ hc)

theorem FourthHurewicz.CubeSubdivision.badPrism_le {q m : ℕ}
    {P : Submodule ℤ (SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m)}
    (hzero : SingularMayerVietoris.formalChainsSupported {z | z.1 = 0} m ≤ P)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → SingularMayerVietoris.formalChainsSupported {z | z.2 ≠ i} m ≤ P) :
    badPrism q m ≤ P :=
  sup_le hzero (iSup_le fun i => homit i.val i.property)

theorem FourthHurewicz.CubeSubdivision.badPrism_le_ker {q m : ℕ} {M : Type*} [AddCommGroup M]
    [Module ℤ M] (f : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m →ₗ[ℤ] M)
    (hzero : ∀ v, (∀ j, (v j).1 = 0) → f (SingularMayerVietoris.formalSimplex v) = 0)
    (homit :
      ∀ i : Fin (q + 1),
        i ≠ 0 → ∀ v, (∀ j, (v j).2 ≠ i) → f (SingularMayerVietoris.formalSimplex v) = 0) :
    badPrism q m ≤ LinearMap.ker f := by
  apply badPrism_le
  · exact SingularMayerVietoris.formalChainsSupported_le hzero
  · intro i hi
    exact SingularMayerVietoris.formalChainsSupported_le (homit i hi)

theorem FourthHurewicz.CubeSubdivision.formalCone_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalCone (0, 0) m c ∈ badPrism q (m + 1) := by
  have hle :
    badPrism q m ≤ (badPrism q (m + 1)).comap (SingularMayerVietoris.formalCone (0, 0) m) := by
    apply badPrism_le
    · intro d hd
      exact
        mem_badPrism_of_left_zero
          (SingularMayerVietoris.formalCone_mem_supported (S :=
            {z : Fin 2 × Fin (q + 1) | z.1 = 0}) (a := (0, 0)) rfl hd)
    · intro i hi d hd
      exact
        mem_badPrism_of_omit i hi (SingularMayerVietoris.formalCone_mem_supported (Ne.symm hi) hd)
  exact hle hc

theorem FourthHurewicz.CubeSubdivision.formalMap_succ_mem_badPrism {q m : ℕ}
    {c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) m} (hc : c ∈ badPrism q m) :
    SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2))) m c ∈
      badPrism (q + 1) m := by
  have hle :
    badPrism q m ≤
      (badPrism (q + 1) m).comap
        (SingularMayerVietoris.formalMap (Prod.map id (Fin.succ : Fin (q + 1) → Fin (q + 2)))
          m) := by
    apply badPrism_le
    · intro d hd
      apply mem_badPrism_of_left_zero
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.1 = 0})
          (T := {z : Fin 2 × Fin (q + 2) | z.1 = 0}) (Prod.map id Fin.succ) (fun _ hz => hz) hd
    · intro i hi d hd
      apply mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i)
      exact
        SingularMayerVietoris.formalMap_mem_supported (S := {z : Fin 2 × Fin (q + 1) | z.2 ≠ i})
          (T := {z : Fin 2 × Fin (q + 2) | z.2 ≠ i.succ}) (Prod.map id Fin.succ)
          (fun _ hz h => hz (Fin.succ_injective _ h)) hd
  exact hle hc

theorem FourthHurewicz.CubeSubdivision.formalEdgeCrossProduct_mem_badPrism_of_omit {q r : ℕ}
    (i : Fin (q + 1)) (hi : i ≠ 0) (c : SingularMayerVietoris.FormalChains (Fin 2) 2)
    {d : SingularMayerVietoris.FormalChains (Fin (q + 1)) (r + 1)}
    (hd : d ∈ SingularMayerVietoris.formalChainsSupported {j | j ≠ i} (r + 1)) :
    PeriodTorusHigherHomology.formalEdgeCrossProduct r c d ∈ badPrism q (r + 2) := by
  apply mem_badPrism_of_omit i hi
  apply
    SingularMayerVietoris.formalChainsSupported_mono (S :=
      (Set.univ : Set (Fin 2)) ×ˢ {j : Fin (q + 1) | j ≠ i}) (fun _ hz => hz.2)
  exact
    PeriodTorusHigherHomology.formalEdgeCrossProduct_mem_supported r (S := Set.univ) (by simp) hd

def FourthHurewicz.CubeSubdivision.retainedFirstBoundary {W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains W (q + 2) →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) :=
  SingularMayerVietoris.formalLift fun w =>
    ∑ i : Fin (q + 1),
      (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove)

@[simp]
theorem FourthHurewicz.CubeSubdivision.retainedFirstBoundary_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) =
      ∑ i : Fin (q + 1),
        (-1 : ℤ) ^ (i.val + 1) • SingularMayerVietoris.formalSimplex (w ∘ i.succ.succAbove) :=
  SingularMayerVietoris.formalLift_simplex _ _

theorem FourthHurewicz.CubeSubdivision.formalBoundary_firstFace_split_simplex {W : Type*} (q : ℕ)
    (w : Fin (q + 2) → W) :
    SingularMayerVietoris.formalBoundary (q + 1) (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (Fin.tail w) +
        retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w) := by
  rw [SingularMayerVietoris.formalBoundary_simplex, Fin.sum_univ_succ,
    retainedFirstBoundary_simplex]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.succAbove_zero]
  rfl

def FourthHurewicz.CubeSubdivision.shufflePrismVertices {V W : Type*} {q : ℕ} (v : Fin 2 → V)
    (w : Fin (q + 1) → W) (i : Fin (q + 1)) : Fin (q + 2) → V × W := fun k =>
  (if k ≤ i.castSucc then v 0 else v 1, w (i.predAbove k))

@[simp]
theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_first {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i 0 = (v 0, w 0) := by simp [shufflePrismVertices]

theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_zero_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    shufflePrismVertices v w 0 = Fin.cons (v 0, w 0) (fun j => (v 1, w j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices]

theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_succ_index {V W : Type*} {q : ℕ}
    (v : Fin 2 → V) (w : Fin (q + 2) → W) (i : Fin (q + 1)) :
    shufflePrismVertices v w i.succ =
      Fin.cons (v 0, w 0) (shufflePrismVertices v (Fin.tail w) i) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · simp [shufflePrismVertices, Fin.tail, Fin.le_castSucc_iff]

theorem FourthHurewicz.CubeSubdivision.shufflePrismVertices_map {V W V' W' : Type*} {q : ℕ}
    (f : V → V') (g : W → W') (v : Fin 2 → V) (w : Fin (q + 1) → W) (i : Fin (q + 1)) :
    Prod.map f g ∘ shufflePrismVertices v w i = shufflePrismVertices (f ∘ v) (g ∘ w) i := by
  funext k
  simp only [shufflePrismVertices, Function.comp_apply, Prod.map_apply]
  split_ifs <;> rfl

def FourthHurewicz.CubeSubdivision.standardPrism {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  ∑ i : Fin (q + 1),
    (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (shufflePrismVertices v w i)

theorem FourthHurewicz.CubeSubdivision.standardPrism_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) :
    standardPrism 0 v w = SingularMayerVietoris.formalSimplex (fun i => (v i, w 0)) := by
  rw [standardPrism, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.eq_zero j]
    rfl

theorem FourthHurewicz.CubeSubdivision.standardPrism_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    standardPrism (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (SingularMayerVietoris.formalMap (fun z => (v 1, z)) (q + 2)
            (SingularMayerVietoris.formalSimplex w) -
          standardPrism q v (Fin.tail w)) := by
  rw [standardPrism, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, shufflePrismVertices_zero_index, map_sub,
    SingularMayerVietoris.formalMap_simplex, SingularMayerVietoris.formalCone_simplex,
    standardPrism, map_sum, map_smul, SingularMayerVietoris.formalCone_simplex]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, shufflePrismVertices_succ_index]

theorem FourthHurewicz.CubeSubdivision.formalMap_standardPrism {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (standardPrism q v w) =
      standardPrism q (f ∘ v) (g ∘ w) := by
  simp only [standardPrism, map_sum, map_smul, SingularMayerVietoris.formalMap_simplex,
    shufflePrismVertices_map]

def FourthHurewicz.CubeSubdivision.prismDiscrepancy {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 1) → W) : SingularMayerVietoris.FormalChains (V × W) (q + 2) :=
  PeriodTorusHigherHomology.formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
      (SingularMayerVietoris.formalSimplex w) -
    standardPrism q v w

@[simp]
theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_zero {V W : Type*} (v : Fin 2 → V)
    (w : Fin 1 → W) : prismDiscrepancy 0 v w = 0 := by
  simp only [prismDiscrepancy,
    PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, standardPrism_zero, Function.comp_def, sub_self]

theorem FourthHurewicz.CubeSubdivision.formalMap_prismDiscrepancy {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (prismDiscrepancy q v w) =
      prismDiscrepancy q (f ∘ v) (g ∘ w) := by
  simp only [prismDiscrepancy, map_sub, PeriodTorusHigherHomology.formalMap_edgeCrossProduct,
    formalMap_standardPrism, SingularMayerVietoris.formalMap_simplex]

def FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy (q : ℕ) :
    SingularMayerVietoris.FormalChains (Fin 2 × Fin (q + 1)) (q + 2) :=
  prismDiscrepancy q (fun i => i) (fun j => j)

@[simp]
theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_zero :
    canonicalPrismDiscrepancy 0 = 0 :=
  prismDiscrepancy_zero _ _

theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_eq_map_canonical {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 1) → W) :
    prismDiscrepancy q v w =
      SingularMayerVietoris.formalMap (Prod.map v w) (q + 2) (canonicalPrismDiscrepancy q) := by
  simpa only [canonicalPrismDiscrepancy, Function.comp_def] using
    (formalMap_prismDiscrepancy v w q (fun i => i) (fun j => j)).symm

theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_succ {V W : Type*} (q : ℕ) (v : Fin 2 → V)
    (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            PeriodTorusHigherHomology.formalEdgeCrossProduct q
              (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalBoundary (q + 1)
                (SingularMayerVietoris.formalSimplex w)) +
          standardPrism q v (Fin.tail w)) := by
  rw [prismDiscrepancy, PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ,
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary, standardPrism_succ]
  simp only [map_sub, map_add, map_neg]
  abel

theorem FourthHurewicz.CubeSubdivision.prismDiscrepancy_succ_retained {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    prismDiscrepancy (q + 1) v w =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (-SingularMayerVietoris.formalMap (fun z => (v 0, z)) (q + 2)
                (SingularMayerVietoris.formalSimplex w) -
            prismDiscrepancy q v (Fin.tail w) -
          PeriodTorusHigherHomology.formalEdgeCrossProduct q
            (SingularMayerVietoris.formalSimplex v)
            (retainedFirstBoundary q (SingularMayerVietoris.formalSimplex w))) := by
  rw [prismDiscrepancy_succ, formalBoundary_firstFace_split_simplex, map_add, prismDiscrepancy]
  simp only [map_sub, map_add, map_neg]
  abel

theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_succ (q : ℕ) :
    canonicalPrismDiscrepancy (q + 1) =
      SingularMayerVietoris.formalCone ((0 : Fin 2), (0 : Fin (q + 2))) (q + 2)
        (-SingularMayerVietoris.formalSimplex (fun j : Fin (q + 2) => ((0 : Fin 2), j)) -
            SingularMayerVietoris.formalMap (Prod.map (fun i : Fin 2 => i) Fin.succ) (q + 2)
              (canonicalPrismDiscrepancy q) -
          ∑ i : Fin (q + 1),
            (-1 : ℤ) ^ (i.val + 1) •
              PeriodTorusHigherHomology.formalEdgeCrossProduct q
                (SingularMayerVietoris.formalSimplex (fun j : Fin 2 => j))
                (SingularMayerVietoris.formalSimplex i.succ.succAbove)) := by
  change prismDiscrepancy (q + 1) (fun i : Fin 2 => i) (fun j : Fin (q + 2) => j) = _
  rw [prismDiscrepancy_succ_retained, prismDiscrepancy_eq_map_canonical]
  simp only [retainedFirstBoundary_simplex, map_sum, map_smul,
    SingularMayerVietoris.formalMap_simplex, Function.comp_def]
  rfl

theorem FourthHurewicz.CubeSubdivision.canonicalPrismDiscrepancy_mem_badPrism (q : ℕ) :
    canonicalPrismDiscrepancy q ∈ badPrism q (q + 2) := by
  induction q with
  | zero =>
    rw [canonicalPrismDiscrepancy_zero]
    exact Submodule.zero_mem _
  | succ q ih =>
    rw [canonicalPrismDiscrepancy_succ]
    apply formalCone_mem_badPrism
    apply Submodule.sub_mem
    · apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact
          mem_badPrism_of_left_zero
            (SingularMayerVietoris.formalSimplex_mem_supported fun _ => rfl)
      · exact formalMap_succ_mem_badPrism ih
    · apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      exact
        formalEdgeCrossProduct_mem_badPrism_of_omit i.succ (Fin.succ_ne_zero i) _
          (SingularMayerVietoris.formalSimplex_mem_supported fun j => Fin.succAbove_ne i.succ j)

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_left_zero {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).1 = 0) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (FirstHurewicz.Simplex m) x := by
    ext s
    exact GenLoop.boundary p _ ⟨0, Or.inl (prismCubeSimplex_zero_of_left_zero e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_last_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ Fin.last (n + 2)) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  have hconst (e : Equiv.Perm (Fin (n + 2))) :
    p.val.comp (prismCubeSimplex e v) = ContinuousMap.const (FirstHurewicz.Simplex m) x := by
    ext s
    exact
      GenLoop.boundary p _
        ⟨(e (Fin.last (n + 1))).succ, Or.inl (prismCubeSimplex_zero_of_last_omitted e v hv s)⟩
  simp only [orientedPrismRealization_simplex, hconst]
  exact signed_sum_constant_eq_zero _

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_interior_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 1))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  rw [orientedPrismRealization_simplex]
  apply
    signed_sum_eq_zero_of_swap_invariant i.castSucc i.succ
      (by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega)
  intro e
  exact
    congrArg (fun f => FirstHurewicz.simplexChain X m (p.val.comp f))
      (prismCubeSimplex_swap_of_omitted e i v hv).symm

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_nonzero_omitted {X : Type}
    [TopologicalSpace X] {x : X} {m n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (i : Fin (n + 3))
    (hi : i ≠ 0) (v : Fin (m + 1) → Fin 2 × Fin (n + 3)) (hv : ∀ j, (v j).2 ≠ i) :
    orientedPrismRealization p.val m (SingularMayerVietoris.formalSimplex v) = 0 := by
  by_cases hlast : i = Fin.last (n + 2)
  · subst i
    exact orientedPrismRealization_last_omitted p v hv
  have hi0 : i.val ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  have hilast : i.val ≠ n + 2 := by
    intro h
    exact hlast (Fin.ext h)
  have hi_lt := i.isLt
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hj : j.succ.castSucc = i := by
    apply Fin.ext
    dsimp [j]
    omega
  apply orientedPrismRealization_interior_omitted p j v
  simpa only [hj] using hv

theorem FourthHurewicz.CubeSubdivision.badPrism_le_ker_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) (m : ℕ) :
    badPrism (n + 2) (m + 1) ≤ LinearMap.ker (orientedPrismRealization p.val m) :=
  badPrism_le_ker _ (fun v hv => orientedPrismRealization_left_zero p v hv)
    (fun i hi v hv => orientedPrismRealization_nonzero_omitted p i hi v hv)

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_canonicalPrismDiscrepancy
    {X : Type} [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3) (canonicalPrismDiscrepancy (n + 2)) = 0 :=
  badPrism_le_ker_orientedPrismRealization p (n + 3)
    (canonicalPrismDiscrepancy_mem_badPrism (n + 2))

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard {X : Type}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin (n + 3)) X x) :
    orientedPrismRealization p.val (n + 3)
        (PeriodTorusHigherHomology.formalEdgeCrossProduct (n + 2)
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin (n + 3) => j))) =
      orientedPrismRealization p.val (n + 3)
        (standardPrism (n + 2) (fun i : Fin 2 => i) (fun j : Fin (n + 3) => j)) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact orientedPrismRealization_canonicalPrismDiscrepancy p

private theorem FourthHurewicz.CubeSubdivision.linearMap_zsmul_apply_mo1973_8057 {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] (r : ℤ) (f : M →ₗ[ℤ] N) (a : M) :
    (r • f) a = r • f a :=
  map_zsmul (LinearMap.evalAddMonoidHom a) r f

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X))
    (m : ℕ) (c : SingularMayerVietoris.FormalChains (Fin 2 × Fin (n + 1)) (m + 1)) :
    orientedPrismRealization p m c =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m c := by
  classical
  have h :
    orientedPrismRealization p m =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • prismCubeRealization p e m := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [orientedPrismRealization_simplex, LinearMap.sum_apply,
      linearMap_zsmul_apply_mo1973_8057, prismCubeRealization_simplex]
  simpa only [LinearMap.sum_apply, linearMap_zsmul_apply_mo1973_8057] using
    LinearMap.congr_fun h c

def FourthHurewicz.CubeSubdivision.PermutationInsertion.insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e) * k.cycleRange

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_apply_self {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e k = 0 := by
  simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert]

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_apply_succAbove {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e (k.succAbove j) = (e j).succ :=
  by simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert]

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_zero {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm 0 = k := by
  apply (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_symm_apply_succ {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (j : Fin n) :
    (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).symm j.succ =
      k.succAbove (e.symm j) := by
  apply (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e).injective
  simp

@[simp]
theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sign_insert {n : ℕ} (k : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e) =
      (-1) ^ (k : ℕ) * Equiv.Perm.sign e := by
  simp [FourthHurewicz.CubeSubdivision.PermutationInsertion.insert, mul_comm]

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sign_insert_int {n : ℕ}
    (k : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e) : ℤ) =
      (-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ) := by simp

theorem FourthHurewicz.CubeSubdivision.lt_predAbove_iff_succAbove_lt {n : ℕ} (k : Fin (n + 1))
    (j : Fin n) (r : Fin (n + 2)) : j.val < (k.predAbove r).val ↔ (k.succAbove j).val < r.val := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

theorem FourthHurewicz.CubeSubdivision.prismCubeVertex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) (r : Fin (n + 2)) :
    prismCubeVertex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k r) =
      HigherHurewicz.CubeTriangulation.cubeVertex (PermutationInsertion.insert k e) r := by
  funext coord
  refine Fin.cases ?_ (fun j => ?_) coord
  · by_cases h : r ≤ k.castSucc
    · have h' : ¬k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_lt] using h
      simp [prismCubeVertex, shufflePrismVertices, h, HigherHurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
    · have h' : k.val < r.val := by
        simpa only [prismCubeVertex, Fin.le_def, Fin.val_castSucc, not_le] using h
      simp [prismCubeVertex, shufflePrismVertices, h, HigherHurewicz.CubeTriangulation.cubeVertex,
        h', SingularMayerVietoris.stdVertices]
  · simp only [shufflePrismVertices, prismCubeVertex_succ,
      HigherHurewicz.CubeTriangulation.cubeVertex, PermutationInsertion.insert_symm_apply_succ]
    simp only [lt_predAbove_iff_succAbove_lt]

theorem FourthHurewicz.CubeSubdivision.prismCubeSimplex_shuffle {n : ℕ} (e : Equiv.Perm (Fin n))
    (k : Fin (n + 1)) :
    prismCubeSimplex e (shufflePrismVertices (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j) k) =
      HigherHurewicz.CubeTriangulation.cubeSimplex (PermutationInsertion.insert k e) := by
  apply congrArg HigherHurewicz.CubeTriangulation.cubeAffineSimplex
  funext r
  exact prismCubeVertex_shuffle e k r

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_injective {n : ℕ} :
    Function.Injective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        FourthHurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  rintro ⟨k, e⟩ ⟨l, f⟩ h
  have hk : k = l := by simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ.symm 0) h
  subst l
  refine Prod.ext rfl ?_
  apply Equiv.ext
  intro j
  apply Fin.succ_injective n
  simpa using congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (k.succAbove j)) h

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.insert_bijective {n : ℕ} :
    Function.Bijective
      (fun p : Fin (n + 1) × Equiv.Perm (Fin n) =>
        FourthHurewicz.CubeSubdivision.PermutationInsertion.insert p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨insert_injective, by simp [Fintype.card_perm, Nat.factorial_succ]⟩

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_insert {n : ℕ} {A : Type*}
    [AddCommMonoid A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), f σ := by
  rw [← Fintype.sum_prod_type']
  exact insert_bijective.sum_comp f

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_sign_insert {n : ℕ} {A : Type*}
    [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          ((-1 : ℤ) ^ (k : ℕ) * (Equiv.Perm.sign e : ℤ)) •
            f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e)) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [sign_insert_int] using sum_insert (fun σ => (Equiv.Perm.sign σ : ℤ) • f σ)

theorem FourthHurewicz.CubeSubdivision.PermutationInsertion.sum_sign_smul_insert {n : ℕ}
    {A : Type*} [AddCommGroup A] (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ k : Fin (n + 1),
        ∑ e : Equiv.Perm (Fin n),
          (-1 : ℤ) ^ (k : ℕ) •
            ((Equiv.Perm.sign e : ℤ) •
              f (FourthHurewicz.CubeSubdivision.PermutationInsertion.insert k e))) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) • f σ := by
  simpa only [SemigroupAction.mul_smul] using sum_sign_insert f

theorem FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism {X : Type}
    [TopologicalSpace X] {n : ℕ} (p : C(HigherHurewicz.CubeTriangulation.CubeN (n + 1), X)) :
    orientedPrismRealization p (n + 1)
        (standardPrism n (fun i : Fin 2 => i) (fun j : Fin (n + 1) => j)) =
      ∑ perm : Equiv.Perm (Fin (n + 1)),
        HigherHurewicz.CubeTriangulation.cubeOrientation perm •
          FirstHurewicz.simplexChain X (n + 1)
            (p.comp (HigherHurewicz.CubeTriangulation.cubeSimplex perm)) := by
  simp only [standardPrism, map_sum, map_zsmul, orientedPrismRealization_simplex,
    prismCubeSimplex_shuffle, ← Finset.sum_zsmul,
    HigherHurewicz.CubeTriangulation.cubeOrientation]
  exact
    PermutationInsertion.sum_sign_smul_insert
      (fun perm =>
        FirstHurewicz.simplexChain X (n + 1)
          (p.comp (HigherHurewicz.CubeTriangulation.cubeSimplex perm)))

theorem FourthHurewicz.CubeSubdivision.cubeChain_eq_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      orientedPrismRealization p.val 4
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 3
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 4 => j))) := by
  rw [cubeChain_eq_sum_prisms, orientedPrismRealization_eq_sum]
  simp only [intervalTetrahedronChain_eq_prismCubeRealization,
    ThirdHurewicz.Geometry.cubeOrientation, HigherHurewicz.CubeTriangulation.cubeOrientation]

theorem FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    FourthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 4
            (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization, orientedPrismRealization_edge_eq_standard (n := 1) p,
    orientedPrismRealization_standardPrism]

def FourthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 4 X x → SingularMayerVietoris.SingularHomology X 4 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

def FourthHurewicz.hurewiczPi4 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 4 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 4)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 4 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 4)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 4) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

def FourthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 4 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 4
    where
  toFun := (hurewiczPi4 x).toAdditiveLeft
  map_add' := (hurewiczPi4 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi4 x).toAdditiveLeft ℤ ℤ n a

theorem FourthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 4) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 4 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (cubeCycle p) :=
  rfl

theorem FourthHurewicz.cubeChain_basedFourSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : cubeChain (basedFourSimplexLoop τ) = basedFourSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedFourSimplex_simplexChain_sum]

theorem FourthHurewicz.cubeCycle_basedFourSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) : cubeCycle (basedFourSimplexLoop τ) = basedFourSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedFourSimplexLoop τ

theorem FourthHurewicz.hurewicz_basedFourSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    hurewiczMap x (basedFourSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (basedFourSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (cubeCycle (basedFourSimplexLoop τ)) =
      _
  rw [cubeCycle_basedFourSimplexLoop]

theorem FourthHurewicz.hurewiczMap_comp_fourSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    (hurewiczMap x).comp (fourSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4).comp
        (normalizedFourSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 4
  intro smp
  simp only [LinearMap.comp_apply, fourSimplexClassOperator_simplex,
    normalizedFourSimplexCycleOperator_simplex]
  exact hurewicz_basedFourSimplexClass (normalizedFourSimplex x smp)

theorem FourthHurewicz.hurewiczMap_fourSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    hurewiczMap x (fourSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_fourSimplexClassOperator x) c.val
  change
    hurewiczMap x (fourSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4
        (normalizedFourSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedFourSimplexCycleOperator_class x c)

def HigherHurewicz.CubicalBoundary.cubeFacet (n : ℕ) (i : Fin (n + 1)) (ε : (unitInterval)) :
    C(Fin n → (unitInterval), Fin (n + 1) → (unitInterval))
    where
  toFun u := Fin.insertNth (α := fun _ => (unitInterval)) i ε u
  continuous_toFun := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_const : Continuous fun _ : Fin n → (unitInterval) => ε)
    · simpa only [Fin.insertNth_apply_succAbove] using
        (continuous_apply k : Continuous fun u : Fin n → (unitInterval) => u k)

@[simp]
theorem HigherHurewicz.CubicalBoundary.cubeFacet_apply_self (n : ℕ) (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) : cubeFacet n i ε u i = ε :=
  Fin.insertNth_apply_same (α := fun _ => (unitInterval)) i ε u

@[simp]
theorem HigherHurewicz.CubicalBoundary.cubeFacet_apply_succAbove (n : ℕ) (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (j : Fin n) :
    cubeFacet n i ε u (i.succAbove j) = u j :=
  Fin.insertNth_apply_succAbove (α := fun _ => (unitInterval)) i ε u j

def HigherHurewicz.SimplexGeometry.simplexTwoBoundary (n : ℕ) : Set (FirstHurewicz.Simplex n) :=
  {s | ∃ i j : Fin (n + 1), i ≠ j ∧ s i = 0 ∧ s j = 0}

theorem HigherHurewicz.SimplexGeometry.simplexFace_simplexBoundary (n : ℕ) (i : Fin (n + 2))
    (s : FirstHurewicz.Simplex n) (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    FirstHurewicz.simplexFace n i s ∈ simplexTwoBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := hs
  exact
    ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, FirstHurewicz.simplexFace_apply_self n i s,
      (FirstHurewicz.simplexFace_apply_succAbove n i s j).trans hj⟩

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_eq_zero_of_coordinate {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) (k : ℕ) (hik : i.val < k) :
    prefixMinimum u k = 0 :=
  le_antisymm (hi ▸ prefixMinimum_le_coordinate u k i hik) bot_le

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_last_eq_zero_of_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 0) :
    simplexQuotient n u (Fin.last n) = 0 := by
  rw [simplexQuotient_last, prefixMinimum_eq_zero_of_coordinate u i hi n i.isLt]
  rfl

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_one {n : ℕ}
    (u : Fin n → (unitInterval)) (i : Fin n) (hi : u i = 1) :
    simplexQuotient n u i.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_succ u i.val i.isLt]
  change
    (prefixMinimum u i.val : ℝ) - (Min.min (prefixMinimum u i.val) (u i) : (unitInterval)) = 0
  rw [hi, min_eq_left (show prefixMinimum u i.val ≤ 1 from (prefixMinimum u i.val).property.2)]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_castSucc_eq_zero_of_earlier_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (i j : Fin n) (hij : i < j) (hi : u i = 0) :
    simplexQuotient n u j.castSucc = 0 := by
  rw [simplexQuotient_castSucc, prefixMinimum_eq_zero_of_coordinate u i hi j.val hij,
    prefixMinimum_eq_zero_of_coordinate u i hi (j.val + 1)
      ((show i.val < j.val from hij).trans_le (Nat.le_succ j.val))]
  exact sub_self _

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_codimTwo {n : ℕ}
    (u : Fin n → (unitInterval))
    (hu : ∃ i j : Fin n, i ≠ j ∧ (u i = 0 ∨ u i = 1) ∧ (u j = 0 ∨ u j = 1)) :
    simplexQuotient n u ∈ simplexTwoBoundary n := by
  obtain ⟨i, j, hij, hi | hi, hj | hj⟩ := hu
  · rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact
        ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
          simplexQuotient_castSucc_eq_zero_of_earlier_zero u i j hij' hi,
          simplexQuotient_last_eq_zero_of_zero u i hi⟩
    · exact
        ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
          simplexQuotient_castSucc_eq_zero_of_earlier_zero u j i hji' hj,
          simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact
      ⟨j.castSucc, Fin.last n, Fin.castSucc_ne_last j,
        simplexQuotient_castSucc_eq_zero_of_one u j hj,
        simplexQuotient_last_eq_zero_of_zero u i hi⟩
  · exact
      ⟨i.castSucc, Fin.last n, Fin.castSucc_ne_last i,
        simplexQuotient_castSucc_eq_zero_of_one u i hi,
        simplexQuotient_last_eq_zero_of_zero u j hj⟩
  · exact
      ⟨i.castSucc, j.castSucc, fun h => hij (Fin.castSucc_injective n h),
        simplexQuotient_castSucc_eq_zero_of_one u i hi,
        simplexQuotient_castSucc_eq_zero_of_one u j hj⟩

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_bottom_not_last_twoBoundary (n : ℕ)
    (i : Fin (n + 1)) (hi : i ≠ Fin.last n) (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 0 u) ∈
      simplexTwoBoundary (n + 1) := by
  have hil : i < Fin.last n := lt_of_le_of_ne (Fin.le_last i) hi
  exact
    ⟨(Fin.last n).castSucc, Fin.last (n + 1), Fin.castSucc_ne_last _,
      simplexQuotient_castSucc_eq_zero_of_earlier_zero
        (HigherHurewicz.CubicalBoundary.cubeFacet n i 0 u) i (Fin.last n) hil
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n i 0 u),
      simplexQuotient_last_eq_zero_of_zero (HigherHurewicz.CubicalBoundary.cubeFacet n i 0 u) i
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n i 0 u)⟩

def HigherHurewicz.SimplexGeometry.BasedSimplexBoundary (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { τ : C(FirstHurewicz.Simplex n, X) // ∀ s ∈ simplexTwoBoundary n, τ s = x }

def HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 2)) : BasedSimplex n x :=
  ⟨τ.val.comp (FirstHurewicz.simplexFace n i), fun s hs =>
    τ.property _ (simplexFace_simplexBoundary n i s hs)⟩

def HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : C(FirstHurewicz.Simplex (n + 1), X))
    (h :
      ∀ i : Fin (n + 2),
        ∀ s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n,
          (τ.comp (FirstHurewicz.simplexFace n i)) s = x) :
    HigherHurewicz.SimplexGeometry.BasedSimplexBoundary (n + 1) x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n i ⟨s, hi⟩
    have ht : t ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (FirstHurewicz.simplexFace n i t) = x at he
    rw [show FirstHurewicz.simplexFace n i t = s from
        SecondHurewicz.SimplyConnected.simplexFace_inverse n i ⟨s, hi⟩] at he
    exact he⟩

abbrev FourthHurewicz.BasedFiveSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary 5 x

abbrev FourthHurewicz.basedFiveSimplexFace {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) (i : Fin 6) : BasedFourSimplex x :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace τ i

def FourthHurewicz.BasedFiveSimplex.ofFaces {X : Type*} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 5, X))
    (h :
      ∀ i : Fin 6,
        ∀ s ∈ FourthHurewicz.fourSimplexBoundary,
          (τ.comp (FirstHurewicz.simplexFace 4 i)) s = x) :
    FourthHurewicz.BasedFiveSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces τ h

def FourthHurewicz.normalizedFiveSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : BasedFiveSimplex x :=
  BasedFiveSimplex.ofFaces (normalizedFiveSimplexMap x smp)
    (normalizedFiveSimplexMap_face_boundary x smp)

@[simp]
theorem FourthHurewicz.normalizedFiveSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) (i : Fin 6) :
    basedFiveSimplexFace (normalizedFiveSimplex x smp) i =
      normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i)) := by
  apply Subtype.ext
  exact normalizedFiveSimplexMap_face x smp i

def HigherHurewicz.NativeSubdivision.nativeCubePair {N : Type*} (i j : N) :
    C(N → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun u := ![u i, u j]
  continuous_toFun := by
    apply continuous_pi
    intro k
    fin_cases k <;> exact continuous_apply _

def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap {N : Type*} [DecidableEq N]
    (i j : N) : C((unitInterval) × (N → (unitInterval)), N → (unitInterval))
    where
  toFun z
    k :=
    if k = i then
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 0
    else
      if k = j then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (z.1, nativeCubePair i j z.2) 1
      else z.2 k
  continuous_toFun := by
    apply continuous_pi
    intro k
    by_cases hi : k = i
    · simp only [if_pos hi]
      exact
        (continuous_apply (0 : Fin 2)).comp
          (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
            (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
    · by_cases hj : k = j
      · simp only [if_neg hi, if_pos hj]
        exact
          (continuous_apply (1 : Fin 2)).comp
            (SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap.continuous.comp
              (continuous_fst.prodMk ((nativeCubePair i j).continuous.comp continuous_snd)))
      · simp only [if_neg hi, if_neg hj]
        exact (continuous_apply k).comp continuous_snd

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_zero {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (0, u) = u := by
  funext k
  change
    (if k = i then
        SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 0
      else
        if k = j then
          SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap (0, nativeCubePair i j u) 1
        else u k) =
      u k
  simp only [SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_zero]
  change (if k = i then u i else if k = j then u j else u k) = u k
  split_ifs with hi hj <;> simp_all

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_one {N : Type*}
    [DecidableEq N] (i j : N) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnHomotopyMap i j (1, u) = fun k =>
      if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k := by
  funext k
  simp [nativeCubeQuarterTurnHomotopyMap, nativeCubePair]

theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopyMap_boundary {N : Type*}
    [DecidableEq N] (i j : N) (hij : i ≠ j) (t : (unitInterval)) (u : N → (unitInterval))
    (hu : u ∈ Cube.boundary N) : nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
  have hp (h : nativeCubePair i j u ∈ Cube.boundary (Fin 2)) :
    nativeCubeQuarterTurnHomotopyMap i j (t, u) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ :=
      SecondHurewicz.SimplyConnected.quarterTurnHomotopyMap_boundary t (nativeCubePair i j u) h
    fin_cases k
    · exact ⟨i, by simpa [nativeCubeQuarterTurnHomotopyMap] using hk⟩
    · exact ⟨j, by simpa [nativeCubeQuarterTurnHomotopyMap, hij.symm] using hk⟩
  obtain ⟨k, hk⟩ := hu
  by_cases hi : k = i
  · subst k
    exact hp ⟨0, by simpa [nativeCubePair] using hk⟩
  · by_cases hj : k = j
    · subst k
      exact hp ⟨1, by simpa [nativeCubePair] using hk⟩
    · exact ⟨k, by simpa [nativeCubeQuarterTurnHomotopyMap, hi, hj] using hk⟩

def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    GenLoop N X x :=
  ⟨⟨fun u => p (nativeCubeQuarterTurnHomotopyMap i j (1, u)),
      p.val.continuous.comp
        ((nativeCubeQuarterTurnHomotopyMap i j).continuous.comp
          (continuous_const.prodMk continuous_id))⟩,
    fun u hu => p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij 1 u hu)⟩

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_apply {N : Type*}
    [DecidableEq N] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) (u : N → (unitInterval)) :
    nativeCubeQuarterTurnLoop p i j hij u =
      p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) := by
  change p (nativeCubeQuarterTurnHomotopyMap i j (1, u)) = _
  rw [nativeCubeQuarterTurnHomotopyMap_one]

def HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnHomotopy {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    p.val.HomotopyRel (nativeCubeQuarterTurnLoop p i j hij).val (Cube.boundary N)
    where
  toFun z := p (nativeCubeQuarterTurnHomotopyMap i j z)
  continuous_toFun := p.val.continuous.comp (nativeCubeQuarterTurnHomotopyMap i j).continuous
  map_zero_left u := congrArg p (nativeCubeQuarterTurnHomotopyMap_zero i j u)
  map_one_left _ := rfl
  prop' t u
    hu :=
    (p.property _ (nativeCubeQuarterTurnHomotopyMap_boundary i j hij t u hu)).trans
      (p.property u hu).symm

abbrev HigherHurewicz.NativeSubdivision.NativeCube (N : Type*) :=
  N → (unitInterval)

def HigherHurewicz.NativeSubdivision.nativeClass {N X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop N X x) : Additive (HomotopyGroup N X x) :=
  Additive.ofMul (⟦p⟧ : HomotopyGroup N X x)

theorem HigherHurewicz.NativeSubdivision.nativeClass_homotopic {N X : Type*} [TopologicalSpace X]
    {x : X} {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) : nativeClass p = nativeClass q :=
  congrArg (fun a : HomotopyGroup N X x => Additive.ofMul a) (Quotient.sound h)

theorem HigherHurewicz.NativeSubdivision.nativeClass_transAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nontrivial N] (i : N) (p q : GenLoop N X x) :
    nativeClass (GenLoop.transAt i p q) = nativeClass p + nativeClass q :=
  congrArg Additive.ofMul
    ((HomotopyGroup.mul_spec (i := i) (p := q) (q := p)).symm.trans (mul_comm _ _))

theorem HigherHurewicz.NativeSubdivision.nativeClass_symmAt {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] (i : N) (p : GenLoop N X x) :
    nativeClass (GenLoop.symmAt i p) = -nativeClass p :=
  congrArg Additive.ofMul (HomotopyGroup.inv_spec (i := i) (p := p)).symm

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeClass_const {N X : Type*} [TopologicalSpace X]
    {x : X} [DecidableEq N] [Nonempty N] : nativeClass (GenLoop.const : GenLoop N X x) = 0 :=
  rfl

def HigherHurewicz.NativeSubdivision.NativeCubeInternalBased {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) : Prop :=
  ∀ u : NativeCube N, ∀ i j : N, i ≠ j → u i = u j → p u = x

inductive HigherHurewicz.NativeSubdivision.NativeCubeSameFlat {N : Type*} (a b : NativeCube N) :
    Prop
  | zero (i : N) (ha : a i = 0) (hb : b i = 0)
  | one (i : N) (ha : a i = 1) (hb : b i = 1)
  | equal (i j : N) (hij : i ≠ j) (ha : a i = a j) (hb : b i = b j)

def HigherHurewicz.NativeSubdivision.nativeCubeBlend {N : Type*} (t : (unitInterval))
    (a b : NativeCube N) : NativeCube N := fun i => Set.Icc.convexComb (a i) (b i) t

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeBlend_zero {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeBlend_one {N : Type*} (a b : NativeCube N) :
    nativeCubeBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def HigherHurewicz.NativeSubdivision.nativeCubeBlendMap {N : Type*}
    (f g : C(NativeCube N, NativeCube N)) : C((unitInterval) × NativeCube N, NativeCube N)
    where
  toFun u := nativeCubeBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk continuous_fst))

theorem HigherHurewicz.NativeSubdivision.nativeCubeBlend_based {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p) {a b : NativeCube N}
    (h : NativeCubeSameFlat a b) (t : (unitInterval)) : p (nativeCubeBlend t a b) = x := by
  cases h with
  | zero i ha hb => exact p.property _ ⟨i, Or.inl (by simp [nativeCubeBlend, ha, hb])⟩
  | one i ha hb => exact p.property _ ⟨i, Or.inr (by simp [nativeCubeBlend, ha, hb])⟩
  | equal i j hij ha hb => exact hp _ i j hij (by simp only [nativeCubeBlend, ha, hb])

def HigherHurewicz.NativeSubdivision.nativeCubePullbackLoop {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (f : C(NativeCube N, NativeCube N))
    (hf : ∀ u ∈ Cube.boundary N, p (f u) = x) : GenLoop N X x :=
  ⟨p.val.comp f, hf⟩

def HigherHurewicz.NativeSubdivision.nativeCubeLinearHomotopy {N X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (hp : NativeCubeInternalBased p)
    (f g : C(NativeCube N, NativeCube N)) (hf : ∀ u ∈ Cube.boundary N, p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary N, p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary N, NativeCubeSameFlat (f u) (g u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel (nativeCubePullbackLoop p g hg).val
      (Cube.boundary N)
    where
  toFun u := p (nativeCubeBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (nativeCubeBlendMap f g).continuous
  map_zero_left
    u := by
    change p (nativeCubeBlend 0 (f u) (g u)) = p (f u)
    rw [nativeCubeBlend_zero]
  map_one_left
    u := by
    change p (nativeCubeBlend 1 (f u) (g u)) = p (g u)
    rw [nativeCubeBlend_one]
  prop' t u hu := (nativeCubeBlend_based p hp (hfg u hu) t).trans (hf u hu).symm

def HigherHurewicz.NativeSubdivision.permuteCubeCoordinates {N : Type*} (e : Equiv.Perm N) :
    C(N → (unitInterval), N → (unitInterval))
    where
  toFun u i := u (e i)
  continuous_toFun := by fun_prop

theorem HigherHurewicz.NativeSubdivision.permuteCubeCoordinates_boundary {N : Type*}
    (e : Equiv.Perm N) (u : N → (unitInterval)) (hu : u ∈ Cube.boundary N) :
    permuteCubeCoordinates e u ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨e.symm i, by simpa [permuteCubeCoordinates] using hi⟩

def HigherHurewicz.NativeSubdivision.permuteCubeLoop {N : Type*} {X : Type*} [TopologicalSpace X]
    {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) : GenLoop N X x :=
  ⟨p.val.comp (permuteCubeCoordinates e), fun u hu =>
    p.property _ (permuteCubeCoordinates_boundary e u hu)⟩

@[simp]
theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e : Equiv.Perm N) (u : N → (unitInterval)) :
    permuteCubeLoop p e u = p (fun i => u (e i)) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_one {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) : permuteCubeLoop p 1 = p := by
  apply GenLoop.ext
  intro u
  rfl

theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_mul {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (e f : Equiv.Perm N) :
    permuteCubeLoop p (e * f) = permuteCubeLoop (permuteCubeLoop p f) e := by
  apply GenLoop.ext
  intro u
  rfl

theorem HigherHurewicz.NativeSubdivision.nativeCubeQuarterTurnLoop_eq_symmAt_permute {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N)
    (hij : i ≠ j) :
    nativeCubeQuarterTurnLoop p i j hij = GenLoop.symmAt i (permuteCubeLoop p (Equiv.swap i j)) :=
  by
  apply GenLoop.ext
  intro u
  rw [nativeCubeQuarterTurnLoop_apply]
  change
    p (fun k => if k = i then u j else if k = j then (unitInterval.symm) (u i) else u k) =
      p
        (fun k =>
          if Equiv.swap i j k = i then (unitInterval.symm) (u i) else u (Equiv.swap i j k))
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [hij.symm]
  · by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj]

theorem HigherHurewicz.NativeSubdivision.nativeClass_quarterTurn {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i j : N) (hij : i ≠ j) :
    nativeClass (nativeCubeQuarterTurnLoop p i j hij) = nativeClass p :=
  (nativeClass_homotopic ⟨nativeCubeQuarterTurnHomotopy p i j hij⟩).symm

theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass {N : Type*}
    {X : Type*} [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] (p : GenLoop N X x)
    (i j : N) (hij : i ≠ j) : nativeClass (permuteCubeLoop p (Equiv.swap i j)) = -nativeClass p :=
  by
  have h := nativeClass_quarterTurn p i j hij
  rw [nativeCubeQuarterTurnLoop_eq_symmAt_permute, nativeClass_symmAt] at h
  simpa only [neg_neg] using congrArg Neg.neg h

theorem HigherHurewicz.NativeSubdivision.permuteCubeLoop_additiveClass {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] [Nontrivial N] [Fintype N] (p : GenLoop N X x)
    (e : Equiv.Perm N) :
    nativeClass (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [permuteCubeLoop_mul, permuteCubeLoop_swap_additiveClass _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

def HigherHurewicz.CubicalBoundary.BasedCubicalCell (n : ℕ) {X : Type*} [TopologicalSpace X]
    (x : X) :=
  { F : C(Fin n → (unitInterval), X) //
    ∀ u i j, i ≠ j → (u i = 0 ∨ u i = 1) → (u j = 0 ∨ u j = 1) → F u = x }

def HigherHurewicz.CubicalBoundary.cubicalFace {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
    (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) :
    GenLoop (Fin n) X x :=
  ⟨F.val.comp (cubeFacet n i ε), fun u ⟨j, hj⟩ =>
    by
    apply F.property _ i (i.succAbove j) (Fin.ne_succAbove i j)
    · simpa only [cubeFacet_apply_self] using hε
    · simpa only [cubeFacet_apply_succAbove] using hj⟩

@[simp]
theorem HigherHurewicz.CubicalBoundary.cubicalFace_apply {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin n → (unitInterval)) :
    cubicalFace F i ε hε u = F.val (cubeFacet n i ε u) :=
  rfl

abbrev HigherHurewicz.CubicalBoundary.cubicalLowerFace {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 0 (Or.inl rfl)

abbrev HigherHurewicz.CubicalBoundary.cubicalUpperFace {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (F : BasedCubicalCell (n + 1) x) (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 1 (Or.inr rfl)

structure HigherHurewicz.CubicalBoundary.CubicalEvaluator {X : Type*} [TopologicalSpace X] (n : ℕ)
    (x : X) (A : Type*) [AddCommGroup A] where
  evaluate : GenLoop (Fin n) X x → A
  map_const : evaluate GenLoop.const = 0
  map_homotopic : ∀ {p q}, GenLoop.Homotopic p q → evaluate p = evaluate q
  map_transAt : ∀ i p q, evaluate (GenLoop.transAt i p q) = evaluate p + evaluate q
  map_symmAt : ∀ i p, evaluate (GenLoop.symmAt i p) = -evaluate p
  map_swap :
    ∀ p i j,
      i ≠ j →
        evaluate (HigherHurewicz.NativeSubdivision.permuteCubeLoop p (Equiv.swap i j)) =
          -evaluate p

instance HigherHurewicz.CubicalBoundary.instCoeFun1 {X : Type*} [TopologicalSpace X] {n : ℕ}
    {x : X} {A : Type*} [AddCommGroup A] :
    CoeFun (CubicalEvaluator n x A) (fun _ => GenLoop (Fin n) X x → A) :=
  ⟨CubicalEvaluator.evaluate⟩

theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_permutation {X : Type*}
    [TopologicalSpace X] {n : ℕ} {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator n x A) (p : GenLoop (Fin n) X x)
    (e : Equiv.Perm (Fin n)) :
    E (HigherHurewicz.NativeSubdivision.permuteCubeLoop p e) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • E p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij
    ih =>
    rw [HigherHurewicz.NativeSubdivision.permuteCubeLoop_mul, E.map_swap _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_finRotate {X : Type*}
    [TopologicalSpace X] {n : ℕ} {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator n x A) (p : GenLoop (Fin n) X x) :
    E (HigherHurewicz.NativeSubdivision.permuteCubeLoop p (finRotate n)) =
      (-1 : ℤ) ^ (n - 1) • E p := by
  rw [E.map_permutation, sign_finRotate]
  simp

def HigherHurewicz.CubicalBoundary.cubicalBoundaryValue {X : Type*} [TopologicalSpace X] {n : ℕ}
    {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator n x A)
    (F : BasedCubicalCell (n + 1) x) : A :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • (E (cubicalUpperFace F i) - E (cubicalLowerFace F i))

def HigherHurewicz.CubicalBoundary.nativeCubicalEvaluator {X : Type*} [TopologicalSpace X] (n : ℕ)
    (x : X) : CubicalEvaluator (n + 2) x (Additive (π_ (n + 2) X x))
    where
  evaluate := HigherHurewicz.NativeSubdivision.nativeClass
  map_const := HigherHurewicz.NativeSubdivision.nativeClass_const
  map_homotopic := HigherHurewicz.NativeSubdivision.nativeClass_homotopic
  map_transAt := HigherHurewicz.NativeSubdivision.nativeClass_transAt
  map_symmAt := HigherHurewicz.NativeSubdivision.nativeClass_symmAt
  map_swap := HigherHurewicz.NativeSubdivision.permuteCubeLoop_swap_additiveClass

private theorem HigherHurewicz.SimplexGeometry.succAbove_lt_prefix_iff_mo1973_8180 {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : k ≤ i.val) : (i.succAbove j).val < k ↔ j.val < k :=
  by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    rfl
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_succ]
    omega

private theorem HigherHurewicz.SimplexGeometry.succAbove_lt_prefix_succ_iff_mo1973_8181 {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) (k : ℕ) (h : i.val ≤ k) :
    (i.succAbove j).val < k + 1 ↔ j.val < k := by
  by_cases hji : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt i j hji]
    simp only [Fin.lt_def, Fin.val_castSucc] at hji
    simp only [Fin.val_castSucc]
    omega
  · rw [Fin.succAbove_of_le_castSucc i j (le_of_not_gt hji)]
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right]

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_le {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i ε u) k = prefixMinimum u k := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_iff_mo1973_8180 i _ k h, not_lt_of_ge h, false_implies, true_and]

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_succ {n : ℕ} (i : Fin (n + 1))
    (ε : (unitInterval)) (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i ε u) (k + 1) = Min.min ε (prefixMinimum u k) := by
  apply eq_of_forall_le_iff
  intro a
  simp only [prefixMinimum, Finset.le_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    le_min_iff]
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    succAbove_lt_prefix_succ_iff_mo1973_8181 i _ k h, Nat.lt_succ_of_le h, true_implies]

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : k ≤ i.val) :
    prefixMinimum (Fin.insertNth i 1 u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le i 1 u k h

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_one_succ {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (h : i.val ≤ k) :
    prefixMinimum (Fin.insertNth i 1 u) (k + 1) = prefixMinimum u k := by
  rw [prefixMinimum_insertNth_succ i 1 u k h]
  exact min_eq_right (show prefixMinimum u k ≤ (⊤ : (unitInterval)) from le_top)

theorem HigherHurewicz.SimplexGeometry.prefixMinimum_insertNth_last_le {n : ℕ}
    (u : Fin n → (unitInterval)) (ε : (unitInterval)) (k : ℕ) (hk : k ≤ n) :
    prefixMinimum (Fin.insertNth (Fin.last n) ε u) k = prefixMinimum u k :=
  prefixMinimum_insertNth_le (Fin.last n) ε u k hk

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_cubeFacet_one_le {n : ℕ} (i : Fin (n + 1))
    (u : Fin n → (unitInterval)) (k : ℕ) (hk : k ≤ i.val) :
    extendedMinimum (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) k = extendedMinimum u k := by
  have hkn : k ≤ n := hk.trans (Nat.le_of_lt_succ i.isLt)
  rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)), extendedMinimum_of_le u k hkn]
  exact prefixMinimum_insertNth_one_le i u k hk

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_cubeFacet_one_succ {n : ℕ}
    (i : Fin (n + 1)) (u : Fin n → (unitInterval)) (k : ℕ) (hk : i.val ≤ k) :
    extendedMinimum (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) (k + 1) =
      extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ (k + 1) (Nat.succ_le_succ hkn), extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_one_succ i u k hk
  · simp only [extendedMinimum, if_neg hkn,
      if_neg (show ¬k + 1 ≤ n + 1 from fun h => hkn (Nat.succ_le_succ_iff.mp h))]

theorem HigherHurewicz.SimplexGeometry.extendedMinimum_cubeFacet_last_zero {n : ℕ}
    (u : Fin n → (unitInterval)) (k : ℕ) :
    extendedMinimum (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) k =
      extendedMinimum u k := by
  by_cases hkn : k ≤ n
  · rw [extendedMinimum_of_le _ k (hkn.trans (Nat.le_succ n)), extendedMinimum_of_le u k hkn]
    exact prefixMinimum_insertNth_last_le u 0 k hkn
  · by_cases hks : k ≤ n + 1
    · have hk : k = n + 1 := by omega
      subst k
      rw [extendedMinimum_of_le _ (n + 1) le_rfl, extendedMinimum_last_succ]
      change prefixMinimum (Fin.insertNth (Fin.last n) 0 u) (n + 1) = 0
      rw [prefixMinimum_insertNth_succ (Fin.last n) 0 u n le_rfl]
      exact min_eq_left (show (0 : (unitInterval)) ≤ prefixMinimum u n from bot_le)
    · simp only [extendedMinimum, if_neg hkn, if_neg hks]

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeFacet_one_apply (n : ℕ)
    (i : Fin (n + 1)) (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) =
      FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u) k =
      FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u) k
  refine Fin.succAboveCases i.castSucc ?_ (fun j => ?_) k
  · rw [FirstHurewicz.simplexFace_apply_self]
    exact
      simplexQuotient_castSucc_eq_zero_of_one _ i
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n i 1 u)
  · rw [FirstHurewicz.simplexFace_apply_succAbove]
    by_cases hji : j < i
    · rw [Fin.succAbove_of_castSucc_lt i.castSucc j (show j.castSucc < i.castSucc from hji)]
      simp only [simplexQuotient_apply, Fin.val_castSucc]
      rw [extendedMinimum_cubeFacet_one_le i u j.val (le_of_lt hji),
        extendedMinimum_cubeFacet_one_le i u (j.val + 1) (Nat.succ_le_of_lt hji)]
    · rw [Fin.succAbove_of_le_castSucc i.castSucc j
          (show i.castSucc ≤ j.castSucc from le_of_not_gt hji)]
      simp only [simplexQuotient_apply, Fin.val_succ]
      rw [extendedMinimum_cubeFacet_one_succ i u j.val (le_of_not_gt hji),
        extendedMinimum_cubeFacet_one_succ i u (j.val + 1)
          ((show i.val ≤ j.val from le_of_not_gt hji).trans (Nat.le_succ j.val))]

theorem HigherHurewicz.SimplexGeometry.simplexQuotient_cubeFacet_last_zero_apply (n : ℕ)
    (u : Fin n → (unitInterval)) :
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) =
      FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) := by
  apply Subtype.ext
  funext k
  change
    simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u) k =
      FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u) k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [FirstHurewicz.simplexFace_apply_self]
    exact
      simplexQuotient_last_eq_zero_of_zero _ (Fin.last n)
        (HigherHurewicz.CubicalBoundary.cubeFacet_apply_self n (Fin.last n) 0 u)
  · rw [show j.castSucc = (Fin.last (n + 1)).succAbove j by simp,
      FirstHurewicz.simplexFace_apply_succAbove]
    simp only [Fin.succAbove_last, simplexQuotient_apply, Fin.val_castSucc,
      extendedMinimum_cubeFacet_last_zero]

def HigherHurewicz.SimplexGeometry.simplexBoundaryCube {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (τ : BasedSimplexBoundary n x) :
    HigherHurewicz.CubicalBoundary.BasedCubicalCell n x :=
  ⟨τ.val.comp (simplexQuotient n), fun u i j hij hi hj =>
    τ.property _ (simplexQuotient_codimTwo u ⟨i, j, hij, hi, hj⟩)⟩

theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_upper {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 1)) :
    HigherHurewicz.CubicalBoundary.cubicalUpperFace (simplexBoundaryCube τ) i =
      basedSimplexLoop (basedSimplexBoundaryFace τ i.castSucc) := by
  apply GenLoop.ext
  intro u
  change
    τ.val (simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n i 1 u)) =
      τ.val (FirstHurewicz.simplexFace n i.castSucc (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_one_apply]

theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_lower_last {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) :
    HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) (Fin.last n) =
      basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1))) := by
  apply GenLoop.ext
  intro u
  change
    τ.val
        (simplexQuotient (n + 1) (HigherHurewicz.CubicalBoundary.cubeFacet n (Fin.last n) 0 u)) =
      τ.val (FirstHurewicz.simplexFace n (Fin.last (n + 1)) (simplexQuotient n u))
  rw [simplexQuotient_cubeFacet_last_zero_apply]

theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_lower_constant {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact τ.property _ (simplexQuotient_bottom_not_last_twoBoundary n i hi u)

theorem HigherHurewicz.SimplexGeometry.simplexBoundaryCube_boundaryValue {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] {n : ℕ}
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator n x A)
    (τ : BasedSimplexBoundary (n + 1) x) :
    HigherHurewicz.CubicalBoundary.cubicalBoundaryValue E (simplexBoundaryCube τ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • E (basedSimplexLoop (basedSimplexBoundaryFace τ i)) :=
  by
  have hzero (i : Fin n) :
    E (HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i.castSucc) = 0 := by
    rw [simplexBoundaryCube_lower_constant τ i.castSucc (Fin.castSucc_ne_last i)]
    exact E.map_const
  have hlower :
    (∑ i : Fin (n + 1),
        (-1 : ℤ) ^ i.val •
          E (HigherHurewicz.CubicalBoundary.cubicalLowerFace (simplexBoundaryCube τ) i)) =
      (-1 : ℤ) ^ n • E (basedSimplexLoop (basedSimplexBoundaryFace τ (Fin.last (n + 1)))) := by
    rw [Fin.sum_univ_castSucc]
    simp only [hzero, smul_zero, Finset.sum_const_zero, zero_add, Fin.val_last,
      simplexBoundaryCube_lower_last]
  unfold HigherHurewicz.CubicalBoundary.cubicalBoundaryValue
  simp_rw [simplexBoundaryCube_upper, smul_sub]
  rw [Finset.sum_sub_distrib, hlower]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, pow_succ', neg_mul, one_mul, neg_smul,
    sub_eq_add_neg]

def HigherHurewicz.CubicalBoundary.whiskerStartTrack :
    Path ((0 : (unitInterval)), (0 : (unitInterval))) ((0 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (0, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def HigherHurewicz.CubicalBoundary.whiskerMiddleTrack :
    Path ((0 : (unitInterval)), (1 : (unitInterval))) ((1 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (s, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def HigherHurewicz.CubicalBoundary.whiskerFinishTrack :
    Path ((1 : (unitInterval)), (0 : (unitInterval))) ((1 : (unitInterval)), (1 : (unitInterval)))
    where
  toFun s := (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

def HigherHurewicz.CubicalBoundary.whiskerTrack :
    Path ((0 : (unitInterval)), (0 : (unitInterval)))
      ((1 : (unitInterval)), (0 : (unitInterval))) :=
  whiskerStartTrack.trans (whiskerMiddleTrack.trans whiskerFinishTrack.symm)

theorem HigherHurewicz.CubicalBoundary.whiskerTrack_boundary (s : (unitInterval)) :
    ((whiskerTrack s).1 = 0 ∨ (whiskerTrack s).1 = 1) ∨ (whiskerTrack s).2 = 1 := by
  unfold whiskerTrack
  rw [Path.trans_apply]
  split_ifs
  · exact Or.inl (Or.inl rfl)
  · rw [Path.trans_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Or.inr rfl)

def HigherHurewicz.CubicalBoundary.whiskerMap (n : ℕ) :
    C((Fin (n + 1) → (unitInterval)) × (unitInterval), Fin (n + 2) → (unitInterval))
    where
  toFun
    z :=
    Fin.cons (whiskerTrack z.2).1
      (Fin.snoc (Fin.init z.1) ((whiskerTrack z.2).2 * z.1 (Fin.last n)))
  continuous_toFun := by
    apply Continuous.finCons
    · exact (whiskerTrack.continuous.comp continuous_snd).fst
    · apply Continuous.finSnoc
      · apply continuous_pi
        intro i
        exact (continuous_apply i.castSucc).comp continuous_fst
      · apply Continuous.subtype_mk
        exact
          (continuous_subtype_val.comp (whiskerTrack.continuous.comp continuous_snd).snd).mul
            (continuous_subtype_val.comp ((continuous_apply (Fin.last n)).comp continuous_fst))

@[simp]
theorem HigherHurewicz.CubicalBoundary.whiskerMap_apply (n : ℕ) (u : Fin (n + 1) → (unitInterval))
    (s : (unitInterval)) :
    whiskerMap n (u, s) =
      Fin.cons (whiskerTrack s).1 (Fin.snoc (Fin.init u) ((whiskerTrack s).2 * u (Fin.last n))) :=
  rfl

@[simp]
theorem HigherHurewicz.CubicalBoundary.whiskerMap_first (n : ℕ) (u : Fin (n + 1) → (unitInterval))
    (s : (unitInterval)) : whiskerMap n (u, s) 0 = (whiskerTrack s).1 := by simp

@[simp]
theorem HigherHurewicz.CubicalBoundary.whiskerMap_middle (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i : Fin n) :
    whiskerMap n (u, s) i.castSucc.succ = u i.castSucc := by simp [Fin.init]

@[simp]
theorem HigherHurewicz.CubicalBoundary.whiskerMap_start (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) :
    whiskerMap n (u, 0) = Fin.cons 0 (Fin.snoc (Fin.init u) 0) := by simp

@[simp]
theorem HigherHurewicz.CubicalBoundary.whiskerMap_finish (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) :
    whiskerMap n (u, 1) = Fin.cons 1 (Fin.snoc (Fin.init u) 0) := by simp

theorem HigherHurewicz.CubicalBoundary.whiskerMap_last_zero (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (hu : u (Fin.last n) = 0) :
    whiskerMap n (u, s) (Fin.last n).succ = 0 := by simp [hu]

theorem HigherHurewicz.CubicalBoundary.whiskerCorner_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (v : Fin n → (unitInterval)) : F.val (Fin.cons ε (Fin.snoc v 0)) = x := by
  apply F.property _ 0 (Fin.last n).succ (by simp)
  · simpa only [Fin.cons_zero] using hε
  · exact Or.inl (by simp)

theorem HigherHurewicz.CubicalBoundary.whiskerMap_based_of_two_prefix {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i j : Fin n) (hij : i ≠ j)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1) (hj : u j.castSucc = 0 ∨ u j.castSucc = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  apply F.property _ i.castSucc.succ j.castSucc.succ (by simpa using hij)
  · simpa only [whiskerMap_middle] using hi
  · simpa only [whiskerMap_middle] using hj

theorem HigherHurewicz.CubicalBoundary.whiskerMap_based_of_prefix_last {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i : Fin n)
    (hi : u i.castSucc = 0 ∨ u i.castSucc = 1) (hz : u (Fin.last n) = 0 ∨ u (Fin.last n) = 1) :
    F.val (whiskerMap n (u, s)) = x := by
  rcases hz with hz | hz
  · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
    · simpa only [whiskerMap_middle] using hi
    · exact Or.inl (whiskerMap_last_zero n u s hz)
  · rcases whiskerTrack_boundary s with ht | hr
    · apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
      · simpa only [whiskerMap_first] using ht
      · simpa only [whiskerMap_middle] using hi
    · apply F.property _ i.castSucc.succ (Fin.last n).succ (by simp)
      · simpa only [whiskerMap_middle] using hi
      · exact Or.inr (by simp [hr, hz])

theorem HigherHurewicz.CubicalBoundary.whiskerMap_codimTwo_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) (i j : Fin (n + 1)) (hij : i ≠ j)
    (hi : u i = 0 ∨ u i = 1) (hj : u j = 0 ∨ u j = 1) : F.val (whiskerMap n (u, s)) = x := by
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j => exact whiskerMap_based_of_prefix_last F u s j hj hi
  | cast i =>
    cases j using Fin.lastCases with
    | last => exact whiskerMap_based_of_prefix_last F u s i hi hj
    | cast j => exact whiskerMap_based_of_two_prefix F u s i j (by simpa using hij) hi hj

theorem HigherHurewicz.CubicalBoundary.cubeFacet_succ_cons (n : ℕ) (i : Fin (n + 1))
    (ε s : (unitInterval)) (u : Fin n → (unitInterval)) :
    cubeFacet (n + 1) i.succ ε (Fin.cons s u) = Fin.cons s (cubeFacet n i ε u) :=
  Fin.insertNth_succ_cons i ε s u

theorem HigherHurewicz.CubicalBoundary.whiskerFacetNormal_arm_based {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1))
    (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) (h : i ≠ Fin.last n ∨ ε = 0)
    (u : Fin n → (unitInterval)) (a : (unitInterval)) (ha : a = 0 ∨ a = 1) (r : (unitInterval)) :
    F.val
        (Fin.cons a
          (Fin.snoc (Fin.init (cubeFacet n i ε u)) (r * cubeFacet n i ε u (Fin.last n)))) =
      x := by
  cases i using Fin.lastCases with
  | last =>
    have hzero : ε = 0 := h.resolve_left (not_not_intro rfl)
    subst ε
    apply F.property _ 0 (Fin.last n).succ (by simp)
    · simpa only [Fin.cons_zero] using ha
    · exact Or.inl (by simp)
  | cast i =>
    apply F.property _ 0 i.castSucc.succ (Fin.succ_ne_zero i.castSucc).symm
    · simpa only [Fin.cons_zero] using ha
    · simpa [Fin.init] using hε

def HigherHurewicz.CubicalBoundary.whiskeredLoop {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (F : BasedCubicalCell (n + 2) x) (u : Fin (n + 1) → (unitInterval)) : GenLoop (Fin 1) X x :=
  ⟨⟨fun q => F.val (whiskerMap n (u, q 0)), by fun_prop⟩,
    by
    intro q hq
    obtain ⟨i, hi⟩ := hq
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    rcases hi with hi | hi
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_start]
      exact whiskerCorner_based F 0 (Or.inl rfl) (Fin.init u)
    · change F.val (whiskerMap n (u, q 0)) = x
      rw [hi, whiskerMap_finish]
      exact whiskerCorner_based F 1 (Or.inr rfl) (Fin.init u)⟩

def HigherHurewicz.CubicalBoundary.whiskeredLoopMap {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X} (F : BasedCubicalCell (n + 2) x) :
    C(Fin (n + 1) → (unitInterval), GenLoop (Fin 1) X x)
    where
  toFun := whiskeredLoop F
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    change
      Continuous
        (fun z : (Fin (n + 1) → (unitInterval)) × (Fin 1 → (unitInterval)) =>
          F.val (whiskerMap n (z.1, z.2 0)))
    exact F.val.continuous.comp ((whiskerMap n).continuous.comp (by fun_prop))

def HigherHurewicz.CubicalBoundary.whiskeredCell {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
    (F : BasedCubicalCell (n + 2) x) :
    BasedCubicalCell (n + 1) (GenLoop.const : GenLoop (Fin 1) X x) :=
  ⟨whiskeredLoopMap F, by
    intro u i j hij hi hj
    apply GenLoop.ext
    intro q
    exact whiskerMap_codimTwo_based F u (q 0) i j hij hi hj⟩

@[simp]
theorem HigherHurewicz.CubicalBoundary.whiskeredCell_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) (q : Fin 1 → (unitInterval)) :
    (whiskeredCell F).val u q = F.val (whiskerMap n (u, q 0)) :=
  rfl

theorem HigherHurewicz.CubicalBoundary.whiskerTrack_concat (s : (unitInterval)) :
    whiskerTrack s =
      if (s : ℝ) ≤ 1 / 2 then (0, Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), 1)
        else (1, (unitInterval.symm) (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1))) :=
  rfl

theorem HigherHurewicz.CubicalBoundary.whiskerMap_concat (n : ℕ)
    (u : Fin (n + 1) → (unitInterval)) (s : (unitInterval)) :
    whiskerMap n (u, s) =
      if (s : ℝ) ≤ 1 / 2 then
        Fin.cons 0
          (Fin.snoc (Fin.init u) (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ)) * u (Fin.last n)))
      else
        let t := Set.projIcc 0 1 zero_le_one (2 * (s : ℝ) - 1)
        if (t : ℝ) ≤ 1 / 2 then Fin.cons (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) u
        else
          Fin.cons 1
            (Fin.snoc (Fin.init u)
              ((unitInterval.symm) (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) *
                u (Fin.last n))) := by
  rw [whiskerMap_apply, whiskerTrack_concat]
  dsimp only
  split_ifs
  · rfl
  · simp only [one_mul, Fin.snoc_init_self]
  · rfl

def HigherHurewicz.CubicalBoundary.uncurryLoop {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) : GenLoop (Fin (n + 1)) X x :=
  ⟨⟨fun u => p (fun i => u i.succ) (fun _ => u 0), by fun_prop⟩,
    by
    intro u hu
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero => exact GenLoop.boundary (p (fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
      change p (fun i => u i.succ) (fun _ => u 0) = x
      rw [GenLoop.boundary p _ ⟨j, hi⟩]
      rfl⟩

@[simp]
theorem HigherHurewicz.CubicalBoundary.uncurryLoop_apply {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const)
    (u : Fin (n + 1) → (unitInterval)) : uncurryLoop p u = p (fun i => u i.succ) (fun _ => u 0) :=
  rfl

@[simp]
theorem HigherHurewicz.CubicalBoundary.uncurryLoop_const {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} :
    uncurryLoop (GenLoop.const : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) =
      (GenLoop.const : GenLoop (Fin (n + 1)) X x) := by
  apply GenLoop.ext
  intro u
  rfl

def HigherHurewicz.CubicalBoundary.uncurryLoopHomotopy {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (uncurryLoop p).val.HomotopyRel (uncurryLoop q).val (Cube.boundary (Fin (n + 1)))
    where
  toFun z := H (z.1, fun i => z.2 i.succ) (fun _ => z.2 0)
  continuous_toFun := by fun_prop
  map_zero_left
    u := by
    change H (0, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left
    u := by
    change H (1, fun i => u i.succ) (fun _ => u 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  prop' t u
    hu := by
    change H (t, fun i => u i.succ) (fun _ => u 0) = uncurryLoop p u
    rw [GenLoop.boundary (uncurryLoop p) u hu]
    obtain ⟨i, hi⟩ := hu
    cases i using Fin.cases with
    | zero => exact GenLoop.boundary (H (t, fun i => u i.succ)) (fun _ => u 0) ⟨0, hi⟩
    | succ j =>
      rw [H.eq_fst t ⟨j, hi⟩]
      change p (fun i => u i.succ) (fun _ => u 0) = x
      rw [GenLoop.boundary p _ ⟨j, hi⟩]
      rfl

theorem HigherHurewicz.CubicalBoundary.uncurryLoop_homotopic {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} {p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (uncurryLoop p) (uncurryLoop q) := by
  obtain ⟨H⟩ := h
  exact ⟨uncurryLoopHomotopy H⟩

theorem HigherHurewicz.CubicalBoundary.whiskeredCell_face_normal {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1))
    (ε : (unitInterval)) (hε : ε = 0 ∨ ε = 1) (h : i ≠ Fin.last n ∨ ε = 0) :
    uncurryLoop (cubicalFace (whiskeredCell F) i ε hε) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) := by
  apply GenLoop.ext
  intro u
  have hcons (s : (unitInterval)) : Function.update u 0 s = Fin.cons s (fun j => u j.succ) := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simp
  change
    F.val (whiskerMap n (cubeFacet n i ε (fun j => u j.succ), u 0)) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) u
  rw [whiskerMap_concat]
  simp only [GenLoop.transAt, GenLoop.coe_copy, GenLoop.const_apply, Function.update_self,
    Function.update_idem]
  split_ifs with hs ht
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 0 (Or.inl rfl) _
  · rw [cubicalFace_apply, hcons, cubeFacet_succ_cons]
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 1 (Or.inr rfl) _

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_rotate_coordinates {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) :
    (fun i => u (finRotate (n + 1) i)) = Fin.snoc (Fin.tail u) (u 0) := by
  simpa only [Fin.cons_self_tail] using (Fin.snoc_eq_cons_rotate (Fin.tail u) (u 0)).symm

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_zero_coordinates {n : ℕ} (ε : (unitInterval))
    (u : Fin (n + 1) → (unitInterval)) : cubeFacet (n + 1) 0 ε u = Fin.cons ε u :=
  Fin.insertNth_zero' ε u

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_last_coordinates {n : ℕ} (ε : (unitInterval))
    (u : Fin n → (unitInterval)) : cubeFacet n (Fin.last n) ε u = Fin.snoc u ε :=
  Fin.insertNth_last' ε u

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_rotated_face_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → (unitInterval)) :
    HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalFace F 0 ε hε) (finRotate (n + 1))
        u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) (u 0))) := by
  rw [HigherHurewicz.NativeSubdivision.permuteCubeLoop_apply, cubicalFace_apply,
    whiskerFacet_zero_coordinates, whiskerFacet_rotate_coordinates]

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_last_upper_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) :
    cubicalUpperFace F (Fin.last (n + 1)) u = F.val (Fin.cons (u 0) (Fin.snoc (Fin.tail u) 1)) := by
  rw [cubicalFace_apply, whiskerFacet_last_coordinates, Fin.cons_snoc_eq_snoc_cons,
    Fin.cons_self_tail]

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_symmAt_zero_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.symmAt 0 p u = p (Function.update u 0 ((unitInterval.symm) (u 0))) := by
  change p (fun j => if j = 0 then (unitInterval.symm) (u 0) else u j) = _
  congr 1
  funext j
  simp only [Function.update_apply]

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_reflected_rotated_face_apply {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) (ε : (unitInterval))
    (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.symmAt 0
        (HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalFace F 0 ε hε)
          (finRotate (n + 1)))
        u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) ((unitInterval.symm) (u 0)))) := by
  rw [whiskerFacet_symmAt_zero_apply, whiskerFacet_rotated_face_apply]
  simp only [Fin.tail_update_zero, Function.update_self]

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_last_upper_uncurry_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → (unitInterval)) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) u =
      F.val (Fin.cons (whiskerTrack (u 0)).1 (Fin.snoc (Fin.tail u) (whiskerTrack (u 0)).2)) := by
  rw [uncurryLoop_apply, cubicalFace_apply, whiskeredCell_apply, whiskerFacet_last_coordinates,
    whiskerMap_apply]
  simp only [Fin.init_snoc, Fin.snoc_last, mul_one]
  rfl

theorem HigherHurewicz.CubicalBoundary.whiskerFacet_transAt_zero_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p q : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → (unitInterval)) :
    GenLoop.transAt 0 p q u =
      if (u 0 : ℝ) ≤ 1 / 2 then
        p (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))
      else q (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))) :=
  rfl

theorem HigherHurewicz.CubicalBoundary.whiskeredCell_face_last_upper {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell (n + 2) x) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      GenLoop.transAt 0
        (HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalLowerFace F 0)
          (finRotate (n + 1)))
        (GenLoop.transAt 0 (cubicalUpperFace F (Fin.last (n + 1)))
          (GenLoop.symmAt 0
            (HigherHurewicz.NativeSubdivision.permuteCubeLoop (cubicalUpperFace F 0)
              (finRotate (n + 1))))) := by
  apply GenLoop.ext
  intro u
  rw [whiskerFacet_last_upper_uncurry_apply, whiskerTrack_concat, whiskerFacet_transAt_zero_apply]
  by_cases h₀ : (u 0 : ℝ) ≤ 1 / 2
  · simp only [if_pos h₀, whiskerFacet_rotated_face_apply, Fin.tail_update_zero,
      Function.update_self]
  · simp only [if_neg h₀]
    rw [whiskerFacet_transAt_zero_apply]
    simp only [Function.update_self]
    split_ifs
    · rw [whiskerFacet_last_upper_apply]
      simp only [Fin.tail_update_zero, Function.update_self]
    · rw [whiskerFacet_reflected_rotated_face_apply]
      simp only [Fin.tail_update_zero, Function.update_self]

theorem HigherHurewicz.CubicalBoundary.uncurryTail_update_succ {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) (i : Fin n) (t : (unitInterval)) :
    (fun j : Fin n => Function.update u i.succ t j.succ) =
      Function.update (fun j : Fin n => u j.succ) i t := by
  funext j
  simp only [Function.update_apply, Fin.succ_inj]

@[simp]
theorem HigherHurewicz.CubicalBoundary.uncurryHead_update_succ {n : ℕ}
    (u : Fin (n + 1) → (unitInterval)) (i : Fin n) (t : (unitInterval)) :
    Function.update u i.succ t 0 = u 0 := by
  simp only [Function.update_apply, (Fin.succ_ne_zero i).symm, if_false]

theorem HigherHurewicz.CubicalBoundary.uncurryLoop_transAt {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (i : Fin n)
    (p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.transAt i p q) =
      GenLoop.transAt i.succ (uncurryLoop p) (uncurryLoop q) := by
  apply GenLoop.ext
  intro u
  change
    ((if (u i.succ : ℝ) ≤ 1 / 2 then _ else _) : GenLoop (Fin 1) X x) (fun _ => u 0) =
      if (u i.succ : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;> simp only [uncurryLoop_apply, uncurryTail_update_succ, uncurryHead_update_succ]

theorem HigherHurewicz.CubicalBoundary.uncurryLoop_symmAt {n : ℕ} {X : Type*} [TopologicalSpace X]
    {x : X} (i : Fin n) (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.symmAt i p) = GenLoop.symmAt i.succ (uncurryLoop p) := by
  apply GenLoop.ext
  intro u
  change
    p (fun j => if j = i then (unitInterval.symm) (u i.succ) else u j.succ) (fun _ => u 0) =
      p (fun j => if j.succ = i.succ then (unitInterval.symm) (u i.succ) else u j.succ)
        (fun _ => if (0 : Fin (n + 1)) = i.succ then (unitInterval.symm) (u i.succ) else u 0)
  simp only [Fin.succ_inj, (Fin.succ_ne_zero i).symm, if_false]

theorem HigherHurewicz.CubicalBoundary.uncurryLoop_swap {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) (i j : Fin n) :
    uncurryLoop (HigherHurewicz.NativeSubdivision.permuteCubeLoop p (Equiv.swap i j)) =
      HigherHurewicz.NativeSubdivision.permuteCubeLoop (uncurryLoop p)
        (Equiv.swap i.succ j.succ) := by
  have hzero : Equiv.swap i.succ j.succ (0 : Fin (n + 1)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm
  have hsucc (k : Fin n) : Equiv.swap i.succ j.succ k.succ = (Equiv.swap i j k).succ := by
    by_cases hki : k = i
    · subst k
      simp
    by_cases hkj : k = j
    · subst k
      simp
    have hki' : k.succ ≠ i.succ := fun h => hki (Fin.succ_inj.mp h)
    have hkj' : k.succ ≠ j.succ := fun h => hkj (Fin.succ_inj.mp h)
    rw [Equiv.swap_apply_of_ne_of_ne hki' hkj', Equiv.swap_apply_of_ne_of_ne hki hkj]
  apply GenLoop.ext
  intro u
  change
    p (fun k => u (Equiv.swap i j k).succ) (fun _ => u 0) =
      p (fun k => u (Equiv.swap i.succ j.succ k.succ)) (fun _ => u (Equiv.swap i.succ j.succ 0))
  simp only [hsucc, hzero]

def HigherHurewicz.CubicalBoundary.CubicalEvaluator.uncurry {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A) :
    HigherHurewicz.CubicalBoundary.CubicalEvaluator n (GenLoop.const : GenLoop (Fin 1) X x) A
    where
  evaluate p := E (HigherHurewicz.CubicalBoundary.uncurryLoop p)
  map_const := by rw [HigherHurewicz.CubicalBoundary.uncurryLoop_const]; exact E.map_const
  map_homotopic h := E.map_homotopic (HigherHurewicz.CubicalBoundary.uncurryLoop_homotopic h)
  map_transAt i p
    q := by
    rw [HigherHurewicz.CubicalBoundary.uncurryLoop_transAt]
    exact E.map_transAt i.succ _ _
  map_symmAt i
    p := by
    rw [HigherHurewicz.CubicalBoundary.uncurryLoop_symmAt]
    exact E.map_symmAt i.succ _
  map_swap p i j
    hij := by
    rw [HigherHurewicz.CubicalBoundary.uncurryLoop_swap]
    exact E.map_swap _ i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

@[simp]
theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.uncurry_apply {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    E.uncurry p = E (HigherHurewicz.CubicalBoundary.uncurryLoop p) :=
  rfl

theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_constantClosingPaths {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (p : GenLoop (Fin (n + 1)) X x) :
    E (GenLoop.transAt 0 GenLoop.const (GenLoop.transAt 0 p GenLoop.const)) = E p := by
  rw [E.map_transAt, E.map_transAt, E.map_const, zero_add, add_zero]

theorem HigherHurewicz.CubicalBoundary.CubicalEvaluator.map_cyclicClosingPaths {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (l p r : GenLoop (Fin (n + 1)) X x) :
    E
        (GenLoop.transAt 0
          (HigherHurewicz.NativeSubdivision.permuteCubeLoop l (finRotate (n + 1)))
          (GenLoop.transAt 0 p
            (GenLoop.symmAt 0
              (HigherHurewicz.NativeSubdivision.permuteCubeLoop r (finRotate (n + 1)))))) =
      E p - (-1 : ℤ) ^ n • (E r - E l) := by
  rw [E.map_transAt, E.map_transAt, E.map_symmAt, E.map_finRotate, E.map_finRotate]
  simp only [Nat.add_sub_cancel, smul_sub]
  abel

theorem HigherHurewicz.CubicalBoundary.alternatingSign_smul_involution {A : Type*}
    [AddCommGroup A] (n : ℕ) (a : A) : (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • a) = a := by
  rw [smul_smul, ← mul_pow]
  simp

theorem HigherHurewicz.CubicalBoundary.alternatingSum_head {A : Type*} [AddCommGroup A] (n : ℕ)
    (a : Fin (n + 2) → A) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) =
      a 0 - ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ', neg_mul, one_mul,
    neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem HigherHurewicz.CubicalBoundary.alternatingSum_dimension_reduction {A : Type*}
    [AddCommGroup A] (n : ℕ) (a : Fin (n + 2) → A) (b : Fin (n + 1) → A)
    (hmid : ∀ i : Fin n, b i.castSucc = a i.castSucc.succ)
    (hlast : b (Fin.last n) = a (Fin.last (n + 1)) - (-1 : ℤ) ^ n • a 0) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) = -(∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) := by
  have htail :
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • b i) =
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • a i.succ) - a 0 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hmid, hlast, Fin.val_castSucc, Fin.val_last, Fin.succ_last, smul_sub,
      alternatingSign_smul_involution]
    abel
  rw [alternatingSum_head, htail]
  abel

theorem HigherHurewicz.CubicalBoundary.whiskeredCell_lower_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin (n + 1)) :
    E.uncurry (cubicalLowerFace (whiskeredCell F) i) = E (cubicalLowerFace F i.succ) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_normal F i 0 (Or.inl rfl) (Or.inr rfl)]
  exact E.map_constantClosingPaths _

theorem HigherHurewicz.CubicalBoundary.whiskeredCell_upper_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) (i : Fin n) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) i.castSucc) =
      E (cubicalUpperFace F i.castSucc.succ) := by
  rw [CubicalEvaluator.uncurry_apply,
    whiskeredCell_face_normal F i.castSucc 1 (Or.inr rfl) (Or.inl (Fin.castSucc_ne_last i))]
  exact E.map_constantClosingPaths _

theorem HigherHurewicz.CubicalBoundary.whiskeredCell_last_upper_value {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator (n + 1) x A)
    (F : BasedCubicalCell (n + 2) x) :
    E.uncurry (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      E (cubicalUpperFace F (Fin.last (n + 1))) -
        (-1 : ℤ) ^ n • (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) := by
  rw [CubicalEvaluator.uncurry_apply, whiskeredCell_face_last_upper]
  exact E.map_cyclicClosingPaths _ _ _

theorem HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_dimension_reduction {n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A]
    (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x) :
    cubicalBoundaryValue E F = -cubicalBoundaryValue E.uncurry (whiskeredCell F) := by
  unfold cubicalBoundaryValue
  apply alternatingSum_dimension_reduction n
  · intro i
    rw [whiskeredCell_upper_value, whiskeredCell_lower_value]
  · rw [whiskeredCell_last_upper_value, whiskeredCell_lower_value, Fin.succ_last]
    abel

def HigherHurewicz.CubicalBoundary.squareLowerRoute :
    C(Fin 1 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)),
      Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

def HigherHurewicz.CubicalBoundary.squareUpperRoute :
    C(Fin 1 → (unitInterval), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1),
      Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

@[simp]
theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_zero (u : Fin 1 → (unitInterval))
    (hu : u 0 = 0) : squareLowerRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp]
theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_one (u : Fin 1 → (unitInterval))
    (hu : u 0 = 1) : squareLowerRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp]
theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_zero (u : Fin 1 → (unitInterval))
    (hu : u 0 = 0) : squareUpperRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

@[simp]
theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_one (u : Fin 1 → (unitInterval))
    (hu : u 0 = 1) : squareUpperRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_of_le (u : Fin 1 → (unitInterval))
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)), 0] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)

theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_of_not_le (u : Fin 1 → (unitInterval))
    (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![1, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)
  · rfl

theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_of_le (u : Fin 1 → (unitInterval))
    (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![0, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)
  · rfl

theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_of_not_le (u : Fin 1 → (unitInterval))
    (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), 1] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)

def HigherHurewicz.CubicalBoundary.squareRoutesBlend :
    C((unitInterval) × (Fin 1 → (unitInterval)), Fin 2 → (unitInterval))
    where
  toFun
    u :=
    HigherHurewicz.NativeSubdivision.nativeCubeBlend u.1 (squareLowerRoute u.2)
      (squareUpperRoute u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact
      Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (squareLowerRoute.continuous.comp continuous_snd)).prodMk
          (((continuous_apply i).comp (squareUpperRoute.continuous.comp continuous_snd)).prodMk
            continuous_fst))

@[simp]
theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_zero (u : Fin 1 → (unitInterval)) :
    squareRoutesBlend (0, u) = squareLowerRoute u :=
  HigherHurewicz.NativeSubdivision.nativeCubeBlend_zero _ _

@[simp]
theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_one (u : Fin 1 → (unitInterval)) :
    squareRoutesBlend (1, u) = squareUpperRoute u :=
  HigherHurewicz.NativeSubdivision.nativeCubeBlend_one _ _

theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_endpoint_zero (t : (unitInterval))
    (u : Fin 1 → (unitInterval)) (hu : u 0 = 0) : squareRoutesBlend (t, u) = fun _ => 0 := by
  funext i
  simp [squareRoutesBlend, HigherHurewicz.NativeSubdivision.nativeCubeBlend,
    squareLowerRoute_zero u hu, squareUpperRoute_zero u hu]

theorem HigherHurewicz.CubicalBoundary.squareRoutesBlend_endpoint_one (t : (unitInterval))
    (u : Fin 1 → (unitInterval)) (hu : u 0 = 1) : squareRoutesBlend (t, u) = fun _ => 1 := by
  funext i
  simp [squareRoutesBlend, HigherHurewicz.NativeSubdivision.nativeCubeBlend,
    squareLowerRoute_one u hu, squareUpperRoute_one u hu]

theorem HigherHurewicz.CubicalBoundary.squareFacet_zero (ε : (unitInterval))
    (u : Fin 1 → (unitInterval)) : cubeFacet 1 0 ε u = ![ε, u 0] := by
  funext i
  fin_cases i
  · exact cubeFacet_apply_self 1 0 ε u
  · change cubeFacet 1 0 ε u ((0 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 0 ε u 0

theorem HigherHurewicz.CubicalBoundary.squareFacet_one (ε : (unitInterval))
    (u : Fin 1 → (unitInterval)) : cubeFacet 1 1 ε u = ![u 0, ε] := by
  funext i
  fin_cases i
  · change cubeFacet 1 1 ε u ((1 : Fin 2).succAbove 0) = u 0
    exact cubeFacet_apply_succAbove 1 1 ε u 0
  · exact cubeFacet_apply_self 1 1 ε u

theorem HigherHurewicz.CubicalBoundary.squareLowerRoute_transAt_apply {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) (u : Fin 1 → (unitInterval)) :
    GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u =
      F.val (squareLowerRoute u) := by
  change
    (if (u 0 : ℝ) ≤ 1 / 2 then
        F.val
          (cubeFacet 1 1 0 (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        F.val
          (cubeFacet 1 0 1
            (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) =
      _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [if_pos hu, squareLowerRoute_of_le u hu]
    simp only [squareFacet_one, Function.update_self]
  · rw [if_neg hu, squareLowerRoute_of_not_le u hu]
    simp only [squareFacet_zero, Function.update_self]

theorem HigherHurewicz.CubicalBoundary.squareUpperRoute_transAt_apply {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) (u : Fin 1 → (unitInterval)) :
    GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1) u =
      F.val (squareUpperRoute u) := by
  change
    (if (u 0 : ℝ) ≤ 1 / 2 then
        F.val
          (cubeFacet 1 0 0 (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)))))
      else
        F.val
          (cubeFacet 1 1 1
            (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))))) =
      _
  by_cases hu : (u 0 : ℝ) ≤ 1 / 2
  · rw [if_pos hu, squareUpperRoute_of_le u hu]
    simp only [squareFacet_zero, Function.update_self]
  · rw [if_neg hu, squareUpperRoute_of_not_le u hu]
    simp only [squareFacet_one, Function.update_self]

def HigherHurewicz.CubicalBoundary.squareCubicalFacesHomotopy {X : Type*} [TopologicalSpace X]
    {x : X} (F : BasedCubicalCell 2 x) :
    (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).val.HomotopyRel
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)).val
      (Cube.boundary (Fin 1))
    where
  toFun z := F.val (squareRoutesBlend z)
  continuous_toFun := F.val.continuous.comp squareRoutesBlend.continuous
  map_zero_left
    u := by
    rw [squareRoutesBlend_zero]
    exact (squareLowerRoute_transAt_apply F u).symm
  map_one_left
    u := by
    rw [squareRoutesBlend_one]
    exact (squareUpperRoute_transAt_apply F u).symm
  prop' t u
    hu := by
    change
      F.val (squareRoutesBlend (t, u)) =
        GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0) u
    refine
      Eq.trans (b := x) ?_
        ((GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0)).property u hu).symm
    obtain ⟨i, hi⟩ := hu
    have hi0 : u 0 = 0 ∨ u 0 = 1 := by simpa only [Fin.fin_one_eq_zero] using hi
    rcases hi0 with hi0 | hi0
    · exact
        (congrArg F.val (squareRoutesBlend_endpoint_zero t u hi0)).trans
          (F.property (fun _ => 0) 0 1 (by decide) (Or.inl rfl) (Or.inl rfl))
    · exact
        (congrArg F.val (squareRoutesBlend_endpoint_one t u hi0)).trans
          (F.property (fun _ => 1) 0 1 (by decide) (Or.inr rfl) (Or.inr rfl))

theorem HigherHurewicz.CubicalBoundary.squareCubicalFaces_homotopic {X : Type*}
    [TopologicalSpace X] {x : X} (F : BasedCubicalCell 2 x) :
    GenLoop.Homotopic (GenLoop.transAt 0 (cubicalLowerFace F 1) (cubicalUpperFace F 0))
      (GenLoop.transAt 0 (cubicalLowerFace F 0) (cubicalUpperFace F 1)) :=
  ⟨squareCubicalFacesHomotopy F⟩

theorem HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_square {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] (E : CubicalEvaluator 1 x A)
    (F : BasedCubicalCell 2 x) : cubicalBoundaryValue E F = 0 := by
  have h := E.map_homotopic (squareCubicalFaces_homotopic F)
  rw [E.map_transAt, E.map_transAt] at h
  unfold cubicalBoundaryValue
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ,
    Nat.zero_add, pow_zero, pow_one, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]
  change
    (E (cubicalUpperFace F 0) - E (cubicalLowerFace F 0)) -
        (E (cubicalUpperFace F 1) - E (cubicalLowerFace F 1)) =
      0
  apply sub_eq_zero.mpr
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h

theorem HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_eq_zero (n : ℕ) :
    ∀ {X : Type u} [TopologicalSpace X] {x : X} {A : Type v} [AddCommGroup A]
      (E : CubicalEvaluator (n + 1) x A) (F : BasedCubicalCell (n + 2) x),
      cubicalBoundaryValue E F = 0 := by
  induction n with
  | zero =>
    intro X _ x A _ E F
    exact cubicalBoundaryValue_square E F
  | succ n ih =>
    intro X _ x A _ E F
    rw [cubicalBoundaryValue_dimension_reduction, ih E.uncurry (whiskeredCell F), neg_zero]

theorem HigherHurewicz.SimplexGeometry.basedSimplexBoundary_evaluation {X : Type*}
    [TopologicalSpace X] {x : X} {A : Type*} [AddCommGroup A] {n : ℕ}
    (E : HigherHurewicz.CubicalBoundary.CubicalEvaluator (n + 1) x A)
    (τ : BasedSimplexBoundary (n + 2) x) :
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • E (basedSimplexLoop (basedSimplexBoundaryFace τ i))) =
      0 := by
  rw [← simplexBoundaryCube_boundaryValue]
  exact HigherHurewicz.CubicalBoundary.cubicalBoundaryValue_eq_zero n E (simplexBoundaryCube τ)

theorem HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (τ : BasedSimplexBoundary (n + 3) x) :
    (∑ i : Fin (n + 4), (-1 : ℤ) ^ i.val • basedSimplexClass (basedSimplexBoundaryFace τ i)) =
      0 :=
  basedSimplexBoundary_evaluation (HigherHurewicz.CubicalBoundary.nativeCubicalEvaluator n x) τ

theorem FourthHurewicz.basedFiveSimplex_signed_relation {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    (∑ i : Fin 6, (-1 : ℤ) ^ i.val • basedFourSimplexClass (basedFiveSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 2) τ

theorem FourthHurewicz.normalizedFourSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) :
    ∑ i : Fin 6,
        (-1 : ℤ) ^ i.val •
          basedFourSimplexClass
            (normalizedFourSimplex x (smp.comp (FirstHurewicz.simplexFace 4 i))) =
      0 := by
  simpa only [normalizedFiveSimplex_face] using
    basedFiveSimplex_signed_relation (normalizedFiveSimplex x smp)

theorem FourthHurewicz.fourSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (b : FirstHurewicz.Chains X 5) :
    fourSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 5 4).hom b) = 0 := by
  have h : (fourSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 5 4).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 5
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      fourSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedFourSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

def HigherHurewicz.CubeGluing.CubeCompatible {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin n)) (s t : FirstHurewicz.Simplex n),
    HigherHurewicz.CubeTriangulation.cubeSimplex e s =
        HigherHurewicz.CubeTriangulation.cubeSimplex f t →
      ∀ r : (unitInterval), F e (r, s) = F f (r, t)

def HigherHurewicz.CubeGluing.cubeFamilyMap {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X)) :
    C((Σ _e : Equiv.Perm (Fin n), (unitInterval) × FirstHurewicz.Simplex n), X)
    where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

theorem HigherHurewicz.CubeGluing.cubeFamilyMap_factorsThrough {n : ℕ} {X : Type}
    [TopologicalSpace X] (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F)
      (HigherHurewicz.CubeTriangulation.cubeCylinderCover n) := by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs :
    HigherHurewicz.CubeTriangulation.cubeSimplex e s =
      HigherHurewicz.CubeTriangulation.cubeSimplex f t :=
    congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

def HigherHurewicz.CubeGluing.glueCubeHomotopies {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) : C((unitInterval) × HigherHurewicz.CubeTriangulation.CubeN n, X) :=
  (HigherHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap n).lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp]
theorem HigherHurewicz.CubeGluing.glueCubeHomotopies_cell {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) (e : Equiv.Perm (Fin n)) (r : (unitInterval))
    (s : FirstHurewicz.Simplex n) :
    glueCubeHomotopies F hF (r, HigherHurewicz.CubeTriangulation.cubeSimplex e s) = F e (r, s) :=
  DFunLike.congr_fun
    ((HigherHurewicz.CubeTriangulation.cubeCylinderCover_isQuotientMap n).lift_comp
      (cubeFamilyMap F) (cubeFamilyMap_factorsThrough F hF))
    ⟨e, (r, s)⟩

theorem HigherHurewicz.CubeGluing.glueCubeHomotopies_time {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) (r : (unitInterval))
    (g : HigherHurewicz.CubeTriangulation.CubeN n → X)
    (h :
      ∀ (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n),
        F e (r, s) = g (HigherHurewicz.CubeTriangulation.cubeSimplex e s))
    (u : HigherHurewicz.CubeTriangulation.CubeN n) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := HigherHurewicz.CubeTriangulation.exists_cubeSimplex u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

theorem HigherHurewicz.CubeGluing.glueCubeHomotopies_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    (F : Equiv.Perm (Fin n) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (hF : CubeCompatible F) (g : C(HigherHurewicz.CubeTriangulation.CubeN n, X))
    (h :
      ∀ (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n),
        F e (0, s) = g (HigherHurewicz.CubeTriangulation.cubeSimplex e s))
    (u : HigherHurewicz.CubeTriangulation.CubeN n) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

theorem HigherHurewicz.CubeGluing.cubeOriginal_face_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
        (FirstHurewicz.simplexFace n 0) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (HigherHurewicz.CubeTriangulation.cubeSimplex_face_zero_boundary e s)

theorem HigherHurewicz.CubeGluing.cubeOriginal_face_last {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
        (FirstHurewicz.simplexFace n (Fin.last (n + 1))) =
      ContinuousMap.const (FirstHurewicz.Simplex n) x := by
  ext s
  exact GenLoop.boundary p _ (HigherHurewicz.CubeTriangulation.cubeSimplex_face_last_boundary e s)

theorem HigherHurewicz.CubeGluing.cubeOriginal_face_swap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
        (FirstHurewicz.simplexFace n i.succ.castSucc) =
      (p.val.comp
            (HigherHurewicz.CubeTriangulation.cubeSimplex
              ((Equiv.swap i.castSucc i.succ).trans e))).comp
        (FirstHurewicz.simplexFace n i.succ.castSucc) := by
  simpa only [ContinuousMap.comp_assoc] using
    congrArg
      (fun f : C(FirstHurewicz.Simplex n, HigherHurewicz.CubeTriangulation.CubeN (n + 1)) =>
        p.val.comp f)
      (HigherHurewicz.CubeTriangulation.cubeSimplex_face_swap e i)

theorem HigherHurewicz.CubeGluing.coherentCubeCell_face {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2))
    (r : (unitInterval)) (s : FirstHurewicz.Simplex n) :
    H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))
        (r, FirstHurewicz.simplexFace n i s) =
      H₀
        ((p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)).comp
          (FirstHurewicz.simplexFace n i))
        (r, s) :=
  DFunLike.congr_fun (hface (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) i)
    (r, s)

theorem HigherHurewicz.CubeGluing.coherentCubeCell_swap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (r : (unitInterval)) (s : FirstHurewicz.Simplex (n + 1)) (hs : s i.succ.castSucc = 0) :
    H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) (r, s) =
      H₁
        (p.val.comp
          (HigherHurewicz.CubeTriangulation.cubeSimplex ((Equiv.swap i.castSucc i.succ).trans e)))
        (r, s) := by
  let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n i.succ.castSucc ⟨s, hs⟩
  have ht : FirstHurewicz.simplexFace n i.succ.castSucc t = s :=
    SecondHurewicz.SimplyConnected.simplexFace_inverse n i.succ.castSucc ⟨s, hs⟩
  rw [← ht, coherentCubeCell_face H₀ H₁ hface, coherentCubeCell_face H₀ H₁ hface,
    cubeOriginal_face_swap]

theorem HigherHurewicz.CubeGluing.coherentCubeCell_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (r : (unitInterval))
    (s : FirstHurewicz.Simplex (n + 1))
    (hs : HigherHurewicz.CubeTriangulation.cubeSimplex e s ∈ Cube.boundary (Fin (n + 1))) :
    H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) (r, s) = x := by
  rcases (HigherHurewicz.CubeTriangulation.cubeSimplex_mem_boundary_iff e s).mp hs with hs | hs
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n 0 ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace n 0 t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse n 0 ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_zero, hconst]
    rfl
  · let t := SecondHurewicz.SimplyConnected.simplexFaceInverse n (Fin.last (n + 1)) ⟨s, hs⟩
    have ht : FirstHurewicz.simplexFace n (Fin.last (n + 1)) t = s :=
      SecondHurewicz.SimplyConnected.simplexFace_inverse n (Fin.last (n + 1)) ⟨s, hs⟩
    rw [← ht, coherentCubeCell_face H₀ H₁ hface, cubeOriginal_face_last, hconst]
    rfl

theorem HigherHurewicz.CubeGluing.coherentCubeFamily_compatible {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) :
    CubeCompatible (fun e => H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  intro e f s t h r
  have hst := HigherHurewicz.CubeTriangulation.cubeSimplex_overlap_preimage e f s t h
  subst t
  have hf :
    HigherHurewicz.CubeTriangulation.SortedCoordinates
      (HigherHurewicz.CubeTriangulation.cubeSimplex e s) f := by
    rw [h]
    exact HigherHurewicz.CubeTriangulation.cubeSimplex_sorted f s
  apply
    HigherHurewicz.CubeTriangulation.eq_of_sorted_adjacent
      (HigherHurewicz.CubeTriangulation.cubeSimplex e s)
      (fun g => H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex g)) (r, s)) ?_
      (HigherHurewicz.CubeTriangulation.cubeSimplex_sorted e s) hf
  intro g hg i ht
  apply coherentCubeCell_swap H₀ H₁ hface p g i r s
  apply HigherHurewicz.CubeTriangulation.cubeSimplex_tie g s i
  simpa only [HigherHurewicz.CubeTriangulation.cubeSimplex_eq_of_sorted e g s hg] using ht

def HigherHurewicz.CubeGluing.coherentCubeHomotopyMap {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X} (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) :
    C((unitInterval) × HigherHurewicz.CubeTriangulation.CubeN (n + 1), X) :=
  glueCubeHomotopies (fun e => H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)))
    (coherentCubeFamily_compatible H₀ H₁ hface p)

@[simp]
theorem HigherHurewicz.CubeGluing.coherentCubeHomotopyMap_cell {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) (r : (unitInterval))
    (s : FirstHurewicz.Simplex (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, HigherHurewicz.CubeTriangulation.cubeSimplex e s) =
      H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

theorem HigherHurewicz.CubeGluing.coherentCubeHomotopyMap_zero {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex (n + 1), X)) (s : FirstHurewicz.Simplex (n + 1)),
        H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) (u : HigherHurewicz.CubeTriangulation.CubeN (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) s) u

theorem HigherHurewicz.CubeGluing.coherentCubeHomotopyMap_boundary {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (r : (unitInterval))
    (u : HigherHurewicz.CubeTriangulation.CubeN (n + 1)) (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := HigherHurewicz.CubeTriangulation.exists_cubeSimplex u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₀ H₁ hface hconst p e r s hu

def HigherHurewicz.CubeGluing.coherentCubeEndpoint {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) : GenLoop (Fin (n + 1)) X x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (coherentCubeHomotopyMap H₀ H₁ hface p) 1, fun u hu =>
    coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p 1 u hu⟩

theorem HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell {n : ℕ} {X : Type}
    [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1))) :
    (coherentCubeEndpoint H₀ H₁ hface hconst p).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      SecondHurewicz.SimplyConnected.timeSlice
        (H₁ (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₀ H₁ hface p e 1 s

def HigherHurewicz.CubeGluing.coherentCubeHomotopy {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (H₀ : C(FirstHurewicz.Simplex n, X) → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H₁ :
      C(FirstHurewicz.Simplex (n + 1), X) → C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H₀ H₁)
    (hconst :
      H₀ (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hzero :
      ∀ (smp : C(FirstHurewicz.Simplex (n + 1), X)) (s : FirstHurewicz.Simplex (n + 1)),
        H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₀ H₁ hface hconst p).val
      (Cube.boundary (Fin (n + 1)))
    where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₀ H₁ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₀ H₁ hface hzero p
      map_one_left _ := rfl }
  prop' r u
    hu :=
    (coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

theorem HigherHurewicz.simplex_coordinate_zero_of_tail_eq {n : ℕ} (s : FirstHurewicz.Simplex n)
    {i j : Fin n} (hij : i < j)
    (h :
      (∑ k : Fin (n + 1), if i.val < k.val then s k else 0) =
        ∑ k : Fin (n + 1), if j.val < k.val then s k else 0) :
    s i.succ = 0 := by
  classical
  let A := Finset.univ.filter (fun k : Fin (n + 1) => i.val < k.val)
  let B := Finset.univ.filter (fun k : Fin (n + 1) => j.val < k.val)
  have hAB : (∑ k ∈ A, s k) = ∑ k ∈ B, s k := by simpa only [A, B, Finset.sum_filter] using h
  have hiB : i.succ ∉ B := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, not_lt]
    exact hij
  have hsub : Insert.insert i.succ B ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      simp [A]
    · have hjk : j.val < k.val := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hij hjk⟩
  have hle : s i.succ + ∑ k ∈ B, s k ≤ ∑ k ∈ A, s k := by
    calc
      s i.succ + ∑ k ∈ B, s k = ∑ k ∈ Insert.insert i.succ B, s k := (Finset.sum_insert hiB).symm
      _ ≤ ∑ k ∈ A, s k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => stdSimplex.zero_le s k)
  exact le_antisymm (by linarith) (stdSimplex.zero_le s i.succ)

theorem HigherHurewicz.cubeSimplex_ordered_coordinate_equality_boundary {n : ℕ}
    (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s (e i) = CubeTriangulation.cubeSimplex e s (e j)) :
    s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  have hreal := congrArg (fun t : (unitInterval) => (t : ℝ)) h
  rw [CubeTriangulation.cubeSimplex_coordinate, CubeTriangulation.cubeSimplex_coordinate] at hreal
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i.succ, simplex_coordinate_zero_of_tail_eq s hlt hreal⟩
  · exact ⟨j.succ, simplex_coordinate_zero_of_tail_eq s hgt hreal.symm⟩

theorem HigherHurewicz.cubeSimplex_coordinate_equality_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (s : FirstHurewicz.Simplex n) {i j : Fin n} (hij : i ≠ j)
    (h : CubeTriangulation.cubeSimplex e s i = CubeTriangulation.cubeSimplex e s j) :
    s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  apply cubeSimplex_ordered_coordinate_equality_boundary e s (e.symm.injective.ne hij)
  simpa only [Equiv.apply_symm_apply] using h

theorem HigherHurewicz.coherentCubeEndpoint_cell_boundary {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (e : Equiv.Perm (Fin (n + 1)))
    (s : FirstHurewicz.Simplex (n + 1))
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary (n + 1)) :
    CubeGluing.coherentCubeEndpoint H H' hface hconst p (CubeTriangulation.cubeSimplex e s) = x :=
  by
  have he :=
    congrArg (fun f : C(FirstHurewicz.Simplex (n + 1), X) => f s)
      (CubeGluing.coherentCubeEndpoint_cell H H' hface hconst p e)
  exact he.trans (simplexEndpoint_boundary H H' hface x hone _ s hs)

theorem HigherHurewicz.coherentCubeEndpoint_internalBased {n : ℕ} {X : Type} [TopologicalSpace X]
    {x : X}
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hconst :
      H (ContinuousMap.const (FirstHurewicz.Simplex n) x) =
        ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex n) x)
    (hone :
      ∀ smp,
        SecondHurewicz.SimplyConnected.timeSlice (H smp) 1 =
          ContinuousMap.const (FirstHurewicz.Simplex n) x)
    (p : GenLoop (Fin (n + 1)) X x) (u : Fin (n + 1) → (unitInterval)) (i j : Fin (n + 1))
    (hij : i ≠ j) (hu : u i = u j) : CubeGluing.coherentCubeEndpoint H H' hface hconst p u = x := by
  obtain ⟨e, s, rfl⟩ := CubeTriangulation.exists_cubeSimplex u
  exact
    coherentCubeEndpoint_cell_boundary H H' hface hconst hone p e s
      (cubeSimplex_coordinate_equality_boundary e s hij hu)

def FourthHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] (p : GenLoop (Fin 4) X x) :
    GenLoop (Fin 4) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) p

theorem FourthHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 4)) :
    (normalizedCube x p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      (normalizedFourSimplex x
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) p e

def FourthHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 4)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) (normalizationFourSimplexHomotopy_zero x) p

theorem FourthHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) (u : Fin 4 → (unitInterval)) (i j : Fin 4) (hij : i ≠ j)
    (hu : u i = u j) : normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationThreeSimplexHomotopy_const x) (normalizationThreeSimplexHomotopy_endpoint x) p u
    i j hij hu

def HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (HigherHurewicz.CubeTriangulation.cubeSimplex e).comp
    (HigherHurewicz.SimplexGeometry.simplexQuotient n)

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplex_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (s : FirstHurewicz.Simplex n)
    (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    p (HigherHurewicz.CubeTriangulation.cubeSimplex e s) = x := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := hs
    have hi0 : i = 0 := Fin.ext (by omega)
    subst i
    have hsum : s 0 = 1 := by
      simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using stdSimplex.sum_eq_one s
    exact False.elim (by linarith)
  | succ
    n =>
    rcases HigherHurewicz.CubeTriangulation.cubeSimplex_simplexBoundary e s hs with h |
      ⟨i, j, hij, h⟩
    · exact p.property _ h
    · exact hp _ i j hij h

def HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) : HigherHurewicz.SimplexGeometry.BasedSimplex n x :=
  ⟨p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e), nativeCubeSimplex_based p hp e⟩

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeCubeSimplexQuotient e u) = x :=
  nativeCubeSimplex_based p hp e _ (HigherHurewicz.SimplexGeometry.simplexQuotient_boundary u hu)

theorem FourthHurewicz.normalizedCube_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) (e : Equiv.Perm (Fin 4)) :
    HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x p)
        (normalizedCube_internalBased x p) e =
      normalizedFourSimplex x (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

theorem FourthHurewicz.fourSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    fourSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          basedFourSimplexClass
            (normalizedFourSimplex x
              (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, fourSimplexClassOperator_simplex]

def HigherHurewicz.NativeSubdivision.insertPermutation {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' r).trans (e.optionCongr.trans finSuccEquivLast.symm)

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_apply_at {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : insertPermutation e r r = Fin.last n := by
  simp [insertPermutation]

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_apply_succAbove {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (j : Fin n) :
    insertPermutation e r (r.succAbove j) = (e j).castSucc := by simp [insertPermutation]

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_symm_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) : (insertPermutation e r).symm (Fin.last n) = r := by
  apply (insertPermutation e r).injective
  simp

theorem HigherHurewicz.NativeSubdivision.insertPermutation_pair_injective {n : ℕ} :
    Function.Injective
      (fun er : Equiv.Perm (Fin n) × Fin (n + 1) => insertPermutation er.1 er.2) := by
  rintro ⟨e, r⟩ ⟨f, s⟩ h
  have hrs : r = s := by
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E.symm (Fin.last n)) h
  subst s
  have hef : e = f := by
    apply Equiv.ext
    intro j
    apply Fin.castSucc_injective n
    simpa using congrArg (fun E : Equiv.Perm (Fin (n + 1)) => E (r.succAbove j)) h
  exact congrArg (fun e : Equiv.Perm (Fin n) => (e, r)) hef

theorem HigherHurewicz.NativeSubdivision.optionCongr_removeNone_of_none {α β : Type*}
    (e : Option α ≃ Option β) (h : e Option.none = Option.none) : e.removeNone.optionCongr = e := by
  apply Equiv.ext
  intro a
  cases a with
  | none => simpa using h.symm
  | some a =>
    change Option.some (e.removeNone a) = e (Option.some a)
    cases ha : e (Option.some a) with
    | none =>
      have : Option.some a = Option.none := e.injective (ha.trans h.symm)
      cases this
    | some b => simpa only [ha] using e.removeNone_some ⟨b, ha⟩

def HigherHurewicz.NativeSubdivision.deletePermutationOption {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Option (Fin n)) :=
  (finSuccEquiv' (E.symm (Fin.last n))).symm.trans (E.trans finSuccEquivLast)

@[simp]
theorem HigherHurewicz.NativeSubdivision.deletePermutationOption_none {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) : deletePermutationOption E Option.none = Option.none := by
  simp [deletePermutationOption]

def HigherHurewicz.NativeSubdivision.deletePermutation {n : ℕ} (E : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin n) :=
  (deletePermutationOption E).removeNone

theorem HigherHurewicz.NativeSubdivision.deletePermutation_castSucc {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) (j : Fin n) :
    (deletePermutation E j).castSucc = E ((E.symm (Fin.last n)).succAbove j) := by
  have h :=
    congrArg (fun e : Equiv.Perm (Option (Fin n)) => e (Option.some j))
      (optionCongr_removeNone_of_none (deletePermutationOption E)
        (deletePermutationOption_none E))
  have h' := congrArg finSuccEquivLast.symm h
  simpa only [deletePermutation, Equiv.optionCongr_apply, Option.map_some,
    finSuccEquivLast_symm_some, deletePermutationOption, Equiv.trans_apply,
    finSuccEquiv'_symm_some, Equiv.symm_apply_apply] using h'

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertPermutation_deletePermutation {n : ℕ}
    (E : Equiv.Perm (Fin (n + 1))) :
    insertPermutation (deletePermutation E) (E.symm (Fin.last n)) = E := by
  ext i
  refine Fin.succAboveCases (E.symm (Fin.last n)) ?_ (fun j => ?_) i
  · simp
  · rw [insertPermutation_apply_succAbove, deletePermutation_castSucc]

def HigherHurewicz.NativeSubdivision.insertPermutationEquiv (n : ℕ) :
    (Equiv.Perm (Fin n) × Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 1))
    where
  toFun er := insertPermutation er.1 er.2
  invFun E := (deletePermutation E, E.symm (Fin.last n))
  left_inv
    er :=
    insertPermutation_pair_injective
      (insertPermutation_deletePermutation (insertPermutation er.1 er.2))
  right_inv := insertPermutation_deletePermutation

theorem HigherHurewicz.NativeSubdivision.sum_insertPermutation {n : ℕ} {A : Type*}
    [AddCommMonoid A] (F : Equiv.Perm (Fin (n + 1)) → A) :
    ∑ E, F E = ∑ e : Equiv.Perm (Fin n), ∑ r : Fin (n + 1), F (insertPermutation e r) := by
  rw [← (insertPermutationEquiv n).sum_comp F, Fintype.sum_prod_type]
  rfl

structure HigherHurewicz.NativeSubdivision.NativeChamberChart {n : ℕ}
    (e : Equiv.Perm (Fin n)) where
  toContinuousMap : C(NativeCube (Fin n), NativeCube (Fin n))
  zero_last : ∀ u i, i.val + 1 = n → u (e i) = 0 → toContinuousMap u (e i) = 0
  zero_adjacent :
    ∀ u i j, i.val + 1 = j.val → u (e i) = 0 → toContinuousMap u (e i) = toContinuousMap u (e j)
  one_first : ∀ u i, i.val = 0 → u (e i) = 1 → toContinuousMap u (e i) = 1
  one_adjacent :
    ∀ u i j, j.val + 1 = i.val → u (e i) = 1 → toContinuousMap u (e i) = toContinuousMap u (e j)

def HigherHurewicz.NativeSubdivision.chamberLower {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : r.val < n then (ContinuousMap.eval (e ⟨r.val, h⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 0

def HigherHurewicz.NativeSubdivision.chamberUpper {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : C(NativeCube (Fin n), (unitInterval)) :=
  if h : 0 < r.val then (ContinuousMap.eval (e ⟨r.val - 1, by omega⟩)).comp chart.toContinuousMap
  else ContinuousMap.const _ 1

theorem HigherHurewicz.NativeSubdivision.chamberLower_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) : chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  have hr : r.val < n := h ▸ k.isLt
  have hk : (⟨r.val, hr⟩ : Fin n) = k := Fin.ext h
  simp [chamberLower, hr, hk]

theorem HigherHurewicz.NativeSubdivision.chamberLower_last {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = n) :
    chamberLower e r chart u = 0 := by simp [chamberLower, h]

theorem HigherHurewicz.NativeSubdivision.chamberUpper_of_rank {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) : chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  have hr : 0 < r.val := by omega
  have hk : (⟨r.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
  simp [chamberUpper, hr, hk]

theorem HigherHurewicz.NativeSubdivision.chamberUpper_first {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (h : r.val = 0) :
    chamberUpper e r chart u = 1 := by simp [chamberUpper, h]

theorem HigherHurewicz.NativeSubdivision.chamberLower_zero_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val + 1) (hu : u (e k) = 0) :
    chamberLower e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : r.val < n
  · let j : Fin n := ⟨r.val, hr⟩
    rw [chamberLower_of_rank e r chart u j rfl]
    exact (chart.zero_adjacent u k j (by simpa [j] using h.symm) hu).symm
  · have hn : r.val = n := by omega
    rw [chamberLower_last e r chart u hn]
    exact (chart.zero_last u k (by omega) hu).symm

theorem HigherHurewicz.NativeSubdivision.chamberUpper_one_face {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) (k : Fin n)
    (h : r.val = k.val) (hu : u (e k) = 1) :
    chamberUpper e r chart u = chart.toContinuousMap u (e k) := by
  by_cases hr : 0 < r.val
  · let j : Fin n := ⟨r.val - 1, by omega⟩
    rw [chamberUpper_of_rank e r chart u j (by dsimp [j]; omega)]
    exact (chart.one_adjacent u k j (by dsimp [j]; omega) hu).symm
  · have hz : r.val = 0 := by omega
    rw [chamberUpper_first e r chart u hz]
    exact (chart.one_first u k (by omega) hu).symm

def HigherHurewicz.NativeSubdivision.chamberOldCoordinates {n : ℕ} :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin n))
    where
  toFun u k := u k.castSucc
  continuous_toFun := continuous_pi fun _ => continuous_apply _

def HigherHurewicz.NativeSubdivision.insertChamberMap {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) :
    C(NativeCube (Fin (n + 1)), NativeCube (Fin (n + 1)))
    where
  toFun
    u :=
    Fin.lastCases
      (Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)))
      (chart.toContinuousMap (chamberOldCoordinates u))
  continuous_toFun := by
    apply continuous_pi
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.lastCases_last]
      exact
        Set.Icc.continuous_convexComb_prod.comp
          (((chamberLower e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
            (((chamberUpper e r chart).continuous.comp chamberOldCoordinates.continuous).prodMk
              (continuous_apply (Fin.last n))))
    · simp only [Fin.lastCases_castSucc]
      exact
        (continuous_apply j).comp
          (chart.toContinuousMap.continuous.comp chamberOldCoordinates.continuous)

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertChamberMap_apply_castSucc {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (k : Fin n) :
    insertChamberMap e r chart u k.castSucc = chart.toContinuousMap (chamberOldCoordinates u) k :=
  by simp [insertChamberMap]

@[simp]
theorem HigherHurewicz.NativeSubdivision.insertChamberMap_apply_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) :
    insertChamberMap e r chart u (Fin.last n) =
      Set.Icc.convexComb (chamberLower e r chart (chamberOldCoordinates u))
        (chamberUpper e r chart (chamberOldCoordinates u)) (u (Fin.last n)) := by
  simp [insertChamberMap]

theorem HigherHurewicz.NativeSubdivision.chamberSuccAbove_val_cases {n : ℕ} (r : Fin (n + 1))
    (i : Fin n) :
    ((r.succAbove i).val = i.val ∧ i.val < r.val) ∨
      ((r.succAbove i).val = i.val + 1 ∧ r.val ≤ i.val) := by
  by_cases h : i.castSucc < r
  · exact Or.inl ⟨congrArg Fin.val (Fin.succAbove_of_castSucc_lt r i h), h⟩
  · exact
      Or.inr
        ⟨congrArg Fin.val (Fin.succAbove_of_le_castSucc r i (le_of_not_gt h)), le_of_not_gt h⟩

theorem HigherHurewicz.NativeSubdivision.chamberUpper_succ_eq_lower_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin m) (u : NativeCube (Fin m)) :
    chamberUpper e j.succ chart u = chamberLower e j.castSucc chart u := by
  rw [chamberUpper_of_rank e j.succ chart u j rfl,
    chamberLower_of_rank e j.castSucc chart u j rfl]

def HigherHurewicz.NativeSubdivision.chamberCutSequence {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) : Fin (m + 2) → C(NativeCube (Fin m), (unitInterval)) :=
  Fin.cons (ContinuousMap.const _ 0) (fun j : Fin (m + 1) => chamberUpper e j.rev chart)

theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_succ {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (j : Fin (m + 1)) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.succ u = chamberUpper e j.rev chart u := by
  simp [chamberCutSequence]

@[simp]
theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_last {m : ℕ} (e : Equiv.Perm (Fin m))
    (chart : NativeChamberChart e) (u : NativeCube (Fin m)) :
    chamberCutSequence e chart (Fin.last (m + 1)) u = 1 := by
  change chamberUpper e (Fin.last m).rev chart u = 1
  rw [Fin.rev_last]
  exact chamberUpper_first e 0 chart u rfl

theorem HigherHurewicz.NativeSubdivision.chamberCutSequence_castSucc {m : ℕ}
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin m)) :
    chamberCutSequence e chart j.castSucc u = chamberLower e j.rev chart u := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change 0 = chamberLower e (0 : Fin (m + 1)).rev chart u
    rw [Fin.rev_zero]
    exact (chamberLower_last e (Fin.last m) chart u rfl).symm
  · change chamberUpper e k.castSucc.rev chart u = chamberLower e k.succ.rev chart u
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact chamberUpper_succ_eq_lower_castSucc e chart k.rev u

theorem HigherHurewicz.NativeSubdivision.chamberCuts_sum_rev {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (m + 1) → A) : ∑ j : Fin (m + 1), f j.rev = ∑ j : Fin (m + 1), f j :=
  Equiv.sum_comp Fin.revPerm f

def HigherHurewicz.NativeSubdivision.cubeRestriction {m n : ℕ} (h : m ≤ n) :
    C(NativeCube (Fin n), NativeCube (Fin m))
    where
  toFun u i := u (Fin.castLE h i)
  continuous_toFun := continuous_pi fun i => continuous_apply (Fin.castLE h i)

@[simp]
theorem HigherHurewicz.NativeSubdivision.cubeRestriction_apply {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin m) : cubeRestriction h u i = u (Fin.castLE h i) :=
  rfl

def HigherHurewicz.NativeSubdivision.extendCubeMap {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) : C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := if hi : i.val < m then f (cubeRestriction h u) ⟨i.val, hi⟩ else u i
  continuous_toFun := by
    apply continuous_pi
    intro i
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      exact (continuous_apply ⟨i.val, hi⟩).comp (f.continuous.comp (cubeRestriction h).continuous)
    · simpa only [dif_neg hi] using
        (continuous_apply i : Continuous fun u : NativeCube (Fin n) => u i)

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendCubeMap_castLE {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin m) :
    extendCubeMap h f u (Fin.castLE h i) = f (cubeRestriction h u) i := by simp [extendCubeMap]

theorem HigherHurewicz.NativeSubdivision.extendCubeMap_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) : extendCubeMap h f u i = u i := by simp [extendCubeMap, Nat.not_lt.mpr hi]

theorem HigherHurewicz.NativeSubdivision.cubeRestriction_update_outside {m n : ℕ} (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin n) (hi : m ≤ i.val) (v : (unitInterval)) :
    cubeRestriction h (Function.update u i v) = cubeRestriction h u := by
  funext j
  apply Function.update_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  exact (Nat.not_lt.mpr hi) (hv ▸ j.isLt)

theorem HigherHurewicz.NativeSubdivision.extendCubeMap_update_outside {m n : ℕ} (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : m ≤ i.val) (v : (unitInterval)) :
    extendCubeMap h f (Function.update u i v) = Function.update (extendCubeMap h f u) i v := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [extendCubeMap_outside h f _ i hi]
  · rw [Function.update_of_ne hj]
    by_cases hjm : j.val < m
    · simp only [extendCubeMap, ContinuousMap.coe_mk, dif_pos hjm]
      rw [cubeRestriction_update_outside h u i hi v]
    · rw [extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm),
        extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm), Function.update_of_ne hj]

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendCubeMap_refl {n : ℕ}
    (f : C(NativeCube (Fin n), NativeCube (Fin n))) : extendCubeMap (le_refl n) f = f := by
  ext u i
  simp [cubeRestriction, extendCubeMap]

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendCubeMap_zero {n : ℕ} (h : 0 ≤ n)
    (f : C(NativeCube (Fin 0), NativeCube (Fin 0))) : extendCubeMap h f = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro u
  funext i
  exact extendCubeMap_outside h f u i (Nat.zero_le _)

theorem HigherHurewicz.NativeSubdivision.extendCubeMap_sameFlat {m n : ℕ} (h : m ≤ n)
    (f g : C(NativeCube (Fin m), NativeCube (Fin m))) (u : NativeCube (Fin n))
    (hfg : NativeCubeSameFlat (f (cubeRestriction h u)) (g (cubeRestriction h u))) :
    NativeCubeSameFlat (extendCubeMap h f u) (extendCubeMap h g u) := by
  cases hfg with
  | zero i hf hg => exact .zero (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | one i hf hg => exact .one (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | equal i j hij hf hg =>
    exact
      .equal (Fin.castLE h i) (Fin.castLE h j)
        (fun heq => hij (Fin.ext (congrArg (fun k : Fin n => k.val) heq))) (by simpa using hf)
        (by simpa using hg)

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val + 1 = n + 1)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) = 0 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_zero]
    exact chamberLower_last e r chart (chamberOldCoordinates u) (by omega)
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.zero_last (chamberOldCoordinates u) k (by omega) hu

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (hu : u (insertPermutation e r i) = 0) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_zero]
      exact chamberLower_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_zero_face e r chart (chamberOldCoordinates u) k hr hu,
        chamberUpper_of_rank e r chart (chamberOldCoordinates u) k hr]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : k.val + 1 = l.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.zero_adjacent (chamberOldCoordinates u) k l hkl hu

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i : Fin (n + 1)) (hi : i.val = 0)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) = 1 := by
  revert hi hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · intro hi hu
    simp only [insertPermutation_apply_at] at hu ⊢
    rw [insertChamberMap_apply_last, hu, Set.Icc.convexComb_one]
    exact chamberUpper_first e r chart (chamberOldCoordinates u) hi
  · intro hi hu
    have hk := chamberSuccAbove_val_cases r k
    simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
    exact chart.one_first (chamberOldCoordinates u) k (by omega) hu

theorem HigherHurewicz.NativeSubdivision.insertChamberMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (r : Fin (n + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin (n + 1))) (i j : Fin (n + 1)) (hij : j.val + 1 = i.val)
    (hu : u (insertPermutation e r i) = 1) :
    insertChamberMap e r chart u (insertPermutation e r i) =
      insertChamberMap e r chart u (insertPermutation e r j) := by
  revert hij hu
  refine Fin.succAboveCases r ?_ (fun k => ?_) i
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij
      omega
    · intro hij hu
      have hl := chamberSuccAbove_val_cases r l
      have hr : r.val = l.val + 1 := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [hu, Set.Icc.convexComb_one]
      exact chamberUpper_of_rank e r chart (chamberOldCoordinates u) l hr
  · refine Fin.succAboveCases r ?_ (fun l => ?_) j
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hr : r.val = k.val := by omega
      simp only [insertPermutation_apply_at, insertPermutation_apply_succAbove,
        insertChamberMap_apply_last, insertChamberMap_apply_castSucc] at hu ⊢
      rw [chamberLower_of_rank e r chart (chamberOldCoordinates u) k hr,
        chamberUpper_one_face e r chart (chamberOldCoordinates u) k hr hu]
      simp
    · intro hij hu
      have hk := chamberSuccAbove_val_cases r k
      have hl := chamberSuccAbove_val_cases r l
      have hkl : l.val + 1 = k.val := by omega
      simp only [insertPermutation_apply_succAbove, insertChamberMap_apply_castSucc] at hu ⊢
      exact chart.one_adjacent (chamberOldCoordinates u) k l hkl hu

def HigherHurewicz.NativeSubdivision.insertChamberChart {n : ℕ} (e : Equiv.Perm (Fin n))
    (r : Fin (n + 1)) (chart : NativeChamberChart e) : NativeChamberChart (insertPermutation e r)
    where
  toContinuousMap := insertChamberMap e r chart
  zero_last := insertChamberMap_zero_last e r chart
  zero_adjacent := insertChamberMap_zero_adjacent e r chart
  one_first := insertChamberMap_one_first e r chart
  one_adjacent := insertChamberMap_one_adjacent e r chart

@[ext]
theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.ext {n : ℕ} {e : Equiv.Perm (Fin n)}
    {f g : HigherHurewicz.NativeSubdivision.NativeChamberChart e}
    (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

def HigherHurewicz.NativeSubdivision.chamberCutIndex {m n : ℕ} (h : m + 1 ≤ n) : Fin n :=
  Fin.castLE h (Fin.last m)

theorem HigherHurewicz.NativeSubdivision.chamberCutIndex_ne_castLE {m n : ℕ} (h : m + 1 ≤ n)
    (j : Fin m) : Fin.castLE (Nat.le_of_succ_le h) j ≠ chamberCutIndex h := by
  intro he
  have hv := congrArg Fin.val he
  exact (Nat.ne_of_lt j.isLt) hv

@[simp]
theorem HigherHurewicz.NativeSubdivision.chamberOldCoordinates_cubeRestriction {m n : ℕ}
    (h : m + 1 ≤ n) (u : NativeCube (Fin n)) :
    chamberOldCoordinates (cubeRestriction h u) = cubeRestriction (Nat.le_of_succ_le h) u :=
  rfl

theorem HigherHurewicz.NativeSubdivision.extend_insertChamberMap {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (r : Fin (m + 1)) (chart : NativeChamberChart e)
    (u : NativeCube (Fin n)) :
    extendCubeMap h (insertChamberMap e r chart) u =
      Function.update (extendCubeMap (Nat.le_of_succ_le h) chart.toContinuousMap u)
        (chamberCutIndex h)
        (Set.Icc.convexComb (chamberLower e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (chamberUpper e r chart (cubeRestriction (Nat.le_of_succ_le h) u))
          (u (chamberCutIndex h))) := by
  funext j
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k.castSucc = j := Fin.ext rfl
    have hk' : Fin.castLE h k.castSucc = Fin.castLE (Nat.le_of_succ_le h) k := Fin.ext rfl
    have hji : j ≠ chamberCutIndex h := by
      rw [← hk, hk']
      exact chamberCutIndex_ne_castLE h k
    rw [Function.update_of_ne hji, ← hk, extendCubeMap_castLE, insertChamberMap_apply_castSucc,
      chamberOldCoordinates_cubeRestriction, hk', extendCubeMap_castLE]
  · by_cases hji : j = chamberCutIndex h
    · subst j
      rw [Function.update_self]
      change extendCubeMap h (insertChamberMap e r chart) u (Fin.castLE h (Fin.last m)) = _
      rw [extendCubeMap_castLE, insertChamberMap_apply_last,
        chamberOldCoordinates_cubeRestriction]
      rfl
    · have hjval : j.val ≠ m := fun he => hji (Fin.ext he)
      have hmj : m + 1 ≤ j.val := by omega
      rw [extendCubeMap_outside h _ u j hmj, Function.update_of_ne hji,
        extendCubeMap_outside (Nat.le_of_succ_le h) _ u j (Nat.le_of_succ_le hmj)]

def HigherHurewicz.NativeSubdivision.extendedChamberCutSequence {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) :
    Fin (m + 2) → C(NativeCube (Fin n), (unitInterval)) := fun j =>
  (chamberCutSequence e chart j).comp (cubeRestriction (Nat.le_of_succ_le h))

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_zero {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart 0 u = 0 :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_last {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart (Fin.last (m + 1)) u = 1 :=
  chamberCutSequence_last e chart _

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_castSucc {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.castSucc u =
      chamberLower e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_castSucc e chart j _

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_succ {m n : ℕ} (h : m + 1 ≤ n)
    (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1))
    (u : NativeCube (Fin n)) :
    extendedChamberCutSequence h e chart j.succ u =
      chamberUpper e j.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) :=
  chamberCutSequence_succ e chart j _

theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.sameFlat {m : ℕ}
    {e : Equiv.Perm (Fin m)} (chart other : HigherHurewicz.NativeSubdivision.NativeChamberChart e)
    (u : HigherHurewicz.NativeSubdivision.NativeCube (Fin m)) (hu : u ∈ Cube.boundary (Fin m)) :
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  let i := e.symm j
  have hei : e i = j := e.apply_symm_apply j
  rcases hj with hj | hj
  · have hi : u (e i) = 0 := hei ▸ hj
    by_cases hilast : i.val + 1 = m
    · exact .zero (e i) (chart.zero_last u i hilast hi) (other.zero_last u i hilast hi)
    · let k : Fin m := ⟨i.val + 1, by have := i.isLt; omega⟩
      have hik : i.val + 1 = k.val := rfl
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.zero_adjacent u i k hik hi)
          (other.zero_adjacent u i k hik hi)
  · have hi : u (e i) = 1 := hei ▸ hj
    by_cases hifirst : i.val = 0
    · exact .one (e i) (chart.one_first u i hifirst hi) (other.one_first u i hifirst hi)
    · let k : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hki : k.val + 1 = i.val := by dsimp [k]; omega
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact
        .equal (e i) (e k) hne (chart.one_adjacent u i k hki hi) (other.one_adjacent u i k hki hi)

theorem HigherHurewicz.NativeSubdivision.extendedChamberMap_sameFlat {m n : ℕ} (h : m ≤ n)
    {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (extendCubeMap h chart.toContinuousMap u)
      (extendCubeMap h other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k = j := Fin.ext rfl
    apply extendCubeMap_sameFlat
    apply chart.sameFlat other
    refine ⟨k, ?_⟩
    simpa only [cubeRestriction_apply, hk] using hj
  · rcases hj with hj | hj
    · exact
        .zero j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
    · exact
        .one j ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
          ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)

theorem HigherHurewicz.NativeSubdivision.extendedChamberMap_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (extendCubeMap h chart.toContinuousMap u) = x := by
  simpa only [nativeCubeBlend_zero] using
    nativeCubeBlend_based p hp (extendedChamberMap_sameFlat h chart chart u hu) 0

def HigherHurewicz.NativeSubdivision.extendedChamberLoop {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) : GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (extendCubeMap h chart.toContinuousMap)
    (extendedChamberMap_based p hp h chart)

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberLoop_apply {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberLoop p hp h chart u = p (extendCubeMap h chart.toContinuousMap u) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.extendedChamberLoop_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : 0 ≤ n) {e : Equiv.Perm (Fin 0)} (chart : NativeChamberChart e) :
    extendedChamberLoop p hp h chart = p := by
  apply GenLoop.ext
  intro u
  simp

def HigherHurewicz.NativeSubdivision.extendedChamberHomotopy {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    (extendedChamberLoop p hp h chart).val.HomotopyRel (extendedChamberLoop p hp h other).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (extendCubeMap h chart.toContinuousMap)
    (extendCubeMap h other.toContinuousMap) (extendedChamberMap_based p hp h chart)
    (extendedChamberMap_based p hp h other) (extendedChamberMap_sameFlat h chart other)

theorem HigherHurewicz.NativeSubdivision.nativeClass_extendedChamber_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp h chart) =
      nativeClass (extendedChamberLoop p hp h other) :=
  nativeClass_homotopic ⟨extendedChamberHomotopy p hp h chart other⟩

def HigherHurewicz.NativeSubdivision.CutIndependent {N : Type*} [DecidableEq N] (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u v, a (Function.update u i v) = a u

def HigherHurewicz.NativeSubdivision.CutBased {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a : C(NativeCube N, (unitInterval))) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

def HigherHurewicz.NativeSubdivision.sliceMap {N : Type*} [DecidableEq N] (i : N)
    (a b : C(NativeCube N, (unitInterval))) : C(NativeCube N, NativeCube N)
    where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun :=
    continuous_id.update i
      (Set.Icc.continuous_convexComb_prod.comp
        (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

theorem HigherHurewicz.NativeSubdivision.sliceMap_based {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) (hu : u ∈ Cube.boundary N) : p (sliceMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [sliceMap, hj] using ha u
    · simpa [sliceMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [sliceMap, hji] using hj⟩

def HigherHurewicz.NativeSubdivision.sliceLoop {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b) :
    GenLoop N X x :=
  ⟨p.val.comp (sliceMap i a b), sliceMap_based p i a b ha hb⟩

@[simp]
theorem HigherHurewicz.NativeSubdivision.sliceLoop_apply {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) :
    sliceLoop p i a b ha hb u = p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) :=
  rfl

theorem HigherHurewicz.NativeSubdivision.sliceLoop_self {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (a : C(NativeCube N, (unitInterval)))
    (ha : CutBased p i a) : sliceLoop p i a a ha ha = GenLoop.const := by
  apply GenLoop.ext
  intro u
  simpa only [sliceLoop_apply, Set.Icc.convexComb_eq, GenLoop.const_apply] using ha u

theorem HigherHurewicz.NativeSubdivision.sliceLoop_full {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (ha0 : ∀ u, a u = 0) (hb1 : ∀ u, b u = 1) : sliceLoop p i a b ha hb = p := by
  apply GenLoop.ext
  intro u
  simp [ha0 u, hb1 u]

def HigherHurewicz.NativeSubdivision.sliceHomotopyOfCoordinate {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N)
    (a b : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (q : GenLoop N X x) (w : C(NativeCube N, (unitInterval)))
    (hq : ∀ u, q u = p (Function.update u i (w u))) (hw0 : ∀ u, u i = 0 → w u = a u)
    (hw1 : ∀ u, u i = 1 → w u = b u) :
    (sliceLoop p i a b ha hb).val.HomotopyRel q.val (Cube.boundary N)
    where
  toFun
    v :=
    p
      (Function.update v.2 i
        (Set.Icc.convexComb (Set.Icc.convexComb (a v.2) (b v.2) (v.2 i)) (w v.2) v.1))
  continuous_toFun :=
    p.val.continuous.comp
      (continuous_snd.update i
        (Set.Icc.continuous_convexComb_prod.comp
          ((Set.Icc.continuous_convexComb_prod.comp
                ((a.continuous.comp continuous_snd).prodMk
                  ((b.continuous.comp continuous_snd).prodMk
                    ((continuous_apply i).comp continuous_snd)))).prodMk
            ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 0)) =
        _
    rw [Set.Icc.convexComb_zero]
    rfl
  map_one_left
    u := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 1)) =
        q u
    rw [Set.Icc.convexComb_one]
    exact (hq u).symm
  prop' t u
    hu := by
    change
      p
          (Function.update u i
            (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) t)) =
        sliceLoop p i a b ha hb u
    have hs : sliceLoop p i a b ha hb u = x := (sliceLoop p i a b ha hb).property u hu
    rw [hs]
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · simpa [hj, hw0 u hj] using ha u
      · simpa [hj, hw1 u hj] using hb u
    · exact p.property _ ⟨j, by simpa [hji] using hj⟩

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_independent {m n : ℕ}
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutIndependent (chamberCutIndex h) (extendedChamberCutSequence h e chart j) := by
  intro u v
  change
    chamberCutSequence e chart j
        (cubeRestriction (Nat.le_of_succ_le h) (Function.update u (chamberCutIndex h) v)) =
      chamberCutSequence e chart j (cubeRestriction (Nat.le_of_succ_le h) u)
  rw [cubeRestriction_update_outside (Nat.le_of_succ_le h) u (chamberCutIndex h) (le_refl m) v]

theorem HigherHurewicz.NativeSubdivision.extendedChamberCutSequence_based {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 2)) :
    CutBased (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (extendedChamberCutSequence h e chart j) := by
  intro u
  rw [extendedChamberLoop_apply,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  refine Fin.cases ?_ (fun r => ?_) j
  · rw [extendedChamberCutSequence_zero]
    exact p.property _ ⟨chamberCutIndex h, Or.inl (Function.update_self _ _ _)⟩
  · rw [extendedChamberCutSequence_succ]
    by_cases hr : 0 < r.rev.val
    · let k : Fin m := ⟨r.rev.val - 1, by have := r.rev.isLt; omega⟩
      have hk : r.rev.val = k.val + 1 := by
        change r.rev.val = (r.rev.val - 1) + 1
        omega
      rw [chamberUpper_of_rank e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) k hk]
      apply
        hp _ (chamberCutIndex h) (Fin.castLE (Nat.le_of_succ_le h) (e k))
          (chamberCutIndex_ne_castLE h (e k)).symm
      rw [Function.update_self, Function.update_of_ne (chamberCutIndex_ne_castLE h (e k)),
        extendCubeMap_castLE]
    · have hr0 : r.rev.val = 0 := by omega
      rw [chamberUpper_first e r.rev chart (cubeRestriction (Nat.le_of_succ_le h) u) hr0]
      exact p.property _ ⟨chamberCutIndex h, Or.inr (Function.update_self _ _ _)⟩

def HigherHurewicz.NativeSubdivision.cutBinaryWarp :
    C(((unitInterval) × (unitInterval) × (unitInterval)) × (unitInterval), (unitInterval))
    where
  toFun
    p :=
    Set.Icc.convexComb
      (Set.Icc.convexComb p.1.1 p.1.2.1 (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ)))) p.1.2.2
      (Set.projIcc 0 1 zero_le_one (2 * (p.2 : ℝ) - 1))
  continuous_toFun := by
    unfold Set.Icc.convexComb
    fun_prop

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_apply (a b c t : (unitInterval)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb (Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)))) c
        (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_zero (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 0) = a := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

@[simp]
theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_one (a b c : (unitInterval)) :
    cutBinaryWarp ((a, b, c), 1) = c := by
  norm_num [cutBinaryWarp, Set.projIcc, Set.Icc.convexComb]

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_le_half (a b c t : (unitInterval))
    (ht : (t : ℝ) ≤ 1 / 2) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb a b (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))) := by
  have hz : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = (0 : (unitInterval)) :=
    Set.projIcc_of_le_left zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, hz, Set.Icc.convexComb_zero]

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_half_le (a b c t : (unitInterval))
    (ht : 1 / 2 ≤ (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) := by
  have ho : Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)) = (1 : (unitInterval)) :=
    Set.projIcc_of_right_le zero_le_one (by linarith)
  rw [cutBinaryWarp_apply, ho, Set.Icc.convexComb_one]

theorem HigherHurewicz.NativeSubdivision.cutBinaryWarp_of_half_lt (a b c t : (unitInterval))
    (ht : 1 / 2 < (t : ℝ)) :
    cutBinaryWarp ((a, b, c), t) =
      Set.Icc.convexComb b c (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)) :=
  cutBinaryWarp_of_half_le a b c t ht.le

def HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) : C(NativeCube N, (unitInterval))
    where
  toFun u := cutBinaryWarp ((a u, b u, c u), u i)
  continuous_toFun :=
    cutBinaryWarp.continuous.comp
      ((a.continuous.prodMk (b.continuous.prodMk c.continuous)).prodMk (continuous_apply i))

theorem HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate_zero {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 0) :
    sliceBinaryCoordinate i a b c u = a u := by simp [sliceBinaryCoordinate, hu]

theorem HigherHurewicz.NativeSubdivision.sliceBinaryCoordinate_one {N : Type*} (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (u : NativeCube N) (hu : u i = 1) :
    sliceBinaryCoordinate i a b c u = c u := by simp [sliceBinaryCoordinate, hu]

theorem HigherHurewicz.NativeSubdivision.sliceTrans_apply {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) (u : NativeCube N) :
    GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc) u =
      p (Function.update u i (sliceBinaryCoordinate i a b c u)) := by
  change
    (if (u i : ℝ) ≤ 1 / 2 then
        sliceLoop p i a b ha hb
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
      else
        sliceLoop p i b c hb hc
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))) =
      p (Function.update u i (cutBinaryWarp ((a u, b u, c u), u i)))
  split_ifs with h
  · rw [sliceLoop_apply, haInd u _, hbInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_le_half (a u) (b u) (c u) (u i) h).symm
  · rw [sliceLoop_apply, hbInd u _, hcInd u _, Function.update_self, Function.update_idem]
    exact
      congrArg (fun v => p (Function.update u i v))
        (cutBinaryWarp_of_half_lt (a u) (b u) (c u) (u i) (lt_of_not_ge h)).symm

theorem HigherHurewicz.NativeSubdivision.slice_homotopic_trans {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, (unitInterval))) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) :
    GenLoop.Homotopic (sliceLoop p i a c ha hc)
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc)) :=
  ⟨sliceHomotopyOfCoordinate p i a c ha hc
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc))
      (sliceBinaryCoordinate i a b c) (sliceTrans_apply p i a b c ha hb hc haInd hbInd hcInd)
      (sliceBinaryCoordinate_zero i a b c) (sliceBinaryCoordinate_one i a b c)⟩

theorem HigherHurewicz.NativeSubdivision.slice_toLoop_transAt {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) (a b : GenLoop N X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) = (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

theorem HigherHurewicz.NativeSubdivision.slice_transAt_homotopic {N : Type*} {X : Type*}
    [TopologicalSpace X] {x : X} [DecidableEq N] (i : N) {a b c d : GenLoop N X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [slice_toLoop_transAt, slice_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

def HigherHurewicz.NativeSubdivision.sliceConcat {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) :
    (k : ℕ) →
      (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) →
        (∀ j, CutBased p i (a j)) → GenLoop N X x
  | 0, _, _ => GenLoop.const
  | k + 1, a, ha =>
    GenLoop.transAt i
      (sliceLoop p i (a 0) (a (0 : Fin (k + 1)).succ) (ha 0) (ha (0 : Fin (k + 1)).succ))
      (sliceConcat p i k (fun j => a j.succ) (fun j => ha j.succ))

theorem HigherHurewicz.NativeSubdivision.slice_homotopic_concat {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) :
    GenLoop.Homotopic (sliceLoop p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)))
      (sliceConcat p i k a ha) := by
  induction k with
  | zero =>
    change GenLoop.Homotopic (sliceLoop p i (a 0) (a 0) (ha 0) (ha 0)) GenLoop.const
    rw [sliceLoop_self]
  | succ k
    ih =>
    have ht := ih (fun j => a j.succ) (fun j => ha j.succ) (fun j => hInd j.succ)
    have hs :=
      slice_homotopic_trans p i (a 0) (a (0 : Fin (k + 1)).succ) (a (Fin.last (k + 1))) (ha 0)
        (ha (0 : Fin (k + 1)).succ) (ha (Fin.last (k + 1))) (hInd 0) (hInd (0 : Fin (k + 1)).succ)
        (hInd (Fin.last (k + 1)))
    apply hs.trans
    apply slice_transAt_homotopic
    · exact GenLoop.Homotopic.refl _
    · exact ht

theorem HigherHurewicz.NativeSubdivision.sliceConcat_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j)) :
    nativeClass (sliceConcat p i k a ha) =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) := by
  induction k with
  | zero => simp [sliceConcat]
  | succ k ih =>
    rw [sliceConcat, nativeClass_transAt, ih, Fin.sum_univ_succ]
    rfl

theorem HigherHurewicz.NativeSubdivision.finiteCuts_homotopic {N : Type*} [DecidableEq N]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) : GenLoop.Homotopic p (sliceConcat p i k a ha) := by
  have h := slice_homotopic_concat p i k a ha hInd
  rwa [sliceLoop_full p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)) hzero hone] at h

theorem HigherHurewicz.NativeSubdivision.finiteCuts_class {N : Type*} [DecidableEq N] {X : Type*}
    [TopologicalSpace X] {x : X} [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, (unitInterval))) (ha : ∀ j, CutBased p i (a j))
    (hInd : ∀ j, CutIndependent i (a j)) (hzero : ∀ u, a 0 u = 0)
    (hone : ∀ u, a (Fin.last k) u = 1) :
    nativeClass p =
      ∑ j : Fin k,
        nativeClass (sliceLoop p i (a j.castSucc) (a j.succ) (ha j.castSucc) (ha j.succ)) :=
  (nativeClass_homotopic (finiteCuts_homotopic p i k a ha hInd hzero hone)).trans
    (sliceConcat_class p i k a ha)

theorem HigherHurewicz.NativeSubdivision.extendedChamberCut_slice_eq {m n : ℕ} {X : Type*}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m + 1 ≤ n) (e : Equiv.Perm (Fin m)) (chart : NativeChamberChart e) (j : Fin (m + 1)) :
    sliceLoop (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
        (extendedChamberCutSequence h e chart j.castSucc)
        (extendedChamberCutSequence h e chart j.succ)
        (extendedChamberCutSequence_based p hp h e chart j.castSucc)
        (extendedChamberCutSequence_based p hp h e chart j.succ) =
      extendedChamberLoop p hp h (insertChamberChart e j.rev chart) := by
  apply GenLoop.ext
  intro u
  rw [sliceLoop_apply, extendedChamberLoop_apply, extendedChamberCutSequence_castSucc,
    extendedChamberCutSequence_succ,
    extendCubeMap_update_outside (Nat.le_of_succ_le h) chart.toContinuousMap u (chamberCutIndex h)
      (le_refl m)]
  exact congrArg p (extend_insertChamberMap h e j.rev chart u).symm

theorem HigherHurewicz.NativeSubdivision.nativeClass_extendedChamber_eq_sum_insertions {m n : ℕ}
    {X : Type*} [TopologicalSpace X] {x : X} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m + 1 ≤ n) {e : Equiv.Perm (Fin m)}
    (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ r : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart)) := by
  have hcut :=
    finiteCuts_class (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) (chamberCutIndex h)
      (m + 1) (extendedChamberCutSequence h e chart)
      (extendedChamberCutSequence_based p hp h e chart)
      (extendedChamberCutSequence_independent h e chart)
      (extendedChamberCutSequence_zero h e chart) (extendedChamberCutSequence_last h e chart)
  have hrev :
    nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) chart) =
      ∑ j : Fin (m + 1),
        nativeClass (extendedChamberLoop p hp h (insertChamberChart e j.rev chart)) := by
    simpa only [extendedChamberCut_slice_eq p hp h e chart] using hcut
  exact
    hrev.trans
      (chamberCuts_sum_rev
        (fun r => nativeClass (extendedChamberLoop p hp h (insertChamberChart e r chart))))

def HigherHurewicz.NativeSubdivision.prefixProduct {n : ℕ} (u : NativeCube (Fin n)) (k : ℕ) :
    (unitInterval) :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), u i

@[simp]
theorem HigherHurewicz.NativeSubdivision.prefixProduct_zero {n : ℕ} (u : NativeCube (Fin n)) :
    prefixProduct u 0 = 1 := by simp [prefixProduct]

theorem HigherHurewicz.NativeSubdivision.prefixProduct_succ {n : ℕ} (u : NativeCube (Fin n))
    (k : ℕ) (hk : k < n) : prefixProduct u (k + 1) = prefixProduct u k * u ⟨k, hk⟩ := by
  have hs :
    (Finset.univ.filter fun i : Fin n => i.val < k + 1) =
      Insert.insert ⟨k, hk⟩ (Finset.univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert (by simp)]
  exact mul_comm _ _

theorem HigherHurewicz.NativeSubdivision.prefixProduct_eq_zero_of_coordinate {n : ℕ}
    (u : NativeCube (Fin n)) (k : ℕ) (i : Fin n) (hik : i.val < k) (hi : u i = 0) :
    prefixProduct u k = 0 :=
  Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik⟩) hi

theorem HigherHurewicz.NativeSubdivision.prefixProduct_succ_of_one {n : ℕ}
    (u : NativeCube (Fin n)) (i : Fin n) (hi : u i = 1) :
    prefixProduct u (i.val + 1) = prefixProduct u i.val := by
  rw [prefixProduct_succ u i.val i.isLt, hi, mul_one]

theorem HigherHurewicz.NativeSubdivision.continuous_prefixProduct (n k : ℕ) :
    Continuous (fun u : NativeCube (Fin n) => prefixProduct u k) := by
  unfold prefixProduct
  generalize Finset.univ.filter (fun i : Fin n => i.val < k) = s
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using
      (continuous_const : Continuous (fun _ : NativeCube (Fin n) => (1 : (unitInterval))))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact
      ((continuous_subtype_val.comp (continuous_apply i)).mul
            (continuous_subtype_val.comp ih)).subtype_mk
        _

def HigherHurewicz.NativeSubdivision.nativeDuffyCubeCanonical (n : ℕ) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := prefixProduct u (i.val + 1)
  continuous_toFun := continuous_pi fun i => continuous_prefixProduct n (i.val + 1)

def HigherHurewicz.NativeSubdivision.nativeDuffyCube {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n))
    where
  toFun u i := nativeDuffyCubeCanonical n u (e.symm i)
  continuous_toFun :=
    continuous_pi fun i =>
      (continuous_apply (e.symm i)).comp (nativeDuffyCubeCanonical n).continuous

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u i = prefixProduct u ((e.symm i).val + 1) :=
  rfl

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeDuffyCube e u (e i) = prefixProduct u (i.val + 1) := by simp [nativeDuffyCube_apply]

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeDuffyCube e u (e j) = 0 := by
  rw [nativeDuffyCube_coordinate]
  exact prefixProduct_eq_zero_of_coordinate u _ i (by omega) hi

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeDuffyCube e u (e 0) = 1 := by
  rw [nativeDuffyCube_coordinate, prefixProduct_succ_of_one u 0 hu]
  exact prefixProduct_zero u

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) : nativeDuffyCube e u (e i.castSucc) = nativeDuffyCube e u (e i.succ) := by
  rw [nativeDuffyCube_coordinate, nativeDuffyCube_coordinate,
    prefixProduct_succ_of_one u i.succ hi]
  rfl

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_boundary {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin n) ∨
      ∃ i j : Fin n, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact Or.inl ⟨e i, Or.inl (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)⟩
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero => exact Or.inl ⟨e 0, Or.inr (nativeDuffyCube_coordinate_zero_of_one e u hi)⟩
      | succ i =>
        exact
          Or.inr
            ⟨e i.castSucc, e i.succ,
              e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this),
              nativeDuffyCube_adjacent_of_one e u i hi⟩

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_based {X : Type*} [TopologicalSpace X]
    {x : X} {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

def HigherHurewicz.NativeSubdivision.nativeDuffyCubeLoop {X : Type*} [TopologicalSpace X] {x : X}
    {n : ℕ} (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

def HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeOrderedDuffyMap e u (e i) = prefixProduct (fun k => u (e k)) (i.val + 1) := by
  exact nativeDuffyCube_coordinate e (permuteCubeCoordinates e u) i

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j)
    (hi : u (e i) = 0) : nativeOrderedDuffyMap e u (e j) = 0 :=
  nativeDuffyCube_coordinate_eq_zero e (permuteCubeCoordinates e u) i j hij hi

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (_hi : i.val + 1 = n)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = 0 :=
  nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i.val + 1 = j.val)
    (hu : u (e i) = 0) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu,
    nativeOrderedDuffyMap_coordinate_eq_zero e u i j (by omega) hu]

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) (hi : i.val = 0)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = 1 := by
  rw [nativeOrderedDuffyMap_coordinate, prefixProduct_succ_of_one (fun k => u (e k)) i hu, hi,
    prefixProduct_zero]

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hji : j.val + 1 = i.val)
    (hu : u (e i) = 1) : nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate, nativeOrderedDuffyMap_coordinate,
    prefixProduct_succ_of_one (fun k => u (e k)) i hu, hji]

theorem HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap_based {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeOrderedDuffyMap e u) = x :=
  nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)

def HigherHurewicz.NativeSubdivision.nativeCubeOrderedDuffyHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (nativeOrderedDuffyMap_based p hp e) hfg

theorem HigherHurewicz.NativeSubdivision.nativeClass_commonOrderedDuffy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass (nativeDuffyCubeLoop p hp e) := by
  calc
    nativeClass (nativeCubePullbackLoop p f hf) =
        nativeClass (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e) :=
      nativeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp e f hf hfg⟩
    _ = _ := permuteCubeLoop_additiveClass _ e

def HigherHurewicz.NativeSubdivision.orderedDuffyChart {n : ℕ} (e : Equiv.Perm (Fin n)) :
    NativeChamberChart e
    where
  toContinuousMap := nativeOrderedDuffyMap e
  zero_last := nativeOrderedDuffyMap_zero_last e
  zero_adjacent := nativeOrderedDuffyMap_zero_adjacent e
  one_first := nativeOrderedDuffyMap_one_first e
  one_adjacent := nativeOrderedDuffyMap_one_adjacent e

theorem HigherHurewicz.NativeSubdivision.NativeChamberChart.commonOrderedDuffy {n : ℕ}
    {e : Equiv.Perm (Fin n)} (chart : HigherHurewicz.NativeSubdivision.NativeChamberChart e)
    (u : HigherHurewicz.NativeSubdivision.NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    HigherHurewicz.NativeSubdivision.NativeCubeSameFlat (chart.toContinuousMap u)
      (HigherHurewicz.NativeSubdivision.nativeOrderedDuffyMap e u) :=
  chart.sameFlat (HigherHurewicz.NativeSubdivision.orderedDuffyChart e) u hu

theorem HigherHurewicz.NativeSubdivision.nativeClass_eq_sum_partialChambers {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (m : ℕ) (h : m ≤ n) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin m), nativeClass (extendedChamberLoop p hp h (orderedDuffyChart e)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_insertPermutation]
    calc
      nativeClass p =
          ∑ e : Equiv.Perm (Fin m),
            nativeClass (extendedChamberLoop p hp (Nat.le_of_succ_le h) (orderedDuffyChart e)) :=
        ih (Nat.le_of_succ_le h)
      _ =
          ∑ e : Equiv.Perm (Fin m),
            ∑ r : Fin (m + 1),
              nativeClass
                (extendedChamberLoop p hp h (orderedDuffyChart (insertPermutation e r))) := by
        apply Finset.sum_congr rfl
        intro e _
        rw [nativeClass_extendedChamber_eq_sum_insertions p hp h (orderedDuffyChart e)]
        apply Finset.sum_congr rfl
        intro r _
        exact
          nativeClass_extendedChamber_eq p hp h (insertChamberChart e r (orderedDuffyChart e))
            (orderedDuffyChart (insertPermutation e r))

@[simp]
theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeCubeSimplexQuotient e u (e i) =
      HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) :=
  Subtype.ext (HigherHurewicz.SimplexGeometry.cubeSimplex_quotient_coordinate e u i)

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeCubeSimplexQuotient e u (e j) = 0 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  exact
    le_antisymm (hi ▸ HigherHurewicz.SimplexGeometry.prefixMinimum_le_coordinate u _ i (by omega))
      bot_le

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (hu : u 0 = 1) :
    nativeCubeSimplexQuotient e u (e 0) = 1 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  change HigherHurewicz.SimplexGeometry.prefixMinimum u (0 + 1) = 1
  rw [HigherHurewicz.SimplexGeometry.prefixMinimum_succ u 0 (Nat.zero_lt_succ n),
    HigherHurewicz.SimplexGeometry.prefixMinimum_zero]
  simp [hu]

theorem HigherHurewicz.NativeSubdivision.nativeCubeSimplexQuotient_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1))) (i : Fin n)
    (hi : u i.succ = 1) :
    nativeCubeSimplexQuotient e u (e i.castSucc) = nativeCubeSimplexQuotient e u (e i.succ) := by
  rw [nativeCubeSimplexQuotient_coordinate, nativeCubeSimplexQuotient_coordinate,
    HigherHurewicz.SimplexGeometry.prefixMinimum_succ u i.succ.val i.succ.isLt]
  change
    HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) =
      Min.min (HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)) (u i.succ)
  rw [hi,
    min_eq_left
      (show HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1) ≤ 1 from
        (HigherHurewicz.SimplexGeometry.prefixMinimum u (i.val + 1)).property.2)]

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_simplex_sameFlat {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeSimplexQuotient e u) := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact
      .zero (e i) (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)
        (nativeCubeSimplexQuotient_coordinate_eq_zero e u i i le_rfl hi)
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero =>
        exact
          .one (e 0) (nativeDuffyCube_coordinate_zero_of_one e u hi)
            (nativeCubeSimplexQuotient_coordinate_zero_of_one e u hi)
      | succ i =>
        exact
          .equal (e i.castSucc) (e i.succ)
            (e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this))
            (nativeDuffyCube_adjacent_of_one e u i hi)
            (nativeCubeSimplexQuotient_adjacent_of_one e u i hi)

def HigherHurewicz.NativeSubdivision.nativeDuffyCubeSimplexHomotopy {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (HigherHurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)).val
      (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeSimplexQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeSimplexQuotient_based p hp e)
    (nativeDuffyCube_simplex_sameFlat e)

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCube_homotopic_basedSimplexLoop {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (HigherHurewicz.SimplexGeometry.basedSimplexLoop (nativeBasedCubeSimplex p hp e)) :=
  ⟨nativeDuffyCubeSimplexHomotopy p hp e⟩

theorem HigherHurewicz.NativeSubdivision.nativeDuffyCubeClass_eq_basedSimplexClass {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    nativeClass (nativeDuffyCubeLoop p hp e) =
      HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_homotopic (nativeDuffyCube_homotopic_basedSimplexLoop p hp e)

theorem HigherHurewicz.NativeSubdivision.nativeClass_commonOrderedSimplex {X : Type*}
    [TopologicalSpace X] {x : X} {n : ℕ} [Nontrivial (Fin n)] (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  rw [nativeClass_commonOrderedDuffy p hp e f hf hfg, nativeDuffyCubeClass_eq_basedSimplexClass]
  rfl

theorem HigherHurewicz.NativeSubdivision.nativeClass_chamber_eq_orientedSimplex {n : ℕ}
    [Nontrivial (Fin n)] {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (chart : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp (le_refl n) chart) =
      HigherHurewicz.CubeTriangulation.cubeOrientation e •
        HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  apply
    nativeClass_commonOrderedSimplex p hp e (extendCubeMap (le_refl n) chart.toContinuousMap)
      (extendedChamberMap_based p hp (le_refl n) chart)
  intro u hu
  rw [extendCubeMap_refl]
  exact chart.commonOrderedDuffy u hu

theorem HigherHurewicz.NativeSubdivision.nativeClass_eq_sum_simplices {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    nativeClass p =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  calc
    nativeClass p =
        ∑ e : Equiv.Perm (Fin n),
          nativeClass (extendedChamberLoop p hp (le_refl n) (orderedDuffyChart e)) :=
      nativeClass_eq_sum_partialChambers p hp n (le_refl n)
    _ = _ :=
      Finset.sum_congr rfl fun e _ =>
        nativeClass_chamber_eq_orientedSimplex p hp e (orderedDuffyChart e)

theorem HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class {n : ℕ} [Nontrivial (Fin n)]
    {X : Type*} [TopologicalSpace X] {x : X} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ n X x) =
      ∑ e : Equiv.Perm (Fin n),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          HigherHurewicz.SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_eq_sum_simplices p hp

theorem FourthHurewicz.fourSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    fourSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 4 X x) := by
  rw [fourSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 4 X x) := by
      simpa only [normalizedCube_simplex, basedFourSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
            (normalizedCube_internalBased x p)).symm
    _ = _ :=
      congrArg Additive.ofMul
        (Quotient.sound
          (show GenLoop.Homotopic (normalizedCube x p) p from
            ⟨(normalizationCubeHomotopy x p).symm⟩))

def FourthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SingularMayerVietoris.SingularHomology X 4 →ₗ[ℤ] Additive (π_ 4 X x) :=
  HigherHurewicz.singularHomologyDesc 4 (fourSimplexClassOperator x)
    (fourSimplexClassOperator_boundary x)

@[simp]
theorem FourthHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 4) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 4 c) =
      fourSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 4 _ _ c

theorem FourthHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 4 (fourSimplexClassOperator x)
    (fourSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_fourSimplexClassOperator_cycle x)

@[simp]
theorem FourthHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (c : SingularMayerVietoris.SingularHomology X 4) : hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp]
theorem FourthHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (p : GenLoop (Fin 4) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 4 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 4 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact fourSimplexClassOperator_cubeChain x p

@[simp]
theorem FourthHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (a : Additive (π_ 4 X x)) : hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem FourthHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

def FourthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    Additive (π_ 4 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 4 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x) (hurewiczMap_comp_hurewiczInverse x)
    (hurewiczInverse_comp_hurewiczMap x)

def FourthHurewicz.hurewiczPi4Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    π_ 4 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 4)
    where
  __ := hurewiczPi4 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

def FifthHurewicz.lowerSixSimplexHomotopy {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) : C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) smp

@[simp]
theorem FifthHurewicz.lowerSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) (s : FirstHurewicz.Simplex 6) :
    lowerSixSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FifthHurewicz.lowerSixSimplexHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5
      (FourthHurewicz.normalizationFiveSimplexHomotopy x) (lowerSixSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveHomotopy_face x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)

def FifthHurewicz.fourFiveSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) smp

@[simp]
theorem FifthHurewicz.fourFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5)
    (s : FirstHurewicz.Simplex 5) : fourFiveSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FifthHurewicz.fourFiveSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4
      (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)

@[simp]
theorem FifthHurewicz.fourFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] :
    fourFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.extendCoherentSimplexHomotopy_const
    (SecondHurewicz.SimplyConnected.stationarySimplexHomotopy 3)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (HigherHurewicz.simplexStraighteningHomotopy_face 3 x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) x
    (HigherHurewicz.simplexStraighteningHomotopy_const 4 x)

def FifthHurewicz.fourSixSimplexHomotopy {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) :
    C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy
    (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy_face x) (fourFiveSimplexHomotopy_zero x) smp

@[simp]
theorem FifthHurewicz.fourSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : fourSixSimplexHomotopy x smp (0, s) = smp s :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_zero _ _ _ _ smp s

theorem FifthHurewicz.fourSixSimplexHomotopy_face {X : Type} [TopologicalSpace X] (x : X)
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5 (fourFiveSimplexHomotopy x)
      (fourSixSimplexHomotopy x) :=
  SecondHurewicz.SimplyConnected.extendCoherentSimplexHomotopy_face
    (HigherHurewicz.simplexStraighteningHomotopy 4 x) (fourFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy_face x) (fourFiveSimplexHomotopy_zero x)

def FifthHurewicz.normalizationFourSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.SingularSimplex X 4 → C((unitInterval) × FirstHurewicz.Simplex 4, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)

def FifthHurewicz.normalizationFiveSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.SingularSimplex X 5 → C((unitInterval) × FirstHurewicz.Simplex 5, X) :=
  ThirdHurewicz.composeSimplexHomotopies (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (fourFiveSimplexHomotopy_zero x)

def FifthHurewicz.normalizationSixSimplexHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.SingularSimplex X 6 → C((unitInterval) × FirstHurewicz.Simplex 6, X) :=
  ThirdHurewicz.composeSimplexHomotopies (lowerSixSimplexHomotopy x) (fourSixSimplexHomotopy x)
    (lowerSixSimplexHomotopy_zero x) (fourSixSimplexHomotopy_zero x)

@[simp]
theorem FifthHurewicz.normalizationFiveSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5)
    (s : FirstHurewicz.Simplex 5) : normalizationFiveSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

@[simp]
theorem FifthHurewicz.normalizationSixSimplexHomotopy_zero {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6)
    (s : FirstHurewicz.Simplex 6) : normalizationSixSimplexHomotopy x smp (0, s) = smp s :=
  ThirdHurewicz.composeSimplexHomotopies_zero _ _ _ _ smp s

theorem FifthHurewicz.normalizationHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 4 (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy x) (fourFiveSimplexHomotopy x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x)
    (FourthHurewicz.normalizationFiveHomotopy_face x) (fourFiveSimplexHomotopy_face x)

theorem FifthHurewicz.normalizationSixHomotopy_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies 5 (normalizationFiveSimplexHomotopy x)
      (normalizationSixSimplexHomotopy x) :=
  ThirdHurewicz.composeSimplexHomotopies_face (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (lowerSixSimplexHomotopy x) (fourSixSimplexHomotopy x)
    (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x) (fourFiveSimplexHomotopy_zero x)
    (lowerSixSimplexHomotopy_zero x) (fourSixSimplexHomotopy_zero x)
    (lowerSixSimplexHomotopy_face x) (fourSixSimplexHomotopy_face x)

@[simp]
theorem FifthHurewicz.normalizationFourSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    normalizationFourSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 4) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 4) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (FourthHurewicz.normalizationFourSimplexHomotopy x)
    (HigherHurewicz.simplexStraighteningHomotopy 4 x)
    (FourthHurewicz.normalizationFourSimplexHomotopy_zero x)
    (HigherHurewicz.simplexStraighteningHomotopy_zero 4 x) x
    (FourthHurewicz.normalizationFourSimplexHomotopy_const x)
    (HigherHurewicz.simplexStraighteningHomotopy_const 4 x)

@[simp]
theorem FifthHurewicz.normalizationFiveSimplexHomotopy_const {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    normalizationFiveSimplexHomotopy x (ContinuousMap.const (FirstHurewicz.Simplex 5) x) =
      ContinuousMap.const ((unitInterval) × FirstHurewicz.Simplex 5) x :=
  ThirdHurewicz.composeSimplexHomotopies_const (FourthHurewicz.normalizationFiveSimplexHomotopy x)
    (fourFiveSimplexHomotopy x) (FourthHurewicz.normalizationFiveSimplexHomotopy_zero x)
    (fourFiveSimplexHomotopy_zero x) x (FourthHurewicz.normalizationFiveSimplexHomotopy_const x)
    (fourFiveSimplexHomotopy_const x)

@[simp]
theorem FifthHurewicz.normalizationFourSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 4) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFourSimplexHomotopy x smp) 1 =
      ContinuousMap.const (FirstHurewicz.Simplex 4) x := by
  rw [normalizationFourSimplexHomotopy, ThirdHurewicz.timeSlice_composeSimplexHomotopies_one,
    FourthHurewicz.normalizationFourSimplexHomotopy_endpoint]
  ext s
  exact
    HigherHurewicz.simplexStraighteningHomotopy_one 4 x
      (FourthHurewicz.normalizedFourSimplex x smp).val
      (FourthHurewicz.normalizedFourSimplex x smp).property s

abbrev FifthHurewicz.fiveSimplexBoundary : Set (FirstHurewicz.Simplex 5) :=
  SecondHurewicz.SimplyConnected.simplexBoundary 5

abbrev FifthHurewicz.BasedFiveSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplex 5 x

abbrev FifthHurewicz.basedFiveSimplexLoop {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : GenLoop (Fin 5) X x :=
  HigherHurewicz.SimplexGeometry.basedSimplexLoop τ

abbrev FifthHurewicz.basedFiveSimplexClass {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : Additive (π_ 5 X x) :=
  HigherHurewicz.SimplexGeometry.basedSimplexClass τ

theorem FifthHurewicz.basedFiveSimplex_face {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) (i : Fin 6) :
    τ.val.comp (FirstHurewicz.simplexFace 4 i) =
      ContinuousMap.const (FirstHurewicz.Simplex 4) x :=
  HigherHurewicz.SimplexGeometry.basedSimplex_face τ i

def FifthHurewicz.normalizedFiveSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (smp : FirstHurewicz.SingularSimplex X 5) : BasedFiveSimplex x :=
  ⟨SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1,
    HigherHurewicz.simplexEndpoint_boundary (normalizationFourSimplexHomotopy x)
      (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x) x
      (normalizationFourSimplexHomotopy_endpoint x) smp⟩

theorem FifthHurewicz.normalizationFiveSimplexHomotopy_endpoint {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    SecondHurewicz.SimplyConnected.timeSlice (normalizationFiveSimplexHomotopy x smp) 1 =
      (normalizedFiveSimplex x smp).val :=
  rfl

def FifthHurewicz.normalizedSixSimplexMap {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) : FirstHurewicz.SingularSimplex X 6 :=
  SecondHurewicz.SimplyConnected.timeSlice (normalizationSixSimplexHomotopy x smp) 1

theorem FifthHurewicz.normalizedSixSimplexMap_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) (i : Fin 7) :
    (normalizedSixSimplexMap x smp).comp (FirstHurewicz.simplexFace 5 i) =
      (normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i))).val :=
  SecondHurewicz.SimplyConnected.timeSlice_face (normalizationSixHomotopy_face x) smp i 1

theorem FifthHurewicz.normalizedSixSimplexMap_face_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) (i : Fin 7)
    (s : FirstHurewicz.Simplex 5) (hs : s ∈ fiveSimplexBoundary) :
    normalizedSixSimplexMap x smp (FirstHurewicz.simplexFace 5 i s) = x := by
  have hf :=
    congrArg (fun f : C(FirstHurewicz.Simplex 5, X) => f s) (normalizedSixSimplexMap_face x smp i)
  exact
    hf.trans ((normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i))).property s hs)

def FifthHurewicz.fiveSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] : FirstHurewicz.Chains X 5 →ₗ[ℤ] Additive (π_ 5 X x) :=
  FirstHurewicz.chainLift X 5 fun smp => basedFiveSimplexClass (normalizedFiveSimplex x smp)

@[simp]
theorem FifthHurewicz.fiveSimplexClassOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    fiveSimplexClassOperator x (FirstHurewicz.simplexChain X 5 smp) =
      basedFiveSimplexClass (normalizedFiveSimplex x smp) :=
  FirstHurewicz.chainLift_simplex X 5 _ smp

abbrev FifthHurewicz.BasedSixSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary 6 x

abbrev FifthHurewicz.basedSixSimplexFace {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) (i : Fin 7) : BasedFiveSimplex x :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundaryFace τ i

def FifthHurewicz.BasedSixSimplex.ofFaces {X : Type*} [TopologicalSpace X] {x : X}
    (τ : C(FirstHurewicz.Simplex 6, X))
    (h :
      ∀ i : Fin 7,
        ∀ s ∈ FifthHurewicz.fiveSimplexBoundary, (τ.comp (FirstHurewicz.simplexFace 5 i)) s = x) :
    FifthHurewicz.BasedSixSimplex x :=
  HigherHurewicz.SimplexGeometry.BasedSimplexBoundary.ofFaces τ h

theorem FifthHurewicz.basedSixSimplex_signed_relation {X : Type*} [TopologicalSpace X] {x : X}
    (τ : BasedSixSimplex x) :
    (∑ i : Fin 7, (-1 : ℤ) ^ i.val • basedFiveSimplexClass (basedSixSimplexFace τ i)) = 0 :=
  HigherHurewicz.SimplexGeometry.basedSimplexBoundary_signed_relation (n := 3) τ

def FifthHurewicz.normalizedSixSimplex {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (smp : FirstHurewicz.SingularSimplex X 6) : BasedSixSimplex x :=
  BasedSixSimplex.ofFaces (normalizedSixSimplexMap x smp)
    (normalizedSixSimplexMap_face_boundary x smp)

@[simp]
theorem FifthHurewicz.normalizedSixSimplex_face {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) (i : Fin 7) :
    basedSixSimplexFace (normalizedSixSimplex x smp) i =
      normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i)) := by
  apply Subtype.ext
  exact normalizedSixSimplexMap_face x smp i

theorem FifthHurewicz.normalizedFiveSimplex_boundary_relation {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 6) :
    ∑ i : Fin 7,
        (-1 : ℤ) ^ i.val •
          basedFiveSimplexClass
            (normalizedFiveSimplex x (smp.comp (FirstHurewicz.simplexFace 5 i))) =
      0 := by
  simpa only [normalizedSixSimplex_face] using
    basedSixSimplex_signed_relation (normalizedSixSimplex x smp)

theorem FifthHurewicz.fiveSimplexClassOperator_boundary {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (b : FirstHurewicz.Chains X 6) :
    fiveSimplexClassOperator x (((FirstHurewicz.singularComplex X).d 6 5).hom b) = 0 := by
  have h : (fiveSimplexClassOperator x).comp ((FirstHurewicz.singularComplex X).d 6 5).hom = 0 := by
    apply FirstHurewicz.chainMap_ext X 6
    intro smp
    simp only [LinearMap.comp_apply, FirstHurewicz.boundary_simplex, map_sum, map_zsmul,
      fiveSimplexClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedFiveSimplex_boundary_relation x smp
  exact LinearMap.congr_fun h b

def FifthHurewicz.normalizedCube {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (p : GenLoop (Fin 5) X x) : GenLoop (Fin 5) X x :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) p

theorem FifthHurewicz.normalizedCube_cell {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)]
    (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 5)) :
    (normalizedCube x p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e) =
      (normalizedFiveSimplex x
          (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))).val :=
  HigherHurewicz.CubeGluing.coherentCubeEndpoint_cell (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) p e

def FifthHurewicz.normalizationCubeHomotopy {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    p.val.HomotopyRel (normalizedCube x p).val (Cube.boundary (Fin 5)) :=
  HigherHurewicz.CubeGluing.coherentCubeHomotopy (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) (normalizationFiveSimplexHomotopy_zero x) p

theorem FifthHurewicz.normalizedCube_internalBased {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) (u : Fin 5 → (unitInterval)) (i j : Fin 5)
    (hij : i ≠ j) (hu : u i = u j) : normalizedCube x p u = x :=
  HigherHurewicz.coherentCubeEndpoint_internalBased (normalizationFourSimplexHomotopy x)
    (normalizationFiveSimplexHomotopy x) (normalizationHomotopy_face x)
    (normalizationFourSimplexHomotopy_const x) (normalizationFourSimplexHomotopy_endpoint x) p u i
    j hij hu

theorem FifthHurewicz.normalizedCube_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 5)) :
    HigherHurewicz.NativeSubdivision.nativeBasedCubeSimplex (normalizedCube x p)
        (normalizedCube_internalBased x p) e =
      normalizedFiveSimplex x (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

abbrev FifthHurewicz.Remaining :=
  { j : Fin 5 // j ≠ 0 }

def FifthHurewicz.remainingCoordinates : C(Fin 4 → (unitInterval), Remaining → (unitInterval))
    where
  toFun u j := u (j.val.pred j.property)
  continuous_toFun := by fun_prop

@[simp]
theorem FifthHurewicz.remainingCoordinates_succ (u : Fin 4 → (unitInterval)) (i : Fin 4) :
    remainingCoordinates u ⟨i.succ, Fin.succ_ne_zero i⟩ = u i := by simp [remainingCoordinates]

theorem FifthHurewicz.remainingCoordinates_boundary {u : Fin 4 → (unitInterval)}
    (h : u ∈ Cube.boundary (Fin 4)) : remainingCoordinates u ∈ Cube.boundary Remaining := by
  obtain ⟨i, hi⟩ := h
  exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simpa using hi⟩

abbrev FifthHurewicz.BasedLoopSpace {X : Type} [TopologicalSpace X] (x : X) :=
  GenLoop Remaining X x

def FifthHurewicz.evaluation {X : Type} [TopologicalSpace X] (x : X) :
    C(BasedLoopSpace x × (Fin 4 → (unitInterval)), X)
    where
  toFun z := z.1 (remainingCoordinates z.2)
  continuous_toFun := by fun_prop

theorem FifthHurewicz.evaluation_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p : BasedLoopSpace x) (u : Fin 4 → (unitInterval)) (hu : u ∈ Cube.boundary (Fin 4)) :
    evaluation x (p, u) = x :=
  GenLoop.boundary p _ (remainingCoordinates_boundary hu)

theorem FifthHurewicz.evaluation_comp_boundary {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (x : X) (f : C(A, Fin 4 → (unitInterval)))
    (hf : ∀ a, f a ∈ Cube.boundary (Fin 4)) :
    (evaluation x).comp ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) =
      ContinuousMap.const (BasedLoopSpace x × A) x := by
  ext z
  exact evaluation_boundary x z.1 (f z.2) (hf z.2)

def FifthHurewicz.cubeCoordinates :
    C((unitInterval) × (Fin 4 → (unitInterval)), Fin 5 → (unitInterval))
    where
  toFun z := Cube.insertAt (0 : Fin 5) (z.1, remainingCoordinates z.2)
  continuous_toFun := by fun_prop

@[simp]
theorem FifthHurewicz.cubeCoordinates_zero (z : (unitInterval) × (Fin 4 → (unitInterval))) :
    cubeCoordinates z 0 = z.1 := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply]

@[simp]
theorem FifthHurewicz.cubeCoordinates_succ (z : (unitInterval) × (Fin 4 → (unitInterval)))
    (i : Fin 4) : cubeCoordinates z i.succ = z.2 i := by
  simp [cubeCoordinates, Cube.insertAt, Homeomorph.funSplitAt_symm_apply, remainingCoordinates]

def FifthHurewicz.cubeMap {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    C((unitInterval) × (Fin 4 → (unitInterval)), X) :=
  p.val.comp cubeCoordinates

theorem FifthHurewicz.evaluation_comp_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    (evaluation x).comp
        ((GenLoop.toLoop (0 : Fin 5) p).toContinuousMap.prodMap
          (ContinuousMap.id (Fin 4 → (unitInterval)))) =
      cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.remainingCubeSideFirst (t : (unitInterval)) :
    C(Fin 3 → (unitInterval), Fin 4 → (unitInterval)) :=
  FourthHurewicz.cubeCoordinates.comp (PeriodTorusHigherHomology.crossInsertLeft t)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.remainingCubeSide {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 3 → (unitInterval))) : C((unitInterval) × A, Fin 4 → (unitInterval)) :=
  FourthHurewicz.cubeCoordinates.comp ((ContinuousMap.id (unitInterval)).prodMap f)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.remainingCubeSideFirst_boundary (t : (unitInterval)) (ht : t = 0 ∨ t = 1)
    (u : Fin 3 → (unitInterval)) : remainingCubeSideFirst t u ∈ Cube.boundary (Fin 4) := by
  refine ⟨0, ?_⟩
  change FourthHurewicz.cubeCoordinates (t, u) 0 = 0 ∨ FourthHurewicz.cubeCoordinates (t, u) 0 = 1
  simpa only [FourthHurewicz.cubeCoordinates_zero] using ht

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.remainingCubeSide_boundary {A : Type} [TopologicalSpace A]
    (f : C(A, Fin 3 → (unitInterval))) (hf : ∀ a, f a ∈ Cube.boundary (Fin 3))
    (z : (unitInterval) × A) : remainingCubeSide f z ∈ Cube.boundary (Fin 4) := by
  obtain ⟨i, hi⟩ := hf z.2
  refine ⟨i.succ, ?_⟩
  change
    FourthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 0 ∨
      FourthHurewicz.cubeCoordinates (z.1, f z.2) i.succ = 1
  simpa only [FourthHurewicz.cubeCoordinates_succ] using hi

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.remainingCubeSide_chain {A : Type} [TopologicalSpace A] (k : ℕ)
    (f : C(A, Fin 3 → (unitInterval))) (b : FirstHurewicz.Chains A k) :
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) k
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (remainingCubeSide f) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) A k
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval)) f k
      SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (unitInterval)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.productThreeIntervalChain :
    FirstHurewicz.Chains ((unitInterval) × ((unitInterval) × (unitInterval))) 3 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) ((unitInterval) × (unitInterval)) 2
    SecondHurewicz.intervalChain SecondHurewicz.productSquareChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.remainingCubeChain_boundary :
    ((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
        FourthHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (remainingCubeSideFirst 1) 3 ThirdHurewicz.fundamentalCubeChain -
          FirstHurewicz.inducedChain (remainingCubeSideFirst 0) 3
            ThirdHurewicz.fundamentalCubeChain -
        (FirstHurewicz.inducedChain (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 1))
              3 ThirdHurewicz.productCubeChain -
            FirstHurewicz.inducedChain
              (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst 0)) 3
              ThirdHurewicz.productCubeChain -
          (FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 1)))
                3 productThreeIntervalChain -
              FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft 0)))
                3 productThreeIntervalChain -
            (FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 1)))
                3 productThreeIntervalChain -
              FirstHurewicz.inducedChain
                (remainingCubeSide
                  (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight 0)))
                3 productThreeIntervalChain))) := by
  have hpoint (t : (unitInterval)) :
    PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 3 → (unitInterval)) 3
        (FirstHurewicz.pointChain t) ThirdHurewicz.fundamentalCubeChain =
      FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 3
        ThirdHurewicz.fundamentalCubeChain := by
    rw [FirstHurewicz.pointChain, PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left]
    rfl
  have hfirst (t : (unitInterval)) :
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 3
        (FirstHurewicz.inducedChain (PeriodTorusHigherHomology.crossInsertLeft t) 3
          ThirdHurewicz.fundamentalCubeChain) =
      FirstHurewicz.inducedChain (remainingCubeSideFirst t) 3
        ThirdHurewicz.fundamentalCubeChain := by
    rw [remainingCubeSideFirst, FirstHurewicz.inducedChain_comp]
    rfl
  rw [FourthHurewicz.fundamentalCubeChain, ← FirstHurewicz.inducedChain_boundary]
  change
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 3
        (((FirstHurewicz.singularComplex ((unitInterval) × (Fin 3 → (unitInterval)))).d 4 3).hom
          (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 3
            SecondHurewicz.intervalChain ThirdHurewicz.fundamentalCubeChain)) =
      _
  rw [PeriodTorusHigherHomology.crossProductEdge_boundary 2]
  change
    FirstHurewicz.inducedChain FourthHurewicz.cubeCoordinates 3
        (PeriodTorusHigherHomology.crossProductZeroLeft (unitInterval) (Fin 3 → (unitInterval)) 3
            (FirstHurewicz.boundaryOne (unitInterval) SecondHurewicz.intervalChain)
            ThirdHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 3 → (unitInterval)) 2
            SecondHurewicz.intervalChain
            (((FirstHurewicz.singularComplex (Fin 3 → (unitInterval))).d 3 2).hom
              ThirdHurewicz.fundamentalCubeChain)) =
      _
  rw [SecondHurewicz.intervalChain_boundary, FourthHurewicz.remainingCubeChain_boundary]
  simp only [map_sub, LinearMap.sub_apply, hpoint, hfirst, remainingCubeSide_chain]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.evaluated_edge_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 4 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 4)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) k
          a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 1)
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (BasedLoopSpace x)) f k a
      b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 1)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.evaluated_triangle_boundaryMap {X A : Type} [TopologicalSpace X]
    [TopologicalSpace A] (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) (k : ℕ)
    (b : FirstHurewicz.Chains A k) (f : C(A, Fin 4 → (unitInterval)))
    (hf : ∀ t, f t ∈ Cube.boundary (Fin 4)) :
    FirstHurewicz.inducedChain (evaluation x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 4 → (unitInterval)) k a (FirstHurewicz.inducedChain f k b)) =
      FirstHurewicz.inducedChain (ContinuousMap.const (BasedLoopSpace x × A) x) (k + 2)
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) A k a b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductTriangle_natural (ContinuousMap.id (BasedLoopSpace x)) f
      k a b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) (k + 2)).comp
          (FirstHurewicz.inducedChain ((ContinuousMap.id (BasedLoopSpace x)).prodMap f) (k + 2)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_boundary x f hf]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.evaluated_edge_cubeBoundary_cancel {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 3
          a
          (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
            FourthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 ThirdHurewicz.fundamentalCubeChain (remainingCubeSideFirst t)
      (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 ThirdHurewicz.productCubeChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideLeft_boundary t ht)))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_edge_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideRight_boundary t ht)))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl),
    hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.evaluated_triangle_cubeBoundary_cancel {X : Type} [TopologicalSpace X]
    (x : X) (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 4 → (unitInterval)) 3 a
          (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
            FourthHurewicz.fundamentalCubeChain)) =
      0 := by
  have hF (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 ThirdHurewicz.fundamentalCubeChain
      (remainingCubeSideFirst t) (remainingCubeSideFirst_boundary t ht)
  have hS (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 ThirdHurewicz.productCubeChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSideFirst t))
      (remainingCubeSide_boundary _ (FourthHurewicz.remainingCubeSideFirst_boundary t ht))
  have hL (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideLeft t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideLeft_boundary t ht)))
  have hR (t : (unitInterval)) (ht : t = 0 ∨ t = 1) :=
    evaluated_triangle_boundaryMap x a 3 productThreeIntervalChain
      (remainingCubeSide (FourthHurewicz.remainingCubeSide (ThirdHurewicz.squareSideRight t)))
      (remainingCubeSide_boundary _
        (FourthHurewicz.remainingCubeSide_boundary _
          (ThirdHurewicz.squareSideRight_boundary t ht)))
  simp only [remainingCubeChain_boundary, map_sub, hF 1 (Or.inr rfl), hF 0 (Or.inl rfl),
    hS 1 (Or.inr rfl), hS 0 (Or.inl rfl), hL 1 (Or.inr rfl), hL 0 (Or.inl rfl), hR 1 (Or.inr rfl),
    hR 0 (Or.inl rfl), sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.suspensionOne {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 1 →ₗ[ℤ] FirstHurewicz.Chains X 5 :=
  (FirstHurewicz.inducedChain (evaluation x) 5).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 4)
      FourthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem FifthHurewicz.suspensionOne_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1) :
    suspensionOne x a =
      FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 4
          a FourthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.suspensionTwo {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains (BasedLoopSpace x) 2 →ₗ[ℤ] FirstHurewicz.Chains X 6 :=
  (FirstHurewicz.inducedChain (evaluation x) 6).comp
    (PeriodTorusHigherHomology.integerBilinearRightApply
      (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x) (Fin 4 → (unitInterval))
        4)
      FourthHurewicz.fundamentalCubeChain)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem FifthHurewicz.suspensionTwo_apply {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    suspensionTwo x a =
      FirstHurewicz.inducedChain (evaluation x) 6
        (PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
          (Fin 4 → (unitInterval)) 4 a FourthHurewicz.fundamentalCubeChain) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.boundaryFive_suspensionOne_of_cycle {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 1)
    (ha : FirstHurewicz.boundaryOne (BasedLoopSpace x) a = 0) :
    ((FirstHurewicz.singularComplex X).d 5 4).hom (suspensionOne x a) = 0 := by
  rw [suspensionOne_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductEdge_boundary 3]
  change
    FirstHurewicz.inducedChain (evaluation x) 4
        (PeriodTorusHigherHomology.crossProductZeroLeft (BasedLoopSpace x)
            (Fin 4 → (unitInterval)) 4 (FirstHurewicz.boundaryOne (BasedLoopSpace x) a)
            FourthHurewicz.fundamentalCubeChain -
          PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 3
            a
            (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
              FourthHurewicz.fundamentalCubeChain)) =
      0
  rw [ha, map_zero, LinearMap.zero_apply, zero_sub, map_neg, evaluated_edge_cubeBoundary_cancel,
    neg_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.boundarySix_suspensionTwo {X : Type} [TopologicalSpace X] (x : X)
    (a : FirstHurewicz.Chains (BasedLoopSpace x) 2) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom (suspensionTwo x a) =
      suspensionOne x (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) := by
  rw [suspensionTwo_apply, ← FirstHurewicz.inducedChain_boundary,
    PeriodTorusHigherHomology.crossProductTriangle_boundary 3]
  change
    FirstHurewicz.inducedChain (evaluation x) 5
        (PeriodTorusHigherHomology.crossProductEdge (BasedLoopSpace x) (Fin 4 → (unitInterval)) 4
            (FirstHurewicz.boundaryTwo (BasedLoopSpace x) a) FourthHurewicz.fundamentalCubeChain +
          PeriodTorusHigherHomology.crossProductTriangle (BasedLoopSpace x)
            (Fin 4 → (unitInterval)) 3 a
            (((FirstHurewicz.singularComplex (Fin 4 → (unitInterval))).d 4 3).hom
              FourthHurewicz.fundamentalCubeChain)) =
      _
  rw [map_add, evaluated_triangle_cubeBoundary_cancel, add_zero]
  rfl

def FifthHurewicz.pathCubeCycle {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 5
    (suspensionOne x (FirstHurewicz.pathChain p))
    (boundaryFive_suspensionOne_of_cycle x (FirstHurewicz.pathChain p)
      (FirstHurewicz.boundaryOne_loop p))

@[simp]
theorem FifthHurewicz.pathCubeCycle_val {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    (pathCubeCycle x p).1 = suspensionOne x (FirstHurewicz.pathChain p) :=
  rfl

def FifthHurewicz.pathCubeClass {X : Type} [TopologicalSpace X] (x : X)
    (p : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    SingularMayerVietoris.SingularHomology X 5 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
    (pathCubeCycle x p)

theorem FifthHurewicz.pathCube_homotopy_boundary {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom
        (suspensionTwo x (FirstHurewicz.homotopyChain H)) =
      (pathCubeCycle x p).1 - (pathCubeCycle x q).1 := by
  rw [boundarySix_suspensionTwo, FirstHurewicz.boundaryTwo_loopHomotopy, map_sub]
  rfl

theorem FifthHurewicz.pathCubeClass_homotopy {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (H : p.Homotopy q) :
    pathCubeClass x p = pathCubeClass x q :=
  (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 5 _
        _).mpr
    ⟨suspensionTwo x (FirstHurewicz.homotopyChain H), pathCube_homotopy_boundary x H⟩

theorem FifthHurewicz.pathCubeClass_homotopic {X : Type} [TopologicalSpace X] (x : X)
    {p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const} (h : p.Homotopic q) :
    pathCubeClass x p = pathCubeClass x q := by
  obtain ⟨H⟩ := h
  exact pathCubeClass_homotopy x H

@[simp]
theorem FifthHurewicz.pathCubeClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathCubeClass x (Path.refl (GenLoop.const : BasedLoopSpace x)) = 0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff (FirstHurewicz.singularComplex X)
        5 _).mpr
  refine
    ⟨suspensionTwo x (FirstHurewicz.constantTriangleChain (GenLoop.const : BasedLoopSpace x)), ?_⟩
  rw [boundarySix_suspensionTwo, FirstHurewicz.boundaryTwo_constantTriangleChain]
  rfl

theorem FifthHurewicz.pathCube_concat_boundary {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    ((FirstHurewicz.singularComplex X).d 6 5).hom
        (-suspensionTwo x (FirstHurewicz.concatChain p q)) =
      (pathCubeCycle x (p.trans q)).1 - ((pathCubeCycle x p).1 + (pathCubeCycle x q).1) := by
  rw [map_neg, boundarySix_suspensionTwo, FirstHurewicz.boundaryTwo_concatChain, map_add, map_sub]
  simp only [pathCubeCycle_val]
  abel

theorem FifthHurewicz.pathCubeClass_trans {X : Type} [TopologicalSpace X] (x : X)
    (p q : Path (GenLoop.const : BasedLoopSpace x) GenLoop.const) :
    pathCubeClass x (p.trans q) = pathCubeClass x p + pathCubeClass x q := by
  unfold pathCubeClass
  rw [← map_add]
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 5 _
        _).mpr
  exact ⟨-suspensionTwo x (FirstHurewicz.concatChain p q), pathCube_concat_boundary x p q⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.productCubeChain :
    FirstHurewicz.Chains ((unitInterval) × (Fin 4 → (unitInterval))) 5 :=
  PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 4
    SecondHurewicz.intervalChain FourthHurewicz.fundamentalCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.fundamentalCubeChain : FirstHurewicz.Chains (Fin 5 → (unitInterval)) 5 :=
  FirstHurewicz.inducedChain cubeCoordinates 5 productCubeChain

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.suspensionOne_toLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 5) p)) =
      FirstHurewicz.inducedChain (cubeMap p) 5 productCubeChain := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural
      (GenLoop.toLoop (0 : Fin 5) p).toContinuousMap (ContinuousMap.id (Fin 4 → (unitInterval))) 4
      SecondHurewicz.intervalChain FourthHurewicz.fundamentalCubeChain
  rw [SecondHurewicz.induced_intervalChain, FirstHurewicz.inducedChain_id,
    LinearMap.id_apply] at h
  rw [suspensionOne_apply, ← h]
  change
    ((FirstHurewicz.inducedChain (evaluation x) 5).comp
          (FirstHurewicz.inducedChain
            ((GenLoop.toLoop (0 : Fin 5) p).toContinuousMap.prodMap
              (ContinuousMap.id (Fin 4 → (unitInterval))))
            5))
        productCubeChain =
      _
  rw [← FirstHurewicz.inducedChain_comp, evaluation_comp_toLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.cubeChain {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    FirstHurewicz.Chains X 5 :=
  suspensionOne x (FirstHurewicz.pathChain (GenLoop.toLoop (0 : Fin 5) p))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.cubeChain_eq_induced {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    cubeChain p = FirstHurewicz.inducedChain p.val 5 fundamentalCubeChain := by
  rw [cubeChain, suspensionOne_toLoop]
  change
    FirstHurewicz.inducedChain (p.val.comp cubeCoordinates) 5 productCubeChain =
      ((FirstHurewicz.inducedChain p.val 5).comp (FirstHurewicz.inducedChain cubeCoordinates 5))
        productCubeChain
  rw [FirstHurewicz.inducedChain_comp]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.cubeCycle {X : Type} [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  pathCubeCycle x (GenLoop.toLoop (0 : Fin 5) p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.cubeHomologyClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) : SingularMayerVietoris.SingularHomology X 5 :=
  SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
    (cubeCycle p)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.cubeHomologyClass_eq_pathCubeClass {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    cubeHomologyClass p = pathCubeClass x (GenLoop.toLoop (0 : Fin 5) p) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.cubeHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 5) X x} (h : GenLoop.Homotopic p q) :
    cubeHomologyClass p = cubeHomologyClass q :=
  pathCubeClass_homotopic x (GenLoop.homotopicTo (0 : Fin 5) h)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.toLoop_const {X : Type} [TopologicalSpace X] {x : X} :
    GenLoop.toLoop (0 : Fin 5) (GenLoop.const : GenLoop (Fin 5) X x) =
      Path.refl (GenLoop.const : BasedLoopSpace x) := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro u
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
theorem FifthHurewicz.cubeHomologyClass_const {X : Type} [TopologicalSpace X] {x : X} :
    cubeHomologyClass (GenLoop.const : GenLoop (Fin 5) X x) = 0 := by
  rw [cubeHomologyClass_eq_pathCubeClass, toLoop_const, pathCubeClass_refl]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.toLoop_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 5) X x) :
    GenLoop.toLoop (0 : Fin 5) (GenLoop.transAt (0 : Fin 5) p q) =
      (GenLoop.toLoop (0 : Fin 5) p).trans (GenLoop.toLoop (0 : Fin 5) q) := by
  have h :=
    congrArg (GenLoop.toLoop (0 : Fin 5))
      (GenLoop.fromLoop_trans_toLoop (i := (0 : Fin 5)) (p := p) (q := q))
  rw [GenLoop.to_from] at h
  exact h.symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.cubeHomologyClass_transAt {X : Type} [TopologicalSpace X] {x : X}
    (p q : GenLoop (Fin 5) X x) :
    cubeHomologyClass (GenLoop.transAt (0 : Fin 5) p q) =
      cubeHomologyClass p + cubeHomologyClass q := by
  simp only [cubeHomologyClass_eq_pathCubeClass, toLoop_transAt, pathCubeClass_trans]

theorem FifthHurewicz.CubeSubdivision.cubeCoordinates_boundary_right (s : (unitInterval))
    {u : Fin 4 → (unitInterval)} (hu : u ∈ Cube.boundary (Fin 4)) :
    FifthHurewicz.cubeCoordinates (s, u) ∈ Cube.boundary (Fin 5) := by
  obtain ⟨i, hi⟩ := hu
  exact ⟨i.succ, by simpa only [FifthHurewicz.cubeCoordinates_succ] using hi⟩

def FifthHurewicz.CubeSubdivision.curryLoop {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) :
    GenLoop (Fin 4) C((unitInterval), X) (ContinuousMap.const (unitInterval) x) :=
  ⟨((FifthHurewicz.cubeMap p).comp ContinuousMap.prodSwap).curry,
    by
    intro u hu
    apply ContinuousMap.ext
    intro s
    exact GenLoop.boundary p _ (cubeCoordinates_boundary_right s hu)⟩

theorem FifthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 5) X x) :
    (FourthHurewicz.CubeSubdivision.evalLeft X).comp
        ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      FifthHurewicz.cubeMap p := by
  ext z
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.CubeSubdivision.evalLeft_crossProductEdge_curryLoop {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) (n : ℕ)
    (b : FirstHurewicz.Chains (Fin 4 → (unitInterval)) n) :
    FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) n
          SecondHurewicz.intervalChain (FirstHurewicz.inducedChain (curryLoop p).val n b)) =
      FirstHurewicz.inducedChain (FifthHurewicz.cubeMap p) (n + 1)
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) n
          SecondHurewicz.intervalChain b) := by
  have h :=
    PeriodTorusHigherHomology.crossProductEdge_natural (ContinuousMap.id (unitInterval))
      (curryLoop p).val n SecondHurewicz.intervalChain b
  rw [FirstHurewicz.inducedChain_id, LinearMap.id_apply] at h
  rw [← h]
  change
    ((FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) (n + 1)).comp
          (FirstHurewicz.inducedChain
            ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) (n + 1)))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp, evalLeft_comp_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.CubeSubdivision.cubeChain_eq_curriedCrossProduct {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 5
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 4
          SecondHurewicz.intervalChain (FourthHurewicz.cubeChain (curryLoop p))) := by
  rw [FourthHurewicz.cubeChain_eq_induced, evalLeft_crossProductEdge_curryLoop,
    FifthHurewicz.cubeChain_eq_induced, FifthHurewicz.fundamentalCubeChain]
  change
    (FirstHurewicz.inducedChain p.val 5)
        ((FirstHurewicz.inducedChain FifthHurewicz.cubeCoordinates 5)
          FifthHurewicz.productCubeChain) =
      (FirstHurewicz.inducedChain (p.val.comp FifthHurewicz.cubeCoordinates) 5)
        FifthHurewicz.productCubeChain
  rw [FirstHurewicz.inducedChain_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
def FifthHurewicz.CubeSubdivision.intervalFourSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) : FirstHurewicz.Chains X 5 :=
  FirstHurewicz.inducedChain (FourthHurewicz.CubeSubdivision.evalLeft X) 5
    (PeriodTorusHigherHomology.crossProductEdge (unitInterval) C((unitInterval), X) 4
      SecondHurewicz.intervalChain
      (FirstHurewicz.simplexChain C((unitInterval), X) 4
        ((curryLoop p).val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.CubeSubdivision.intervalFourSimplexChain_eq_original {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) :
    intervalFourSimplexChain p e =
      FirstHurewicz.inducedChain (FifthHurewicz.cubeMap p) 5
        (PeriodTorusHigherHomology.crossProductEdge (unitInterval) (Fin 4 → (unitInterval)) 4
          SecondHurewicz.intervalChain
          (FirstHurewicz.simplexChain (Fin 4 → (unitInterval)) 4
            (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [intervalFourSimplexChain, ← FirstHurewicz.inducedChain_simplex,
    evalLeft_crossProductEdge_curryLoop]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_prisms {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e • intervalFourSimplexChain p e := by
  rw [cubeChain_eq_curriedCrossProduct, FourthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices]
  simp only [map_sum, map_zsmul, intervalFourSimplexChain]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.CubeSubdivision.prismCubeMap_four (e : Equiv.Perm (Fin 4)) :
    FifthHurewicz.cubeCoordinates.comp
        ((FirstHurewicz.pathSimplex Path.id).prodMap
          (HigherHurewicz.CubeTriangulation.cubeSimplex e)) =
      FourthHurewicz.CubeSubdivision.prismCubeMap e := by
  apply ContinuousMap.ext
  intro z
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact FifthHurewicz.cubeCoordinates_zero _
  · change
      FifthHurewicz.cubeCoordinates
          (FirstHurewicz.pathSimplex Path.id z.1,
            HigherHurewicz.CubeTriangulation.cubeSimplex e z.2)
          j.succ =
        _
    rw [FifthHurewicz.cubeCoordinates_succ]
    rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
theorem FifthHurewicz.CubeSubdivision.intervalFourSimplexChain_eq_prismCubeRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) (e : Equiv.Perm (Fin 4)) :
    intervalFourSimplexChain p e =
      FourthHurewicz.CubeSubdivision.prismCubeRealization p.val e 5
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 4
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 5 => j))) := by
  rw [intervalFourSimplexChain_eq_original, SecondHurewicz.intervalChain, FirstHurewicz.pathChain,
    PeriodTorusHigherHomology.crossProductEdge_simplex,
    FourthHurewicz.CubeSubdivision.prismCubeRealization_edgeCrossProduct]
  change
    ((FirstHurewicz.inducedChain (FifthHurewicz.cubeMap p) 5).comp
          (FirstHurewicz.inducedChain
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))
            5))
        _ =
      _
  rw [← FirstHurewicz.inducedChain_comp]
  change
    FirstHurewicz.inducedChain
        (p.val.comp
          (FifthHurewicz.cubeCoordinates.comp
            ((FirstHurewicz.pathSimplex Path.id).prodMap
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))))
        5 _ =
      _
  rw [prismCubeMap_four]

theorem FifthHurewicz.CubeSubdivision.cubeChain_eq_orientedPrismRealization {X : Type}
    [TopologicalSpace X] {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      FourthHurewicz.CubeSubdivision.orientedPrismRealization p.val 5
        (PeriodTorusHigherHomology.formalEdgeCrossProduct 4
          (SingularMayerVietoris.formalSimplex (fun i : Fin 2 => i))
          (SingularMayerVietoris.formalSimplex (fun j : Fin 5 => j))) := by
  rw [cubeChain_eq_sum_prisms, FourthHurewicz.CubeSubdivision.orientedPrismRealization_eq_sum]
  simp only [intervalFourSimplexChain_eq_prismCubeRealization]

theorem FifthHurewicz.CubeSubdivision.cubeChain_eq_sum_simplices {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 5) X x) :
    FifthHurewicz.cubeChain p =
      ∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 5
            (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e)) := by
  rw [cubeChain_eq_orientedPrismRealization,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_edge_eq_standard (n := 2) p,
    FourthHurewicz.CubeSubdivision.orientedPrismRealization_standardPrism]

theorem FifthHurewicz.fiveSimplexClassOperator_cubeChain_sum {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    fiveSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          basedFiveSimplexClass
            (normalizedFiveSimplex x
              (p.val.comp (HigherHurewicz.CubeTriangulation.cubeSimplex e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, fiveSimplexClassOperator_simplex]

theorem FifthHurewicz.fiveSimplexClassOperator_cubeChain {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    fiveSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 5 X x) := by
  rw [fiveSimplexClassOperator_cubeChain_sum]
  calc
    _ = Additive.ofMul (⟦normalizedCube x p⟧ : π_ 5 X x) := by
      simpa only [normalizedCube_simplex, basedFiveSimplexClass] using
        (HigherHurewicz.NativeSubdivision.nativeCubeSubdivision_class (normalizedCube x p)
            (normalizedCube_internalBased x p)).symm
    _ = _ :=
      congrArg Additive.ofMul
        (Quotient.sound
          (show GenLoop.Homotopic (normalizedCube x p) p from
            ⟨(normalizationCubeHomotopy x p).symm⟩))

def FifthHurewicz.basedFiveSimplexChain {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : FirstHurewicz.Chains X 5 :=
  HigherHurewicz.correctedSimplexChain 5 x τ.val

def FifthHurewicz.basedFiveSimplexCycle {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  HigherHurewicz.correctedSimplexCycle 4 x τ.val (basedFiveSimplex_face τ)

theorem FifthHurewicz.basedFiveSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    (∑ e : Equiv.Perm (Fin 5),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 5
            ((basedFiveSimplexLoop τ).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedFiveSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 3) τ

def HigherHurewicz.normalizedCycleAssignment {X : Type} [TopologicalSpace X] (n : ℕ) (x : X)
    (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x) :
    FirstHurewicz.Chains X (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1) :=
  FirstHurewicz.chainLift X (n + 1) fun smp =>
    correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp))

@[simp]
theorem HigherHurewicz.normalizedCycleAssignment_simplex {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (smp : FirstHurewicz.SingularSimplex X (n + 1)) :
    normalizedCycleAssignment n x f (FirstHurewicz.simplexChain X (n + 1) smp) =
      correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp)) :=
  FirstHurewicz.chainLift_simplex X (n + 1) _ smp

theorem HigherHurewicz.normalizedCycleAssignment_val {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (c : FirstHurewicz.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      FirstHurewicz.chainLift X (n + 1)
        (fun smp =>
          FirstHurewicz.simplexChain X (n + 1) (f smp).val - constantSimplexChain (n + 1) x)
        c := by
  have h :
    (SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X)
            (n + 1)).subtype.comp
        (normalizedCycleAssignment n x f) =
      FirstHurewicz.chainLift X (n + 1)
        (fun smp =>
          FirstHurewicz.simplexChain X (n + 1) (f smp).val - constantSimplexChain (n + 1) x) := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, normalizedCycleAssignment_simplex,
      correctedSimplexCycle_val, FirstHurewicz.chainLift_simplex]
  exact LinearMap.congr_fun h c

theorem HigherHurewicz.normalizedCycleAssignment_val_endpoint {X : Type} [TopologicalSpace X]
    (n : ℕ) (x : X)
    (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (c : FirstHurewicz.Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 c -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c •
          constantSimplexChain (n + 1) x := by
  rw [normalizedCycleAssignment_val, SecondHurewicz.SimplyConnected.chainLift_sub_constant]
  have hmap :
    FirstHurewicz.chainLift X (n + 1)
        (fun smp => FirstHurewicz.simplexChain X (n + 1) (f smp).val) =
      SecondHurewicz.SimplyConnected.simplexEndpointOperator (n + 1) H' 1 := by
    apply FirstHurewicz.chainMap_ext X (n + 1)
    intro smp
    rw [FirstHurewicz.chainLift_simplex,
      SecondHurewicz.SimplyConnected.simplexEndpointOperator_simplex, hf]
  rw [hmap]

theorem HigherHurewicz.normalizedCycleAssignment_evenCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (heven : Even (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val = straightenedCycle n H H' hface c := by
  apply Subtype.ext
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf,
    chainAugmentation_evenCycle X (n + 1) heven (Nat.zero_lt_succ n), zero_smul, sub_zero,
    straightenedCycle_val]

theorem HigherHurewicz.normalizedCycleAssignment_oddCycle {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (hodd : Odd (n + 1))
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    normalizedCycleAssignment n x f c.val =
      straightenedCycle n H H' hface c -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c.val •
          constantSimplexCycle (n + 1) x hodd := by
  apply Subtype.ext
  change
    (normalizedCycleAssignment n x f c.val).val =
      (straightenedCycle n H H' hface c).val -
        SecondHurewicz.SimplyConnected.chainAugmentation X (n + 1) c.val •
          (constantSimplexCycle (n + 1) x hodd).val
  rw [normalizedCycleAssignment_val_endpoint n x f H' hf, straightenedCycle_val,
    constantSimplexCycle_val]

theorem HigherHurewicz.normalizedCycleAssignment_class {X : Type} [TopologicalSpace X] (n : ℕ)
    (x : X) (f : FirstHurewicz.SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)
    (H : FirstHurewicz.SingularSimplex X n → C((unitInterval) × FirstHurewicz.Simplex n, X))
    (H' :
      FirstHurewicz.SingularSimplex X (n + 1) →
        C((unitInterval) × FirstHurewicz.Simplex (n + 1), X))
    (hface : SecondHurewicz.SimplyConnected.FaceCompatibleHomotopies n H H')
    (h₀ : ∀ smp, SecondHurewicz.SimplyConnected.timeSlice (H' smp) 0 = smp)
    (hf : ∀ smp, (f smp).val = SecondHurewicz.SimplyConnected.timeSlice (H' smp) 1)
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) (n + 1)) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        (normalizedCycleAssignment n x f c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
        c := by
  by_cases heven : Even (n + 1)
  · rw [normalizedCycleAssignment_evenCycle n x f H H' hface hf heven]
    exact straightenedCycle_class n H H' hface h₀ c
  · have hodd : Odd (n + 1) := Nat.not_even_iff_odd.mp heven
    rw [normalizedCycleAssignment_oddCycle n x f H H' hface hf hodd, map_sub, map_zsmul,
      constantSimplexCycle_class, zsmul_zero, sub_zero]
    exact straightenedCycle_class n H H' hface h₀ c

def FifthHurewicz.normalizedFiveSimplexCycleOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    FirstHurewicz.Chains X 5 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5 :=
  HigherHurewicz.normalizedCycleAssignment 4 x (normalizedFiveSimplex x)

@[simp]
theorem FifthHurewicz.normalizedFiveSimplexCycleOperator_simplex {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (smp : FirstHurewicz.SingularSimplex X 5) :
    normalizedFiveSimplexCycleOperator x (FirstHurewicz.simplexChain X 5 smp) =
      basedFiveSimplexCycle (normalizedFiveSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 4 x (normalizedFiveSimplex x) smp

theorem FifthHurewicz.normalizedFiveSimplexCycleOperator_class {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5) :
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (normalizedFiveSimplexCycleOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 c := by
  apply
    HigherHurewicz.normalizedCycleAssignment_class 4 x (normalizedFiveSimplex x)
      (normalizationFourSimplexHomotopy x) (normalizationFiveSimplexHomotopy x)
      (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationFiveSimplexHomotopy_zero x smp s

def FifthHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (x : X) :
    π_ 5 X x → SingularMayerVietoris.SingularHomology X 5 :=
  Quotient.lift cubeHomologyClass (fun _ _ h => cubeHomologyClass_homotopic h)

def FifthHurewicz.hurewiczPi5 {X : Type} [TopologicalSpace X] (x : X) :
    π_ 5 X x →* Multiplicative (SingularMayerVietoris.SingularHomology X 5)
    where
  toFun a := Multiplicative.ofAdd (hurewiczFunction x a)
  map_one' := congrArg Multiplicative.ofAdd (cubeHomologyClass_const (x := x))
  map_mul' a
    b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    refine
      (congrArg (fun c : π_ 5 X x => Multiplicative.ofAdd (hurewiczFunction x c))
            (HomotopyGroup.mul_spec (i := (0 : Fin 5)) (p := p) (q := q))).trans
        ?_
    change
      Multiplicative.ofAdd (cubeHomologyClass (GenLoop.transAt (0 : Fin 5) q p)) =
        Multiplicative.ofAdd (cubeHomologyClass p + cubeHomologyClass q)
    rw [cubeHomologyClass_transAt, add_comm]

def FifthHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (x : X) :
    Additive (π_ 5 X x) →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 5
    where
  toFun := (hurewiczPi5 x).toAdditiveLeft
  map_add' := (hurewiczPi5 x).toAdditiveLeft.map_add
  map_smul' n a := by simpa using map_intCast_smul (hurewiczPi5 x).toAdditiveLeft ℤ ℤ n a

theorem FifthHurewicz.hurewiczMap_representative {X : Type} [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin 5) X x) :
    hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 5 X x)) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (cubeCycle p) :=
  rfl

theorem FifthHurewicz.cubeChain_basedFiveSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : cubeChain (basedFiveSimplexLoop τ) = basedFiveSimplexChain τ := by
  rw [CubeSubdivision.cubeChain_eq_sum_simplices, basedFiveSimplex_simplexChain_sum]

theorem FifthHurewicz.cubeCycle_basedFiveSimplexLoop {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) : cubeCycle (basedFiveSimplexLoop τ) = basedFiveSimplexCycle τ := by
  apply Subtype.ext
  exact cubeChain_basedFiveSimplexLoop τ

theorem FifthHurewicz.hurewicz_basedFiveSimplexClass {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFiveSimplex x) :
    hurewiczMap x (basedFiveSimplexClass τ) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (basedFiveSimplexCycle τ) := by
  change
    SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (cubeCycle (basedFiveSimplexLoop τ)) =
      _
  rw [cubeCycle_basedFiveSimplexLoop]

theorem FifthHurewicz.hurewiczMap_comp_fiveSimplexClassOperator {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] :
    (hurewiczMap x).comp (fiveSimplexClassOperator x) =
      (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5).comp
        (normalizedFiveSimplexCycleOperator x) := by
  apply FirstHurewicz.chainMap_ext X 5
  intro smp
  simp only [LinearMap.comp_apply, fiveSimplexClassOperator_simplex,
    normalizedFiveSimplexCycleOperator_simplex]
  exact hurewicz_basedFiveSimplexClass (normalizedFiveSimplex x smp)

theorem FifthHurewicz.hurewiczMap_fiveSimplexClassOperator_cycle {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5) :
    hurewiczMap x (fiveSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_fiveSimplexClassOperator x) c.val
  change
    hurewiczMap x (fiveSimplexClassOperator x c.val) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5
        (normalizedFiveSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedFiveSimplexCycleOperator_class x c)

def FifthHurewicz.hurewiczInverse {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X)
    [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    SingularMayerVietoris.SingularHomology X 5 →ₗ[ℤ] Additive (π_ 5 X x) :=
  HigherHurewicz.singularHomologyDesc 5 (fiveSimplexClassOperator x)
    (fiveSimplexClassOperator_boundary x)

@[simp]
theorem FifthHurewicz.hurewiczInverse_cycleClass {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)]
    (c : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 5) :
    hurewiczInverse x
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 5 c) =
      fiveSimplexClassOperator x c.val :=
  HigherHurewicz.singularHomologyDesc_cycleClass 5 _ _ c

theorem FifthHurewicz.hurewiczMap_comp_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] : (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  HigherHurewicz.comp_singularHomologyDesc_eq_id 5 (fiveSimplexClassOperator x)
    (fiveSimplexClassOperator_boundary x) (hurewiczMap x)
    (hurewiczMap_fiveSimplexClassOperator_cycle x)

@[simp]
theorem FifthHurewicz.hurewiczMap_hurewiczInverse {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (c : SingularMayerVietoris.SingularHomology X 5) :
    hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

@[simp]
theorem FifthHurewicz.hurewiczInverse_hurewiczMap_mk {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (p : GenLoop (Fin 5) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 5 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 5 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact fiveSimplexClassOperator_cubeChain x p

@[simp]
theorem FifthHurewicz.hurewiczInverse_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] (a : Additive (π_ 5 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
      Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem FifthHurewicz.hurewiczInverse_comp_hurewiczMap {X : Type} [TopologicalSpace X]
    [SimplyConnectedSpace X] (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] : (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

def FifthHurewicz.hurewiczLinearEquiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    Additive (π_ 5 X x) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology X 5 :=
  LinearEquiv.ofLinearMap (hurewiczMap x) (hurewiczInverse x) (hurewiczMap_comp_hurewiczInverse x)
    (hurewiczInverse_comp_hurewiczMap x)

def FifthHurewicz.hurewiczPi5Equiv {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)] [Subsingleton (π_ 4 X x)] :
    π_ 5 X x ≃* Multiplicative (SingularMayerVietoris.SingularHomology X 5)
    where
  __ := hurewiczPi5 x
  invFun c := Additive.toMul (hurewiczInverse x (Multiplicative.toAdd c))
  left_inv a := congrArg Additive.toMul (hurewiczInverse_hurewiczMap x (Additive.ofMul a))
  right_inv
    c := congrArg Multiplicative.ofAdd (hurewiczMap_hurewiczInverse x (Multiplicative.toAdd c))

abbrev SixSphereCube.StandardSphere :=
  SphereHomology.UnitSphere 6

def SixSphereCube.euclideanOnePointSphereHomeomorph :
    OnePoint (EuclideanSpace ℝ (Fin 6)) ≃ₜ StandardSphere :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 6)) (ι := Fin 7) (by simp)

def SixSphereCube.sphereBasePoint : StandardSphere :=
  euclideanOnePointSphereHomeomorph (OnePoint.infty)

theorem Degree.Sphere.piTwo_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 2 SixSphereCube.StandardSphere x) :=
  SphereHomology.unitSphere_piTwo_subsingleton 3 x

theorem Degree.Sphere.piThree_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 3 SixSphereCube.StandardSphere x) := by
  let := piTwo_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 3 (by decide) (by decide)
  exact (ThirdHurewicz.hurewiczPi3Equiv x).injective.subsingleton

theorem Degree.Sphere.piFour_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 4 SixSphereCube.StandardSphere x) := by
  let := piTwo_subsingleton x
  let := piThree_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 4 (by decide) (by decide)
  exact (FourthHurewicz.hurewiczPi4Equiv x).injective.subsingleton

theorem Degree.Sphere.piFive_subsingleton (x : SixSphereCube.StandardSphere) :
    Subsingleton (π_ 5 SixSphereCube.StandardSphere x) := by
  let := piTwo_subsingleton x
  let := piThree_subsingleton x
  let := piFour_subsingleton x
  let := SphereHomology.unitSphere_homology_subsingleton 5 5 (by decide) (by decide)
  exact (FifthHurewicz.hurewiczPi5Equiv x).injective.subsingleton

end Mathoverflow1973

end
