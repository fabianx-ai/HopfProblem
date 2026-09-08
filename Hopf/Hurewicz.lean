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

theorem FourthHurewicz.basedFourSimplex_simplexChain_sum {X : Type} [TopologicalSpace X] {x : X}
    (τ : BasedFourSimplex x) :
    (∑ e : Equiv.Perm (Fin 4),
        HigherHurewicz.CubeTriangulation.cubeOrientation e •
          FirstHurewicz.simplexChain X 4
            ((basedFourSimplexLoop τ).val.comp
              (HigherHurewicz.CubeTriangulation.cubeSimplex e))) =
      basedFourSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum τ

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

theorem FourthHurewicz.CubeSubdivision.evalLeft_comp_curryLoop {X : Type} [TopologicalSpace X]
    {x : X} (p : GenLoop (Fin 4) X x) :
    (evalLeft X).comp ((ContinuousMap.id (unitInterval)).prodMap (curryLoop p).val) =
      FourthHurewicz.cubeMap p := by
  ext z
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
