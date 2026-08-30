/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Pushout
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Surjectivity consequences of the two-open-cover van Kampen theorem

This module contains the generic textbook corollary used by an iterated attachment argument: if
every loop in one chart comes from the overlap, then every loop in the union comes from the other
chart. It also provides basepoint-transport and simple-connectivity consequences used by such
arguments.
-/

@[expose] public noncomputable section

open Set Function Topology

/--
If the overlap map onto the `V` chart is surjective, the inclusion of the `U` chart into the
covered space is surjective on fundamental groups.
-/
theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomU_surjective_of_overlapHomV_surjective
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (hV : Function.Surjective D.overlapHomV) : Function.Surjective D.inclusionHomU := by
  intro gamma
  obtain ⟨q, rfl⟩ := D.pushoutEquiv.surjective gamma
  induction q using Monoid.PushoutI.induction_on with
  | of i g =>
    cases i with
    | false => exact ⟨g, (D.pushoutEquiv_of Bool.false g).symm⟩
    | true =>
      obtain ⟨a, rfl⟩ := hV g
      exact
        ⟨D.overlapHomU a,
          (DFunLike.congr_fun D.inclusionHom_compatible a).trans
            (D.pushoutEquiv_of Bool.true (D.overlapHomV a)).symm⟩
  | base a =>
    refine ⟨D.overlapHomU a, ?_⟩
    exact
      (D.pushoutEquiv_of Bool.false (D.overlapHomU a)).symm.trans
        (congrArg D.pushoutEquiv
          (Monoid.PushoutI.of_apply_eq_base D.overlapHom Bool.false a))
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

/--
The symmetric form: if the overlap map onto the `U` chart is surjective, the inclusion of the
`V` chart into the covered space is surjective on fundamental groups.
-/
theorem FundamentalGroup.VanKampen.TwoOpenCover.inclusionHomV_surjective_of_overlapHomU_surjective
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X)
    (hU : Function.Surjective D.overlapHomU) : Function.Surjective D.inclusionHomV := by
  intro gamma
  obtain ⟨q, rfl⟩ := D.pushoutEquiv.surjective gamma
  induction q using Monoid.PushoutI.induction_on with
  | of i g =>
    cases i with
    | false =>
      obtain ⟨a, rfl⟩ := hU g
      exact
        ⟨D.overlapHomV a,
          (DFunLike.congr_fun D.inclusionHom_compatible a).symm.trans
            (D.pushoutEquiv_of Bool.false (D.overlapHomU a)).symm⟩
    | true => exact ⟨g, (D.pushoutEquiv_of Bool.true g).symm⟩
  | base a =>
    refine ⟨D.overlapHomV a, ?_⟩
    exact
      (D.pushoutEquiv_of Bool.true (D.overlapHomV a)).symm.trans
        (congrArg D.pushoutEquiv
          (Monoid.PushoutI.of_apply_eq_base D.overlapHom Bool.true a))
  | mul x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

/-! ## Moving surjectivity between basepoints -/

/-- Naturality of fundamental-group basepoint change under a continuous map. -/
theorem FundamentalGroup.basepointChange_naturality {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x0 x1 : X} (f : C(X, Y)) (p : Path x0 x1) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)).toMonoidHom.comp
        (FundamentalGroup.map f x0) =
      (FundamentalGroup.map f x1).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom := by
  apply MonoidHom.ext
  intro gamma
  induction gamma using Path.Homotopic.Quotient.ind with
  | mk gamma =>
    change
      Path.Homotopic.Quotient.mk
          ((p.map f.continuous).symm.trans
            ((gamma.map f.continuous).trans (p.map f.continuous))) =
        Path.Homotopic.Quotient.mk ((p.symm.trans (gamma.trans p)).map f.continuous)
    apply congrArg Path.Homotopic.Quotient.mk
    rw [Path.map_trans, Path.map_trans, Path.map_symm]

/-- Elementwise form of `FundamentalGroup.basepointChange_naturality`. -/
theorem FundamentalGroup.basepointChange_naturality_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x0 x1 : X} (f : C(X, Y)) (p : Path x0 x1)
    (gamma : FundamentalGroup X x0) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x0 gamma) =
      FundamentalGroup.map f x1
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p gamma) :=
  DFunLike.congr_fun (FundamentalGroup.basepointChange_naturality f p) gamma

/-- Surjectivity of a fundamental-group map is independent of the chosen source basepoint. -/
theorem FundamentalGroup.map_surjective_at_of_path {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x0 x1 : X} (f : C(X, Y)) (p : Path x0 x1)
    (hf : Function.Surjective (FundamentalGroup.map f x0)) :
    Function.Surjective (FundamentalGroup.map f x1) := by
  intro gamma
  obtain ⟨delta, rfl⟩ :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)).surjective gamma
  obtain ⟨epsilon, hepsilon⟩ := hf delta
  refine ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath p epsilon, ?_⟩
  exact
    (FundamentalGroup.basepointChange_naturality_apply f p epsilon).symm.trans
      (congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)) hepsilon)

/-- Path-connected specialization of `FundamentalGroup.map_surjective_at_of_path`. -/
theorem FundamentalGroup.map_surjective_at_of_pathConnected {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] (f : C(X, Y)) (x0 x1 : X)
    (hf : Function.Surjective (FundamentalGroup.map f x0)) :
    Function.Surjective (FundamentalGroup.map f x1) :=
  FundamentalGroup.map_surjective_at_of_path f (PathConnectedSpace.somePath x0 x1) hf

/-! ## Recovering simple connectivity from one fundamental group -/

/-- Triviality of a fundamental group transports along a path between basepoints. -/
theorem FundamentalGroup.eq_one_of_path {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (hx : ∀ g : FundamentalGroup X x, g = 1)
    (g : FundamentalGroup X y) : g = 1 := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  obtain ⟨h, rfl⟩ := e.surjective g
  rw [hx h, map_one]

/--
For a path-connected space, simple connectivity is equivalent to triviality of the fundamental
group at one chosen basepoint.
-/
theorem FundamentalGroup.simplyConnectedSpace_iff_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) :
    SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 := by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    exact fun _ => Subsingleton.elim _ _
  · intro hx
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, ?_⟩
    intro y gamma
    exact
      Path.Homotopic.Quotient.eq.mp
        (FundamentalGroup.eq_one_of_path (PathConnectedSpace.somePath x y) hx
          (Path.Homotopic.Quotient.mk gamma))

/-- Constructor form of `FundamentalGroup.simplyConnectedSpace_iff_eq_one`. -/
theorem FundamentalGroup.simplyConnectedSpace_of_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hx : ∀ g : FundamentalGroup X x, g = 1) :
    SimplyConnectedSpace X :=
  (FundamentalGroup.simplyConnectedSpace_iff_eq_one x).mpr hx

/-- A two-open-cover datum already proves that its ambient space is path connected. -/
theorem FundamentalGroup.VanKampen.TwoOpenCover.pathConnectedSpace {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroup.VanKampen.TwoOpenCover X) :
    PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩
