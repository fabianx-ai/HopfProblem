/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Fundamental groups of two-simply-connected-open covers

This module packages the textbook path argument for a space covered by two simply connected
opens.  The switch class of a point in the overlap depends only on its overlap component, and a
subgroup containing every switch class is the whole fundamental group.  It also identifies a
switch class with any explicit pair of paths through the two opens.

The development is generic: it contains no distinguished space, cover, meridian, or
application-specific relator.  It extracts and normalizes legacy copies that previously lived in
application modules, reusing the path-class induction machinery in `VanKampen.Basic`.
-/

@[expose] public noncomputable section

set_option warningAsError true
set_option autoImplicit false

open Set TopologicalSpace

namespace FundamentalGroup.VanKampen

/-- Two simply connected open subsets covering a space, with a base point in their overlap. -/
structure TwoSimplyConnectedCover (X : Type*) [TopologicalSpace X] where
  U : Opens X
  V : Opens X
  cover : (U : Set X) ∪ V = Set.univ
  simplyU : IsSimplyConnected (U : Set X)
  simplyV : IsSimplyConnected (V : Set X)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

/-- Two paths contained in a simply connected set and having the same endpoints are homotopic. -/
theorem paths_homotopic_of_mem {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsSimplyConnected s) {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ s)
    (hq : ∀ t, q t ∈ s) : Path.Homotopic p q := by
  let _ : SimplyConnectedSpace s := hs
  have hx : x ∈ s := by simpa using hp 0
  have hy : y ∈ s := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact p.source
      target' := by apply Subtype.ext; exact p.target }
  let q' : Path (⟨x, hx⟩ : s) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := by apply Subtype.ext; exact q.source
      target' := by apply Subtype.ext; exact q.target }
  have h :=
    (SimplyConnectedSpace.paths_homotopic p' q').map
      (⟨Subtype.val, continuous_subtype_val⟩ : ContinuousMap s X)
  have hp' : p'.map continuous_subtype_val = p := by ext t; rfl
  have hq' : q'.map continuous_subtype_val = q := by ext t; rfl
  exact hp' ▸ hq' ▸ h

namespace TwoSimplyConnectedCover

/-- A chosen path from the base point to a point of the first open. -/
def pathU {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.U) : Path D.base x :=
  (D.simplyU.isPathConnected.joinedIn D.base D.baseU x hx).somePath

/-- A chosen path from the base point to a point of the second open. -/
def pathV {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.V) : Path D.base x :=
  (D.simplyV.isPathConnected.joinedIn D.base D.baseV x hx).somePath

theorem pathU_mem {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.U) (t : unitInterval) : D.pathU x hx t ∈ D.U :=
  JoinedIn.somePath_mem _ t

theorem pathV_mem {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (x : X) (hx : x ∈ D.V) (t : unitInterval) : D.pathV x hx t ∈ D.V :=
  JoinedIn.somePath_mem _ t

theorem pathU_trans {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    {x y : X} (hx : x ∈ D.U) (hy : y ∈ D.U) (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    (Path.Homotopic.Quotient.mk (D.pathU x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathU y hy) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  exact paths_homotopic_of_mem D.simplyU _ _ (Path.trans_mem _ _ (D.pathU_mem x hx) hp)
    (D.pathU_mem y hy)

theorem pathV_trans {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    {x y : X} (hx : x ∈ D.V) (hy : y ∈ D.V) (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    (Path.Homotopic.Quotient.mk (D.pathV x hx)).trans (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (D.pathV y hy) := by
  rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
  exact paths_homotopic_of_mem D.simplyV _ _ (Path.trans_mem _ _ (D.pathV_mem x hx) hp)
    (D.pathV_mem y hy)

/-- The loop obtained by reaching an overlap point through `U` and returning through `V`. -/
def switchClass {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (x : X) (hxU : x ∈ D.U) (hxV : x ∈ D.V) : FundamentalGroup X D.base :=
  (Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
    (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm

/-- The switch class is constant on each path component of the overlap. -/
theorem switchClass_eq_of_joinedIn {X : Type*} [TopologicalSpace X]
    (D : TwoSimplyConnectedCover X) {x y : X} (hxU : x ∈ D.U) (hxV : x ∈ D.V)
    (hyU : y ∈ D.U) (hyV : y ∈ D.V) (hxy : JoinedIn ((D.U : Set X) ∩ D.V) x y) :
    D.switchClass x hxU hxV = D.switchClass y hyU hyV := by
  let p := hxy.somePath
  have hU := D.pathU_trans hxU hyU p (fun t => (hxy.somePath_mem t).1)
  have hV := D.pathV_trans hxV hyV p (fun t => (hxy.somePath_mem t).2)
  apply PathClass.quotient_trans_right_cancel (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  change
    ((Path.Homotopic.Quotient.mk (D.pathU x hxU)).trans
            (Path.Homotopic.Quotient.mk (D.pathV x hxV)).symm).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV)) =
      ((Path.Homotopic.Quotient.mk (D.pathU y hyU)).trans
            (Path.Homotopic.Quotient.mk (D.pathV y hyV)).symm).trans
        (Path.Homotopic.Quotient.mk (D.pathV y hyV))
  rw [Path.Homotopic.Quotient.trans_assoc, ← hV, PathClass.quotient_symm_trans_cancel, hU]
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

@[simp]
theorem switchClass_base {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X) :
    D.switchClass D.base D.baseU D.baseV = 1 := by
  have hU :
      Path.Homotopic.Quotient.mk (D.pathU D.base D.baseU) =
        Path.Homotopic.Quotient.refl D.base := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact paths_homotopic_of_mem D.simplyU _ _ (D.pathU_mem _ _) (fun _ => D.baseU)
  have hV :
      Path.Homotopic.Quotient.mk (D.pathV D.base D.baseV) =
        Path.Homotopic.Quotient.refl D.base := by
    apply Path.Homotopic.Quotient.eq.mpr
    exact paths_homotopic_of_mem D.simplyV _ _ (D.pathV_mem _ _) (fun _ => D.baseV)
  simp only [switchClass, hU, hV, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def]

private theorem memV_of_not_memU {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    {x : X} (hx : x ∉ D.U) : x ∈ D.V := by
  have h : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact h.resolve_left hx

/-- A path class from the base to every point, chosen from the first open when possible. -/
private def basedSection {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (x : X) : Path.Homotopic.Quotient D.base x := by
  classical
  exact if hx : x ∈ D.U then Path.Homotopic.Quotient.mk (D.pathU x hx)
    else Path.Homotopic.Quotient.mk (D.pathV x (D.memV_of_not_memU hx))

private theorem basedSection_eq_U {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    {x : X} (hx : x ∈ D.U) :
    D.basedSection x = Path.Homotopic.Quotient.mk (D.pathU x hx) := by
  simp only [basedSection, dif_pos hx]

private theorem basedSection_eq_V {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    {x : X} (hxU : x ∉ D.U) (hxV : x ∈ D.V) :
    D.basedSection x = Path.Homotopic.Quotient.mk (D.pathV x hxV) := by
  simp only [basedSection, dif_neg hxU]

@[simp]
private theorem basedSection_base {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X) :
    D.basedSection D.base = Path.Homotopic.Quotient.refl D.base := by
  rw [D.basedSection_eq_U D.baseU]
  apply Path.Homotopic.Quotient.eq.mpr
  exact paths_homotopic_of_mem D.simplyU _ _ (D.pathU_mem _ _) (fun _ => D.baseU)

private theorem comparisonU_mem {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base)) {x : X} (hx : x ∈ D.U) :
    PathClass.pathDifference (D.basedSection x)
        (Path.Homotopic.Quotient.mk (D.pathU x hx)) ∈ H := by
  rw [D.basedSection_eq_U hx]
  simpa only [PathClass.pathDifference, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def] using H.one_mem

private theorem comparisonV_mem {X : Type*} [TopologicalSpace X] (D : TwoSimplyConnectedCover X)
    (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H)
    {x : X} (hx : x ∈ D.V) :
    PathClass.pathDifference (D.basedSection x)
        (Path.Homotopic.Quotient.mk (D.pathV x hx)) ∈ H := by
  by_cases hxU : x ∈ D.U
  · rw [D.basedSection_eq_U hxU]
    exact hH x hxU hx
  · rw [D.basedSection_eq_V hxU hx]
    simpa only [PathClass.pathDifference, Path.Homotopic.Quotient.trans_symm,
      FundamentalGroup.one_def] using H.one_mem

private theorem basedLoop_mem_of_path_in_U {X : Type*} [TopologicalSpace X]
    (D : TwoSimplyConnectedCover X) (H : Subgroup (FundamentalGroup X D.base))
    {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.U) :
    PathClass.basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈ H := by
  have hx : x ∈ D.U := by simpa using hp 0
  have hy : y ∈ D.U := by simpa using hp 1
  rw [PathClass.basedLoop_comparison D.basedSection
      (Path.Homotopic.Quotient.mk (D.pathU x hx))
      (Path.Homotopic.Quotient.mk (D.pathU y hy))
      (Path.Homotopic.Quotient.mk p) (D.pathU_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonU_mem H hy)) (D.comparisonU_mem H hx)

private theorem basedLoop_mem_of_path_in_V {X : Type*} [TopologicalSpace X]
    (D : TwoSimplyConnectedCover X) (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H)
    {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.V) :
    PathClass.basedLoop D.basedSection (Path.Homotopic.Quotient.mk p) ∈ H := by
  have hx : x ∈ D.V := by simpa using hp 0
  have hy : y ∈ D.V := by simpa using hp 1
  rw [PathClass.basedLoop_comparison D.basedSection
      (Path.Homotopic.Quotient.mk (D.pathV x hx))
      (Path.Homotopic.Quotient.mk (D.pathV y hy))
      (Path.Homotopic.Quotient.mk p) (D.pathV_trans hx hy p hp)]
  exact H.mul_mem (H.inv_mem (D.comparisonV_mem H hH hy)) (D.comparisonV_mem H hH hx)

/-- A subgroup containing every overlap switch class is the whole fundamental group. -/
theorem subgroup_eq_top_of_switchClass_mem {X : Type*} [TopologicalSpace X]
    (D : TwoSimplyConnectedCover X) (H : Subgroup (FundamentalGroup X D.base))
    (hH : ∀ x (hxU : x ∈ D.U) (hxV : x ∈ D.V), D.switchClass x hxU hxV ∈ H) : H = ⊤ := by
  let W : Bool → Set X := fun b => if b then D.V else D.U
  have hopen : ∀ b, IsOpen (W b) := by
    intro b
    cases b
    · exact D.U.isOpen
    · exact D.V.isOpen
  have hcover : ⋃ b, W b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩
  have hall :
      ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
        PathClass.basedLoop D.basedSection q ∈ H := by
    apply PathClass.pathClass_induction_of_open_cover W hopen hcover
      (fun q => PathClass.basedLoop D.basedSection q ∈ H)
    · intro x
      rw [PathClass.basedLoop_refl]
      exact H.one_mem
    · intro x y z p q hp hq
      rw [PathClass.basedLoop_trans]
      exact H.mul_mem hq hp
    · intro b x y p hp
      cases b
      · exact D.basedLoop_mem_of_path_in_U H p (fun t => hp ⟨t, rfl⟩)
      · exact D.basedLoop_mem_of_path_in_V H hH p (fun t => hp ⟨t, rfl⟩)
  apply top_unique
  intro q _
  have hq := hall q
  have hrefl :
      (Path.Homotopic.Quotient.refl D.base).symm =
        Path.Homotopic.Quotient.refl D.base := by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  simpa only [PathClass.basedLoop, D.basedSection_base,
    Path.Homotopic.Quotient.refl_trans, hrefl,
    Path.Homotopic.Quotient.trans_refl] using hq

/-- Any paths to an overlap point through the two opens compute its switch class. -/
theorem switchClass_eq_of_paths {X : Type*} [TopologicalSpace X]
    (D : TwoSimplyConnectedCover X) {x : X} (hxU : x ∈ D.U) (hxV : x ∈ D.V)
    (p q : Path D.base x) (hp : ∀ t, p t ∈ D.U) (hq : ∀ t, q t ∈ D.V) :
    D.switchClass x hxU hxV =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.trans q.symm)) := by
  have hU : Path.Homotopic.Quotient.mk (D.pathU x hxU) = Path.Homotopic.Quotient.mk p :=
    Path.Homotopic.Quotient.eq.mpr
      (paths_homotopic_of_mem D.simplyU _ _ (D.pathU_mem x hxU) hp)
  have hV : Path.Homotopic.Quotient.mk (D.pathV x hxV) = Path.Homotopic.Quotient.mk q :=
    Path.Homotopic.Quotient.eq.mpr
      (paths_homotopic_of_mem D.simplyV _ _ (D.pathV_mem x hxV) hq)
  simp only [switchClass, hU, hV, FundamentalGroup.fromPath, FundamentalGroup.fromArrow,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]

end TwoSimplyConnectedCover

end FundamentalGroup.VanKampen
