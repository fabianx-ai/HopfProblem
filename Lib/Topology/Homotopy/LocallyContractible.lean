/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Transfer principles for local contractibility

This file proves that classical local contractibility descends along a continuous retraction,
and that strong local contractibility can be checked on open neighborhoods and descends through
a surjective local homeomorphism.
-/

@[expose] public section

noncomputable section

open Filter Function Set TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Classical local contractibility descends along a continuous retraction. -/
theorem locallyContractibleSpace_of_retract
    (i : C(X, Y)) (r : C(Y, X))
    (hri : r.comp i = ContinuousMap.id X)
    (hY : LocallyContractibleSpace Y) :
    LocallyContractibleSpace X := by
  intro x U hU
  have hrix : r (i x) = x := ContinuousMap.congr_fun hri x
  have hpre : r ⁻¹' U ∈ nhds (i x) := by
    apply r.continuous.continuousAt
    simpa only [hrix] using hU
  obtain ⟨W, hWsub, hWnhds, hWnull⟩ := hY (i x) (r ⁻¹' U) hpre
  let V : Set X := i ⁻¹' W
  have hVU : V ⊆ U := by
    intro y hy
    have hriy : r (i y) = y := ContinuousMap.congr_fun hri y
    rw [← hriy]
    exact hWsub hy
  have hVnhds : V ∈ nhds x := i.continuous.continuousAt hWnhds
  refine ⟨V, hVU, hVnhds, ?_⟩
  let iV : C(V, W) :=
    { toFun := fun y => ⟨i y.1, y.property⟩
      continuous_toFun := (i.continuous.comp continuous_subtype_val).subtype_mk _ }
  let rU : C({y : Y // y ∈ r ⁻¹' U}, U) :=
    { toFun := fun y => ⟨r y.1, y.property⟩
      continuous_toFun := (r.continuous.comp continuous_subtype_val).subtype_mk _ }
  have hnull := (hWnull.comp_left iV).comp_right rU
  have hcomp :
      rU.comp ((ContinuousMap.inclusion hWsub).comp iV) =
        ContinuousMap.inclusion hVU := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    exact ContinuousMap.congr_fun hri y.1
  rw [← hcomp]
  exact hnull

/-- A space is strongly locally contractible when every point has an open neighborhood which is
strongly locally contractible in its subspace topology. -/
theorem StronglyLocallyContractibleSpace.of_open_neighborhoods
    (h : ∀ y : Y, ∃ U : Opens Y, y ∈ U ∧ StronglyLocallyContractibleSpace U) :
    StronglyLocallyContractibleSpace Y := by
  constructor
  intro y
  rw [Filter.hasBasis_self]
  intro W hW
  obtain ⟨U, hyU, hU⟩ := h y
  let : StronglyLocallyContractibleSpace U := hU
  have hb : (nhds y).HasBasis
      (fun S : Set U => S ∈ nhds (⟨y, hyU⟩ : U) ∧ ContractibleSpace S)
      (fun S => (Subtype.val : U → Y) '' S) := by
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (⟨y, hyU⟩ : U)]
    exact (contractible_basis (⟨y, hyU⟩ : U)).map Subtype.val
  obtain ⟨S, hS, hSW⟩ := hb.mem_iff.mp hW
  have hcontract : ContractibleSpace ((Subtype.val : U → Y) '' S) :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage S).contractibleSpace_iff.mp hS.2
  exact ⟨(Subtype.val : U → Y) '' S, hb.mem_of_mem hS, hcontract, hSW⟩

/-- A surjective local homeomorphism transports strong local contractibility from its source to
its target. -/
theorem IsLocalHomeomorph.stronglyLocallyContractibleSpace_of_surjective
    [StronglyLocallyContractibleSpace X] {f : X → Y}
    (hf : IsLocalHomeomorph f) (hs : Function.Surjective f) :
    StronglyLocallyContractibleSpace Y := by
  apply StronglyLocallyContractibleSpace.of_open_neighborhoods
  intro y
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨e, hx, rfl⟩ := hf x
  refine ⟨⟨e.target, e.open_target⟩, e.map_source hx, ?_⟩
  let : StronglyLocallyContractibleSpace e.source :=
    e.open_source.stronglyLocallyContractibleSpace
  exact e.toHomeomorphSourceTarget.symm.isOpenEmbedding.stronglyLocallyContractibleSpace
