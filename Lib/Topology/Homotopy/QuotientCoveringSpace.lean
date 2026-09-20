/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Elementary transfer and recognition results for covering spaces

Two standard facts about covering spaces: local path-connectedness transfers to the source of a
local homeomorphism, and a path-connected principal cover whose deck monodromy acts faithfully
on the fibre is simply connected.  The second is the recognition criterion for the universal
cover.

## References

* A. Hatcher, *Algebraic Topology*, Propositions 1.31 and 1.39
-/

@[expose] public section

noncomputable section

open Function Set Topology Filter

universe u v w

namespace IsLocalHomeomorph

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]

/-- Local path-connectedness pulls back through a local homeomorphism: if the base is locally
path-connected, so is the source. -/
theorem locallyPathConnectedSpace
    [LocallyPathConnectedSpace X] {p : E → X} (hp : IsLocalHomeomorph p) :
    LocallyPathConnectedSpace E := by
  constructor
  intro e
  obtain ⟨h, he, -⟩ := hp e
  let _ : LocallyPathConnectedSpace h.target := h.open_target.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace h.source :=
    h.toHomeomorphSourceTarget.isOpenEmbedding.locallyPathConnectedSpace
  let e' : h.source := ⟨e, he⟩
  have hb := (path_connected_basis e').map (Subtype.val : h.source → E)
  rw [h.open_source.isOpenEmbedding_subtypeVal.map_nhds_eq] at hb
  refine hb.to_hasBasis' ?_ ?_
  · intro s hs
    refine ⟨Subtype.val '' s, ⟨hb.mem_of_mem hs, ?_⟩, Subset.rfl⟩
    exact hs.2.image continuous_subtype_val
  · intro s hs
    exact hs.1

end IsLocalHomeomorph

namespace IsQuotientCoveringMap

variable {X : Type u} {E : Type v} {G : Type w}
  [TopologicalSpace X] [TopologicalSpace E]
  [Group G] [MulAction G E]
  {p : E → X}

/-- A path-connected principal cover with faithful deck monodromy is simply connected: this is
the recognition criterion for the universal cover (Hatcher, *Algebraic Topology*, Prop. 1.39). -/
theorem simplyConnectedSpace_of_fundamentalGroupToMulOpposite_injective
    (hp : IsQuotientCoveringMap p G) [PathConnectedSpace E]
    {x : X} (e : p ⁻¹' {x})
    (hinj : Injective (hp.fundamentalGroupToMulOpposite e)) :
    SimplyConnectedSpace E := by
  have he : p e.1 = x := Set.mem_singleton_iff.mp e.2
  have hmap : Injective
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he) := by
    intro γ γ' hγ
    apply hp.isCoveringMap.injective_path_homotopic_map e.1 e.1
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply] at hγ
    have hγ' := congrArg
      (fun q : Path.Homotopic.Quotient x x ↦ q.cast he he) hγ
    simpa using hγ'
  have hsub : Subsingleton (FundamentalGroup E e.1) := by
    constructor
    intro γ γ'
    apply hmap
    have hrange :
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range = ⊥ := by
      rw [← hp.ker_monodromyPerm e, ← hp.ker_fundamentalGroupToMulOpposite]
      rw [MonoidHom.ker_eq_bot_iff]
      exact hinj
    have hγ_one : FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he γ = 1 := by
      have : FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he γ ∈
          (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range :=
        ⟨γ, rfl⟩
      rw [hrange] at this
      exact this
    have hγ'_one : FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he γ' = 1 := by
      have : FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he γ' ∈
          (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range :=
        ⟨γ', rfl⟩
      rw [hrange] at this
      exact this
    exact hγ_one.trans hγ'_one.symm
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro y γ
  let b : FundamentalGroup E e.1 ≃* FundamentalGroup E y :=
    FundamentalGroup.fundamentalGroupMulEquivOfPathConnected e.1 y
  have hy : Subsingleton (FundamentalGroup E y) :=
    @Equiv.subsingleton.symm _ _ b.toEquiv hsub
  rw [← Path.Homotopic.Quotient.eq]
  exact hy.elim _ _

end IsQuotientCoveringMap
