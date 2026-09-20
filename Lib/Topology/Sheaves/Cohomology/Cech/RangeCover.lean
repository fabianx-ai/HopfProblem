/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.DirectedSystem

/-!
# Range covers and covering dimension

An indexed open cover is replaced by the set-valued cover of its distinct members. A chosen
refinement descends to this range cover, and the index-counting multiplicity bound is preserved.
Consequently, a covering-dimension bound provides low-multiplicity covers cofinal in the thin
refinement preorder of set-valued covers; this is the cofinality step behind Godement, *Topologie
algébrique et théorie des faisceaux*, II.5.12 (on a space of covering dimension at most `n`, the
covers of multiplicity at most `n + 1` are cofinal).

The chosen refinement functions witness inequalities in the preorder; they are not retained as
distinct morphism data. No separation, compactness, or sheaf-theoretic hypothesis is used.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

universe u v w

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- The set-valued open cover consisting of the distinct values of an indexed open cover. -/
def rangeCover {κ : Type v} (V : κ → TopologicalSpace.Opens X)
    (hV : TopologicalSpace.IsOpenCover V) : SetOpenCover X where
  members := Set.range V
  isOpenCover := by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro x _
    obtain ⟨k, hxk⟩ := hV.exists_mem x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨⟨V k, ⟨k, rfl⟩⟩, hxk⟩

/-- A chosen refinement of an indexed cover descends to its set-valued range cover. A
representative is chosen for each distinct member of the range. This choice depends only on the
fine family, not on the coarse family or its refinement assignment. -/
noncomputable def rangeCoverRefinement {κ : Type v} {ι : Type w}
    (V : κ → TopologicalSpace.Opens X) (hV : TopologicalSpace.IsOpenCover V)
    {U : ι → TopologicalSpace.Opens X} (r : Refinement V U) :
    Refinement (rangeCover V hV).family U where
  index W := r.index (Set.rangeSplitting V W)
  le W := by
    have hW : V (Set.rangeSplitting V W) = W.1 := Set.apply_rangeSplitting V W
    change W.1 ≤ U (r.index (Set.rangeSplitting V W))
    rw [← hW]
    exact r.le _

/-- Removing repeated values from an indexed open cover preserves every index-counting
multiplicity bound. -/
theorem rangeCover_multiplicityLE {κ : Type v} (V : κ → TopologicalSpace.Opens X)
    (hV : TopologicalSpace.IsOpenCover V) {m : ℕ} (h : MultiplicityLE V m) :
    MultiplicityLE (rangeCover V hV).family m := by
  intro x s hs
  let e : (rangeCover V hV).Index ↪ κ :=
    ⟨Set.rangeSplitting V, Set.rangeSplitting_injective V⟩
  have hs' : ∀ k : s.map e, x ∈ V k := by
    intro k
    obtain ⟨W, hWs, hWk⟩ := Finset.mem_map.mp k.property
    rw [← hWk]
    change x ∈ V (Set.rangeSplitting V W)
    have hxW := hs ⟨W, hWs⟩
    change x ∈ W.1 at hxW
    rw [← Set.apply_rangeSplitting V W] at hxW
    exact hxW
  simpa using h x (s.map e) hs'

end TopologicalSpace.OpenCover.SetOpenCover

namespace HasCoveringDimensionLE

open TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-- If `X` has covering dimension at most `n`, then every set-valued open cover has a finer
set-valued cover of multiplicity at most `n + 1`. This is upper cofinality in the thin
refinement preorder: chosen refinement functions only witness its inequalities. -/
theorem exists_multiplicityLE_refinement (h : HasCoveringDimensionLE X n)
    (U : SetOpenCover X) :
    ∃ V : SetOpenCover X, U ≤ V ∧ MultiplicityLE V.family (n + 1) := by
  obtain ⟨κ, V, r, hV, hmult⟩ := h U.family U.isOpenCover
  exact ⟨SetOpenCover.rangeCover V hV,
    ⟨SetOpenCover.rangeCoverRefinement V hV r⟩,
    SetOpenCover.rangeCover_multiplicityLE V hV hmult⟩

end HasCoveringDimensionLE
