/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.RangeCover
public import Mathlib.Topology.Compactness.Paracompact

/-!
# Locally finite refinements in the set-cover preorder

On a paracompact space the locally finite open covers are cofinal in the refinement preorder.
Mathlib's `precise_refinement` gives a locally finite open refinement indexed by the original
cover; passing to the set-valued range cover removes repeated members while preserving local
finiteness and the chosen refinement.  This is the cofinality used when direct-limit Cech
cohomology is computed on locally finite covers.

## References

* J. R. Munkres, *Topology*, §41 (paracompactness)
* Mathlib's `precise_refinement` (`Mathlib/Topology/Compactness/Paracompact.lean`)
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

universe u v

namespace TopologicalSpace.OpenCover.SetOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- A set-valued open cover is locally finite when its family of underlying subsets is locally
finite. -/
def IsLocallyFinite (U : SetOpenCover X) : Prop :=
  LocallyFinite fun i : U.Index => (U.family i : Set X)

/-- Removing repeated members from an indexed open cover preserves local finiteness. -/
theorem rangeCover_isLocallyFinite {κ : Type v}
    (V : κ → TopologicalSpace.Opens X) (hV : TopologicalSpace.IsOpenCover V)
    (hVfin : LocallyFinite fun k => (V k : Set X)) :
    (rangeCover V hV).IsLocallyFinite := by
  change LocallyFinite fun W : Set.range V => (W.1 : Set X)
  convert hVfin.comp_injective (Set.rangeSplitting_injective V) using 1
  funext W
  exact congrArg ((↑) : TopologicalSpace.Opens X → Set X)
    (Set.apply_rangeSplitting V W).symm

/-- On a paracompact space, every set-valued open cover has a finer locally finite set-valued
open cover. This is upper cofinality in the thin refinement preorder. -/
theorem exists_isLocallyFinite_refinement [ParacompactSpace X] (U : SetOpenCover X) :
    ∃ V : SetOpenCover X, U ≤ V ∧ V.IsLocallyFinite := by
  obtain ⟨V, hVopen, hVcover, hVfin, hVle⟩ :=
    precise_refinement (fun i : U.Index => (U.family i : Set X))
      (fun i => (U.family i).isOpen) U.isOpenCover.iSup_set_eq_univ
  let Vopen : U.Index → TopologicalSpace.Opens X := fun i => ⟨V i, hVopen i⟩
  have hVopenCover : TopologicalSpace.IsOpenCover Vopen :=
    TopologicalSpace.IsOpenCover.of_sets hVopen hVcover
  let r : Refinement Vopen U.family :=
    { index := id
      le := hVle }
  exact ⟨rangeCover Vopen hVopenCover,
    ⟨rangeCoverRefinement Vopen hVopenCover r⟩,
    rangeCover_isLocallyFinite Vopen hVopenCover hVfin⟩

end TopologicalSpace.OpenCover.SetOpenCover
