/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.LocallyFiniteRefinement
public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinkable locally finite refinements

An indexed open shrinking of a cover has the same index type, still covers the space, and has the
closure of each shrunk member contained in the corresponding original member.  Mathlib's
shrinking lemma `exists_iUnion_eq_closure_subset` supplies such a shrinking for every locally
finite open cover of a normal space (Engelking, *General Topology*, 5.1.6; Munkres, *Topology*,
§41).

Combining this with the locally finite set-cover refinement already provided by
`SetOpenCover.exists_isLocallyFinite_refinement` shows that every open cover of a paracompact
Hausdorff space has a locally finite shrinkable refinement.  The fine cover remains in the thin
set-valued refinement preorder; its shrinking retains the indexed family needed by subsequent
point-set arguments.

No Cech cochain, locally-zero-presheaf, or cohomological comparison result is developed here.
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace TopologicalSpace.OpenCover

variable {X : Type u} [TopologicalSpace X]

/-- An indexed open shrinking of `U`: the shrunk family still covers the space and the closure of
each shrunk member lies in the corresponding member of `U`. -/
structure Shrinking {ι : Type v} (U : ι → TopologicalSpace.Opens X) where
  /-- The indexed family of shrunk open sets. -/
  family : ι → TopologicalSpace.Opens X
  /-- The shrunk family still covers the whole space. -/
  isOpenCover : TopologicalSpace.IsOpenCover family
  /-- The closure of each shrunk member lies in its corresponding original member. -/
  closure_subset : ∀ i, closure (family i : Set X) ⊆ U i

namespace Shrinking

variable {ι : Type v} {U : ι → TopologicalSpace.Opens X}

/-- A shrinking is, in particular, a chosen same-index refinement of the original family. -/
def refinement (S : Shrinking U) : Refinement S.family U where
  index := id
  le i := subset_closure.trans (S.closure_subset i)

end Shrinking

/-- The shrinking lemma, packaged for indexed families of open sets.  Local finiteness supplies
the point-finiteness hypothesis in Mathlib's `exists_iUnion_eq_closure_subset`. -/
theorem exists_shrinking_of_isLocallyFinite [NormalSpace X]
    {ι : Type v} (U : ι → TopologicalSpace.Opens X)
    (hU : TopologicalSpace.IsOpenCover U)
    (hUfin : LocallyFinite fun i => (U i : Set X)) :
    Nonempty (Shrinking U) := by
  obtain ⟨V, hVcover, hVopen, hVclosure⟩ :=
    exists_iUnion_eq_closure_subset
      (u := fun i => (U i : Set X))
      (fun i => (U i).isOpen)
      (fun x => hUfin.point_finite x)
      hU.iSup_set_eq_univ
  let Vopen : ι → TopologicalSpace.Opens X := fun i => ⟨V i, hVopen i⟩
  refine ⟨{
    family := Vopen
    isOpenCover := ?_
    closure_subset := ?_
  }⟩
  · exact TopologicalSpace.IsOpenCover.of_sets hVopen hVcover
  · exact hVclosure

namespace SetOpenCover

/-- A set-valued refinement together with a same-index open shrinking of the fine cover.  The
fine cover is locally finite, while `refines` records its arrow from the original cover in the
thin refinement preorder. -/
structure ShrinkableRefinement (U : SetOpenCover X) where
  /-- The locally finite set-valued fine cover. -/
  fine : SetOpenCover X
  /-- The fine cover refines the original cover in the thin refinement preorder. -/
  refines : U ≤ fine
  /-- The fine cover is locally finite. -/
  locallyFinite : fine.IsLocallyFinite
  /-- A same-index open shrinking of the fine cover. -/
  shrinking : Shrinking fine.family

/-- Every set-valued open cover of a paracompact Hausdorff space has a locally finite
set-valued refinement together with an indexed open shrinking whose closures lie in the
corresponding fine members. -/
theorem exists_isLocallyFinite_shrinkable_refinement
    [ParacompactSpace X] [T2Space X] (U : SetOpenCover X) :
    Nonempty (ShrinkableRefinement U) := by
  obtain ⟨V, hUV, hVfin⟩ := U.exists_isLocallyFinite_refinement
  obtain ⟨S⟩ := exists_shrinking_of_isLocallyFinite V.family V.isOpenCover hVfin
  exact ⟨{
    fine := V
    refines := hUV
    locallyFinite := hVfin
    shrinking := S
  }⟩

end SetOpenCover

end TopologicalSpace.OpenCover
