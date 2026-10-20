/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
SPDX-License-Identifier: Apache-2.0
-/
module

public import Lib.Topology.Sheaves.Cohomology.Cech.RefinementHomotopy
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.SetTheory.Cardinal.Order

/-!
# The refinement-directed system of open covers

The open covers of a space, preordered by refinement, form a nonempty filtered category.  This
is the directed index category over which Cech cohomology is formed as a direct limit.  A cover
is presented set-sized, as a set of open subsets indexed by its subtype; an arrow points from a
coarse cover to a finer one, and the pairwise intersections of two covers give a common
refinement.

Each cover subtype is equipped noncomputably with the well-order supplied by the well-ordering
theorem.  This is only the arbitrary total order required by the normalized alternating Cech
complex; it does not order open subsets by inclusion.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.7
* G. E. Bredon, *Sheaf Theory*, III.4
-/

@[expose] public section

set_option warningAsError true
set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace TopologicalSpace.OpenCover

variable (X : Type u) [TopologicalSpace X]

/-- A set-sized open cover, represented without duplicate members and indexed by the subtype of
its set of open subsets. -/
@[ext]
structure SetOpenCover where
  /-- The set of open subsets belonging to the cover. -/
  members : Set (TopologicalSpace.Opens X)
  /-- The members cover the whole space. -/
  isOpenCover : TopologicalSpace.IsOpenCover fun U : members => U.1

namespace SetOpenCover

variable {X}

/-- The set-sized index type of a set-valued open cover. -/
abbrev Index (U : SetOpenCover X) : Type u := U.members

/-- The indexed family underlying a set-valued open cover. -/
abbrev family (U : SetOpenCover X) : U.Index → TopologicalSpace.Opens X :=
  Subtype.val

/-- The arbitrary well-order used for normalized alternating Cech cochains. -/
noncomputable instance indexLinearOrder (U : SetOpenCover X) : LinearOrder U.Index :=
  IsWellOrder.linearOrder WellOrderingRel

/-- The refinement preorder: `U ≤ V` means that the cover `V` refines the cover `U`.
The witness is truncated because arrows should remember only the existence of a refinement
function, and the induced map on Cech cohomology is independent of that choice. -/
instance instPreorder : Preorder (SetOpenCover X) where
  le U V := Nonempty (Refinement V.family U.family)
  le_refl U := ⟨Refinement.refl U.family⟩
  le_trans U V W hUV hVW := ⟨hUV.some.comp hVW.some⟩

/-- Choose a refinement function witnessing an arrow in the refinement preorder. -/
noncomputable def refinementOfLE {U V : SetOpenCover X} (h : U ≤ V) :
    Refinement V.family U.family :=
  Classical.choice h

/-- The singleton cover by the whole space. -/
def singletonTop : SetOpenCover X where
  members := {⊤}
  isOpenCover := by
    rw [TopologicalSpace.IsOpenCover]
    simp

/-- Every space carries at least one set-valued open cover, namely the singleton cover by the
whole space. -/
instance instNonempty : Nonempty (SetOpenCover X) :=
  ⟨singletonTop⟩

/-- The canonical set-valued common refinement consists of all intersections of one member from
each input cover. -/
def commonRefinement (U V : SetOpenCover X) : SetOpenCover X where
  members := Set.range fun p : U.Index × V.Index => U.family p.1 ⊓ V.family p.2
  isOpenCover := by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_unique
    intro x _
    obtain ⟨i, hxi⟩ := U.isOpenCover.exists_mem x
    obtain ⟨j, hxj⟩ := V.isOpenCover.exists_mem x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨⟨U.family i ⊓ V.family j, ⟨(i, j), rfl⟩⟩, ⟨hxi, hxj⟩⟩

/-- The common intersection cover refines its left input. -/
noncomputable def commonRefinementLeft (U V : SetOpenCover X) :
    Refinement (commonRefinement U V).family U.family where
  index W := (Classical.choose W.property).1
  le W := by
    let p := Classical.choose W.property
    have hp : U.family p.1 ⊓ V.family p.2 = W.1 := Classical.choose_spec W.property
    change W.1 ≤ U.family p.1
    exact hp ▸ inf_le_left

/-- The common intersection cover refines its right input. -/
noncomputable def commonRefinementRight (U V : SetOpenCover X) :
    Refinement (commonRefinement U V).family V.family where
  index W := (Classical.choose W.property).2
  le W := by
    let p := Classical.choose W.property
    have hp : U.family p.1 ⊓ V.family p.2 = W.1 := Classical.choose_spec W.property
    change W.1 ≤ V.family p.2
    exact hp ▸ inf_le_right

/-- Open covers ordered toward finer covers form a directed preorder. -/
instance instIsDirectedOrder : IsDirectedOrder (SetOpenCover X) where
  directed U V :=
    ⟨commonRefinement U V, ⟨commonRefinementLeft U V⟩, ⟨commonRefinementRight U V⟩⟩

/-- The refinement category of set-valued open covers is filtered. -/
instance instIsFiltered : CategoryTheory.IsFiltered (SetOpenCover X) :=
  inferInstance

end SetOpenCover

end TopologicalSpace.OpenCover
